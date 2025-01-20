##################################
# CUDD Compilation
##################################

export BDDCompiler, compile, enable_reordering, num_nodes, dump_dot

mutable struct BDDCompiler
    mgr::CuddMgr
    roots::Set{AnyBool}
    num_uncompiled_parents::Dict{Dist{Bool}, Int}
    cache::Dict{AnyBool, CuddNode}
    level_to_flip::Dict{Integer, Flip}
    time_limit::Float64
    time_start::Float64
    cudd_limit::Int
end

function BDDCompiler()
    c = BDDCompiler(
        initialize_cudd(),
        Set{AnyBool}(),
        Dict{Dist{Bool}, Int}(),
        Dict{AnyBool, CuddNode}(),
        Dict{Integer, Any}(),
        0.0,
        0.0,
        -1,
    )
    Cudd_DisableGarbageCollection(c.mgr)
    c.cache[false] = constant(c.mgr, false)
    c.cache[true] = constant(c.mgr, true)
    finalizer(c) do x
        Cudd_Quit(x.mgr)
    end
    c
end

# It's okay if not all of these are actually actually roots (i.e. some are
# descendants of others), because including a descendant will not change the set
# of nodes that foreach_node(roots) considers.
#
# It may be problematic to add roots once we've started compiling, though.
# Currently all users of this code add all roots at the start, but if this
# changes, we need to think more about GC.
function BDDCompiler(roots)
    c = BDDCompiler()
    add_roots!(c, roots)
    c
end

function add_roots!(c::BDDCompiler, roots)
    # De-dupe
    roots = unique(setdiff(roots, c.roots))
    union!(c.roots, roots)

    # Collect flips and reference count
    flips = Vector{Flip}()
    foreach_node(roots) do node
        node isa Flip && push!(flips, node)
        for child in unique(children(node))
            get!(c.num_uncompiled_parents, child, 0)
            c.num_uncompiled_parents[child] += 1
        end
    end

    # Compile flips so variable order matches instantiation order, and save
    # levels.
    sort!(flips; by=f -> f.global_id)
    for f in unique(flips)
        haskey(c.cache, f) && continue
        n = new_var(c.mgr)
        c.cache[f] = n
        c.level_to_flip[level(n)] = f
    end    
end

function compile(c::BDDCompiler, root::AnyBool)::CuddNode
    compile(c, [root])[1]
end

function compile(c::BDDCompiler, roots::Vector{<:AnyBool})::Vector{CuddNode}
    # TODO: don't add here; maintain set of covered nodes, panic if not covered
    add_roots!(c, roots)
    [compile_existing(c, root) for root in roots]
end

struct DiceTimeoutException <: Exception
    c::BDDCompiler
end
function exception_if_timeout(c::BDDCompiler)
    if c.time_limit > 0. && time() - c.time_start > c.time_limit
        throw(DiceTimeoutException(c))
    end
end

function set_time_limit(c::BDDCompiler, time_limit::Float64, start_time::Float64)
    c.time_limit = time_limit
    c.time_start = start_time
    nothing
end

function set_cudd_limit(c::BDDCompiler)
    if c.time_limit > 0.
        elapsed = time() - c.time_start
        remaining = max(0, c.time_limit - elapsed) + 2 # 2 second wiggle room because CUDD sometimes exits earlier than it should. Worht changing this to 1.2x or something instead
        c.cudd_limit = ceil(Int, remaining * 1000) # ms
        return c.cudd_limit
    end
    nothing
end

function start_timer(c::BDDCompiler)
    if c.time_limit > 0.
        set_cudd_limit(c)
        Cudd_ResetStartTime(c.mgr)
        Cudd_SetTimeLimit(c.mgr, c.cudd_limit)
    end
    nothing
end


# function start_timer(c::BDDCompiler)
#     if c.cudd_limit > -1
#         Cudd_SetTimeLimit(c.mgr, c.cudd_limit)
#         # @assert Cudd_ReadTimeLimit(c.mgr) == c.cudd_limit
#     end
#     nothing
# end

function stop_timer(c::BDDCompiler)
    if c.cudd_limit > -1
        # @assert Cudd_ReadTimeLimit(c.mgr) == c.cudd_limit
        Cudd_UnsetTimeLimit(c.mgr)
    end
    nothing
end

function compile_existing(c::BDDCompiler, root::AnyBool)::CuddNode
    haskey(c.cache, root) && return c.cache[root]
    root ∉ c.roots && error("Can only compile roots added to BDDCompiler")

    # TODO implement shortcuts for equivalence, etc.
    function mark_as_compiled(node)
        for child in unique(children(node))
            c.num_uncompiled_parents[child] -= 1
            @assert c.num_uncompiled_parents[child] >= 0
            if c.num_uncompiled_parents[child] == 0
                Cudd_RecursiveDeref(c.mgr, c.cache[child])
            end
        end
    end
    
    fl(n::Flip) = begin
        exception_if_timeout(c)
        if !haskey(c.cache, n)
            error("flip not precompiled")
            # c.cache[n] = new_var(c.mgr)
        end
        c.cache[n]
    end

    fi(n::DistAnd, call) = begin
        exception_if_timeout(c)
        if !haskey(c.cache, n)
            call(n.x)
            call(n.y)
            # println("conjoin at $(time() - c.time_start)")
            start_timer(c)
            res = conjoin(c.mgr, c.cache[n.x], c.cache[n.y])
            stop_timer(c)
            res == C_NULL && throw(DiceTimeoutException(c))
            c.cache[n] = res
            # println("conjoin done")
            mark_as_compiled(n)
        end
        c.cache[n]
    end

    fi(n::DistOr, call) = begin
        exception_if_timeout(c)
        if !haskey(c.cache, n)
            call(n.x)
            call(n.y)
            # println("disjoin")
            start_timer(c)
            res = disjoin(c.mgr, c.cache[n.x], c.cache[n.y])
            stop_timer(c)
            res == C_NULL && throw(DiceTimeoutException(c))
            # println("disjoin done")
            c.cache[n] = res
            mark_as_compiled(n)
        end
        c.cache[n]
    end

    # TODO: is GC right with complement arcs? I think so... - Ryan
    fi(n::DistNot, call) = begin
        exception_if_timeout(c)
        if !haskey(c.cache, n)
            call(n.x)
            # println("negate")
            start_timer(c)
            res = negate(c.mgr, c.cache[n.x])
            stop_timer(c)
            # println("negate done")
            res == C_NULL && throw(DiceTimeoutException(c))
            c.cache[n] = res
            mark_as_compiled(n)
        end
        c.cache[n]
    end

    foldup(root, fl, fi, CuddNode)
end

function enable_reordering(c::BDDCompiler, reordering_type::CUDD.Cudd_ReorderingType)
    if reordering_type != CUDD.CUDD_REORDER_NONE
        Cudd_AutodynEnable(c.mgr, reordering_type)
    end
end

# Given `context`, a surrounding path condition, and a test
# returns (path condition if test, path condition if !test)
function split(c::BDDCompiler, context::CuddNode, test::AnyBool)::Tuple{CuddNode, CuddNode}
    # TODO: Think about GC
    testbdd = compile(c, test)
    ifbdd = conjoin(c.mgr, context, testbdd)
    if ifbdd === context
        context, constant(c.mgr, false)
    elseif !issat(c.mgr, ifbdd)
        constant(c.mgr, false), context
    else
        nottestbdd = negate(c.mgr, testbdd)
        elsebdd = conjoin(c.mgr, context, nottestbdd)
        ifbdd, elsebdd
    end
end

num_nodes(x; as_add=true) = begin
    c = BDDCompiler()
    bdd = compile(c, tobits(x))
    num_nodes(c, bdd; as_add)
end

num_nodes(c::BDDCompiler, xs::Vector{<:Ptr}; as_add=true) = begin
    as_add && (xs = map(x -> rref(Cudd_BddToAdd(c.mgr, x)), xs))
    Cudd_SharingSize(xs, length(xs))
end

dump_dot(x; filename, as_add=true) = begin
    c = BDDCompiler()
    bdd = compile(c, tobits(x))
    dump_dot(c, bdd, filename; as_add=true)
end

dump_dot(c::BDDCompiler, xs::Vector{<:Ptr}, filename; as_add=true) = begin
    # convert to ADDs in order to properly print terminals
    if as_add
        xs = map(x -> rref(Cudd_BddToAdd(c.mgr, x)), xs)
    end
    outfile = ccall(:fopen, Ptr{FILE}, (Cstring, Cstring), filename, "w")
    Cudd_DumpDot(c.mgr, length(xs), xs, C_NULL, C_NULL, outfile) 
    @assert ccall(:fclose, Cint, (Ptr{FILE},), outfile) == 0
    nothing
end

# function dump_dot(xs, filename)
#     xs = map(x -> rref(Cudd_BddToAdd(mgr, x.cudd_ptr)), xs)
#     outfile = ccall(:fopen, Ptr{FILE}, (Cstring, Cstring), filename, "w")
#     Cudd_DumpDot(mgr, length(xs), xs, C_NULL, C_NULL, outfile) 
#     @assert ccall(:fclose, Cint, (Ptr{FILE},), outfile) == 0
#     nothing
# end