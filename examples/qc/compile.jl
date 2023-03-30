# Contain ugly CUDD stuff/interaction with Dice compilation here.

# Returns a pair:
#   1. bdds_to_maximize: CUDD BDD nodes we want to maximize likelihood of
#   2. level_to_flip_id: map CUDD decisionvar level to corresponding flip_id
mgr = nothing
ccache = nothing
function compile_helper(bools_to_maximize::Vector{<:AnyBool}, flips::Dict{Any, Dice.Flip})
    bools_to_maximize = [x for x in bools_to_maximize if x isa Dist{Bool}]
    debug_info_ref = Ref{CuddDebugInfo}()
    pr(vcat(bools_to_maximize, collect(values(flips)))..., algo=Cudd(debug_info_ref=debug_info_ref))

    # Keep manager in scope so Cudd_Quit doesn't get called
    global mgr = debug_info_ref[].mgr
    global ccache = debug_info_ref[].ccache

    bdds_to_maximize = [ccache[b] for b in bools_to_maximize]
    level_to_flip_id = Dict(
        level(ccache[f]) => f_id
        for (f_id, f) in flips
    )
    bdds_to_maximize, level_to_flip_id
end
