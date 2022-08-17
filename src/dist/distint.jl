
export DistInt, uniform

##################################
# types, structs, and constructors
##################################

struct DistInt{W} <: Dist{Int}
    # first index is most significant bit
    bits::Vector{AnyBool}
    function DistInt{W}(b) where W
        @assert length(b) == W
        @assert W <= 63
        new{W}(b)
    end
end

DistInt(b) = DistInt{length(b)}(b)

function DistInt{W}(i::Int) where W
    @assert i >= 0
    num_b = ndigits(i, base = 2)
    bits = Vector{AnyBool}(undef, W)
    for bit_idx = W:-1:1
        bits[bit_idx] = (bit_idx > W - num_b) ? Bool(i & 1) : false
        i = i >> 1
    end
    DistInt{W}(bits)
end

##################################
# inference
##################################

tobits(x::DistInt) = 
    filter(y -> y isa Dist{Bool}, x.bits)

function frombits(x::DistInt{W}, world) where W
    v = 0
    for i = 1:W
        if frombits(x.bits[i], world)
            v += 2^(W-i)
        end
    end
    v
end

##################################
# methods
##################################

bitwidth(::DistInt{W}) where W = W

function uniform(::Type{DistInt{W}}, n = W) where W
    @assert W >= n >= 0
    DistInt{W}([i > W-n ? flip(0.5) : false for i=1:W])
end

function uniform_arith(i::Type{DistInt{W}}, start::Int, stop::Int)::DistInt{W} where W
    @assert start >= 0
    @assert stop <= 2^W
    @assert stop > start
    if start > 0
        @show start, stop, W
        DistInt{W}(start) + uniform_arith(i, 0, stop-start)
    else
        is_power_of_two = (stop) & (stop-1) == 0
        if is_power_of_two
            uniform(i, ndigits(stop, base=2)-1)
        else 
            power_lt = 2^(ndigits(stop, base=2)-1)
            ifelse(flip(power_lt/stop), uniform_arith(i, 0, power_lt), uniform_arith(i, power_lt, stop))
        end
    end
end



function uniform_ite(i::Type{DistInt{W}}, start::Int, stop::Int)::DistInt{W} where W
    @assert start >= 0
    @assert stop <= 2^W
    @assert stop > start
    # get our initial powers of two 
    upper_pow = floor(Int, log2(stop))
    lower_pow = ceil(Int, log2(start))
    # special case: start = 0 not added

    pivots = [2^p for p=lower_pow:1:upper_pow]

    low_pivot = 2^lower_pow
    while low_pivot > start
        new_pivot = low_pivot - 2^floor(Int, log2(low_pivot-start))
        prepend!(pivots, [new_pivot])
        low_pivot = new_pivot
    end
    high_pivot = 2^upper_pow
    while high_pivot < stop
        new_pivot = high_pivot + 2^floor(Int, log2(stop-high_pivot))
        append!(pivots, [new_pivot])
        high_pivot = new_pivot
    end
    @show pivots
    
    segments = []
    total_length = stop-start
    for j=1:1:length(pivots)-1
        a, b = pivots[j], pivots[j+1]
        segment_length = b-a
        segment = uniform_part(i, a, floor(Int, log2(segment_length)))
        prob = flip(segment_length/total_length)
        total_length -= segment_length
        append!(segments, [(prob, segment)])
    end
    @show segments

    len = length(segments)
    foldr(((x, y), z)->ifelse(x, y, z), segments[1:len-1],init=segments[len][2])        
end


function uniform_part(::Type{DistInt{W}}, lower, bit_length) where W 
    bits = Vector{AnyBool}(undef, W)
    num_b = ndigits(lower, base=2)
    for bit_idx = W:-1:1
        bits[bit_idx] = (bit_idx > W - num_b) ? Bool(lower & 1) : false
        lower = lower >> 1
    end

    for bit_idx = W:-1:W-bit_length+1
        bits[bit_idx] = flip(0.5)
    end
    DistInt{W}(bits)
end
##################################
# other method overloading
##################################

function prob_equals(x::DistInt{W}, y::DistInt{W}) where W
    mapreduce(prob_equals, &, x.bits, y.bits)
end

function Base.isless(x::DistInt{W}, y::DistInt{W}) where W
    foldr(zip(x.bits,y.bits); init=false) do bits, tail_isless
        xbit, ybit = bits
        (xbit < ybit) | prob_equals(xbit,ybit) & tail_isless
    end
end

function Base.:(+)(x::DistInt{W}, y::DistInt{W}) where W
    z = Vector{AnyBool}(undef, W)
    carry = false
    for i=W:-1:1
        z[i] = xor(x.bits[i], y.bits[i], carry)
        carry = atleast_two(x.bits[i], y.bits[i], carry)
    end
    carry && error("integer overflow")
    DistInt{W}(z)
end

function ifelse(cond::Dist{Bool}, then::DistInt{W}, elze::DistInt{W}) where W
    (then == elze) && return then
    bits = map(then.bits, elze.bits) do tb, eb
        ifelse(cond, tb, eb)
    end
    DistInt{W}(bits)
end
  