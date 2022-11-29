################################################################
# free and almost-free groups

"""These are group-type elements that can be represented as words"""
abstract type WordElement{T} <: GroupElement{T} end

"""An enumerator of the letters in a word"""
letters(w::WordElement) = w.x

one(x::WordElement) = one(typeof(x))
one(::Type{T}) where T <: WordElement = T([])
isone(w::WordElement) = isempty(w.x)

==(a::WordElement{T},b::WordElement{T}) where T = a.x == b.x
hash(w::WordElement,h::UInt) = hash(w.x,h)
isless(a::WordElement{T},b::WordElement{T}) where T = isless((length(a.x),a.x),(length(b.x),b.x)) # shortlex

length(w::WordElement) = length(w.x)

copy(w::WordElement) = typeof(w)(copy(w.x))
copy!(dst::WordElement{T},src::WordElement{T}) where T = (copy!(dst.x,src.x); dst)

const SUBSCRIPT_DICT = Dict('0'=>'₀','1'=>'₁','2'=>'₂','3'=>'₃','4'=>'₄',
                            '5'=>'₅','6'=>'₆','7'=>'₇','8'=>'₈','9'=>'₉','-'=>'₋')

################################################################
# Free group words
"""We explore different representations for free group words.

The simplest is an array of Int8's, with 1:N representing generators and -1:-1:-N representing their inverses. Words are always reduced: no xᵢxᵢ⁻¹ may appear.
.

A more efficient representation, with N≤7, is as a UInt64 or UInt128, packing the letters in groups of 4 bits.
"""
struct FreeWord{N} <: WordElement{FreeWord{N}}
    x::Vector{Int8}
end

positivegenerators(T::Type{FreeWord{N}}) where N = [T([Int8(i)]) for i=1:N]
generators(T::Type{FreeWord{N}}) where N = [positivegenerators(T)...,[T([Int8(-i)]) for i=1:N]...]

subscript_string(i) = prod(SUBSCRIPT_DICT[c] for c∈string(i))
#subscript_string(i) = prod(SUBSCRIPT_DICT[c] for c∈string(abs(i))) * (i > 0 ? "" : "⁻¹")

show(io::IO,w::FreeWord{N}) where N = print(io, isone(w) ? "ϵ" : join((e>0 ? '𝑥' : '𝑋')*subscript_string(abs(e)) for e=w.x))

function inv(a::FreeWord{N}) where N
    c = similar(a.x)
    @inbounds for i=1:length(a) c[i] = -a.x[end+1-i] end
    FreeWord{N}(c)
end

function *(a::FreeWord{N},b::FreeWord{N}) where N
    minlen = min(length(a),length(b))
    k = 0
    @inbounds while k<minlen && a.x[end-k] == -b.x[k+1] k += 1 end
    c = typeof(a.x)(undef,length(a)+length(b)-2k)
    @inbounds for i=1:length(a)-k c[i] = a.x[i] end
    @inbounds for i=k+1:length(b) c[i+length(a)-2k] = b.x[i] end
    FreeWord{N}(c)
end

function rmul!(a::FreeWord{N},β::Int8) where N
    @inbounds if length(a)>0 && a.x[end]==-β
        pop!(a.x)
    else
        push!(a.x,β)
    end
    a
end

"""Modifies the argument a in-place"""
function rmul!(a::FreeWord{N},b::FreeWord{N}) where N
    minlen = min(length(a),length(b))
    k = 0
    @inbounds while k<minlen && a.x[end-k] == -b.x[k+1] k += 1 end
    resize!(a.x,length(a)+length(b)-2k)
    @inbounds for i=k+1:length(b) a.x[i+length(a)-length(b)] = b.x[i] end
    a
end

function /(a::FreeWord{N},b::FreeWord{N}) where N
    minlen = min(length(a),length(b))
    k = 0
    @inbounds while k<minlen && a.x[end-k] == b.x[end-k] k += 1 end
    c = typeof(a.x)(undef,length(a)+length(b)-2k)
    @inbounds for i=1:length(a)-k c[i] = a.x[i] end
    @inbounds for i=1:length(b)-k c[end+1-i] = -b.x[i] end
    FreeWord{N}(c)
end

"""Modifies the argument a in-place"""
function rdiv!(a::FreeWord{N},b::FreeWord{N}) where N
    minlen = min(length(a),length(b))
    k = 0
    @inbounds while k<minlen && a.x[end-k] == b.x[end-k] k += 1 end
    resize!(a.x,length(a)+length(b)-2k)
    @inbounds for i=1:length(b)-k a.x[end+1-i] = -b.x[i] end
    a
end
               
function \(a::FreeWord{N},b::FreeWord{N}) where N
    minlen = min(length(a),length(b))
    k = 0
    @inbounds while k<minlen && a.x[k+1] == b.x[k+1] k += 1 end
    c = typeof(a.x)(undef,length(a)+length(b)-2k)
    @inbounds for i=k+1:length(a) c[length(a)+1-i] = -a.x[i] end
    @inbounds for i=k+1:length(b) c[i+length(a)-2k] = b.x[i] end
    FreeWord{N}(c)
end

function ^(a::FreeWord{N},b::FreeWord{N}) where N
    minlen = min(length(a),length(b))
    k = 0
    @inbounds while k<minlen && a.x[k+1] == b.x[k+1] k += 1 end
    l = 0
    @inbounds while l < length(b) && l+k<length(a) && a.x[end-l] == -b.x[l+1] l += 1 end
    m = length(a)-k-l # part of a that remains
    if m == 0 # a completely disappeared, cancel b[k+1:end]\b[l+1:end] with itself
        while k<length(b) && l<length(b) && b.x[k+1] == b.x[l+1] k += 1; l += 1 end
    end
    v = typeof(a.x)(undef,m+2length(b)-k-l)        
    @inbounds for i=k+1:length(b) v[length(b)+1-i] = -b.x[i] end
    @inbounds for i=k+1:length(a)-l v[i+length(b)-2k] = a.x[i] end
    @inbounds for i=l+1:length(b) v[i+m+length(b)-k-l] = b.x[i] end
    FreeWord{N}(v)
end

function ^(a::FreeWord{N},n::Int) where N
    n==0 && return FreeWord{N}([])
    n==1 && return a
    n==-1 && return inv(a)
    
    k = 0
    while 2k<length(a)-1 && a.x[k+1] == -a.x[end-k] k += 1 end
    absn = abs(n)
    c = typeof(a.x)(undef,length(a)+(absn-1)*(length(a)-2k))
    for i=1:k c[i] = a.x[i] end
    pos = k+1
    if n>0
        for _=1:absn, i=k+1:length(a)-k
            c[pos] = a.x[i]
            pos += 1
        end
    else
        for _=1:absn, i=length(a)-k:-1:k+1
            c[pos] = -a.x[i]
            pos += 1
        end
    end        
    for i=length(a)-k+1:length(a)
        c[pos] = a.x[i]
        pos += 1
    end
    FreeWord{N}(c)
end

"""Change the letters in a according to the "permutation" p.
p is actually a vector of length 2N+1, storing
[p(-N),p(1-N),...,p(-1),0,p(1),...,p(N)]
at positions 1:2N+1.
Thus permuted(FreeWord{3}([-1,2,-3]),[2,1,3,0,-3,-1,-2]) == FreeWord{3}([3,-1,2]).
This is actually a permutation only if p[2N+2-i] == -p[i].
"""
function permuted(a::FreeWord{N},p::Vector{Int8}) where N
    x = similar(a.x)
    for i=1:length(a)
        @inbounds x[i] = p[a.x[i]+N+1]
    end
    FreeWord{N}(x)
end

"""How much would a become longer if a were conjugated by s?"""
function lengthenconjugate(a::FreeWord{N}, s::Int8) where N
    length(a)==0 && return 0
    return (a.x[1]==s ? -1 : 1) + (a.x[end]==-s ? -1 : 1)
end

"""Conjugate a by s"""
function conjugate(a::FreeWord{N}, s::Int8) where N
    length(a)==0 && return a
    beginshift = (a.x[1]==s ? -1 : 1)
    endshift = (a.x[end]==-s ? -1 : 1)
    length(a)==1 && beginshift+endshift==0 && return a
    x = Vector{Int8}(undef, length(a)+beginshift+endshift)
    x[1] = -s
    x[end] = s
    for i=1+(beginshift==-1):length(a)-(endshift==-1)
        x[i+beginshift] = a.x[i]
    end
    FreeWord{N}(x)
end

"""Conjugate a by s in-place"""
function conjugate!(a::FreeWord{N}, s::Int8) where N
    length(a)==0 && return a
    if a.x[1]==s
        for i=2:length(a) a.x[i-1] = a.x[i] end
        if a.x[end]==-s
            resize!(a.x,length(a)-2)
        else
            a.x[end] = s
        end
    else
        if a.x[end]==-s
            for i=length(a):-1:2 a.x[i] = a.x[i-1] end
        else
            resize!(a.x,length(a)+2)
            a.x[end] = s
            for i=length(a)-1:-1:2 a.x[i] = a.x[i-1] end
        end
        a.x[1] = -s
    end
    a
end

"""A straightforward implementation of Duval's algorithm to find the minimal cyclic permutation of a word."""
function findminimalcyclicpermutation(arr)
    len = length(arr)
    ans = 0
    i = 1; while i≤len
        ans = i
        j = i+1
        k = i
        while j≤2len && (jj = (j > len ? j-len : j); kk = k > len ? k-len : k; arr[kk] ≤ arr[jj])
            j += 1
            k = arr[kk] < arr[jj] ? i : k+1
        end
        while i≤k i += j-k end
    end
    ans
end

"""Returns the minimal conjugate b of a, and an element that conjugates a
to b."""
function minimalconjugate(a::FreeWord{N}) where N
    if isone(a)
        return a,a
    end
    start = 1
    stop = length(a)
    while start<stop && a.x[start]==-a.x[stop]
        start += 1
        stop -= 1
    end
    m = findminimalcyclicpermutation(view(a.x,start:stop))+start-1
    v = Array{Int8}(undef,stop-start+1)
    for i=m:stop v[i-m+1] = a.x[i] end
    for i=start:m-1 v[i-start+stop-m+2] = a.x[i] end 
    typeof(a)(v), typeof(a)(a.x[1:m-1])
end

"""Find the minimal conjugate of a by a power of b, and return (that conjugate,i such that a^(b^i) is minimal)."""
function minimalconjugate(a::WordElement,b::WordElement)
    len = length(a)
    len == 0 && return 0
    binv = inv(b)
    m = (a,0)
    c = a
    i = 0; while true
        i += 1
        c = rmul!(rmul!(copy(binv),c),b)
        if length(c) > length(m[1]) || c == a
            break
        elseif c<m[1]
            m = (c,i)
        end
    end
    binv = inv(b)
    c = a
    i = 0; while true
        i -= 1
        c = rmul!(rmul!(copy(b),c),binv)
        if length(c) > length(m[1]) || c == a
            break
        elseif c<m[1]
            m = (c,i)
        end
    end
    m
end
    
function abelianization(a::FreeWord{N}) where N
    v = zeros(Int,N)
    @inbounds for e=letters(a)
        v[abs(e)] += sign(e)
    end
    v
end

ball(T::Type{FreeWord{N}},r::Int) where N = ball(generators(T),r)
    
runtests && @testset "Free word operations" begin
    F = FreeWord{10}
    a = F([1])
    b = F([2])
    ab = a*b
    ainv = inv(a)
    @test ab == F([1,2])
    @test ainv == F([-1])
    @test a/a == a\a == a*ainv == ainv*a == one(a) == F([])
    @test a^a == a
    @test ab^ab == ab
    @test ab^a == b*a
    @test a^ab == inv(b)*ab
    @test rmul!(ainv,ab) == b == ainv
    @test ab^1 == ab
    @test ab^2 == ab*ab
    @test (a^b)^10 == (a^10)^b
    @test (a^b)^-10 == (a^-10)^b
    @test abelianization(ab) == [1,1,(0 for _=3:10)...]
    @test minimalconjugate(F([-4,3,2,1,1,-3,4])) == (F([1,1,2]),F([-4,3,2]))
end

