################################################################
# Endomorphisms
"""An endomorphism of an N-generated group is stored by the images of
the generators, represented as an N-tuple of group elements.
For example, in a free group F₄, the tuple ([1,2,-1],[1,3],[1],[4])
encodes the endomorphism of F₄ given by
        x₁↦x₁x₂x₁⁻¹, x₂↦x₁x₃, x₃↦x₁, x₄↦x₄
"""
struct Endomorphism{N,W} <: GroupElement{nothing}
    v::NTuple{N,W}
end

const FreeGroupEndomorphism{N} = Endomorphism{N,FreeWord{N}}

Endomorphism{N,W}(v::NTuple{N,Vector{Int}}) where {N,W} = Endomorphism{N,W}(ntuple(i->W(v[i]),N))
Endomorphism{N,W}(v...) where {N,W} = Endomorphism{N,W}(v)

one(::Endomorphism{N,W}) where {N,W} = one(Endomorphism{N,W})
one(::Type{Endomorphism{N,W}}) where {N,W <: WordElement} = Endomorphism{N,W}(ntuple(i->W([i]),N))

zero(::Endomorphism{N,W}) where {N,W} = zero(Endomorphism{N,W})
zero(::Type{Endomorphism{N,W}}) where {N,W <: WordElement} = Endomorphism{N,W}(ntuple(i->W([]),N))

copy(a::Endomorphism{N,W}) where {N,W} = Endomorphism{N,W}(ntuple(i->copy(a.v[i]),N))

==(a::Endomorphism{N,W},b::Endomorphism{N,W}) where {N,W} = a.v == b.v
hash(a::Endomorphism,h::UInt) = hash(a.v,h)
isless(a::Endomorphism{N,W},b::Endomorphism{N,W}) where {N,W} = isless(a.v,b.v)
function isone(a::Endomorphism{N,W}) where {N,W <: WordElement}
    for i=1:N
        l = letters(a.v[i])
        (length(l)==1 && first(l)==i) || return false
    end
    return true
end
iszero(a::Endomorphism) = all(isone,a.v)

length(a::Endomorphism) = sum(length.(a.v))

"""Endomorphism xᵢ↦xᵢxⱼ (with conventions x₋ⱼ = xⱼ⁻¹ if j<0)"""
function transvection(T::Type{Endomorphism{N,W}},i::Int,j::Int) where {N,W <: WordElement}
    @assert i≠j && 0<abs(i)≤N && 0<abs(j)≤N
    T(ntuple(k->(k == i ? W([i,j]) : (k == -i ? W([j,k]) : W([k]))),N))
end

"""Endomorphism xᵢ↦xᵢ⁻¹"""
function flip(T::Type{Endomorphism{N,W}},i::Int) where {N,W <: WordElement}
    @assert 0<i≤N
    T(ntuple(j->W([i==j ? -j : j]),N))
end

"""Endomorphism xᵢ↦xₚ₍ᵢ₎"""
function permutation(T::Type{Endomorphism{N,W}},p::Permutation) where {N,W <: WordElement}
    T(ntuple(i->W([p[i]]),N))
end

function show(io::IO,a::Endomorphism{N,W}) where {N,W}
    print(io, "⟨")
    for i=1:N show(io,a.v[i]); i==N || print(io,",") end
    print(io,"⟩")
end

function print(io::IO,a::Endomorphism{N,W}) where {N,W}
    print(io,"Endomorphism{$N,$W}(",join([string(w) for w=a.v],","),")")
end

"""Evaluation"""
function (a::Endomorphism{N,W})(w::W) where {N,W <: WordElement}
    x = one(W)
    for e=letters(w)
        if e>0
            rmul!(x,a.v[e])
        else
            rdiv!(x,a.v[-e])
        end
    end
    x
end

"""Composition in order a*b = b∘a"""
function *(a::Endomorphism{N,W},b::Endomorphism{N,W}) where {N,W}
    Endomorphism{N,W}(ntuple(i->b(a.v[i]),N))
end

function conjugate(a::Endomorphism{N,W}, s::Int8) where {N,W <: WordElement}
    Endomorphism{N,W}(ntuple(i->conjugate(a.v[i],s),N))
end

function conjugate!(a::Endomorphism{N,W}, s::Int8) where {N,W <: WordElement}
    for w=a.v conjugate!(w,s) end
    a
end

"""Return an integer matrix of the abelianization of a"""
function abelianization(a::Endomorphism{N,W}) where {N,W <: WordElement}
    m = zeros(Int,N,N)
    @inbounds for i=1:N, e=letters(a.v[i])
        m[i,abs(e)] += sign(e)
    end
    m # SMatrix{N,N}(m)
end

function inner(T::Type{Endomorphism{N,W}}, w::W) where {N,W <: WordElement}
    winv = inv(w)
    T(ntuple(i->rmul!(rmul!(copy(winv),Int8(i)),w),N))
end

sanitycheck(::Endomorphism{N,W}) where {N,W} = true
function sanitycheck(a::Endomorphism{N,W}) where {N,A,Rules,G, W <: RWSWord{N,A,Rules,G}}
    for (lhs,rhs)=Rules
        (lw,rw) = (W([]),W([]))
        for e=lhs
            e>0 ? rmul!(lw,a.v[e]) : rdiv!(lw,a.v[-e])
        end
        for e=rhs
            e>0 ? rmul!(rw,a.v[e]) : rdiv!(rw,a.v[-e])
        end
        lw==rw || return false
    end
    true
end

"""Surface rotation: aᵢ ↦ aᵢ₊₁, bᵢ ↦ bᵢ₊₁
"""
function surface_rotation(T::Type{Endomorphism{N,W}},i::Int) where {N,W}
    g = N÷2
    i = (i%g+g)%g
    T(ntuple(j->[(j≤g ? 1+((j+i-1)%g) : g+1+((j+i-1)%g))],N))
end

"""Surface flip: aᵢ ↦ b_{g+1-i}, bᵢ ↦ a_{g+1-i}
"""
function surface_flip(T::Type{Endomorphism{N,W}}) where {N,W}
    T(ntuple(j->[N+1-j],N))
end

"""Surface group transvections:
:a = aᵢ ↦ bᵢaᵢ
:b = bᵢ ↦ aᵢbᵢ
:c = aᵢ ↦ aᵢ₊₁aᵢ, bᵢ₊₁ ↦ bᵢ⁻*bᵢ₊₁
:d = aᵢ₊₁ ↦ aᵢ*aᵢ₊₁, bᵢ ↦ bᵢbᵢ₊₁⁻*
:e = aᵢ ↦ bᵢ₊₁*aᵢ, aᵢ₊₁ ↦ (aᵢ₊₁bᵢ⁻¹)*
:aa = aᵢ ↦ x\aᵢ, bᵢ ↦ bᵢ^x, aᵢ₊₁ ↦ aᵢ₊₁x with x=bᵢbᵢ₊₁^(-aᵢ₊₁)
:bb = bᵢ ↦ bᵢx, aᵢ₊₁ ↦ aᵢ₊₁^x, bᵢ₊₁ ↦ x\bᵢ₊₁ with x=aᵢ₊₁aᵢ^(-bᵢ)
"""
function surface_transvection(T::Type{Endomorphism{N,W}},s::Symbol,i::Int) where {N,W}
    g = N÷2
    1≤abs(i)≤g || error("Invalid argument to transvection, should be an integer in range ±(1:$g)")

    (aᵢ,bᵢ,aᵢ₊₁,bᵢ₊₁) = (abs(i),abs(i)+g,(abs(i)%g)+1,(abs(i)%g)+1+g)

    if s==:a
        T(ntuple(j->(j==aᵢ ? [bᵢ*sign(i),aᵢ] : [j]),N))
    elseif s==:b
        T(ntuple(j->(j==bᵢ ? [aᵢ*sign(i),bᵢ] : [j]),N))
    elseif s==:c
        if i>0
            T(ntuple(j->j==aᵢ ? [aᵢ₊₁,aᵢ] : j==bᵢ ? [aᵢ₊₁,bᵢ,-aᵢ₊₁] : j==aᵢ₊₁ ? [aᵢ₊₁,-bᵢ,aᵢ₊₁,bᵢ,-aᵢ₊₁] : j==bᵢ₊₁ ? [aᵢ₊₁,-bᵢ,-aᵢ₊₁,bᵢ₊₁] : [j],N))
        else
            T(ntuple(j->j==aᵢ ? [bᵢ,-aᵢ₊₁,-bᵢ,aᵢ] : j==bᵢ ? [bᵢ,-aᵢ₊₁,bᵢ,aᵢ₊₁,-bᵢ] : j==aᵢ₊₁ ? [bᵢ,aᵢ₊₁,-bᵢ] : j==bᵢ₊₁ ? [bᵢ,bᵢ₊₁] : [j],N))
        end
    elseif s==:d
        if i>0
            T(ntuple(j->j==bᵢ ? [bᵢ,-aᵢ₊₁,-bᵢ₊₁,aᵢ₊₁] : j==aᵢ₊₁ ? [bᵢ₊₁,aᵢ₊₁,-bᵢ,aᵢ,bᵢ,-aᵢ₊₁,-bᵢ₊₁,aᵢ₊₁] : [j],N))
        else
            T(ntuple(j->j==bᵢ ? [aᵢ,bᵢ,-aᵢ₊₁,bᵢ₊₁,aᵢ₊₁,-bᵢ,-aᵢ,bᵢ] : j==aᵢ₊₁ ? [aᵢ₊₁,-bᵢ,-aᵢ,bᵢ] : [j],N))
        end
    elseif s==:e
        if i>0
            T(ntuple(j->j==aᵢ ? [bᵢ,bᵢ₊₁,-bᵢ,aᵢ] : j==bᵢ ? [bᵢ,bᵢ₊₁,bᵢ,-bᵢ₊₁,-bᵢ] : j==aᵢ₊₁ ? [bᵢ,aᵢ₊₁,bᵢ₊₁,bᵢ,-bᵢ₊₁,-bᵢ] : j==bᵢ₊₁ ? [bᵢ,bᵢ₊₁,-bᵢ] : [j],N))
        else
            T(ntuple(j->j==aᵢ ? [-bᵢ₊₁,aᵢ] : j==bᵢ ? [-bᵢ₊₁,bᵢ,bᵢ₊₁] : j==aᵢ₊₁ ? [-bᵢ₊₁,-bᵢ,bᵢ₊₁,aᵢ₊₁,-bᵢ,-bᵢ₊₁,bᵢ,bᵢ₊₁] : j==bᵢ₊₁ ? [-bᵢ₊₁,-bᵢ,bᵢ₊₁,bᵢ,bᵢ₊₁] : [j],N))
        end
    elseif s==:aa
        if i>0
            x = [bᵢ,-aᵢ₊₁,-bᵢ₊₁,aᵢ₊₁]
            T(ntuple(j->j==aᵢ ? [-x[end:-1:1]...,aᵢ] : j==bᵢ ? [-x[end:-1:2]...,bᵢ,x[2:end]...] : j==aᵢ₊₁ ? [aᵢ₊₁,x...] : [j],N))
        else
            x = [-aᵢ₊₁,bᵢ₊₁,aᵢ₊₁,-bᵢ]
            T(ntuple(j->j==aᵢ ? [-x[end:-1:1]...,aᵢ] : j==bᵢ ? [-x[end:-1:1]...,bᵢ,x[1:end]...] : j==aᵢ₊₁ ? x[2:end] : [j],N))
        end
    elseif s==:bb
        if i>0
            x = [aᵢ₊₁,-bᵢ,-aᵢ,bᵢ]
            T(ntuple(j->j==bᵢ ? [bᵢ,x...] : j==aᵢ₊₁ ? [-x[end:-1:1]...,aᵢ₊₁,x[1:end]...] : j==bᵢ₊₁ ? [-x[end:-1:1]...,bᵢ₊₁] : [j],N))
        else
            x = [-bᵢ,aᵢ,bᵢ,-aᵢ₊₁]
            T(ntuple(j->j==bᵢ ? [bᵢ,x...] : j==aᵢ₊₁ ? [-x[end:-1:1]...,aᵢ₊₁,x[1:end]...] : j==bᵢ₊₁ ? [-x[end:-1:1]...,bᵢ₊₁] : [j],N))
        end        
    else
        error("Invalid argument $s, should be in [:a,:b,:c,:d,:e,:aa,:bb]")
    end
end

"""Is a matrix symplectic, in the standard [0 1;-1 0]⊗I basis?"""
function is_symplectic(a::Matrix)
    g = size(a,1)÷2
    M = kron([0 1; -1 0],Matrix(I,g,g))
    a'*M*a == M
end

function left_coset_iterator(T::Type{Endomorphism{N,W}}) where {N,W <: WordElement}
#    pd = Vector{Int}[]
#    for p = permutations(1:N), d = Iterators.product(ntuple(i->[-1,1],N)...)
#        push!(pd,Int8[-reverse(p.*d)...,0,(p.*d)...])
#    end
    pd::Vector{Vector{Int8}} = [[-reverse(p.*d)...,0,(p.*d)...] for p∈permutations(1:N) for d∈Iterators.product([[-1,1] for _=1:N]...)]
    
    # speed-up thanks to the fact that we act by "monomial automorphisms":
    # return x*g for all g given by perms and diags:
    # substitute letters in words of x by their g-images
    (x::Endomorphism{N,W}) -> (Endomorphism{N,W}(ntuple(i->permuted(x.v[i],p),Val(N))) for p=pd)
end

function right_coset_iterator(T::Type{Endomorphism{N,W}}) where {N,W <: WordElement}
    pd::Vector{Vector{Int}} = [(p.*d).+(N+1) for p∈permutations(1:N) for d∈Iterators.product([[-1,1] for _=1:N]...)]
    
    # speed-up thanks to the fact that we act by "monomial automorphisms":
    # return g*x for all g given by perms and diags:
    # permute and invert the words of x by the g-action
    (x::Endomorphism{N,W}) -> begin xv = Vector{W}(undef,2N+1);
        for i=1:N xv[N+1-i] = inv(x.v[i]); xv[N+1+i] = x.v[i] end        
        (Endomorphism{N,W}(ntuple(i->xv[p[i]],Val(N))) for p∈pd)
    end
end
    
runtests && @testset "Free group endomorphisms" begin
    gens = [FreeWord{4}([i]) for i=1:4]
    FGE = FreeGroupEndomorphism{4}
    ginv = inv.(gens)
    img = a->[a(g) for g=gens]
    a = one(FGE); @test img(a) == gens
    t12 = transvection(FGE,1,2)
    @test img(t12) == [gens[1]*gens[2],gens[2],gens[3],gens[4]]
    @test abelianization(t12) == [1 1 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 1]
    @test img(t12^3) == [gens[1]*gens[2]^3,gens[2],gens[3],gens[4]]
    a = transvection(FGE,1,-2);
    @test img(a) == [gens[1]/gens[2],gens[2],gens[3],gens[4]]
    a = transvection(FGE,-1,2);
    @test img(a) == [gens[2]*gens[1],gens[2],gens[3],gens[4]]
    a = transvection(FGE,-1,-2)
    @test img(a) == [gens[2]\gens[1],gens[2],gens[3],gens[4]]
    a = flip(FGE,1)
    @test img(a) == [gens[1]^-1,gens[2],gens[3],gens[4]]
    a = permutation(FGE,Permutation([2,3,1,4]))
    @test img(a) == [gens[2],gens[3],gens[1],gens[4]]
    t23 = transvection(FGE,2,3)
    @test (t12*t23)(gens[1]) == t23(t12(gens[1]))
end

################################################################
# now automorphisms. They're just endomorphisms keeping track of
# their inverse.
const Automorphism{N,W} = InvGroupElement{Endomorphism{N,W}}
const FreeGroupAutomorphism{N} = InvGroupElement{FreeGroupEndomorphism{N}}

one(::Automorphism{N,W}) where {N,W} = one(Automorphism{N,W})
one(::Type{Automorphism{N,W}}) where {N,W} = Automorphism{N,W}(one(Endomorphism{N,W}),one(Endomorphism{N,W}))

transvection(::Val{N},i,j) where N = transvection(FreeGroupAutomorphism{N},i,j)
transvection(T::Type{Automorphism{N,W}},i,j) where {N,W <: WordElement} = T(transvection(Endomorphism{N,W},i,j),transvection(Endomorphism{N,W},i,-j))

flip(::Val{N},i) where N = flip(FreeGroupAutomorphism{N},i)
flip(T::Type{Automorphism{N,W}},i) where {N,W <: WordElement} = T(flip(Endomorphism{N,W},i),flip(Endomorphism{N,W},i))

permutation(::Val{N},i,j) where N = permutation(FreeGroupAutomorphism{N},i,j)
permutation(T::Type{Automorphism{N,W}},p) where {N,W <: WordElement} = T(permutation(Endomorphism{N,W},p),permutation(Endomorphism{N,W},inv(p)))

surface_transvection(T::Type{Automorphism{N,W}},s,i) where {N,W} = T(surface_transvection(Endomorphism{N,W},s,i),surface_transvection(Endomorphism{N,W},s,-i))
surface_rotation(T::Type{Automorphism{N,W}},i) where {N,W} = T(surface_rotation(Endomorphism{N,W},i),surface_rotation(Endomorphism{N,W},-i))
surface_flip(T::Type{Automorphism{N,W}}) where {N,W} = (x = surface_flip(Endomorphism{N,W}); T(x,x))
             
sanitycheck(a::Automorphism) = sanitycheck(a.elt) && sanitycheck(a.inv) && isone(a.elt*a.inv)

abelianization(a::Automorphism) = (ab = (abelianization(a.elt),abelianization(a.inv)); InvGroupElement{typeof(ab[1])}(ab...))

is_symplectic(a::InvGroupElement) = is_symplectic(positive(a))
is_symplectic(a::Automorphism) = is_symplectic(abelianization(a))

conjugate(a::Automorphism{N,W},s::Int8) where {N,W <: WordElement} = Automorphism{N,W}(conjugate(a.elt,s),conjugate(a.inv,s))
conjugate!(a::Automorphism{N,W},s::Int8) where {N,W <: WordElement} = (conjugate!(a.elt,s); conjugate!(a.inv,s); a)
length(a::Automorphism) = length(a.elt)
inner(T::Type{Automorphism{N,W}},w::W) where {N,W} = T(inner(Endomorphism{N,W},w),inner(Endomorphism{N,W},inv(w)))
(a::Automorphism{N,W})(w::W) where {N,W <: WordElement} = a.elt(w)

runtests && @testset "Free group automorphisms" begin
    gens = [FreeWord{4}([i]) for i=1:4]
    FGA = FreeGroupAutomorphism{4}
    @test inv(transvection(FGA,1,2)) == transvection(FGA,1,-2)
    @test inv(flip(FGA,1)) == flip(FGA,1)
    @test flip(FGA,1)^permutation(FGA,Permutation([2,1,3,4])) == flip(FGA,2)
    @test isone(comm(transvection(FGA,1,2),transvection(FGA,-1,2)))
end

################################################################
# finally outer endomorphisms and automorphisms.
#
# we do this is a very special case, that in which we can conjugate by
# generators (the action of inner automorphisms) and decrease the
# length of the automorphism. Then we represent outomorphisms by their
# minimal minimal-length representative
struct Ondomorphism{T <: Endomorphism}
    r::T
    function Ondomorphism{T}(x::T) where T <: Endomorphism{N,W} where {N,W <: WordElement}
        m = minimalconjugate(x.v[1])
        if !isone(m[2])
            minv = inv(m[2])
            x = T(ntuple(i->rmul!(rmul!(copy(minv),x.v[i]),m[2]),N))
        end
        c = minimalconjugate(x.v[2],m[1])
        if c[2]==0
            return new{T}(x)
        elseif c[2]>0
            b = m[1]^c[2]
            binv = inv(b)
        else
            binv = m[1]^-c[2]
            b = inv(binv)
        end
        new{T}(T(ntuple(i->rmul!(rmul!(copy(binv),x.v[i]),b),N)))
    end
    Ondomorphism{T}(x::T,::Val{false}) where T = new{T}(x) # check=false
end
Ondomorphism(x::T) where T = Ondomorphism{T}(x)
convert(::Type{Ondomorphism{T}},x::T) where T = Ondomorphism{T}(x)

copy(a::Ondomorphism{T}) where T = Ondomorphism{T}(a.r,Val(false))
representative(x::Ondomorphism) = x.r

one(::Ondomorphism{T}) where T = one(Ondomorphism{T})
one(::Type{Ondomorphism{T}}) where T = Ondomorphism{T}(one(T))

zero(::Ondomorphism{T}) where T = zero(Ondomorphism{T})
zero(::Type{Ondomorphism{T}}) where T = Ondomorphism{T}(zero(T))

==(a::Ondomorphism{T},b::Ondomorphism{T}) where T = a.r == b.r
hash(a::Ondomorphism,h::UInt) = hash(a.r,h)
isless(a::Ondomorphism{T},b::Ondomorphism{T}) where T = isless(a.r,b.r)
isone(a::Ondomorphism) = isone(a.r)
iszero(a::Ondomorphism) = iszero(a.r)
length(a::Ondomorphism) = length(a.r)

sanitycheck(a::Ondomorphism) = sanitycheck(a.r)

function show(io::IO,a::Ondomorphism)
    repio = IOBuffer()
    show(repio,a.r)
    s = String(take!(repio))
    if s[1]=='⟨' s = s[nextind(s,1):prevind(s,end)] end
    print(io, "⟦",s,"⟧")
end

function print(io::IO,a::Ondomorphism)
    print(io,"Ondomorphism(",a.r,")")
end

*(a::Ondomorphism{T},b::Ondomorphism{T}) where T = Ondomorphism{T}(a.r*b.r)
*(a::T,b::Ondomorphism{T}) where T = Ondomorphism{T}(a*b.r)
*(a::Ondomorphism{T},b::T) where T = Ondomorphism{T}(a.r*b)
^(a::Ondomorphism,n::Int) = (n≥0 ? Base.power_by_squaring(a,n) : throw("$n should be positive in ^(::Ondomorphism,n)"))
abelianization(a::Ondomorphism) = abelianization(a.r)

surface_transvection(U::Type{Ondomorphism{T}},s,i) where T = U(surface_transvection(T,s,i))
surface_rotation(U::Type{Ondomorphism{T}},i) where T = U(surface_rotation(T,i))
surface_flip(U::Type{Ondomorphism{T}}) where T = U(surface_flip(T))
is_symplectic(a::Ondomorphism) = is_symplectic(representative(a))

runtests && @testset "Outer endomorphisms" begin
    Endo = FreeGroupEndomorphism{3}
    t = transvection(Endo,1,2)*transvection(Endo,-1,-2)
    u = transvection(Endo,3,2)*transvection(Endo,-3,-2)
    (ot,ou) = Ondomorphism.((t,u))
    @test representative(ot) == t
    @test isone(ot*ou) && isone(t*ou) && isone(ot*u)
    @test representative(one(ot)) == one(t)
end

################################################################
# outer automorphisms.
# for efficiency, only the element is minimal, the inverse is whatever it is.
# in particular, a.elt*a.inv is inner, but not necessarily trivial.
struct Outomorphism{T <: Endomorphism} <: GroupElement{Ondomorphism{T}}
    elt::Ondomorphism{T}
    inv::T
end
Outomorphism(a::Automorphism{N,W}) where {N,W} = Outomorphism{Endomorphism{N,W}}(Ondomorphism{Endomorphism{N,W}}(a.elt),a.inv)
Outomorphism(elt::T,inv::T) where T = Outomorphism{T}(Ondomorphism(elt),inv)

positive(a::Outomorphism{T}) where T = a.elt
convert(::Type{Ondomorphism{T}},x::Outomorphism{T}) where T = positive(x)
positivetype(::Type{Outomorphism{T}}) where T = Ondomorphism{T}
representative(a::Outomorphism{T}) where T = InvGroupElement{T}(representative(a.elt),a.inv)
promote_rule(::Type{Ondomorphism{T}},::Type{Outomorphism{T}}) where T = Ondomorphism{T}

one(a::Outomorphism{T}) where T = Outomorphism{T}(one(a.elt),one(a.inv))
isone(a::Outomorphism) = isone(a.elt)
hash(a::Outomorphism,h::UInt) = hash(a.elt,h)
==(a::Outomorphism{T},b::Outomorphism{T}) where T = a.elt == b.elt
isless(a::Outomorphism{T},b::Outomorphism{T}) where T = isless(a.elt,b.elt)
copy(a::Outomorphism{T}) where T = Outomorphism{T}(copy(a.elt),copy(a.inv))
show(io::IO,a::Outomorphism) = show(io,a.elt)
print(io::IO,a::Outomorphism) = print(io,"Outomorphism(",a.elt,",",a.inv,")")

abelianization(a::Outomorphism) = abelianization(representative(a))

surface_transvection(U::Type{Outomorphism{T}},s,i) where T = U(surface_transvection(T,s,i),surface_transvection(T,s,-i))
surface_rotation(U::Type{Outomorphism{T}},i) where T = U(surface_rotation(T,i),surface_rotation(T,-i))
surface_flip(U::Type{Outomorphism{T}}) where T = (x = surface_flip(T); U(x,x))

is_symplectic(a::Outomorphism) = is_symplectic(representative(a))

length(a::Outomorphism) = length(a.elt)
    
sanitycheck(a::Outomorphism) = sanitycheck(a.elt) && sanitycheck(a.inv) && isone(a.elt*a.inv)

inv(a::Outomorphism{T}) where T = Outomorphism{T}(Ondomorphism(a.inv),representative(a.elt))
*(a::Outomorphism{T},b::T) where T = a.elt*b
*(a::Union{InvGroupElement{T},Outomorphism{T}},b::Outomorphism{T}) where T = Outomorphism{T}(a.elt*b.elt,b.inv*a.inv)
*(a::Outomorphism{T},b::InvGroupElement{T}) where T = Outomorphism{T}(a.elt*b.elt,b.inv*a.inv)
*(a::T,b::Outomorphism{T}) where T = a*b.elt
/(a::Outomorphism{T},b::Outomorphism{T}) where T = Outomorphism{T}(a.elt*b.inv,representative(b.elt)*a.inv)
/(a::Ondomorphism{T},b::Outomorphism{T}) where T = a.elt*b.inv
/(a::Outomorphism{T},b::InvGroupElement{T}) where T = Outomorphism{T}(a.elt*b.inv,b.elt*a.inv)
/(a::InvGroupElement{T},b::Outomorphism{T}) where T = Outomorphism{T}(a.elt*b.inv,b.elt*a.inv)
\(a::Outomorphism{T},b::Outomorphism{T}) where T = Outomorphism{T}(a.inv*b.elt,b.inv*representative(a.elt))
\(a::Outomorphism{T},b::Ondomorphism{T}) where T = a.inv*b.elt
\(a::Outomorphism{T},b::InvGroupElement{T}) where T = Outomorphism{T}(a.inv*b.elt,b.inv*a.elt)
\(a::InvGroupElement{T},b::Outomorphism{T}) where T = Outomorphism{T}(a.inv*b.elt,b.inv*a.elt)

^(a::Outomorphism{T},b::Outomorphism{T}) where T = Outomorphism{T}(Ondomorphism{T}(b.inv*representative(a.elt)*representative(b.elt)),b.inv*a.inv*representative(b.elt))
^(a::Ondomorphism{T},b::Outomorphism{T}) where T = Ondomorphism{T}(b.inv*representative(a)*representative(b.elt))

runtests && @testset "Outer automorphisms" begin
    Endo = FreeGroupEndomorphism{3}
    Auto = FreeGroupAutomorphism{3}
    t = transvection(Auto,1,2)*transvection(Auto,-1,-2)
    u = transvection(Auto,3,2)*transvection(Auto,-3,-2)
    (ot,ou) = Outomorphism.((t,u))
    @test representative(ot) == t
    @test isone(ot*ou)
    @test representative(one(ot)) == one(t)
    @test inv(ot) == ou
    @test isone(ot*positive(ou)) && isone(positive(ou)*ot)
    @test positive(ot)*transvection(Endo,3,2)*transvection(Endo,-3,-2) == positive(one(ot))
    @test ot*transvection(Auto,3,2)*transvection(Auto,-3,-2) == one(ot)
end
