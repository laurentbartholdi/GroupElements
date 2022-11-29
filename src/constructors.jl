################################################################
"""
Basic class structure:

GroupElement{T} contains an invertible element of type T; if T itself cannot easily compute inverses, then GroupElement{T} stores them.
    Method positive: GroupElement{T} -> T

WordElement{T} is a group-ish element describable as a word. It's defined in "freegroups.jl"

Endomorphism{N,T} stores an endomorphism of an N-generated type T

FreeWord{N} stores an element of free group on N generators

etc.
"""

"""All group-type elements have this type. The parameter T is an underlying type, by default the same"""
abstract type GroupElement{T} end
positive(x::GroupElement{T}) where T = x
positivetype(::Type{GroupElement{T}}) where T = GroupElement{T}
#convert(::Type{T},x::GroupElement{T}) where T = x
for op∈(:*,:(==),:isless)
    @eval $op(x::GroupElement{T},y::T) where T = $op(promote(x,y)...)
    @eval $op(x::T,y::GroupElement{T}) where T = $op(promote(x,y)...)
end

comm(g::GroupElement,h::GroupElement) = inv(g)*g^h

"""Default power operation"""
^(a::GroupElement, n::Int) = (n < 0 ? Base.power_by_squaring(inv(a),-n) : Base.power_by_squaring(a,n))

################################################################
"""
TrivialGroupElement{T} wraps a Julia type T into a GroupElement{T}
"""
struct TrivialGroupElement{T} <: GroupElement{T}
    elt::T
end

################################################################
"""
GapGroupElement{T} wraps a GAP object into a Julia type, which cat be converted to/from Julia type T.
"""
struct GapGroupElement{T} <: GroupElement{T}
   g::GAP.GapObj
end

GapGroupElement{T}(x::T) where T = GapGroupElement{T}(GAP.julia_to_gap(x,recursive=true))
show(io::IO, x::GapGroupElement{T}) where T = show(io, x.g)
one(x::GapGroupElement{T}) where T = GapGroupElement{T}(one(x.g))
inv(x::GapGroupElement{T}) where T = GapGroupElement{T}(inv(x.g))
*(x::GapGroupElement{T}, y::GapGroupElement{T}) where T = GapGroupElement{T}(x.g*y.g)
/(x::GapGroupElement{T}, y::GapGroupElement{T}) where T = GapGroupElement{T}(x.g/y.g)
^(x::GapGroupElement{T}, y::GapGroupElement{T}) where T = GapGroupElement{T}(x.g^y.g)
^(x::GapGroupElement{T}, n::Int) where T = GapGroupElement{T}(x.g^n)
\(x::GapGroupElement{T}, y::GapGroupElement{T}) where T = GapGroupElement{T}(x.g\y.g)
==(x::GapGroupElement{T}, y::GapGroupElement{T}) where T = x.g == y.g
isless(x::GapGroupElement{T}, y::GapGroupElement{T}) where T = GAP.Globals.LT(x.g, y.g)
hash(x::GapGroupElement{T},h::UInt) where T = hash(GAP.gap_to_julia(T,x.g),h)
GAP.gap_to_julia(::Type{GapGroupElement{T}},x) where T = GapGroupElement{T}(x)
GAP.julia_to_gap(x::GapGroupElement{T}) where T = x.g

################################################################
"""
InvGroupElement{T} wraps the Julia type T into a group-like element, by storing its inverse
"""
struct InvGroupElement{T} <: GroupElement{T}
    elt::T
    inv::T
end

InvGroupElement{T}(x::T) where T = InvGroupElement{T}(x,inv(x))
InvGroupElement{T}(x::T) where T <: AbstractMatrix{Int} = (xinv = inv(x); xinvr = round.(xinv); @assert xinv≈xinvr; InvGroupElement{T}(x,xinvr))
InvGroupElement{T}(x) where T = InvGroupElement{T}(convert(T,x))

positive(x::InvGroupElement{T}) where T = x.elt
positivetype(::Type{InvGroupElement{T}}) where T = T
convert(::Type{T},x::InvGroupElement{T}) where T = x.elt
promote_rule(::Type{T},::Type{InvGroupElement{T}}) where T = T

show(io::IO, x::InvGroupElement) = show(io, x.elt)
print(io::IO, x::InvGroupElement) = print(io, typeof(x), "(",x.elt,",",x.inv,")")

one(x::InvGroupElement{T}) where T = (o = one(x.elt); InvGroupElement{T}(o, o))
inv(x::InvGroupElement{T}) where T = InvGroupElement{T}(x.inv, x.elt)
*(x::InvGroupElement{T}, y::InvGroupElement{T}) where T = InvGroupElement{T}(x.elt*y.elt, y.inv*x.inv)
/(x::InvGroupElement{T}, y::InvGroupElement{T}) where T = InvGroupElement{T}(x.elt*y.inv, y.elt*x.inv)
/(x::T, y::InvGroupElement{T}) where T = x*y.inv
^(x::InvGroupElement{T}, y::InvGroupElement{T}) where T = InvGroupElement{T}(y.inv*x.elt*y.elt, y.inv*x.inv*y.elt)
^(x::T, y::InvGroupElement{T}) where T = y.inv*x*y.elt
^(x::InvGroupElement{T}, n::Int) where T = (n ≥ 0 ? InvGroupElement{T}(x.elt^n,x.inv^n) : InvGroupElement{T}(x.inv^(-n),x.elt^(-n)))
\(x::InvGroupElement{T}, y::InvGroupElement{T}) where T = InvGroupElement{T}(x.inv*y.elt, y.inv*x.elt)
\(x::InvGroupElement{T}, y::T) where T = x.inv*y
==(x::InvGroupElement{T},y::InvGroupElement{T}) where T = x.elt==y.elt
isone(x::InvGroupElement{T}) where T = isone(x.elt)
isless(x::InvGroupElement{T}, y::InvGroupElement{T}) where T = isless(x.elt, y.elt)
isless(x::InvGroupElement{T}, y::InvGroupElement{T}) where T <: AbstractArray = isless(x.elt[:], y.elt[:])
hash(x::InvGroupElement{T},h::UInt) where T = hash(x.elt,h)
copy(x::InvGroupElement{T}) where T = InvGroupElement{T}(copy(x.elt),copy(x.inv))
