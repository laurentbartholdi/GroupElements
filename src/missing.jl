################################################################
# missing methods for Permutation
one(x::Permutation) = Permutation(length(x))
isless(x::Permutation,y::Permutation) = isless(x.data,y.data)
GAP.julia_to_gap(x::Permutation) = GAP.Globals.PermList(GAP.julia_to_gap(x.data))
GAP.gap_to_julia(::Type{Permutation},x,n) = Permutation(GAP.gap_to_julia(Vector{Int},GAP.Globals.ListPerm(x,n)))

################################################################
# missing gap_to_julia methods for cyclotomics
const CFloat64 = Union{ComplexF64,Float64}
convert(::Type{CFloat64},x::Int) = Float64(x)

const ROOTS_OF_UNITY = Vector{ComplexF64}[]
function GAP.gap_to_julia(::Type{CFloat64},x)
    GAP.Globals.IsInt(x) && return Float64(GAP.gap_to_julia(Int,x))
    GAP.Globals.IsRat(x) && return Float64(GAP.gap_to_julia(Rational{Int},x))
    GAP.Globals.IsCyc(x) || throw("Cyclotomic expected")
    v = GAP.gap_to_julia(Vector{GAP.Globals.IsCycInt(x) ? Int : Rational{Int}},GAP.Globals.COEFFS_CYC(x))
    n = length(v)
    if length(ROOTS_OF_UNITY) < n || isempty(ROOTS_OF_UNITY[n])
        while length(ROOTS_OF_UNITY) < n
            push!(ROOTS_OF_UNITY,[])
        end
        for i=0:n-1
            push!(ROOTS_OF_UNITY[n], exp(complex(0.0,2π*i/n)))
        end
    end
    w = v⋅ROOTS_OF_UNITY[n]
    abs(imag(w)) < 10*n*eps(Float64) ? real(w) : w
end
GAP.gap_to_julia(::Type{Float64},x) = Float64(GAP.gap_to_julia(CFloat64,x))
GAP.gap_to_julia(::Type{ComplexF64},x) = ComplexF64(GAP.gap_to_julia(CFloat64,x))
