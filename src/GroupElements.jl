module GroupElements

const runtests = false

using Permutations, Combinatorics, GAP, LinearAlgebra, Test, StaticArrays

import Base.one, Base.isone, Base.inv, Base.isequal, Base.isless, Base.hash, Base.copy, Base.copy!, Base.show, Base.print, Base.==, Base.*, Base.\, Base./, Base.^, Base.length, Base.convert, Base.promote_rule

include("missing.jl") # missing methods for GAP

include("constructors.jl") # general group-element constructors
export GroupElement, GapGroupElement, InvGroupElement, comm, positive, positivetype

include("freegroups.jl") # free groups
export FreeWord, abelianization, permuted, generators

include("surfacegroups.jl") # groups with rewriting system?
export SurfaceWordType

include("endomorphisms.jl") # (outer) endomorphisms and automorphisms
export Endomorphism, Automorphism, Ondomorphism, Outomorphism, FreeGroupEndomorphism, FreeGroupAutomorphism, transvection, surface_transvection, is_symplectic, surface_rotation, surface_flip, flip, permutation, inner, right_coset_iterator, left_coset_iterator, representative, sanitycheck

include("helpers.jl") # balls etc.
export action_ball, ball

end
