module TestGroupElements # essentially the same as GroupElements, with runtests = true

const runtests = true

using Permutations, Combinatorics, GAP, LinearAlgebra, Test

import Base.one, Base.inv, Base.isequal, Base.isless, Base.hash, Base.copy, Base.show, Base.==, Base.*, Base.\, Base./, Base.^, Base.length, Base.convert, Base.promote_rule

include("../src/missing.jl") # missing methods for GAP
include("../src/constructors.jl") # general group-element constructors
include("../src/freegroups.jl") # free groups and their automorphisms
include("../src/surface.jl") # free groups and their automorphisms
include("../src/endomorphisms.jl") # free groups and their automorphisms
include("../src/helpers.jl") # balls etc.

end
