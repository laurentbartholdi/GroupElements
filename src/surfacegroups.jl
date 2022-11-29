################################################################
# almost-free groups: surface groups

const AutomatonState = Int16

"""We store the letters of the word, in -N:N, as well as the states of
the accepting automaton. Storing (β,s) means there is a letter β in
the reduced form, and the automaton is in state s after having read β.

The state of the empty word is AutomatonState(1).

Automaton[β+N+1][s] is the state reached when reading β while in state s.
If negative, it means rule number -Automaton[β+N+1][s] should be triggered.
Rules is a tuple of Pairs{LHS,RHS} of Int8 words.
Generator is a function printing a generator (Int8 in -N:N).
"""
struct RWSWord{N,Automaton,Rules,Generator} <: WordElement{RWSWord{N,Automaton,Rules,Generator}}
    x::Vector{Tuple{Int8,AutomatonState}}
end
function RWSWord{N,A,R,G}(x::Vector{<:Number}) where {N,A,R,G}
    v = RWSWord{N,A,R,G}([])
    for e=x
        @assert e≠0 && -N≤e≤N
        rmul!(v,Int8(e))
    end
    v
end
@inline letters(w::RWSWord) = (e[1] for e=w.x)

positivegenerators(T::Type{RWSWord{N,A,R,G}}) where {N,A,R,G} = [T([Int8(i)]) for i=1:N]
generators(T::Type{RWSWord{N,A,R,G}}) where {N,A,R,G} = [positivegenerators(T)...,[T([Int8(-i)]) for i=1:N]...]

Base.show(io::IO, ::Type{RWSWord{N,A,R,G}}) where {N,A,R,G} = print(io,"RWSWord{$N,…}")

function show(io::IO,w::RWSWord{N,A,R,Generator}) where {N,A,R,Generator}
    if isone(w)
        print(io, "ϵ")
        return
    end
    for e=letters(w)
        print(io, Generator(e))
    end
end

function print(io::IO,w::RWSWord)
    print(io,"[",join([string(i) for i=letters(w)],","),"]")
end

function rmul!(w::RWSWord{N,Automaton,R},β::Int8) where {N,Automaton,R}
    @inbounds if isempty(w.x)
        push!(w.x,(β,Automaton[β+N+1][1]))
    elseif β==-w.x[end][1]
        pop!(w.x)
    else
        t = Automaton[β+N+1][w.x[end][2]]
        if t>0
            push!(w.x,(β,t))
        else
            resize!(w.x,length(w.x)+1-length(R[-t].first))
            for γ=R[-t].second rmul!(w,γ) end
        end
    end
    w
end

function lmul!(w::RWSWord{N,Automaton,R},β::Int8) where {N,Automaton,R}
    len = length(w)
    empty!(w.x) # but keep the data!
    for i=1:len
        @inbounds α = w.x[i][1]
        rmul!(w,β)
        β = α
    end
    rmul!(w,β)
end

"""Modifies the argument a in-place"""
function rmul!(a::T,b::T) where {T <: RWSWord}
    for e=b.x
        rmul!(a,e[1])
    end
    a
end

function inv(w::RWSWord)
    v = typeof(w)([])
    @inbounds for i=length(w):-1:1
        rmul!(v,-w.x[i][1])
    end
    v
end

function *(a::T,b::T) where {T <: RWSWord}
    w = copy(a)
    rmul!(w,b)
    w
end

"""Modifies the argument a in-place"""
function rdiv!(a::T,b::T) where {T <: RWSWord}
    @inbounds for i=length(b):-1:1
        rmul!(a,-b.x[i][1])
    end
    a
end

function /(a::T,b::T) where {T <: RWSWord}
    v = copy(a)
    rdiv!(v,b)
    v
end
               
function \(a::T,b::T) where {T <: RWSWord}
    v = inv(a)
    rmul!(v,b)
    v
end

function ^(a::T,b::T) where {T <: RWSWord}
    v = inv(b)
    rmul!(v,a)
    rmul!(v,b)
    v
end

function abelianization(a::RWSWord{N,A,R,G}) where {N,A,R,G}
    v = zeros(Int,N)
    @inbounds for e=letters(a)
        v[abs(e)] += sign(e)
    end
    v
end

"""Conjugate a by s"""
function conjugate(a::RWSWord{N,A,R,G}, s::Int8) where {N,A,R,G}
    v = typeof(a)([])
    rmul!(v,-s)
    rmul!(v,a)
    rmul!(v,s)
    v
end

function conjugate!(a::RWSWord{N,A,R,G}, s::Int8) where {N,A,R,G}
    length(a)==0 && return a

    lmul!(a,-s)
    rmul!(a,s)
    a
end

function lengthenconjugate(a::RWSWord, s::Int8)
    length(a) == 0 && return 0

    l = __lengthenrightmul(a,s)
    l == s && return 0

    lengthenleftmul(a,-s) + (l == 0 ? -1 : 1)
end

lengthenrightmul(a::RWSWord, s::Int8) = __lengthenrightmul(a,s) == 0 ? -1 : 1

"""Returns 0 if shortening, otherwise returns first letter that was changed after all length-preserving rewritings"""
function __lengthenrightmul(a::RWSWord{N,Automaton,Rules,G}, s::Int8) where {N,Automaton,Rules,G}
    p = length(a)

    @inbounds while p>0
        a.x[p][1] == -s && return 0
        t = Automaton[s+N+1][a.x[p][2]]
        t > 0 && return N+1 # some large number far away from generators
        p -= N-1
        s = Rules[-t].second[1]
    end
    return Int(s)
end

function lengthenleftmul(a::RWSWord{N,Automaton,Rules,G}, s::Int8) where {N,Automaton,Rules,G}
    t = AutomatonState(1)
    p = 1
    @inbounds while p≤length(a)
        a.x[p][1] == -s && return -1
        t = Automaton[s+N+1][t]
        a.x[p][2] == t && return 1
        if t<0
            s = Rules[-t].second[end]
            t = AutomatonState(1)
        else
            s = a.x[p][1]
            p += 1
        end
    end
    return 1
end

"""!!! not optimized"""
function minimalconjugate(a::RWSWord{N,Automaton,Rules,G}) where {N,Automaton,Rules,G}
    if isone(a)
        return a,a
    end

    todo = [(a,one(a))]
    m = (a,one(a))
    seen = Set{typeof(a)}()

    while !isempty(todo)
        (w,c) = pop!(todo)
        w∈seen && continue
        push!(seen,w)
        w<m[1] && (m = (w,c))
        for α::Int8=-N:N
            α==0 && continue
            if lengthenconjugate(w,α)≤0
                push!(todo,(conjugate(w,α),rmul!(copy(c),α)))
            end
        end
    end
    m
end

################################################################
# surface groups as a special case    
"""
Surface group elements in genus G are represented as free words on 2G
generators a_1,...,a_g,b_1,...,b_g.

Words are always reduced with respect to the standard (short-lex)
rewriting system for the relator [a_1,b_1]...[a_g,b_g] = 1.
"""
SurfaceRelator(G::Int) = SVector{4G}(vcat([Int8[-i,-G-i,i,G+i] for i=1:G]...))

"""
The rewriting rules of a confluent rewriting system for the surface group of genus G, or more generally the situation in which all rules are of the form u=>v where u,v is a cut of a conjugate of rel in two parts.
"""
function SimpleRules(rel)
    @assert iseven(length(rel))
    N = length(rel)÷2
    rr = vcat(rel,rel)
    r = [(rr[i+1:i+N],-rr[i+2N:-1:i+N+1]) for i=0:2N-1]
    rr = -reverse(rr)
    r = [r...,((rr[i+1:i+N],-rr[i+2N:-1:i+N+1]) for i=0:N-1)...]
    r = sort(unique([abs.(u)>abs.(v) ? u=>v : v=>u for (u,v)=r]))
    tuple((SVector{N}(u)=>SVector{N}(v) for (u,v)=r)...)
end

"""
An automaton parsing surface group elements. Really just a transition table.
It starts in state 1, and keeps track of the longest prefix of a LHS rule.
Transition to a negative state mean apply the corresponding rewrite rule.

More generally, works for any set of rules and N generators, if the set of rules is confluent.
"""
function Automaton(rules,N::Int)
    states = [Int8[]]
    statedict = Dict(Int8[]=>AutomatonState(1))
    next = Dict{Tuple{AutomatonState,Int8},AutomatonState}()

    s = AutomatonState(1)
    while s≤length(states)
        # fill in transitions from state s
        for α=-N:N
            if α==0 || (length(states[s])≥1 && α==-states[s][end])
                next[s,α] = 0
                continue
            end
            news = [states[s]...,α]
            # find maximal suffix of news that is a prefix of a rule
            for i=0:length(news), j=1:length(rules)
                suffs = news[i+1:end]
                if suffs==rules[j].first
                    next[s,α] = -j
                    break
                elseif length(rules[j].first)<length(suffs)
                    continue
                elseif suffs==rules[j].first[1:length(suffs)]
                    if haskey(statedict,suffs)
                        t = statedict[suffs]
                    else
                        push!(states,suffs)
                        t = statedict[suffs] = length(states)
                    end
                    next[s,α] = t
                    break
                end
            end
        end
        s += 1
    end
    tuple((tuple((next[s,a] for s=1:length(states))...) for a=-N:N)...)
#    LinearIndices((1:length(states),-N:N))=>tuple([next[s,α] for s=1:length(states), α=-N:N]...)
#    SMatrix{length(states),2N+1}(next[s,α] for s=1:length(states), α=-N:N) # is too slow
end

SurfaceGenerator(G) = (e::Int8)->if e>G '𝑏'*subscript_string(e-G)  elseif e>0 '𝑎'*subscript_string(e) elseif e≥-G '𝐴'*subscript_string(-e) else '𝐵'*subscript_string(-e-G) end

function SurfaceWordType(G)
    rel = SurfaceRelator(G)
    rules = SimpleRules(rel)
    RWSWord{2G,Automaton(rules,2G),rules,SurfaceGenerator(G)}
end

runtests && @testset "Surface word operations" begin
    F = SurfaceWordType(1)
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
    @test abelianization(ab) == [1,1]
    @test a*b == b*a
    @test b\a == a/b

    F2 = SurfaceWordType(2)
    @test isone(comm(F2([1]),F2([3]))*comm(F2([2]),F2([4])))
end
