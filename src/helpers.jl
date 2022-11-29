################################################################
# some helpers.

"""The ball around a set of seeds, of given radius. Generators must act, i.e. have a method ()."""
function action_ball(generators::Vector, seeds::Vector{GroupElement}, radius::Int = typemax(Int)) where GroupElement
    ball = Set(seeds)
    oldball = Set{GroupElement}()
    i = 0
    (len,oldlen) = (length(ball),0)
    while oldlen≠len && i < radius
        oldball = ball
        ball = Set(g(x) for x∈ball for g∈generators) ∪ ball
        i += 1
        (len,oldlen) = (length(ball),len)
        len÷1000≠oldlen÷1000 && @info "Ball of size at least $(len÷1000)_000"
    end
    collect(ball)
end
action_ball(generators::Vector, seed::GroupElement, radius::Int = typemax(Int)) where GroupElement = action_ball(generators, [seed], radius)

"""Ball in a group, given by symmetric generating set, optional 1 and radius"""
ball(generators::Vector{GroupElement}, radius::Int = typemax(Int), one::GroupElement = one(generators[1])) where GroupElement = action_ball([x->x*g for g∈generators], one, radius)
