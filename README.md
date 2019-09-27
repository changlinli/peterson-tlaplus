# A TLA+ Specification of Peterson's Algorithm

This repository contains a TLA specification of [Peterson's
algorithm](https://en.wikipedia.org/wiki/Peterson%27s_algorithm), an algorithm
that allows multiple processes to share a single-use resource without conflict.

Peterson's algorithm is one of the simplest mutual exclusion concurrency 
algorithms out there, but already has some potentially non-intuitive components,
e.g. understanding why a process "gives its turn away."

For a pretty-printed PDF version, see 
[https://github.com/changlinli/peterson-tlaplus/releases/download/v1.2/Peterson.pdf](https://github.com/changlinli/peterson-tlaplus/releases/download/v1.2/Peterson.pdf).

This specification may seem long, but it is largely comments, which I hope help even non-TLA+ users
understand the intuition behind Peterson's algorithm better.

Note that I've chosen to take a loose translation of Peterson's algorithm as it
is usually presented as opposed to a strict mechanical translation of the usual
pseudo-code. The latter fits more naturally with PlusCal rather than native
TLA+. I may later wrie a PlusCal definition as well to show a more syntactically
faithful specification. In the meanwhile, you can check out Leslie Lamport's 
example here: [https://lamport.azurewebsites.net/tla/peterson.html](https://lamport.azurewebsites.net/tla/peterson.html).

However, I hope that by being a looser translation of the spirit of Peterson's
algorithm, I've also made it clear what parts of Peterson's algorithm are truly
necessary and which are implementation details (in particular the spin locks in
the usual presentation are definitely an implementation detail that fall away in
the TLA+ specification).

## Model checking this specification

You will need the TLA+ Toolbox to syntactically check this specification and run
the model checker TLC against it. This specification comes with a single model
out of the box that has all its parameters already set up. Simply add
`Peterson.tla` as a new spec in the toolbox.
