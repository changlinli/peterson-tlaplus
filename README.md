# A TLA+ Specification of Peterson's Algorithm

This repository contains a TLA specification of [Peterson's
algorithm](https://en.wikipedia.org/wiki/Peterson%27s_algorithm), an algorithm
that allows multiple processes to share a single-use resource without conflict.

For a pretty-printed PDF version, see 
[https://github.com/changlinli/peterson-tlaplus/releases/download/v1.0/Peterson.pdf](https://github.com/changlinli/peterson-tlaplus/releases/download/v1.0/Peterson.pdf).

This is meant as an intermediate introduction to TLA+ users. An example is
someone who has just finished Leslie Lamport's video course on TLA+. The
specification also has a lot of comments which I hope help even non-TLA+ users
understand the intuition behind Peterson's algorithm better.

Note that I've chosen to take a loose translation of Peterson's algorithm as it
is usually presented as opposed to a strict mechanical translation of the usual
pseudo-code. The latter fits more naturally with PlusCal rather than native
TLA+. I may later wrie a PlusCal definition as well to show a more syntactically
faithful specification.

However, I hope that by being a looser translation of the spirit of Peterson's
algorithm, I've also made it clear what parts of Peterson's algorithm are truly
necessary and which are implementation details (in particular the spin locks in
the usual presentation are definitely an implementation detail that fall away in
the TLA+ specification).
