# MRTCCSL

The project consists of the following tools:
- [x] simulator that outputs traces
    - status: works
    - implements all constraints of MRTCCSL
    - uses automata with state implemented in OCaml itself (i.e. non-symbolic)
    - can use several predefined strategies:
        - with at most step
        - at least step
        - random
- [x] analyzer of the real-time and asynchronous fragment by using constraint programming (polyhedra) and k-induction-like reasoning about only live schedules.
    - status: works
    - limitations:
        - uses induction thus only operates in the domain of infinite and "uniform" schedules
        - usually cannot solve for free parameters or not sufficiently constrained parameters because:
            - initial, precondition, induction step and postconditions can have different requirements to the parameters, making "more precise" check fail;
            - union of conditionals (like in fastest constraint) is not representable with the domain used (polyhedra)
        - not all constraints have proper form in denotational encoding, so underapproximation has to be used, which:
            - doesn't exist for all constraints;
            - by the nature of underaproximation, represents only specific solutions, meaning may easily fail to prove anything or requires additional constraints (see example7 in [induction test](./test/induction.ml))
- [ ] abstract interpretation:
    - [ ] finiteness of representation
    - [ ] liveness
    - [ ] inclusion testing
- [ ] text interface and build system
    - parses text version of MRTCCSL, builds the specification(s) and proof obligations for it(them), supposed to use the methods above to solve
    - not implemented

## Development
- install opam from https://opam.ocaml.org
- clone the repo with `git clone https://github.com/PaulRaUnite/mrtccsl`
- (recommended) create local switch with `opam switch create ./` (run inside the directory)
- don't forget to run `eval $(opam env)`
- run `opam install . --deps-only --with-tests --with-docs` to install *all* the dependencies
- finally, `dune build` to build and `dune runtest` to test the library.
