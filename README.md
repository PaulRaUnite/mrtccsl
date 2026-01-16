# MRTCCSL
A toolset and a library implementing the Clock Constraint Specification Language and its stochastic, modular and real-time extensions.
Provides parsing, simulation, some symbolic analysis and behaviour debugging of the specifications.
The provided language allows to accurately model, express higher-level properties and explore temporal behaviour of real-time safety-critical systems.

The project provides the following features:
- [x] simulator (outputs correct schedules/traces satisfying the constraints)
    - implements all constraints of extensions
    - [x] state is implemented as OCaml values (i.e. non-symbolic)
    - [ ] solver on symbolic definition: in progress
    - can use several predefined strategies (not exposed in the CLI):
        - with at most step
        - at least step
        - random
- [x] analyser of the real-time and asynchronous fragment of MRTCCSL by using constraint programming (polyhedra) and k-induction-like reasoning about only live schedules.
    - limitations:
        - uses induction thus only operates in the domain of infinite and pattern repetitive schedules
        - usually cannot solve for free parameters or not sufficiently constrained parameters because:
            - initial, precondition, induction step and postconditions can have different requirements to the parameters, making "more precise" check fail;
            - union of conditionals (like in fastest constraint) is not representable with the domain used (polyhedra)
        - not all constraints have proper form in denotational encoding, so underapproximation has to be used, which:
            - doesn't exist for all constraints;
            - by the nature of underaproximation, represents only specific solutions, meaning may easily fail to prove anything or requires additional constraints (see example7 in the [induction tests](./test/induction.ml))
- [ ] abstract interpretation
    - [ ] finiteness of representation
    - [ ] liveness
    - [ ] inclusion testing
- [ ] symbolic
    - [ ] definitions of CCSL
        - [ ] core constraints
        - [ ] real-time constraints
        - [ ] stochastic constraints
    - [ ] encoding
        - [ ] BDD?
        - [ ] MTBDD?
        - [ ] polyhedra?
- [x] textual interface
    - parses text version of MRTCCSL, see [examples](./test/code/)
- [x] optimization
    - [x] constraint order optimization for faster solving
- [x] auxiliary tools
    - [x] functional chain specification and extraction from simulation traces
    - [x] histogram creation for derived reaction times of functional chains
    - [x] operations on traces
        - [x] conversion to comma-separated list
        - [x] event projection
    - [x] graph representation of the specification

## Used in
- [SDV DSL](https://github.com/jdeantoni/SoftwareDefinedVehicleModelingLanguage) as a flexible mix between event-driven simulator and behaviour explorer; provides traces and extraction of reaction time distributions

## Installation and development
- install opam from https://opam.ocaml.org
- clone the repo with `git clone https://github.com/PaulRaUnite/mrtccsl`
- (recommended) create local switch with `opam switch create ./` (run inside the directory)
- run `eval $(opam env)` (and every time before starting development)
- run `opam install . --deps-only --with-tests --with-docs` to install *all* the dependencies (add `-w` when installing development version different from the published version)
- finally, `dune build` to simply build and `dune runtest` to run the tests of the project
