# MRTCCSL

Consists of the following tools:
- [x] simulator that outputs traces using several strategies (with at most step, at least step, random)
    - works
    - implements all constraints of MRTCCSL
    - uses automata with state implemented in OCaml itself (i.e. non-symbolic)
- [ ] analyzer of the real-time and asynchronous fragment by using constraint programming (polyhedra) and k-induction-like reasoning about only live schedules.
    - only basic structures are made
    - not implemented
- [ ] parser
    - should parse textual version of MRTCCSL
    - not implemented

## Development
- install opam from https://opam.ocaml.org
- clone the repo with `git clone https://github.com/PaulRaUnite/mrtccsl`
- (recommended) create local switch with `opam switch create ./` (run inside the directory)
- don't forget to run `eval $(opam env)`
- run `opam install . --deps-only --with-tests --with-docs` to install *all* the dependencies
- finally, `dune build` to build and `dune runtest` to test the library.
