(lang dune 3.14)

(using menhir 3.0)

(name mrtccsl)

(generate_opam_files true)

(source
 (github PaulRaUnite/mrtccsl))

(authors "Pavlo Tokariev")

(maintainers "Pavlo Tokariev")

(license APACHE-2.0)

(documentation https://github.com/PaulRaUnite/mrtccsl)

(version 0.4-beta)

(package
 (name mrtccsl)
 (synopsis "A collection of tools implementing MRTCCSL")
 (description
  "MRTCCSL stands for Modular Real-Time Clock Constraint Specification Language. It is an extension to CCSL that is used to describe events and their relations in a system. In this project we provide simulator and partial analysis of such specifications implementing real-time and module extentions.")
 (depends
  (ocaml
   (>= 5.3.0))
  (dune :with-build)
  (menhir
   (= 20240715))
  camllib
  (apron
   (>= 0.9.15))
  bddapron
  (ppx_sexp_conv
   (and
    (>= v0.17.0)
    (< v0.18.0)))
  (uuseg
   (>= 16.0.0))
  (uutf
   (>= 1.0.3))
  (ppx_assert
   (and
    (>= v0.17.0)
    (< v0.18.0)))
  (ppx_inline_test
   (and
    (>= v0.17.0)
    (< v0.18.0)))
  (ppx_compare
   (and
    (>= v0.17.0)
    (< v0.18.0)))
  mlgmpidl
  vpl-core
  (ocamlgraph
   (= 2.2.0))
  (ocolor
   (>= 1.3.1))
  (containers
   (>= 3.0.0))
  (alcotest :with-test)
  (domainslib
   (>= 0.5))
  (sexplib0
   (and
    (>= v0.17)
    (< v0.18.0)))
  (ppx_deriving
   (>= 6.0.3))
  (owl
   (>= 1.2))
  bitvectorset
  (cmdliner
   (= 1.3.0))
  dune-build-info
  (csv (= 2.4)))
 (tags
  (simulation
   "model checking"
   "abstract interpretation"
   induction
   "real-time"
   "logical clock"
   "dsl")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
