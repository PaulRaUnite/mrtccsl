(lang dune 3.13)

(using menhir 3.0)

(name mrtccsl)

(generate_opam_files true)

(source
 (github PaulRaUnite/mrtccsl))

(authors "Pavlo Tokariev")

(maintainers "Pavlo Tokariev")

(license APACHE-2.0)

(documentation https://github.com/PaulRaUnite/mrtccsl)

(version 0.2-preview)

(package
 (name mrtccsl)
 (synopsis "A collection of tools implementing MRTCCSL")
 (description
  "MRTCCSL stands for Modular Real-Time Clock Constraint Specification Language. It is an extension to CCSL that is used to describe events and their relations in a system. In this project we provide simulator and partial analysis of such specifications implementing real-time and module extentions.")
 (depends
  (ocaml (>= 4.14.3))
  (dune :with-build)
  menhir
  camllib
  (apron (>= 0.9.15))
  bddapron
  ppx_sexp_conv
  (uuseg (>= 16.0.0))
  (uutf (>= 1.0.3))
  ppx_assert
  ppx_inline_test
  ppx_compare
  mlgmpidl
  vpl-core
  ocamlgraph
  (spectrum (>= 0.6.0))
  containers
  (odoc :with-doc)
  (odig :with-doc)
  (alcotest :with-test)
  (domainslib (>= 0.5))
  (sexplib0 (>= 0.17)))
 (tags
  (simulation "model checking" "abstract interpretation" induction "real-time" "logical clock" "dsl")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
