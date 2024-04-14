(lang dune 3.7)

(name mrtccsl)

(generate_opam_files true)

(source
 (github PaulRaUnite/mrtccsl))

(authors "Pavlo Tokariev")

(maintainers "Pavlo Tokariev")

(license APACHE-2.0)

(documentation https://github.com/PaulRaUnite/mrtccsl)

(version 0.1)

(package
 (name mrtccsl)
 (synopsis "A collection of tools implementing MRTCCSL")
 (description
  "MRTCCSL stands for Modular Real-Time Clock Constraint Specification Language. It is an extension to CCSL which is typically used to describe events and their relations in a system. In this project we provide simulator and partial analysis of such specifications implementing this extention.")
 (depends
  ocaml
  dune
  camllib
  bddapron
  ppx_sexp_conv
  uuseg
  uutf
  ppx_assert
  ppx_inline_test
  (odoc :with-doc)
  (odig :with-doc)
  (alcotest :with-test))
 (tags
  (simulation "model checking" "abstract interpretation" induction)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
