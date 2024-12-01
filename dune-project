(lang dune 3.10)
(using menhir 2.1)
(name cubtype)

(generate_opam_files true)

(source
 (github trey3p/masters-thesis))

(authors "Trey Plante")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name cubtype)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml dune)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
