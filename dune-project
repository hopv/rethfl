(lang dune 3.0)
(using menhir 2.0)
(name hflmc3)
(generate_opam_files)
(source (github hopv/rethfl))
(license Apache-2.0)
(authors "katsura" "Hogeyama")
(maintainers "katsura@kb.is.s.u-tokyo.ac.jp")

(package
  (name hflmc3)
  (synopsis "A nuHFLZ solver based on refinement types")
  ; (description "A longer description")
  (depends cmdliner
          core
          fmt
          logs
          lwt
          menhirLib
          ppx_compare
          ppx_deriving
          ppx_deriving_cmdliner
          ppx_let
          ppx_sexp_conv
 ))
