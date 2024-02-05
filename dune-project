(lang dune 3.0)
(using menhir 2.0)
(name hflmc3)
(generate_opam_files)
(version 0.1)
(source (github hopv/rethfl))
(license Apache-2.0)
(authors "katsura" "Hogeyama")
(maintainers "katsura@kb.is.s.u-tokyo.ac.jp")

(package
  (name hflmc3)
  (synopsis "A nuHFLZ solver based on refinement types")
  ; (description "A longer description")
  (depends
          (ocaml (and (>= 4.14) (< 5.0)))
          cmdliner
          (core (and (>= v0.16) (< v0.17))) ; core v.0.17 is supposed to be for Ocaml 5.0
          core_unix
          fmt
          logs
          lwt
          menhirLib
          ppx_compare
          ppx_deriving
          ;ppx_deriving_cmdliner
          ppx_let
          (ppx_sexp_conv (>= v0.16))
 ))
