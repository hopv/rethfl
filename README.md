# ReTHFL
[![CI](https://github.com/hopv/rethfl/actions/workflows/ci.yml/badge.svg)](https://github.com/hopv/rethfl/actions/workflows/ci.yml)

A nuHFL(Z) (aka higher-order CHC) solver based on refinement types.

## Install and Build

### Creating an opam switch
We use [opam](https://opam.ocaml.org/) for install and build.

If you already have opam, create a new switch for ReTHFL:

``` shell
opam switch create rethfl 4.14.1
eval $(opam env)
```
Even if you have a switch for OCaml 4.14.1 we recommend you to create a new switch to avoid dependency hell.

If this is your first time using opam, then initialize opam as follows before running the above commands:

``` shell
opam init
```

### Install
After you've set up an opam swtich, running the following command will install rethfl:

``` shell
opam pin add rethfl https://github.com/hopv/rethfl.git#master
```

### Manual build
First, clone this repository

``` shell
git clone git@github.com:hopv/rethfl.git
cd rethfl
```

and then, let opam install all packages that are needed

``` shell
opam install --deps-only .
```

Once the dependent packages have been installed, ReTHFL can be compiled by the following command:

``` shell
dune build
```

An alternative way to obtain a reproducible build is to use the lock file.
``` shell
git clone git@github.com:hopv/rethfl.git
cd rethfl
opam switch create . --deps-only --locked
dune build
```
(Note that this creates an opam switch.)

## External Dependencies
ReTHFL uses (extended) CHC solvers for constraint solving.
For most cases, the constraints are of the form of CHCs, so having CHC solvers such as [HoIce](https://github.com/hopv/hoice) or [Z3 (Spacer)](https://github.com/Z3Prover/z3) installed is enough.
The default backend is HoICE. 
For some instances (and if the users specify to do so), ReTHFL generates constraints of the form of extended CHC, and to handle these cases [PCSat](https://github.com/hiroshi-unno/coar) is needed. 
(The PCSat backend is not actively maintained, so we don't recommend users to use it.)
Another optional dependency is [Eldarica](https://github.com/uuverifiers/eldarica), which is needed for counterexample generation.

To summarize, here is the list of external dependencies

* [HoIce](https://github.com/hopv/hoice) 
* (Optional) [Z3 (Spacer)](https://github.com/Z3Prover/z3) 
* (Optional) [Eldarica](https://github.com/uuverifiers/eldarica)
* (Optional; Unmaintained) [PCSat](https://github.com/hiroshi-unno/coar) 

## How to Run

``` shell
rethfl <filename>
```

See `rethfl --help ` for more information.

If you want to run a manually built executable, run the following command instead:

``` shell
dune exec rethfl -- <filename>
```


## Type Annotation (Experimenal Feature)
ReTHFL supports semi-automated verification via user specified refinement type annotations.

### How to use

Use options `--annot <input.annot>` and `--target <CHECK_TARGET>` together with `--no-disprove`.
For example:

```
$ rethfl --no-disprove kmp.hfl --annot kmp.loop.annot --target toplevel
```

`CHECK_TARGET` must be one of the following:

- `toplevel`: Checks whether the toplevel (i.e. the main) formula is valid under the assumption that the type annotation is correct.
- `annotation`: Checks whether the type annotation is correct.

If ReTHFL returns valid for both `--target toplevel` and `--target annotation`, then it means the given formula is valid.
Since the *disprove mode is yet not implemented* for this semi-automated method, `--no-disprove` must be set. 

### Annotation file
Here is an exmalpe of an `.annot` file:
```
%TYPE

LOOP:
  (plen: int ->
  (slen: int ->
  ((i: int -> ((int -> *) -> *[(0 <= i /\ i < plen)])) ->
  ((i: int -> ((v: int -> *[(0 <= v + 1 /\ v + 1 < plen)]) -> *[(0 <= i /\ i < plen)])) ->
  ((i: int -> ((int -> *) -> *[(0 <= i /\ i < slen)])) ->
  (s: int ->
  (p: int ->
  ((int -> *) ->
  *[0<plen /\ 0<slen /\ 0<=p /\ 0<=s]))))))))
```
See `/input/annot` for further examples.
Please consult our paper [1] for the meaning of the refinement types.

LIMITATION: Currently, we only allow  **one recursively defined predicate to be annotated**.

## Papers
1. The main paper: "A New Refinement Type System for Automated νHFLZ Validity Checking". DOI: [10.1007/978-3-030-64437-6_5](https://doi.org/10.1007/978-3-030-64437-6_5)
2. "On the Relationship between Dijkstra Monads and
Higher-Order Fixpoint Logic". (To appear)
