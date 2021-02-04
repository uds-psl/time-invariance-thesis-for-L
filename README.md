# A Mechanised Proof of the Time Invariance Thesis for the Weak Call-by-value λ-Calculus

This repository contains the code of the paper "A Mechanised Proof of the Time Invariance Thesis for the Weak Call-by-value λ-Calculus" by Yannick Forster, Fabian Kunze, Gert Smolka, and Maximilian Wuttke.

A summary of the main results can be found in [`summary.v`](theories/summary.v).

Note that this repository is a fork of the [Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability/), to which we contribute our results.

## Installation Instructions

If you can use `opam 2` on your system, you can follow the instructions here.
If you cannot use `opam 2`, you can use the `noopam` branch of this repository, which has no dependencies, but less available problems.

### Manual installation

You need `Coq 8.12.1` built on OCAML `>= 4.07.1`, the [Smpl](https://github.com/uds-psl/smpl) package, the [Equations](https://mattam82.github.io/Coq-Equations/) package, and the [MetaCoq](https://metacoq.github.io/metacoq/) package for Coq. If you are using opam 2 you can use the following commands to install the dependencies on a new switch:

```
opam switch create coq-library-undecidability 4.07.1+flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install . --deps-only
```

### Building the project

- `make all` builds the library
- `make summary.vo` compiles only the file `theories/summary.v` and its dependencies
- `make html` generates clickable coqdoc `.html` in the `website` subdirectory
- `make clean` removes all build files in `theories` and `.html` files in the `website` directory

#### Compiled interfaces

The library is compatible with Coq's compiled interfaces ([`vos`](https://coq.inria.fr/refman/practical-tools/coq-commands.html#compiled-interfaces-produced-using-vos)) for quick infrastructural access.

- `make vos` builds compiled interfaces for the library
- `make vok` checks correctness of the library 

### Troubleshooting

#### Windows

If you use Visual Studio Code on Windows 10 with Windows Subsystem for Linux (WSL), then local opam switches may cause issues.
To avoid this, you can use a non-local opam switch, i.e. `opam switch create 4.07.1+flambda`.

#### Coq version

Be careful that this branch only compiles under `Coq 8.12.1`. 
