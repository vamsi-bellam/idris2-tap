# Typed, Algebraic Parser in Idris2

Unstaged implementation of the paper - [A Typed, Algebraic Approach to Parsing](https://www.cl.cam.ac.uk/~jdy22/papers/a-typed-algebraic-approach-to-parsing.pdf) by Neelakantan R. Krishnaswami and Jeremy Yallop.

## Run Tests

```sh
make test
```

## Build Docs

```sh
make docs
```

Open `build/docs/index.html` in any browser to see documentation for public API of library.

## To try out examples - Build and run executable

```sh
make build
```

Install [rlwrap](https://github.com/hanslub42/rlwrap)

```sh
rlwrap build/exec/runparser
```
