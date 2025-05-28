# Kearns' matrices generator

This repository contains the implementation of the truth table method (nmatrix generator plus refinement algorithm) in Rocq ([src/forest](src/forest/)) as well as an interface in OCaml ([src/kearns](src/kearns/)).

## Requirements

To run [src/forest](src/forest/), you must have Rocq installed in your system; to run [src/kearns](src/kearns/), you must have OCaml. Alternatively, there is a binary of the interface in [bin/](bin/).

Note that the binary was compiled for Unix and uses the following tools to produce the output:

1. [LaTeX](https://www.latex-project.org/get/)
2. [Pandoc](https://pandoc.org/)
3. [Graphviz](https://graphviz.org/)

So, before using it, make sure you have those programs in your path.
