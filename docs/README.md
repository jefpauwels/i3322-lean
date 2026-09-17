# Proof graph

The [graph](lean_proof_graph.pdf) gives the correspondence between the proof in
[arXiv:2608.29734v1](https://arxiv.org/abs/2608.29734v1) and the Lean declarations.
The [README](../README.md#proof-correspondence) links to the declarations.

[LaTeX source](lean_proof_graph.tex) · [SVG](lean_proof_graph.svg)

With LaTeX/TikZ and Poppler installed, the following commands reproduce the figure
from the repository root:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -cd docs/lean_proof_graph.tex
pdftocairo -svg docs/lean_proof_graph.pdf docs/lean_proof_graph.svg
```

The arrows give the dependencies of the proof. The corresponding definitions and
theorem statements are in [Statement.lean](../I3322/Statement.lean).
