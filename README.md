# Cohesion

## Tight apartness in cohesive homotopy type theory

Assume crisp excluded middle and Shulman’s Axiom C1. Is every tight
apartness relation on a discrete type crisply representable? Given a
tight apartness relation on a type A, is the induced relation on ♭A decidable?

We answer both questions in the negative. Under these hypotheses, each
assertion is equivalent to excluded middle in the cohesive mode. In
particular, each fails in real cohesion.

The Agda formalization uses the native sharp modality in Agda 2.9.0.

- [Apartness README](apartness/README.md)
- [Paper (PDF)](paper/tight-apartness-and-excluded-middle.pdf)
- [Results and Agda names](apartness/README.md#results-and-agda-names)
- [Agda source](typetopology/source/gist/CohesiveApartness/index.lagda)

## Lawvere–Menni on pre-cohesion and local connectedness

Lawvere and Menni ask whether every pre-cohesive geometric morphism stays pre-cohesive on slicing. **No.** A presheaf example built from abelianization on finite groups fails local connectedness. For a **cohesive** geometric morphism between elementary toposes, the answer is **yes**. The public Lean package contains the complete counterexample. [Lawvere–Menni results](docs/lawvere-menni.md) · [Lean source and build instructions](lean/README.md)
