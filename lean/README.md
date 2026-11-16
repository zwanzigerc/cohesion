# Categorical cohesion in Lean

[The Lawvere–Menni guide](../docs/lawvere-menni.md) states the pre-cohesion problem, its negative answer, and the positive theorem under full cohesion. To read the checked counterexample, start with [Counterexample/Main.lean](Counterexample/Main.lean). The definition of local connectedness used there is in [Cohesion/Precohesive.lean](Cohesion/Precohesive.lean); the general Continuity axiom is in [Cohesion/Cohesive.lean](Cohesion/Cohesive.lean).

The public package also includes lemmas on exponential comparisons and intervals and an interpretation of the modalities in terms of the four adjoints. The complete positive Lawvere–Menni proof and the assembled pointless-end and long-ray models use elementary-topos ports for which redistribution permission remains unresolved. [Positive lemmas](Positive.lean) · [Modalities](ModalForm.lean) · [Dependency and port credits](THIRD_PARTY_NOTICES.md)

## Countermodels

### The Lawvere–Menni counterexample

Abelianization gives a precohesive morphism between presheaf toposes. Lean proves that it fails local connectedness and that its Continuity comparison fails to be monic on an explicit pair of representables. The complete proof is public. [`Counterexample.counterexample_specification`](Counterexample/Main.lean) · [Lawvere–Menni question and proof](../docs/lawvere-menni.md#where-pre-cohesion-fails)

### The pointless-end model

For nLab questions 2 and 3, `PointlessEnd.Chart.main` proves in ordinary sheaves that the negations of analytic Markov’s principle, Axiom T and the full fan theorem all hold. The same model satisfies real cohesion, crisp excluded middle and sharp choice. Our higher sheaf proof enlarges the site by Cartesian charts. The public code includes the site and its spatial and Cartesian constructions. The complete ordinary proof was checked locally. [nLab 2, analytic Markov](../docs/shulman.md#2-analytic-markovs-principle) · [nLab 3, full fan theorem](../docs/shulman.md#3-the-full-fan-theorem) · [Site](PointlessEnd/Site.lean) · [Spatial core](PointlessEnd/SpatialCore.lean) · [Cartesian charts](PointlessEnd/CartesianCore.lean)

### The long-ray model

For Shulman’s §10 question, `RealContinuity.main` exhibits two distinct elements with the same image under Lawvere’s Continuity comparison for a countable power. `ContinuityChoice.main` checks real cohesion, crisp excluded middle and sharp choice in the same ordinary sheaf model. The public code includes the coverage, connected powers and separating map. The complete ordinary proof was checked locally. Our paper proof extends the counterexample to full shape in higher sheaves on the same site. [Shulman’s questions](../docs/shulman.md#questions-raised-by-shulman) · [Public Lean constructions](RealContinuity.lean)

### The stack counterexample

For Shulman’s §3.2 question, `StackChart.failure₁` exhibits a counterexample to (3.2) at the chart $B\mathbb R$ in the $(2,1)$-category of groupoid-valued stacks. In that category, `StackChart.sharpChoice_eq_top₁` proves sharp choice (3.3) for every 0-truncated index map in every parameter context. Both proofs were checked locally. The full stack formalization, including the universe of small sets, remains unfinished. Its code is unpublished. [Shulman’s questions](../docs/shulman.md#questions-raised-by-shulman)

## Build and axiom check

With [elan](https://github.com/leanprover/elan) installed, run these commands from this directory.

```sh
lake exe cache get
lake build
lake env lean ProofAudit.lean
lake env lean Counterexample/Audit.lean
```

The toolchain and mathlib revision are pinned. The audit checks declarations in the imported project namespaces against the list `propext`, `Classical.choice`, and `Quot.sound`; an unexpected axiom (including `sorryAx`) fails the check.
