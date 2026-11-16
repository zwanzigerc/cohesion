# Categorical cohesion in Lean

[The Lawvere–Menni guide](../docs/lawvere-menni.md) states the pre-cohesion problem, its negative answer, and the positive theorem under full cohesion. To read the checked counterexample, start with [Counterexample/Main.lean](Counterexample/Main.lean). The definition of local connectedness used there is in [Cohesion/Precohesive.lean](Cohesion/Precohesive.lean); the general Continuity axiom is in [Cohesion/Cohesive.lean](Cohesion/Cohesive.lean).

The public package also includes [lemmas on exponential comparisons and intervals](Positive.lean) and [the generic modal-form interface](ModalForm.lean). The unpublished Lean proofs of the positive Lawvere–Menni theorem and the complete ordinary countermodels below depend on elementary-topos ports whose redistribution terms remain unresolved. [Dependency and port credits](THIRD_PARTY_NOTICES.md)

## Countermodels

| Question | Verified in unpublished Lean | Public source |
| --- | --- | --- |
| Analytic Markov’s principle, Axiom T and the full fan theorem (nLab 2–3) | In ordinary sheaves on the pointless-end site, all three principles fail. The same model satisfies real cohesion, crisp excluded middle and sharp choice. The checked statement is `PointlessEnd.Chart.main`. | [Site and locale constructions](PointlessEnd.lean), including [the spatial core](PointlessEnd/SpatialCore.lean) and [Cartesian charts](PointlessEnd/CartesianCore.lean). |
| Lawvere’s Continuity axiom under real cohesion and sharp choice (Shulman §10) | In ordinary sheaves on the long-ray site, two distinct elements have the same image under the comparison for a countable power. `RealContinuity.main` constructs the witness and `ContinuityChoice.main` checks sharp choice in that model. | [Coverage, connected powers and the separating map](RealContinuity.lean). |
| The stronger choice formula (3.2) (Shulman §3.2) | In the $(2,1)$-category of groupoid-valued stacks, `StackChart.failure₁` exhibits failure of (3.2) at the chart $B\mathbb R$. In the same category, `StackChart.sharpChoice_eq_top₁` proves sharp choice (3.3) for every 0-truncated index map in every parameter context. | The stack development is local. The chart counterexample is checked. The formalization of the full model, including the universe of small sets, remains unfinished. |

The higher sheaf results have paper proofs. For analytic Markov and the fan theorem the proof enlarges the pointless-end site by Cartesian charts. For continuity it uses higher sheaves on the original long-ray site. [nLab resolutions](../docs/shulman.md#the-nlab-open-problems) · [Shulman’s questions](../docs/shulman.md#questions-raised-by-shulman)

## Build and axiom check

With [elan](https://github.com/leanprover/elan) installed, run these commands from this directory.

```sh
lake exe cache get
lake build
lake env lean ProofAudit.lean
lake env lean Counterexample/Audit.lean
```

The toolchain and mathlib revision are pinned. The audit checks declarations in the imported project namespaces against the list `propext`, `Classical.choice`, and `Quot.sound`; an unexpected axiom (including `sorryAx`) fails the check.
