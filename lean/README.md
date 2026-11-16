# Categorical cohesion in Lean

[The Lawvere–Menni guide](../docs/lawvere-menni.md) states the pre-cohesion problem, its negative answer, and the positive theorem under full cohesion. To read the checked counterexample, start with [Counterexample/Main.lean](Counterexample/Main.lean). The definition of local connectedness used there is in [Cohesion/Precohesive.lean](Cohesion/Precohesive.lean); the general Continuity axiom is in [Cohesion/Cohesive.lean](Cohesion/Cohesive.lean).

The component imports also expose categorical lemmas on [exponential comparisons and intervals](Positive.lean), [coverage and connected powers](RealContinuity.lean), [pointless locales and Cartesian lifts between charts](PointlessEnd.lean), and [the generic modal-form interface](ModalForm.lean). These imports do not give a complete semantic continuity countermodel or a proof of the positive Lawvere–Menni theorem in the public package: those builds require elementary-topos ports that are omitted while redistribution permission is unresolved. See the [dependency and port credits](THIRD_PARTY_NOTICES.md).

From this directory, with [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
lake env lean ProofAudit.lean
lake env lean Counterexample/Audit.lean
```

The toolchain and mathlib revision are pinned. The audit checks declarations in the imported project namespaces against the list `propext`, `Classical.choice`, and `Quot.sound`; an unexpected axiom (including `sorryAx`) fails the check.
