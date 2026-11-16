# Tight apartness and excluded middle in cohesive type theory

Over crisp excluded middle, each of two principles about tight apartness is
equivalent to excluded middle in the cohesive mode. Both principles fail in
real cohesion with crisp excluded middle. The paper gives the mathematical
proofs. This guide gives their precise Agda statements and explains how native
sharp (♯) supplies the discreteness result used in the first principle.
[Paper (PDF)](../paper/tight-apartness-and-excluded-middle.pdf) ·
[LaTeX source](../paper/tight-apartness-and-excluded-middle.tex) ·
[Agda index](../typetopology/source/gist/CohesiveApartness/index.lagda)

## The problems

The problems were posed on the nLab by the prolific contributor Anonymouse.
On 24 October 2026 they read as follows.

1. Suppose a discrete cohesive type A comes with a tight apartness relation.
   Then, assuming crisp excluded middle and axiom C1, is the tight apartness
   relation on A a crisp relation?
2. Suppose a cohesive type A comes with a tight apartness relation. Then,
   assuming crisp excluded middle and axiom C1, is the tight apartness
   relation on ♭A in the cohesive mode decidable?

[The nLab problem list](https://ncatlab.org/nlab/show/open+problems+in+homotopy+type+theory)

Write **P₁** for the first statement and **P₂** for the second. In both,
the carrier A is crisp and its tight apartness relation is an ordinary
variable. P₁ also takes a crisp proof that A is ♭-discrete. A relation is
*crisply representable* if it is merely pointwise equivalent to one coming
from ♭(A → A → Ω), where Ω classifies propositions valued in the join
of the carrier and apartness-value universes.
With propositional extensionality, this says that the relation, after lifting
its values, lies merely in the image of the counit. In P₂, the relation on
♭A is the restriction along the counit ♭A → A. See Definition 2.5 and
Remark 2.6 of the paper.

## What is proved

* **Excluded middle implies both principles.** For P₁ the proof uses the
  fact that under excluded middle every tight apartness agrees pointwise
  with inequality. [TypeTopology, Apartness.Properties](https://martinescardo.github.io/TypeTopology/Apartness.Properties.html)
* **Each principle implies double-negation elimination.** P₁ uses crisp
  excluded middle in this direction. P₂ gives double-negation elimination
  directly. The construction is due to Tom de Jong, following a generalization
  of an idea of Andrew Swan. On the Booleans, define x ♯ y to mean
  P ∧ (x ≠ y). If ¬¬P holds, this is a tight apartness, and evaluating it
  at 0 and 1 recovers P. Under crisp excluded middle, P₁ also gives
  uniqueness of tight apartness on the Booleans up to pointwise equivalence.
  Remark 3.3 explains how propositional extensionality then gives a second
  proof via de Jong’s uniqueness theorem in the first universe.
  [de Jong on the construction](https://mathstodon.xyz/@de_Jong_Tom/113930642479158387)
* **Axiom C1.** Under crisp excluded middle, propositional extensionality
  and Shulman’s C1, each principle is equivalent to every pointed generator
  being 0-connected. This means each of its points is merely equal to its
  base point. The paper also treats the nLab’s single-generator formulation,
  *singly generated punctual cohesion*. If its generator (I, p) is a set,
  the criterion becomes “every point of I is equal to p” and the proof
  needs no propositional extensionality.
  [Shulman, §8.2](https://arxiv.org/abs/1509.07584v3) ·
  [nLab, axiom of punctual cohesion](https://ncatlab.org/nlab/show/axiom+of+punctual+cohesion)
* **Refutation.** A type with two distinct points from which every map to
  the Booleans is constant refutes P₂, and refutes P₁ under crisp excluded
  middle. This argument needs no C1. It applies under Shulman’s C2 and in
  particular to the real line with points 0 and 1. See Theorem 5.1 and
  Corollary 5.2.

The development takes crisp function extensionality and propositional
truncations as parameters. The implications from excluded middle hold for
arbitrary carrier and apartness-value universes. The converses,
equivalences and refutations use carriers in 𝓤₀ with values in an
arbitrary crisp universe 𝓥. The relevant logical principles concern
propositions in 𝓥. In the generator criteria, 𝓥 is the universe of
the generators. [Formal statements](../typetopology/source/gist/CohesiveApartness/TightApartness.lagda)

The paper’s independence remark has a further, semantic hypothesis. The
classical model with ♭ the identity and a singleton generator satisfies
both principles. The non-derivability argument assumes a model of real
cohesion with crisp excluded middle. The Agda development proves the
internal refutations. Remark 5.4 gives the semantic independence
argument and records the conjectural status of the intended semantics.

## Native sharp in Agda 2.9.0

1. `Flat` defines ♭, its counit and ♭-discreteness. `TightApartness`
   proves the apartness theorems, with the discreteness of the Booleans
   as an explicit hypothesis where it is used.
   [Flat](../typetopology/source/gist/CohesiveApartness/Flat.lagda) · [TightApartness](../typetopology/source/gist/CohesiveApartness/TightApartness.lagda)
2. `Sharp` defines ♯A as a record with a native `@♯` field. Its crisp
   induction rule takes a proof of C(x) for crisp x and gives a proof
   of ♯(C(x)) for arbitrary x of a crisp type. In `CrispInduction`,
   ordinary Boolean induction gives a section of the counit ♭𝟚 → 𝟚.
   Transport under ♯ and elimination at crisp elements prove the other
   inverse law, so the counit is an equivalence. The module
   also proves ♭-discreteness of ℕ and of ♭A for crisp A, and shows that
   the constructor of ♭ respects crisp identifications.
   [Sharp](../typetopology/source/gist/CohesiveApartness/Sharp.lagda) · [CrispInduction](../typetopology/source/gist/CohesiveApartness/CrispInduction.lagda)
3. `Theorems` supplies the proof `𝟚-is-♭-discrete` to the results that
   need it. The resulting statements carry a prime (′) in their Agda names.
   Checking the index checks these proofs with
   `--safe --without-K --cohesion`. The separate `FlatSplit` module
   derives the same results by crisp pattern matching with `--flat-split`.
   It remains available on Agda 2.8.0 and is checked outside the safe index.
   [Theorems](../typetopology/source/gist/CohesiveApartness/Theorems.lagda) · [FlatSplit](../typetopology/source/gist/CohesiveApartness/FlatSplit.lagda)

## Results and Agda names

The numbered results of the paper correspond to these names in the
[Agda source](../typetopology/source/gist/CohesiveApartness/). Unless noted otherwise, they are
in `TightApartness.lagda`, where results that need Bool to be ♭-discrete take
this as a hypothesis. `Theorems.lagda` restates those results without the
hypothesis, under the same names followed by ′, and so does `FlatSplit.lagda`.

- Lemma 2.1: `null-iff-maps-are-constant` (`Flat.lagda`)
- Lemma 2.4: `Swan-apartness`
- Definition 2.5: `is-crisp-relation`, and the principles P₁ and P₂ as
  `Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp` and
  `Induced-Apartnesses-On-♭-Are-Decidable`
- Remark 2.6(a), second argument: `crisp-induced-apartness-on-♭-is-decidable`
- Theorem 3.1: `EM-gives-induced-apartnesses-on-♭-are-decidable`,
  `EM-gives-tight-apartnesses-on-♭-discrete-types-are-crisp`,
  `induced-apartnesses-on-♭-are-decidable-gives-DNE`,
  `tight-apartnesses-on-♭-discrete-types-are-crisp-gives-DNE`, and the two
  equivalences ending in `-iff-EM`
- Corollary 3.2: `tight-apartnesses-on-♭-discrete-types-are-crisp-iff-EM′`
  (`Theorems.lagda` and `FlatSplit.lagda`) and
  `induced-apartnesses-on-♭-are-decidable-iff-EM`
- Remark 3.3, the route via de Jong's uniqueness theorem:
  `tight-apartnesses-on-♭-discrete-types-are-crisp-gives-DNE-via-uniqueness`
- Lemma 4.1: `Ω-is-♭-discrete-gives-EM` (`Flat.lagda`)
- Theorem 4.2: `EM-gives-generators-are-connected`,
  `generators-are-connected-gives-EM`,
  `tight-apartnesses-on-♭-discrete-types-are-crisp-iff-generators-are-connected`
  and `induced-apartnesses-on-♭-are-decidable-iff-generators-are-connected`
- Corollary 4.3, for the single-generator axiom
  `Singly-Generated-Punctual-Cohesion` of `Flat.lagda`: the two theorems
  ending in `-iff-every-point-of-I-is-p`; without the assumption that the
  generator is a set, the two ending in `-iff-I-is-connected`
- Theorem 5.1: `two-distinct-points-refute-EM`,
  `two-distinct-points-refute-that-tight-apartnesses-are-crisp` and
  `two-distinct-points-refute-that-induced-apartnesses-are-decidable`
- Corollary 5.2: `Axiom-C2-refutes-that-tight-apartnesses-are-crisp` and
  `Axiom-C2-refutes-that-induced-apartnesses-are-decidable`; for a single
  generator, `not-all-tight-apartnesses-on-♭-discrete-types-are-crisp` and
  `not-all-induced-apartnesses-on-♭-are-decidable`

## Checking

From the root of this repository, with final Agda 2.9.0 on your PATH,
run the following in a UTF-8 locale. The workflow uses the same TypeTopology
revision. The second Agda command can also be run with Agda 2.8.0 in a
fresh checkout of the same revision. [Workflow](../.github/workflows/check.yml)

```sh
git clone https://github.com/martinescardo/TypeTopology.git tt
git -C tt checkout 52ed2eb58d72a6bab0dd70480fa73e2291b08219
cp -R typetopology/source/gist/CohesiveApartness tt/source/gist/
cd tt
agda source/gist/CohesiveApartness/index.lagda
agda source/gist/CohesiveApartness/FlatSplit.lagda
```

The seven literate Agda modules are also available as one
[patch against TypeTopology](../typetopology/cohesive-apartness.patch).
They are maintained here. The pinned TypeTopology library sets
`--no-cohesion`, and its AI policy excludes submissions of AI-generated
code and prose. [TypeTopology’s policy at the pinned revision](https://github.com/martinescardo/TypeTopology/blob/52ed2eb58d72a6bab0dd70480fa73e2291b08219/AI-Policy.md)

## Authors and sources

GPT-6 Astra and Claude Opus 5.5 contributed equally to the mathematics.
Astra suggested using the de Jong–Swan construction. Opus independently
derived the results from that idea, wrote the Agda formalization and wrote
the paper starting from Astra’s draft. Astra also reviewed the
formalization. Colin Zwanziger proposed the problems to the models and
coordinated their work in October 2026.

At Colin’s request, Opus migrated the apartness development to native ♯
in November 2026. Three proofs in `TightApartness` now share the lemma
`decidable-predicates-spread`. The migration preserves the mathematical
statements and discharges the Boolean discreteness hypothesis in safe mode.

The sharp record follows the Agda manual’s example. The recursive map
ℕ → ♭ℕ and its section proof in `CrispInduction` are adapted from
agda-unimath. The retraction proof uses native ♯.
[Agda 2.9.0 manual](https://github.com/agda/agda/blob/v2.9.0/doc/user-manual/language/flat.lagda.rst) ·
[Agda notice](notices/Agda-LICENSE.txt) ·
[agda-unimath source](https://unimath.github.io/agda-unimath/modal-type-theory.flat-discrete-crisp-types.html) ·
[agda-unimath notice](notices/agda-unimath-LICENSE.md)
