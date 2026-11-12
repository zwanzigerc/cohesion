# Tight apartness relations in cohesive type theory

Answers, with Agda formalizations, to two questions about tight apartness
relations in cohesive homotopy type theory, formerly listed as open problems
on the nLab page
[open problems in homotopy type theory](https://ncatlab.org/nlab/show/open+problems+in+homotopy+type+theory).

**Authors and AI disclosure.** The results are joint work of two AI models,
GPT-6 Astra and Claude Opus 5.5, who contributed equally to the
mathematics. The solution idea, to use a construction of Tom de Jong and
Andrew Swan, came from GPT-6 Astra. Claude Opus 5.5, an AI model made by
Anthropic, wrote the Agda code, the prose of this repository and the paper
(from a draft by GPT-6 Astra), prompted by Colin Zwanziger in a
conversation from 24 to 26 October 2026. GPT-6 Astra also reviewed the
formalization. The modules for the native sharp modality of Agda 2.9.0
(`Sharp.lagda`, `CrispInduction.lagda` and `Theorems.lagda`) were added on
11 November 2026, also by Claude Opus 5.5, prompted by Colin Zwanziger in
another conversation, in which three proofs in `TightApartness.lagda` also
became instances of one lemma, with no statement changed.

**Paper.** [Tight apartness and excluded middle in cohesive type
theory](paper/tight-apartness-and-excluded-middle.pdf) presents the
results with complete proofs.

## The problems

The problems were posed on the nLab by the prolific contributor Anonymouse.
On 24 October 2026 they read as follows.

1. Suppose a discrete cohesive type A comes with a tight apartness relation.
   Then, assuming crisp excluded middle and axiom C1, is the tight apartness
   relation on A a crisp relation?
2. Suppose a cohesive type A comes with a tight apartness relation. Then,
   assuming crisp excluded middle and axiom C1, is the tight apartness
   relation on ♭A in the cohesive mode decidable?

## Answers

Over crisp excluded middle, each statement is equivalent to excluded middle
in the cohesive mode. Both are false in real cohesion with crisp excluded
middle. So, by the models described below, crisp excluded middle and axiom
C1 don't refute the statements, and, granting the intended topos models of
real cohesion, they don't prove them either.

The proofs are in `TightApartness.lagda`. Some of them assume that Bool is
♭-discrete, which is a theorem of Shulman's type theory.
`CrispInduction.lagda` proves it from the sharp modality ♯, which Agda 2.9.0
provides natively, and `Theorems.lagda` restates, without the assumption,
every result below that uses it. `FlatSplit.lagda` does the same with Agda's
`--flat-split`, which was the only way in Agda 2.8.

- **Reading.** We formulate both statements for crisp types A, with an
  arbitrary, not necessarily crisp, tight apartness. In the first statement,
  the proof that A is ♭-discrete is also crisp. A relation is *crisp* if it
  is pointwise equivalent to one coming from ♭(A → A → Ω), where Ω is the
  type of propositions in the universe 𝓤 ⊔ 𝓥, for A in 𝓤 and apartness
  values in 𝓥. This is a property, so the existence of such a relation is
  propositionally truncated. The apartness on ♭A is the restriction along
  the counit ♭A → A. `TightApartness.lagda` discusses these choices.
- **Scope.** The results of `TightApartness.lagda`, and their restatements
  in `Theorems.lagda` and `FlatSplit.lagda`, are parameterized by crisp
  function extensionality and by propositional truncations. Excluded middle
  implies both statements for carriers and apartness values in any
  universes. The converse implications, the equivalences and the
  refutations below are formalized for carriers A in the first universe 𝓤₀,
  with apartness values in an arbitrary universe 𝓥, and excluded middle,
  crisp excluded middle and propositional extensionality are then for
  propositions in 𝓥. In the criteria for generators, 𝓥 is the universe of
  the generators.
- **Excluded middle implies both statements.** For the first, this uses
  `EM-gives-tight-apartness-is-≠` from TypeTopology's
  [`Apartness.Properties`](https://martinescardo.github.io/TypeTopology/Apartness.Properties.html).
- **Each statement implies double negation elimination**, the first assuming
  crisp excluded middle. This uses a construction of Tom de Jong, following
  a generalization of an idea of Andrew Swan
  ([Mathstodon thread](https://mathstodon.xyz/@de_Jong_Tom/113930642479158387)):
  for a proposition P, x ♯ y := P ∧ (x ≠ y) is an apartness on a type with
  decidable equality, and it is tight when ¬¬P.
- **Axiom C1.** We take Shulman's formulation
  ([arXiv:1509.07584v3](https://arxiv.org/abs/1509.07584v3), §8.2: a family
  of pointed generators) as authoritative. The problems link to the nLab page
  [axiom of punctual cohesion](https://ncatlab.org/nlab/show/axiom+of+punctual+cohesion),
  which uses a single pointed generator; we call a repaired reading of it
  *singly generated punctual cohesion*, and it is equivalent to Shulman's
  Axiom C1 with one generator.
  - Over crisp excluded middle and Shulman's Axiom C1, and assuming
    propositional extensionality, each statement holds if and only if every
    generator is 0-connected.
  - Over crisp excluded middle and singly generated punctual cohesion with
    generator (I, p), and assuming propositional extensionality, each
    statement holds if and only if I is 0-connected. If I is a set, each
    statement is equivalent to every point of I being equal to p, without
    assuming propositional extensionality.
- **Refutations.** Both statements fail as soon as some type with two
  distinct points has only constant maps to Bool (for the first statement,
  assuming crisp excluded middle). This needs no form of axiom C1. In
  particular, Shulman's Axiom C2 refutes both, as in real cohesion, whose
  generator ℝ has 0 ≠ 1.
- **Not formalized.** Both statements hold in the degenerate model in which
  ♭ is the identity, the only generator is a singleton and excluded middle
  holds. This, and the existence of models of real cohesion with crisp
  excluded middle, are model-theoretic remarks that we don't formalize.

## Files

- `typetopology/source/gist/CohesiveApartness/`: the formalization, written
  in TypeTopology's style.
  - `Flat.lagda` defines ♭, ♭-discreteness, crisp excluded middle and the
    axioms of cohesion, and `TightApartness.lagda` proves the results above.
    Like `index.lagda`, they use `--safe --without-K --cohesion`.
  - `Sharp.lagda` defines the sharp modality ♯ natively, as a record with a
    field of modality ♯, which Agda 2.9.0 allows. `CrispInduction.lagda`
    derives from it that Bool is ♭-discrete (Shulman, Theorems 6.19 and 6.21
    of arXiv version 3), following Shulman's derivation of crisp induction
    from ♯, and `Theorems.lagda` restates the main theorems without that
    assumption. All three use `--safe --without-K --cohesion`, and the index
    imports them, so checking the index checks every result in `--safe`
    mode.
  - `FlatSplit.lagda` proves that Bool is ♭-discrete instead by crisp case
    analysis, and restates the same theorems. Crisp case analysis needs
    Agda's `--flat-split`, which `--safe` mode doesn't allow together with
    `--without-K`. This was the route for Agda 2.8, which has no ♯, and it
    is kept for comparison. It is the one module that isn't `--safe`: the
    index doesn't import it, and it is checked separately.
- `typetopology/cohesive-apartness.patch`: the same folder, as a patch
  against TypeTopology.
- `paper/`: the paper, as LaTeX source and PDF.

This is not a contribution to TypeTopology: TypeTopology's `AI-Policy.md`
says that AI generated Agda code or prose won't be considered. Also,
TypeTopology's library sets `--no-cohesion`, and `--cohesion` is infective,
so TypeTopology's index files couldn't import these modules without
changes.

## Results and Agda names

The numbered results of the paper correspond to these names in
`typetopology/source/gist/CohesiveApartness/`. Unless noted otherwise, they are
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

The workflow in `.github/workflows/check.yml` type-checks the folder with
Agda 2.9.0, release candidate 3, the latest available on 11 November 2026.
The final release of 2.9.0 may differ. Agda 2.8.0 checks every module
except `Sharp.lagda`, `CrispInduction.lagda`, `Theorems.lagda` and the
index. To check by hand, with Agda 2.9.0-rc3 on your PATH, run these
commands from the directory that contains your clone of this repository:

```sh
agda --version    # release candidate 3 prints Agda version 2.9.0
git clone https://github.com/martinescardo/TypeTopology.git
cd TypeTopology
git checkout 52ed2eb58d72a6bab0dd70480fa73e2291b08219
cp -r ../cohesive-apartness/typetopology/source/gist/CohesiveApartness source/gist/
agda source/gist/CohesiveApartness/index.lagda
agda source/gist/CohesiveApartness/FlatSplit.lagda
```

If Agda stops with an encoding error, use a UTF-8 locale. The workflow sets
`LC_ALL=C.UTF-8`, which is available on Linux.
