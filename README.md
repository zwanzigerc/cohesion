# Cohesion

This repository contains Agda formalizations in cohesive type theory and
Lean formalizations about geometric morphisms of toposes.

- [Lawvere–Menni on pre-cohesion and local connectedness](#lawveremenni-on-pre-cohesion-and-local-connectedness)
- [Six nLab open problems and their resolutions](docs/shulman.md#the-nlab-open-problems)
- [Questions raised by Shulman](docs/shulman.md#questions-raised-by-shulman)
- [Weakened and corrected statements](#weakened-and-corrected-statements)
- [Orbifolds, the revised theorem and its axioms](orbifolds/README.md)
- [Source credits and licenses](docs/sources.md)

## Lawvere–Menni on pre-cohesion and local connectedness

**Is every precohesive geometric morphism locally connected? No.**
Lawvere and Menni raised this question immediately after Corollary 10.4.
Our counterexample is a morphism between presheaf toposes
built from abelianization on finite products of $S_3$, $C_2$ and $C_3$.
The pullback square defining the kernel of the sign map witnesses the
failure of local connectedness. [Lawvere and Menni, §10, p. 930](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/TAC/volumes/30/26/30-26.pdf#page=22) · [Lean counterexample](lean/Counterexample/Main.lean)

**Is every cohesive geometric morphism between elementary toposes locally
connected? Yes.** Cohesion adds Lawvere's Continuity axiom to pre-cohesion.
Under that axiom, the morphism also has an open restriction of quality type and a
complementary closed restriction with Boolean base. Both the negative and
positive results were checked in Lean. The [Lean guide](lean/README.md)
specifies which proofs are included in this distribution. [Lawvere–Menni problem, proofs and related weakenings](docs/lawvere-menni.md)

## Our results on Shulman’s *Brouwer’s fixed-point theorem in real-cohesive homotopy type theory*

**Approximate intermediate values.** Shulman’s Theorem 11.4 assumes a crisp
function and a crisp target. We remove both assumptions and obtain a rational
witness. Under real cohesion, for any $f\colon\mathbb R\to\mathbb R$, if
$p<q$, $f(a)<q$ and $p<f(b)$, there merely exists a rational $r$ with
$p<f(r)<q$. [Approximate intermediate value theorem](docs/shulman.md#the-approximate-intermediate-value-theorem)

**Brouwer fixed points.** We extend Shulman’s sharp and crisp fixed-point
theorems for the disc (Theorem 12.4 and Corollary 12.5) to the closed unit
ball in every crisp finite dimension, under weaker assumptions.
Under crisp excluded middle, C1 for crisp pointed generators and
non-discreteness of the Dedekind reals in the sense of ♭, every endomap
of the ball sharply has a fixed point. For a crisp endomap
there merely exists a fixed point in the ordinary mode. The proofs
dispense with Axiom T and univalence. [Sharp and crisp fixed points](docs/shulman.md#the-two-classical-brouwer-fixed-point-theorems)

## Orbifolds

**The Rezk completion of a crisp pregroupoid of ordinary manifolds is an
orbifold if its source is an ordinary local homeomorphism, its anchor is
cover-proper, and its arrow manifold has a supplied crisp countable basis.**
Cover-properness here uses crisp families indexed by discrete sets. These
hypotheses include the unit groupoid of the smooth line. [The revised theorem](orbifolds/README.md#the-revised-main-theorem) · [Foundation](orbifolds/README.md#axioms-of-the-revised-foundation) · [Axioms used in the proof](orbifolds/README.md#axioms-used-by-the-main-theorem)

## Weakened and corrected statements

| Source | Comparison with the original statement |
| --- | --- |
| Lawvere and Menni, §§6, 8, 9 and 10 | [Sufficient cohesion and connected codiscreteness under epi-continuity](docs/lawvere-menni.md#related-weakenings) |
| Shulman, §§8, 11 and 12 | [Corrected quantifiers, weaker assumptions, and the conclusions they give](docs/shulman.md#weakened-and-corrected-statements) |
| Agda results using real cohesion | [Theorem-by-theorem comparison with C1 and a generator carrying a rising real function](docs/weaker-cohesion.md) |
| Myers, *Good fibrations through the modal prism* | [Three comparisons concerning decidability, real order and crispness](docs/shulman.md#consequences-for-myerss-good-fibrations-through-the-modal-prism) |
| Myers, *Orbifolds as microlinear types* | [Definitions, axioms, revised properness and scope of the theorems](orbifolds/corrections.md) |

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

## Checking the code

- [Agda 2.9.0 with TypeTopology](typetopology/README.md#build)
- [Native Agda on pre-cohesion](agda/precohesion/README.md)
- [Lean 4 and mathlib](lean/README.md)
