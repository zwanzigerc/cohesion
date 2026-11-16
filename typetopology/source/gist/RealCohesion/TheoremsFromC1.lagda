Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), in the consolidation that
followed the final audits: W1, W2, W3 and W4 of Claude Fable 5.2's
plan [1], as corrected by its addendum [2] and released by GPT-6 Astra
[3], with the acceptance inventory [4] and, for W4, Astra's independent
review [5]. See the AI disclosure in gist.RealCohesion.index.

C1 and NC in place of Axiom R♭
------------------------------

For an ordinary family R : J → 𝓦 of pointed generators with Axiom C1,
an ordinary hypothesis, NC is a strictly rising map from a generator to
ℝ (Rising-Generator-Path R of gist.RealCohesion.Constancy):

  Σ j ꞉ J , Σ g ꞉ (R j → ℝ) , Σ x ꞉ R j , Σ y ꞉ R j , g x < g y.

It is positive data, in the universe 𝓥 ⊔ 𝓦 ⊔ 𝓤₁, and every theorem
here uses only its propositional truncation. Under these two
hypotheses, every map from ℝ to the quotient Q of levels by finite
chains is constant (C1-and-NC-give-constancy, W1: the general part of
gist.RealCohesion.FiniteChainDiscreteness, with the ♭-discreteness of
𝟚 from gist.CohesiveApartness.CrispInduction). Axiom R♭ is the case of
the one generator ℝ, whose identity map rises from 0 to 1.

The theorems of gist.RealCohesion.Theorems that use Axiom R♭ only
through that constancy (W2, 46 of them) have their forms
…-from-constancy there, and each R♭ theorem is its form applied to the
constancy that Axiom R♭ gives. Here each form is applied to the
constancy that C1 and the propositional truncation of NC give; the
forms for the Euclidean ball and the disc are obtained here from those
for the cube by the retraction of gist.RealCohesion.EuclideanBall, as
in gist.RealCohesion.Theorems, since forwarding them makes Agda compare
two copies of the type of the ball, which is very slow. The
names are C1-and-NC-give-… where the R♭ theorem is R♭-gives-…,
C1-NC-and-T-give-… where it is R♭-and-T-give-…, C1-and-NC-refute-…
for R♭-refutes-…, and …-from-C1-and-NC otherwise. Each type is the
type of the R♭ theorem with the hypothesis R♭ removed, written out in
full where the R♭ theorem has the type of a Target alias of
gist.RealCohesion.BrouwerStatements or
gist.RealCohesion.ShulmanWeakeningsStatements that contains R♭. The
module parameters R, c1 and the truncation of NC take its place, at
the front. Every other hypothesis stays as in the R♭ theorem: crisp
excluded middle at its level and mode, Axiom T, the crispness of maps,
centres and dimensions, the universes, and Kuhn's lemma, which the
forms …-in-every-dimension discharge in every dimension, as their R♭
forms do. Mere NC suffices also where a conclusion is data, since the
truncation is eliminated only into Constancy, a proposition.

The 24 theorems of gist.RealCohesion.Theorems that pass Axiom R♭ to a
lower module which takes it itself (W3) have their forms here too, by
the module checkpoints of the plan. Each of the modules
gist.RealCohesion.IndistinguishablePoints, CrispFunctionsAreContinuous,
CrispFunctionsOfSeveralVariables, FlatRealFunctions,
FlatFunctionsOfSeveralVariables and DiscreteSets has a general module
from an ordinary C1, the ♭-discreteness of 𝟚 and, where it is used, the
truncation of NC; its R♭ module is the instance, with the old names and
types. Under C1 the backward half of Axiom R♭ is needed only for types
that are null for every generator by closure (function types into
♭-discrete types, crisp propositions), which needs no NC; its forward
half is needed only for the ♭-discrete crisp sets 𝟚, Q, ♭ ℝ and the
quotient S of gist.RealCohesion.IndistinguishablePoints, in 𝓤₂, where
it follows from C1 and NC by the transfer lemma for sets, at the
universe of the set. Where the proof in gist.RealCohesion.Theorems does
more than apply a lower module, it is now given once, as a form
…-under-C1, and the R♭ theorem is its instance for the one generator ℝ.
The names follow the rules above, with C1-and-NC-alone-give-… where the
R♭ theorem is R♭-gives-…-from-R♭-alone. Where the R♭ theorem has the
type of a Target alias that contains R♭ (Target-11-5,
Target-crisp-real-continuity, Target-3-4,
Target-3-3-embedding-and-continuity-from-R♭-alone, Target-3-3,
Target-11-6, Target-3-5), its type is written out, with the crisp
excluded middle for 𝓤₀ of the alias, also where the proof does not use
it; the forms without it are there as well. The fiber in
Shulman-Corollary-11-6-without-T-from-C1-and-NC and the equivalence in
crisp-real-functions-are-the-continuous-maps-from-C1-and-NC are data,
and the truncation of NC suffices for them too, since it is eliminated
only into propositions. The third part of Theorem 3.3,
C1-and-NC-give-continuous-maps-are-values, does not use NC.

The three theorems from univalence and Axiom R♭ for the square and the
disc (W4), UA-and-R♭-give-Target-12-6-cube and the forms for the disc
with rational and with real ε, apply Axiom R♭ to the classifier K of
gist.RealCohesion.ApproximateBrouwerSquare, a type of types which is
generally a 1-type and not a set, so the transfer lemma for sets does
not apply to them. Their forms here, UA-C1-and-NC-give-…, take
univalence, an ordinary C1 and the truncation of NC, with the crisp map
and the ordinary rational or real error of the R♭ theorems, and no
excluded middle or Axiom T. K is ♭-discrete from C1 and univalence,
without NC, and a crisp ♭-discrete type is ℝ-null, whatever its
truncation level, by the transfer of nullness along a normalized rising
path of
gist.RealCohesion.HigherTransfer; the truncations are eliminated only
into the proposition that the constant-map function is an equivalence.
The type of the form for the square is Target-12-6-cube written out,
Univalence → Approximate-Fixed-Points-Of-Crisp-Maps 2; those for the
disc are Univalence → … with the statements of
gist.RealCohesion.ApproximateBrouwerDisc, which do not mention Axiom
R♭.

Four further statements, which do not assume NC:

 * ℝ-not-♭-discrete-gives-not-not-NC: under Axiom C1, if ℝ is not
   ♭-discrete, then NC is not refuted. If it were, every map from a
   generator to ℝ would be constant, since x ＝ y as soon as neither
   x < y nor y < x, and ℝ would be ♭-discrete by Axiom C0.

 * C1-and-ℝ-not-♭-discrete-refute-analytic-LLPO: so Axiom C1 and "ℝ
   is not ♭-discrete" refute the analytic LLPO, without excluded
   middle, since the conclusion is a negation.

 * crisp-EM-and-ℝ-not-♭-discrete-give-mere-NC: with crisp excluded
   middle for the universe 𝓥 ⊔ 𝓦 ⊔ 𝓤₁ of NC, applied to the crisp
   proposition ∥ NC ∥, the propositional truncation of NC follows. This
   needs the family and its index type crisp, so that ∥ NC ∥ is crisp,
   but not c1, which does not occur in NC; it is an ordinary
   hypothesis. The forms of the fixed-point theorems from crisp
   excluded middle, Axiom C1 and "ℝ is not ♭-discrete" in
   gist.RealCohesion.Theorems (gate G27) take a crisp C1, except the
   four forms LEM-ordinary-C1-and-ℝ-not-♭-discrete-give-…, which take
   an ordinary C1 for a crisp family; the forms here take an ordinary
   C1 and the truncation of NC. All are kept.

 * crisp-sets-are-♭-discrete-iff-discrete-under-C1: under Axiom C1 and
   crisp excluded middle for the universe of a crisp set A, an ordinary
   hypothesis as in ♭-discrete-sets-are-discrete of
   gist.CohesiveApartness.Flat, A is ♭-discrete if and only if it has
   decidable equality. This is Shulman's Lemma 8.15 for crisp sets,
   with "♭-discrete" for his "discrete": the forward direction is
   ♭-discrete-sets-are-discrete, the converse is from C1
   (gist.RealCohesion.PunctualCohesion). It is not the ℝ-null form,
   Lemma-8-15-for-crisp-sets of gist.RealCohesion.Theorems, which keeps
   Axiom R♭.

What does not transfer: the statements that use the converse half of
Axiom R♭ for a type about which nothing else is known (nLab problem 1,
the ℝ-null form of Lemma 8.15 for crisp sets, the one candidate of W3
that is excluded) keep Axiom R♭.

The 46 + 24 + 3 = 73 forms here are the commissioned rows, not a
partition of the names of gist.RealCohesion.Theorems that take Axiom
R♭. The full-name scan scans/theorems-rflat-uses-full.txt in the
companion of [2] (provenance/COMPANIONS.md lists the archive) lists 86
such names in the frozen delivery r3, of which 74 are the candidates
of W2, W3 and W4. Besides the excluded W3 candidate
Lemma-8-15-for-crisp-sets, these keep Axiom R♭: the six exports for
nLab problem 1, dyadic-image-shape-is-not-a-set,
not-every-subset-of-ℝ-has-a-set-as-shape and
not-every-crisp-subset-of-ℝ-has-a-set-as-shape, each also in a form
…-without-continuity; their public helper crisp-constancy, with its old
telescope; R♭-gives-C1 and R♭-gives-that-ℝ-is-not-♭-discrete, which are
about Axiom R♭ itself; and the two forms
C1-theorem-gives-crisp-cube-fixed-points-in-every-dimension and
C1-theorem-gives-sharp-cube-fixed-points-in-every-dimension, which
reach, through the theorem of gate G27, targets whose statements
assume Axiom R♭. Two more exports keep Axiom R♭ inside their target
types: C1-theorem-gives-Target-3-7-crisp and
C1-theorem-gives-Target-3-7-sharp, which take ordinary R♭
(Singly-Generated-Punctual-Cohesion for ℝ), crisp excluded middle and
crisp Kuhn's lemma; the two …-in-every-dimension forms above discharge
only Kuhn's lemma. These four exports specialize the C1 argument back
to the original R♭ targets. The count 86 is that of the textual scan,
not of names after unfolding aliases. The last scanned name, II, is
not an export but a
local name in a proof: in r3 of R♭-gives-Shulman-11-6, a W3 row, and
now of its form Shulman-11-6-under-C1. Outside
gist.RealCohesion.Theorems, crisp-ℝ-null-sets-are-discrete of
gist.RealCohesion.DiscreteSets and modal-iff-♭-discrete-under-R♭ of
gist.RealCohesion.RealNull keep Axiom R♭ too.

[1] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, Sections 4.1, 4.2 and 4.3.
    references/F02-consolidation-plan.md

[2] Claude Fable 5.2. Addendum 01 to the consolidation plan,
    13 November 2026, Section 2.
    references/F03-consolidation-plan-addendum-01.md

[3] GPT-6 Astra. Consolidation implementation, second release,
    13 November 2026.
    references/A27-consolidation-release-02.txt

[4] GPT-6 Astra. W3/W4 acceptance inventory, frozen r3 to new
    candidate, 13 November 2026.
    references/A30-w3-w4-inventory.txt

[5] GPT-6 Astra. W4 independent mathematical review, 13 November 2026.
    references/A13-w4-review.txt

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

module gist.RealCohesion.TheoremsFromC1 where

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Univalence using (Univalence)
open import gist.CohesiveApartness.Flat
open import gist.CohesiveApartness.CrispInduction
 using (crisp-ap-^♭ ; 𝟚-is-♭-discrete ; ♭-is-♭-discrete)
import gist.RealCohesion.Theorems as Th

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import Notation.CanonicalMap
 open import Notation.Order
 open import UF.DiscreteAndSeparated using (is-discrete)
 open import UF.Embeddings using (is-embedding)
 open import UF.Equiv using (_≃_)
 open import UF.Sets using (is-set)
 open import Rationals.Type using (ℚ ; 0ℚ)
 open import DedekindReals.Type fe pe pt
 open import DedekindReals.Order fe pe pt
 open import gist.RealCohesion.RealOrder fe pe pt using (ℝ<-tight)
 open import gist.RealCohesion.Constancy fe pe pt
  using (Constancy ; Rising-Generator-Path)
 open import gist.RealCohesion.CrispRealAnalysis fe pe pt
  using (Crisp-Real-Continuity)
 open import gist.RealCohesion.BrouwerStatements fe pe pt
  using (Analytic-LLPO ; Closed-Half-Lines-Are-Sequentially-Closed ;
         Sequential-Hitting-For-Functionals ; Kuhn-Lemma ;
         Crisp-Cube-Fixed-Point ; Sharp-Cube-Fixed-Point ;
         Approximate-Cube-Fixed-Point ;
         crisp-retracts-of-the-cube-have-fixed-points ;
         retracts-of-the-cube-have-sharp-fixed-points)
 open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt
  using (Strongly-Extensional ; Rational-Detection ;
         Rational-Detection-In-Dimension ; Crisp-Exact-IVT ; Shulman-11-5 ;
         Approximate-Fixed-Points-Of-Crisp-Maps ; Shulman-11-6 ; ♭-apply₁ ;
         is-♭-ε-δ-continuous ; Remark-3-4 ; ♭-apply-is-injective ;
         ♭-apply-has-continuous-values ;
         continuous-maps-are-values-of-♭-apply ; Theorem-3-3)
 open import gist.RealCohesion.CrispUniformContinuity fe pe pt
  using (is-ε-δ-continuous)
 open import gist.RealCohesion.CrispExactIVTFromTotalOrder fe pe pt
  using (Crisp-Order-Is-Total ; Crisp-Order-Is-Decidable ;
         crisp-EM-gives-decidable-order ; decidable-order-gives-total-order)
 open import gist.RealCohesion.NativeSharp using (native-sharp)
 import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭ as FCD
 import gist.RealCohesion.PunctualCohesion fe as PC
 import gist.RealCohesion.CrispFunctionsEverywhere fe pe pt as CFE
 import gist.RealCohesion.FunctionalHitting fe pe pt as FH
 import gist.RealCohesion.AxiomTObstruction fe pe pt native-sharp as ATO
 import gist.RealCohesion.EuclideanBall fe pe pt as EB
 import gist.RealCohesion.ApproximateIVTReduction fe pe pt as AIVTR
 import gist.RealCohesion.FlatRealFunctions fe pe pt crisp-ap-^♭ as FRF
 import gist.RealCohesion.DiscreteSets fe pe pt as DS
 import gist.RealCohesion.ApproximateBrouwerSquare fe pe pt as ABS
 import gist.RealCohesion.ApproximateBrouwerDisc fe pe pt as ABD
 import gist.CohesiveApartness.Sharp as NS
 open PropositionalTruncation pt

\end{code}

W1: C1 and the propositional truncation of NC give the constancy; and
W2: the forms of the 46 theorems.

\begin{code}

 module _ {𝓥 𝓦 : Universe} {J : 𝓥 ̇ }
          (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
          (nc : ∥ Rising-Generator-Path R ∥)
        where

  C1-and-NC-give-constancy : Constancy
  C1-and-NC-give-constancy =
   FCD.under-C1.constancy-from-C1-and-NC R c1 𝟚-is-♭-discrete nc

  private
   ν : Constancy
   ν = C1-and-NC-give-constancy

  crisp-functions-are-continuous-without-T-from-C1-and-NC
   : (@♭ cem : Crisp-EM 𝓤₁)
   → Crisp-Real-Continuity
  crisp-functions-are-continuous-without-T-from-C1-and-NC =
   Th.crisp-functions-are-continuous-without-T-from-constancy fe pe pt ν

  crisp-exact-IVT-without-T-from-C1-and-NC
   : (@♭ cem : Crisp-EM 𝓤₁)
   → (@♭ f : ℝ → ℝ) (@♭ c a b : ℝ)
   → f a < c → c < f b
   → ∃ x ꞉ ℝ , f x ＝ c
  crisp-exact-IVT-without-T-from-C1-and-NC =
   Th.crisp-exact-IVT-without-T-from-constancy fe pe pt ν

  rational-detection-from-C1-and-NC
   : (h : ℝ → ℝ) (x : ℝ) → 0ℚ < h x → ∃ q ꞉ ℚ , 0ℚ < h (ι q)
  rational-detection-from-C1-and-NC =
   Th.rational-detection-from-constancy fe pe pt ν

  approximate-IVT-with-rational-witness-from-C1-and-NC
   : (f : ℝ → ℝ) (p q a b : ℝ)
   → p < q
   → f a < q
   → p < f b
   → ∃ r ꞉ ℚ , (p < f (ι r)) × (f (ι r) < q)
  approximate-IVT-with-rational-witness-from-C1-and-NC =
   Th.approximate-IVT-with-rational-witness-from-constancy fe pe pt ν

  crisp-functions-are-continuous-everywhere-without-T-from-C1-and-NC
   : (@♭ cem : Crisp-EM 𝓤₁)
   → (@♭ f : ℝ → ℝ) (@♭ t : ℝ) (u v : ℚ)
   → u < f t → f t < v
   → CFE.Holds-Near-Everywhere (λ s → (u < f s) × (f s < v)) t
  crisp-functions-are-continuous-everywhere-without-T-from-C1-and-NC =
   Th.crisp-functions-are-continuous-everywhere-without-T-from-constancy
    fe pe pt ν

  exact-IVT-without-T-from-C1-and-NC
   : (@♭ cem : Crisp-EM 𝓤₁)
   → (@♭ f : ℝ → ℝ) (@♭ c : ℝ) (a b : ℝ)
   → f a < c → c < f b
   → ∃ x ꞉ ℝ , f x ＝ c
  exact-IVT-without-T-from-C1-and-NC =
   Th.exact-IVT-without-T-from-constancy fe pe pt ν

  crisp-real-functions-are-determined-by-crisp-points-from-C1-and-NC
   : (@♭ F G : ℝ → ℝ) → ((@♭ x : ℝ) → F x ＝ G x) → F ＝ G
  crisp-real-functions-are-determined-by-crisp-points-from-C1-and-NC =
   Th.crisp-real-functions-are-determined-by-crisp-points-from-constancy
    fe pe pt ν

  C1-and-NC-refute-analytic-LLPO
   : ¬ Analytic-LLPO
  C1-and-NC-refute-analytic-LLPO = Th.constancy-refutes-analytic-LLPO fe pe pt ν

  C1-and-NC-give-sequential-hitting
   : FH.Sequential-Hitting-In-ℝ^
  C1-and-NC-give-sequential-hitting =
   Th.constancy-gives-sequential-hitting fe pe pt ν

  C1-and-NC-give-positive-sequential-hitting-for-functionals
   : (𝓣 : Universe)
   → FH.Positive-Sequential-Hitting-For-Functionals 𝓣
  C1-and-NC-give-positive-sequential-hitting-for-functionals =
   Th.constancy-gives-positive-sequential-hitting-for-functionals fe pe pt ν

  C1-and-NC-give-sequential-hitting-for-functionals
   : (𝓣 : Universe) → Sequential-Hitting-For-Functionals 𝓣
  C1-and-NC-give-sequential-hitting-for-functionals =
   Th.constancy-gives-sequential-hitting-for-functionals fe pe pt ν

  C1-and-NC-give-closed-half-lines
   : (𝓣 : Universe)
   → Closed-Half-Lines-Are-Sequentially-Closed 𝓣
  C1-and-NC-give-closed-half-lines =
   Th.constancy-gives-closed-half-lines fe pe pt ν

  C1-and-NC-give-crisp-cube-fixed-points
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → (@♭ kuhn : Kuhn-Lemma n)
   → Crisp-Cube-Fixed-Point n
  C1-and-NC-give-crisp-cube-fixed-points =
   Th.constancy-gives-crisp-cube-fixed-points fe pe pt ν

  C1-and-NC-give-sharp-cube-fixed-points
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → (@♭ kuhn : Kuhn-Lemma n)
   → Sharp-Cube-Fixed-Point native-sharp n
  C1-and-NC-give-sharp-cube-fixed-points =
   Th.constancy-gives-sharp-cube-fixed-points fe pe pt ν

  C1-and-NC-give-crisp-cube-fixed-points-in-every-dimension
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → Crisp-Cube-Fixed-Point n
  C1-and-NC-give-crisp-cube-fixed-points-in-every-dimension =
   Th.constancy-gives-crisp-cube-fixed-points-in-every-dimension fe pe pt ν

  C1-and-NC-give-sharp-cube-fixed-points-in-every-dimension
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → Sharp-Cube-Fixed-Point native-sharp n
  C1-and-NC-give-sharp-cube-fixed-points-in-every-dimension =
   Th.constancy-gives-sharp-cube-fixed-points-in-every-dimension fe pe pt ν

  C1-and-NC-give-crisp-fixed-points-in-dimension-0
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Crisp-Cube-Fixed-Point 0
  C1-and-NC-give-crisp-fixed-points-in-dimension-0 =
   Th.constancy-gives-crisp-fixed-points-in-dimension-0 fe pe pt ν

  C1-and-NC-give-crisp-fixed-points-in-dimension-1
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Crisp-Cube-Fixed-Point 1
  C1-and-NC-give-crisp-fixed-points-in-dimension-1 =
   Th.constancy-gives-crisp-fixed-points-in-dimension-1 fe pe pt ν

  C1-and-NC-give-sharp-fixed-points-in-dimension-0
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Sharp-Cube-Fixed-Point native-sharp 0
  C1-and-NC-give-sharp-fixed-points-in-dimension-0 =
   Th.constancy-gives-sharp-fixed-points-in-dimension-0 fe pe pt ν

  C1-and-NC-give-sharp-fixed-points-in-dimension-1
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Sharp-Cube-Fixed-Point native-sharp 1
  C1-and-NC-give-sharp-fixed-points-in-dimension-1 =
   Th.constancy-gives-sharp-fixed-points-in-dimension-1 fe pe pt ν

  C1-NC-and-T-give-approximate-cube-fixed-points
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → ATO.Axiom-T
   → (@♭ kuhn : Kuhn-Lemma n)
   → Approximate-Cube-Fixed-Point n
  C1-NC-and-T-give-approximate-cube-fixed-points =
   Th.constancy-and-T-give-approximate-cube-fixed-points fe pe pt ν

  C1-NC-and-T-give-approximate-cube-fixed-points-in-every-dimension
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → ATO.Axiom-T
   → Approximate-Cube-Fixed-Point n
  C1-NC-and-T-give-approximate-cube-fixed-points-in-every-dimension =
   Th.constancy-and-T-give-approximate-cube-fixed-points-in-every-dimension
    fe pe pt ν

  C1-NC-and-T-give-approximate-fixed-points-in-dimension-0
   : (@♭ cem : Crisp-EM 𝓤₀)
   → ATO.Axiom-T
   → Approximate-Cube-Fixed-Point 0
  C1-NC-and-T-give-approximate-fixed-points-in-dimension-0 =
   Th.constancy-and-T-give-approximate-fixed-points-in-dimension-0 fe pe pt ν

  C1-NC-and-T-give-approximate-fixed-points-in-dimension-1
   : (@♭ cem : Crisp-EM 𝓤₀)
   → ATO.Axiom-T
   → Approximate-Cube-Fixed-Point 1
  C1-NC-and-T-give-approximate-fixed-points-in-dimension-1 =
   Th.constancy-and-T-give-approximate-fixed-points-in-dimension-1 fe pe pt ν

  C1-and-NC-give-crisp-fixed-points-in-dimension-2
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Crisp-Cube-Fixed-Point 2
  C1-and-NC-give-crisp-fixed-points-in-dimension-2 =
   Th.constancy-gives-crisp-fixed-points-in-dimension-2 fe pe pt ν

  C1-and-NC-give-sharp-fixed-points-in-dimension-2
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Sharp-Cube-Fixed-Point native-sharp 2
  C1-and-NC-give-sharp-fixed-points-in-dimension-2 =
   Th.constancy-gives-sharp-fixed-points-in-dimension-2 fe pe pt ν

  C1-NC-and-T-give-approximate-fixed-points-in-dimension-2
   : (@♭ cem : Crisp-EM 𝓤₀)
   → ATO.Axiom-T
   → Approximate-Cube-Fixed-Point 2
  C1-NC-and-T-give-approximate-fixed-points-in-dimension-2 =
   Th.constancy-and-T-give-approximate-fixed-points-in-dimension-2 fe pe pt ν

  C1-and-NC-give-crisp-fixed-points-on-the-ball
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → (@♭ kuhn : Kuhn-Lemma n)
   → (@♭ f : EB.Ball n → EB.Ball n) → ∃ x ꞉ EB.Ball n , f x ＝ x
  C1-and-NC-give-crisp-fixed-points-on-the-ball n cem kuhn =
   crisp-retracts-of-the-cube-have-fixed-points n (EB.Ball n) EB.ball-to-cube
    EB.cube-to-ball EB.ball-is-a-retract-of-the-cube
    (C1-and-NC-give-crisp-cube-fixed-points n cem kuhn)

  C1-and-NC-give-sharp-fixed-points-on-the-ball
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → (@♭ kuhn : Kuhn-Lemma n)
   → (f : EB.Ball n → EB.Ball n) → NS.♯ (∃ x ꞉ EB.Ball n , f x ＝ x)
  C1-and-NC-give-sharp-fixed-points-on-the-ball n cem kuhn =
   retracts-of-the-cube-have-sharp-fixed-points native-sharp n (EB.Ball n)
    EB.ball-to-cube EB.cube-to-ball EB.ball-is-a-retract-of-the-cube
    (C1-and-NC-give-crisp-cube-fixed-points n cem kuhn)

  C1-and-NC-give-crisp-fixed-points-on-the-ball-in-every-dimension
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → (@♭ f : EB.Ball n → EB.Ball n) → ∃ x ꞉ EB.Ball n , f x ＝ x
  C1-and-NC-give-crisp-fixed-points-on-the-ball-in-every-dimension n cem =
   C1-and-NC-give-crisp-fixed-points-on-the-ball n cem
    (Th.kuhn-lemma fe pe pt n)

  C1-and-NC-give-sharp-fixed-points-on-the-ball-in-every-dimension
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → (f : EB.Ball n → EB.Ball n) → NS.♯ (∃ x ꞉ EB.Ball n , f x ＝ x)
  C1-and-NC-give-sharp-fixed-points-on-the-ball-in-every-dimension n cem =
   C1-and-NC-give-sharp-fixed-points-on-the-ball n cem
    (Th.kuhn-lemma fe pe pt n)

  C1-and-NC-give-crisp-fixed-points-on-the-disc
   : (@♭ cem : Crisp-EM 𝓤₀)
   → (@♭ f : EB.Ball 2 → EB.Ball 2) → ∃ x ꞉ EB.Ball 2 , f x ＝ x
  C1-and-NC-give-crisp-fixed-points-on-the-disc cem =
   crisp-retracts-of-the-cube-have-fixed-points 2 (EB.Ball 2) EB.ball-to-cube
    EB.cube-to-ball EB.ball-is-a-retract-of-the-cube
    (C1-and-NC-give-crisp-fixed-points-in-dimension-2 cem)

  C1-and-NC-give-sharp-fixed-points-on-the-disc
   : (@♭ cem : Crisp-EM 𝓤₀)
   → (f : EB.Ball 2 → EB.Ball 2) → NS.♯ (∃ x ꞉ EB.Ball 2 , f x ＝ x)
  C1-and-NC-give-sharp-fixed-points-on-the-disc cem =
   retracts-of-the-cube-have-sharp-fixed-points native-sharp 2 (EB.Ball 2)
    EB.ball-to-cube EB.cube-to-ball EB.ball-is-a-retract-of-the-cube
    (C1-and-NC-give-crisp-fixed-points-in-dimension-2 cem)

  C1-NC-and-T-give-approximate-fixed-points-on-the-ball
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → ATO.Axiom-T
   → (@♭ kuhn : Kuhn-Lemma n)
   → EB.Approximate-Fixed-Points-On-The-Ball n
  C1-NC-and-T-give-approximate-fixed-points-on-the-ball n cem T kuhn =
   EB.approximate-fixed-points-on-the-ball
    (C1-NC-and-T-give-approximate-cube-fixed-points n cem T kuhn)

  C1-NC-and-T-give-approximate-fixed-points-on-the-ball-in-every-dimension
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → ATO.Axiom-T
   → EB.Approximate-Fixed-Points-On-The-Ball n
  C1-NC-and-T-give-approximate-fixed-points-on-the-ball-in-every-dimension
   n cem T =
   C1-NC-and-T-give-approximate-fixed-points-on-the-ball n cem T
    (Th.kuhn-lemma fe pe pt n)

  C1-NC-and-T-give-approximate-fixed-points-on-the-disc
   : (@♭ cem : Crisp-EM 𝓤₀)
   → ATO.Axiom-T
   → EB.Approximate-Fixed-Points-On-The-Ball 2
  C1-NC-and-T-give-approximate-fixed-points-on-the-disc cem T =
   EB.approximate-fixed-points-on-the-ball
    (C1-NC-and-T-give-approximate-fixed-points-in-dimension-2 cem T)

  C1-and-NC-give-strong-extensionality
   : (f : ℝ → ℝ) → Strongly-Extensional f
  C1-and-NC-give-strong-extensionality =
   Th.constancy-gives-strong-extensionality fe pe pt ν

  C1-and-NC-give-rational-detection
   : Rational-Detection
  C1-and-NC-give-rational-detection =
   Th.constancy-gives-rational-detection fe pe pt ν

  C1-and-NC-give-rational-detection-in-dimension
   : (n : ℕ) → Rational-Detection-In-Dimension n
  C1-and-NC-give-rational-detection-in-dimension =
   Th.constancy-gives-rational-detection-in-dimension fe pe pt ν

  C1-and-NC-give-crisp-exact-IVT
   : (@♭ cem : Crisp-EM 𝓤₁)
   → Crisp-Exact-IVT
  C1-and-NC-give-crisp-exact-IVT = Th.constancy-gives-crisp-exact-IVT fe pe pt ν

  C1-and-NC-give-Shulman-11-5
   : (@♭ cem : Crisp-EM 𝓤₁)
   → Shulman-11-5
  C1-and-NC-give-Shulman-11-5 = Th.constancy-gives-Shulman-11-5 fe pe pt ν

  C1-and-NC-give-approximate-fixed-points-of-crisp-maps
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → (@♭ kuhn : Kuhn-Lemma n)
   → Approximate-Fixed-Points-Of-Crisp-Maps n
  C1-and-NC-give-approximate-fixed-points-of-crisp-maps =
   Th.constancy-gives-approximate-fixed-points-of-crisp-maps fe pe pt ν

  C1-and-NC-give-Target-12-6-cube-from-LEM-in-dimension-0
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Approximate-Fixed-Points-Of-Crisp-Maps 0
  C1-and-NC-give-Target-12-6-cube-from-LEM-in-dimension-0 =
   Th.constancy-gives-Target-12-6-cube-from-LEM-in-dimension-0 fe pe pt ν

  C1-and-NC-give-Target-12-6-cube-from-LEM-in-dimension-1
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Approximate-Fixed-Points-Of-Crisp-Maps 1
  C1-and-NC-give-Target-12-6-cube-from-LEM-in-dimension-1 =
   Th.constancy-gives-Target-12-6-cube-from-LEM-in-dimension-1 fe pe pt ν

  C1-and-NC-give-Target-12-6-cube-from-LEM-in-dimension-2
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Approximate-Fixed-Points-Of-Crisp-Maps 2
  C1-and-NC-give-Target-12-6-cube-from-LEM-in-dimension-2 =
   Th.constancy-gives-Target-12-6-cube-from-LEM-in-dimension-2 fe pe pt ν

  C1-and-NC-give-Target-12-6-cube-from-LEM
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → Approximate-Fixed-Points-Of-Crisp-Maps n
  C1-and-NC-give-Target-12-6-cube-from-LEM =
   Th.constancy-gives-Target-12-6-cube-from-LEM fe pe pt ν

\end{code}

W3: the forms of the 24 theorems of gist.RealCohesion.Theorems that
pass Axiom R♭ to a lower module which takes it itself. Where that
module has a general form (gist.RealCohesion.ApproximateIVTReduction,
gist.RealCohesion.FlatRealFunctions, gist.RealCohesion.DiscreteSets),
the form here applies it; otherwise gist.RealCohesion.Theorems proves
the form …-under-C1, of which the R♭ theorem is the instance for the
one generator ℝ, and the form here is that one.

\begin{code}

  approximate-IVT-from-C1-and-NC
   : (f : ℝ → ℝ) (p q a b : ℝ)
   → p < q
   → f a < q
   → p < f b
   → ∃ x ꞉ ℝ , (p < f x) × (f x < q)
  approximate-IVT-from-C1-and-NC = AIVTR.approximate-IVT-from-constancy ν

  canonical-map-is-an-embedding-from-C1-and-NC
   : is-embedding (FRF.♭-action {𝓤₁} {𝓤₁} {ℝ} {ℝ})
  canonical-map-is-an-embedding-from-C1-and-NC =
   FRF.under-C1.♭-action-is-embedding R c1 𝟚-is-♭-discrete nc

  Shulman-Corollary-11-6-without-T-from-C1-and-NC
   : (@♭ cem : Crisp-EM 𝓤₁)
   → is-embedding (FRF.♭-action {𝓤₁} {𝓤₁} {ℝ} {ℝ})
   × ((h : ♭ ℝ → ♭ ℝ) → fiber FRF.♭-action h ↔ is-ε-δ-continuous h)
  Shulman-Corollary-11-6-without-T-from-C1-and-NC =
   FRF.under-C1.Shulman-Corollary-11-6 R c1 𝟚-is-♭-discrete ♭-is-♭-discrete
    nc

  crisp-real-functions-are-the-continuous-maps-from-C1-and-NC
   : (@♭ cem : Crisp-EM 𝓤₁)
   → ♭ (ℝ → ℝ) ≃ (Σ h ꞉ (♭ ℝ → ♭ ℝ) , is-ε-δ-continuous h)
  crisp-real-functions-are-the-continuous-maps-from-C1-and-NC =
   FRF.under-C1.crisp-functions-are-the-continuous-maps R c1 𝟚-is-♭-discrete
    ♭-is-♭-discrete nc

  C1-and-NC-give-Shulman-11-6
   : (@♭ cem : Crisp-EM 𝓤₁)
   → Shulman-11-6
  C1-and-NC-give-Shulman-11-6 = Th.Shulman-11-6-under-C1 fe pe pt R c1 nc

  C1-and-NC-give-♭-apply₁-is-injective
   : (f g : ♭ (ℝ → ℝ)) → ♭-apply₁ f ＝ ♭-apply₁ g → f ＝ g
  C1-and-NC-give-♭-apply₁-is-injective =
   Th.♭-apply₁-is-injective-under-C1 fe pe pt R c1 nc

  C1-and-NC-alone-give-Shulman-11-5
   : Shulman-11-5
  C1-and-NC-alone-give-Shulman-11-5 = Th.Shulman-11-5-under-C1 fe pe pt R c1 nc

  C1-and-NC-give-Target-11-5
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Shulman-11-5
  C1-and-NC-give-Target-11-5 cem = C1-and-NC-alone-give-Shulman-11-5

  C1-and-NC-give-crisp-real-continuity
   : Crisp-Real-Continuity
  C1-and-NC-give-crisp-real-continuity =
   Th.crisp-real-continuity-under-C1 fe pe pt R c1 nc

  C1-and-NC-give-Target-crisp-real-continuity
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Crisp-Real-Continuity
  C1-and-NC-give-Target-crisp-real-continuity cem =
   C1-and-NC-give-crisp-real-continuity

  C1-and-NC-give-continuous-values
   : (F : ♭ (ℝ → ℝ)) → is-♭-ε-δ-continuous (♭-apply₁ F)
  C1-and-NC-give-continuous-values =
   Th.continuous-values-under-C1 fe pe pt R c1 nc

  C1-and-NC-alone-give-Remark-3-4
   : (@♭ n : ℕ) → Remark-3-4 n
  C1-and-NC-alone-give-Remark-3-4 = Th.Remark-3-4-under-C1 fe pe pt R c1 nc

  C1-and-NC-give-Target-3-4
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → Remark-3-4 n
  C1-and-NC-give-Target-3-4 n cem = C1-and-NC-alone-give-Remark-3-4 n

  C1-and-NC-give-continuous-values-in-dimension
   : (@♭ n : ℕ) → ♭-apply-has-continuous-values n
  C1-and-NC-give-continuous-values-in-dimension =
   Th.continuous-values-in-dimension-under-C1 fe pe pt R c1 nc

  C1-and-NC-give-♭-apply-is-injective
   : (@♭ n : ℕ) → ♭-apply-is-injective n
  C1-and-NC-give-♭-apply-is-injective =
   Th.♭-apply-is-injective-under-C1 fe pe pt R c1 nc

  C1-and-NC-give-Target-3-3-embedding-and-continuity
   : (@♭ n : ℕ) → ♭-apply-is-injective n × ♭-apply-has-continuous-values n
  C1-and-NC-give-Target-3-3-embedding-and-continuity n =
   C1-and-NC-give-♭-apply-is-injective n ,
   C1-and-NC-give-continuous-values-in-dimension n

  C1-and-NC-give-continuous-maps-are-values
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → continuous-maps-are-values-of-♭-apply n
  C1-and-NC-give-continuous-maps-are-values =
   Th.continuous-maps-are-values-under-C1 fe pe pt R c1

  C1-and-NC-give-Target-3-3
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → Theorem-3-3 n
  C1-and-NC-give-Target-3-3 n cem =
   C1-and-NC-give-♭-apply-is-injective n ,
   C1-and-NC-give-continuous-values-in-dimension n ,
   C1-and-NC-give-continuous-maps-are-values n cem

  C1-and-NC-give-Target-11-6
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Shulman-11-6
  C1-and-NC-give-Target-11-6 = Th.Target-11-6-under-C1 fe pe pt R c1 nc

  Lemma-8-15-from-decidable-equality-from-C1-and-NC
   : {𝓤 : Universe}
   → (A : 𝓤 ̇ ) → is-discrete A → is-null ℝ A
  Lemma-8-15-from-decidable-equality-from-C1-and-NC =
   DS.under-C1.discrete-types-are-ℝ-null-under-C1 R c1 𝟚-is-♭-discrete nc

  unrestricted-Lemma-8-15-is-false-from-C1-and-NC
   : ¬ ((A : 𝓤₀ ̇ ) → is-set A → is-null ℝ A → is-discrete A)
  unrestricted-Lemma-8-15-is-false-from-C1-and-NC =
   DS.under-C1.ℝ-null-sets-need-not-be-discrete-under-C1 R c1
    𝟚-is-♭-discrete nc

  C1-and-NC-give-crisp-exact-IVT-from-total-order
   : (@♭ total : Crisp-Order-Is-Total) → Crisp-Exact-IVT
  C1-and-NC-give-crisp-exact-IVT-from-total-order =
   Th.crisp-exact-IVT-from-total-order-under-C1 fe pe pt R c1 nc

  C1-and-NC-give-crisp-exact-IVT-from-decidable-order
   : (@♭ d : Crisp-Order-Is-Decidable) → Crisp-Exact-IVT
  C1-and-NC-give-crisp-exact-IVT-from-decidable-order d =
   C1-and-NC-give-crisp-exact-IVT-from-total-order
    (decidable-order-gives-total-order d)

  C1-and-NC-give-Target-3-5
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Crisp-Exact-IVT
  C1-and-NC-give-Target-3-5 cem =
   C1-and-NC-give-crisp-exact-IVT-from-decidable-order
    (crisp-EM-gives-decidable-order cem)

\end{code}

W4: the forms of the three theorems from univalence and Axiom R♭ for
the square and the disc.

\begin{code}

  UA-C1-and-NC-give-Target-12-6-cube
   : Univalence → Approximate-Fixed-Points-Of-Crisp-Maps 2
  UA-C1-and-NC-give-Target-12-6-cube ua =
   ABS.Target-12-6-cube-under-C1 R c1 ua nc

  UA-C1-and-NC-give-approximate-fixed-points-on-the-disc
   : Univalence → ABD.Approximate-Fixed-Points-Of-Crisp-Maps-Of-The-Disc
  UA-C1-and-NC-give-approximate-fixed-points-on-the-disc ua =
   ABD.disc-form-from-the-square-form (UA-C1-and-NC-give-Target-12-6-cube ua)

  UA-C1-and-NC-give-approximate-fixed-points-on-the-disc-for-real-ε
   : Univalence
   → ABD.Approximate-Fixed-Points-Of-Crisp-Maps-Of-The-Disc-For-Real-ε
  UA-C1-and-NC-give-approximate-fixed-points-on-the-disc-for-real-ε ua =
   ABD.real-ε-form-from-the-rational-ε-form
    (UA-C1-and-NC-give-approximate-fixed-points-on-the-disc ua)

\end{code}

Without NC: "ℝ is not ♭-discrete" under Axiom C1.

\begin{code}

 module _ {𝓥 𝓦 : Universe} {J : 𝓥 ̇ }
          (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
        where

  open Axiom-C1 c1

  ℝ-not-♭-discrete-gives-not-not-NC
   : ¬ is-♭-discrete ℝ → ¬¬ Rising-Generator-Path R
  ℝ-not-♭-discrete-gives-not-not-NC nd μ =
   nd (PC.types-null-for-the-generators-are-♭-discrete R c1 ℝ
        (λ j g r → ℝ<-tight (g r) (g (base-point j))
                    (λ l → μ (j , g , r , base-point j , l))
                    (λ l → μ (j , g , base-point j , r , l))))

  C1-and-ℝ-not-♭-discrete-refute-analytic-LLPO
   : ¬ is-♭-discrete ℝ → ¬ Analytic-LLPO
  C1-and-ℝ-not-♭-discrete-refute-analytic-LLPO nd llpo =
   ℝ-not-♭-discrete-gives-not-not-NC nd
    (λ path → C1-and-NC-refute-analytic-LLPO R c1 ∣ path ∣ llpo)

  crisp-sets-are-♭-discrete-iff-discrete-under-C1
   : {@♭ 𝓤 : Universe} → Crisp-EM 𝓤
   → (@♭ A : 𝓤 ̇ ) → @♭ is-set A → is-♭-discrete A ↔ is-discrete A
  crisp-sets-are-♭-discrete-iff-discrete-under-C1 cem A A-is-set =
   ♭-discrete-sets-are-discrete cem A A-is-set ,
   PC.types-with-decidable-equality-are-♭-discrete R c1 𝟚-is-♭-discrete A

 module _ {@♭ 𝓥 𝓦 : Universe} {@♭ J : 𝓥 ̇ }
          (@♭ R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
        where

  crisp-EM-and-ℝ-not-♭-discrete-give-mere-NC
   : Crisp-EM (𝓥 ⊔ 𝓦 ⊔ 𝓤₁)
   → ¬ is-♭-discrete ℝ
   → ∥ Rising-Generator-Path R ∥
  crisp-EM-and-ℝ-not-♭-discrete-give-mere-NC cem nd =
   cases id
    (λ n → 𝟘-elim (ℝ-not-♭-discrete-gives-not-not-NC R c1 nd
                    (λ path → n ∣ path ∣)))
    (cem ∥ Rising-Generator-Path R ∥ ∥∥-is-prop)

\end{code}
