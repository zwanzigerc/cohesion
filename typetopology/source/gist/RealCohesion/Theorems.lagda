Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 and 12 November 2026, from gist.RealCohesion.FlatSplit of
25 October to 11 November 2026. On 13 November 2026, in the
consolidation after the final audits, the transports along bits-agree
were removed, the forms of Lemma 12.3 with a retraction of the
inclusion were added, and Constancy and Constancy-is-prop were made
typed aliases of gist.RealCohesion.Constancy; in its second part, the
theorems that use Axiom R♭ only through the constancy of maps from ℝ to
Q were given forms …-from-constancy, and those that pass Axiom R♭ to a
lower module forms …-under-C1 where their proofs do more than apply
that module, from Axiom C1 and a merely rising generator path; each
theorem under Axiom R♭ keeps its name and type and is the instance of
its form (W2 and W3 of Claude Fable 5.2's consolidation plan, released
by GPT-6 Astra; gist.RealCohesion.TheoremsFromC1 states the forms under
C1 and NC). See the AI disclosure in gist.RealCohesion.index.

The main theorems of this folder with the consequences of crisp
induction discharged, in --safe mode.

The modules of this folder take the consequences of crisp induction
that they need as hypotheses: crisp-ap-^♭, and the ♭-discreteness of
𝟚, of ℕ and of ♭ ℝ. gist.RealCohesion.FlatSplit proves these with
Agda's --flat-split, which is not allowed together with --safe and
--without-K, and restates the main theorems without the hypotheses.
Here the four facts come from gist.CohesiveApartness.CrispInduction,
which derives them from the native ♯ of Agda 2.9.0, as Shulman
derives crisp induction from ♯ [1, §5]. So this module is --safe and
gist.RealCohesion.index imports it.

The statements are those of gist.RealCohesion.FlatSplit, with the same
names and in the same order:

 * the instantiation of gist.RealCohesion.CrispDiscreteness with
   crisp-ap-^♭, re-exported;

 * countable choice for crisp families from the discrete axiom of
   choice, and the finite-height obstruction with it;

 * nLab problem 1, with and without its continuity hypothesis;

 * nLab problem 4, the approximate intermediate value theorem from
   Axiom R♭ alone;

 * the continuity of crisp functions and Shulman's Theorem 11.2
   without Axiom T, at crisp points and at all points;

 * rational detection and the approximate intermediate value theorem
   with a rational witness, from Axiom R♭ alone;

 * Shulman's Corollary 11.6 without Axiom T.

Three sections are new: the results of
gist.RealCohesion.AxiomTObstruction for the native ♯, so with no
assumption about ♯, among them Lemma 4.1 of the write-up and Shulman's
Theorem 8.32 without Axiom C1 in its apartness form, as the targets
Target-4-1 and Target-8-32 of gist.RealCohesion.BrouwerStatements;
Shulman's Theorem 11.7 without crisp excluded
middle (Theorem 7.10 of the write-up), stated as the target Target-7-10
of gist.RealCohesion.BrouwerStatements; and sequential hitting
(Theorem 7.4 of the write-up), for ℝⁿ and for functionals, with the
target Target-hitting and the closed half-lines of the blueprint
addendum. A last section states Kuhn's cubical lemma for n = 0, 1
and 2 with the type of gist.RealCohesion.BrouwerStatements, and the
crisp fixed point on the cube (Corollary 3.7 of the write-up in cube
form) as the targets Target-3-7-crisp and Target-3-7-sharp of that
module, and approximate fixed points on the cube (Theorem 4.3 of the
write-up in cube form) as its target Target-4-3, each also in
dimensions 0, 1 and 2 without Kuhn's lemma as a hypothesis, and, with
Kuhn's lemma in every dimension (gist.RealCohesion.KuhnLemmaGeneral),
in every dimension without it; then the
Euclidean ball (gate G14): Corollary 3.7 and Theorem 4.3 of the
write-up for the ball, with Shulman's Theorem 12.4 and Corollary 12.5
for the disc, and Shulman's Lemma 12.3 from crisp excluded middle and
Axiom T, without his Axiom C1, in every dimension. A final
section states targets of the second addendum
(gist.RealCohesion.ShulmanWeakeningsStatements): strong
extensionality and rational detection in n variables from Axiom R♭
(gate G16), and, from the theorems above, rational detection, the
exact intermediate value theorem, and Shulman's Theorem 11.5 and
Corollary 11.6 in the words of that module; Shulman's Theorem 11.5
from Axiom R♭ alone (gate G23), with the continuity of crisp functions
and two parts of Corollary 11.6 as corollaries; and its n-variable form
from Axiom R♭ alone (gate G24, GPT-6 Astra's Theorem 7.17), with Remark
3.4 of the write-up (gate G18) and the continuity of the values of the
canonical map in n variables; the injectivity of that map, which
completes the first two parts of Theorem 3.3 in n variables from Axiom
R♭ alone (gate G20); and the cube form of Shulman's Theorem 12.6 from
crisp excluded middle and Axiom R♭, a corollary of the crisp fixed
point, outright in dimensions 0, 1 and 2; and Theorem 3.3 in every crisp
dimension, all three parts, from crisp excluded middle for 𝓤₀ and Axiom
R♭ (gate G21), as the target Target-3-3, which for n = 1 gives
Corollary 11.6 in Shulman's words as the target Target-11-6, with
crisp excluded middle for 𝓤₀ only. Last, Shulman's Lemma 8.15 with its
scope (gate G15 of the blueprint addendum): its two directions for
crisp sets, and the refutation of the unrestricted form.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

module gist.RealCohesion.Theorems where

open import MLTT.Spartan
open import UF.DiscreteAndSeparated using (ℕ-is-set)
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.SetTrunc
open import UF.Subsingletons
open import Modal.Subuniverse
open import Quotient.Type
open import UF.Univalence
open import gist.CohesiveApartness.Flat
open import gist.CohesiveApartness.CrispInduction
 using (crisp-ap-^♭ ; 𝟚-is-♭-discrete ; ℕ-is-♭-discrete ; ♭-is-♭-discrete)

\end{code}

The instantiations.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import gist.RealCohesion.CrispDiscreteness fe pe pt crisp-ap-^♭ public
 open import gist.RealCohesion.CrispCountableChoice pt
 open import DedekindReals.Type fe pe pt

\end{code}

The discrete axiom of choice gives countable choice for crisp families,
because ℕ is a crisp ♭-discrete set.

\begin{code}

 discrete-choice-gives-crisp-countable-choice
  : {@♭ 𝓦 : Universe}
  → Discrete-Choice 𝓤₀ 𝓦
  → Crisp-Countable-Choice 𝓦
 discrete-choice-gives-crisp-countable-choice dc B e =
  dc ℕ ℕ-is-♭-discrete ℕ-is-set B e

\end{code}

The finite-height obstruction to Shulman's continuity conjecture, with
the discrete axiom of choice, which Shulman derives from his Axiom AC
[1, Theorem 6.30], in place of countable choice for crisp families.

\begin{code}

 module _ (@♭ st : set-truncations-exist)
          (@♭ sq : set-quotients-exist)
          {@♭ 𝓥 : Universe}
          (@♭ P : subuniverse 𝓤₁ 𝓥)
          (@♭ P-is-reflective : subuniverse-is-reflective P)
          (@♭ P-is-ℝ-null : (X : 𝓤₁ ̇ ) → subuniverse-contains P X
                                        ↔ is-null ℝ X)
        where

  open import gist.RealCohesion.RealShapeContinuity fe pe pt st sq
  open RealShape P P-is-reflective P-is-ℝ-null
  open PropositionalTruncation pt

  shape-continuity-fails-from-discrete-choice
   : Discrete-Choice 𝓤₀ 𝓤₁
   → Finite-Height
   → (@♭ B : ℕ → 𝓤₁ ̇ )
     (@♭ B-is-set : (n : ℕ) → is-set (B n))
     (@♭ b t : (n : ℕ) → B n)
   → @♭ ((n : ℕ) → η₀ (B n) (b n) ＝ η₀ (B n) (t n))
   → ((k : ℕ) → ∃ n ꞉ ℕ , q[ k ] (b n) ≠ q[ k ] (t n))
   → ¬ is-equiv (κ (Σ n ꞉ ℕ , B n))
  shape-continuity-fails-from-discrete-choice dc =
   shape-continuity-fails (discrete-choice-gives-crisp-countable-choice dc)

\end{code}

nLab problem 1. With the proof that 𝟚 is ♭-discrete, the shape of the
image of the dyadic function of gist.RealCohesion.DyadicOscillation, a
subtype of the Dedekind reals, is not a set, assuming standard
univalent and modal structure and the following principles, which hold
in Shulman's intended model: crisp excluded middle, the continuity of
crisp real functions at crisp points, unique Boolean real-path descent,
Axiom R♭, and that the type of two-element types is modal. See
gist.RealCohesion.RealSubsetShape for these assumptions. Unlike the
version there, these restatements discharge the ♭-discreteness of 𝟚,
here by the native ♯ (gist.CohesiveApartness.CrispInduction).

\begin{code}

module _ (@♭ ua : Univalence)
         (@♭ pt : propositional-truncations-exist)
       where

 open import gist.RealCohesion.RealSubsetShape ua pt
  using (fe ; pe ; dyadic-image ; dyadic-image-predicate ;
         shape-of-the-dyadic-image-is-not-a-set ;
         subsets-of-ℝ-need-not-have-set-shape ;
         crisp-subsets-of-ℝ-need-not-have-set-shape)
 open import UF.SubtypeClassifier using (Ω ; _holds)
 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import gist.RealCohesion.CrispRealAnalysis fe pe pt
  using (Crisp-Real-Continuity)
 open import gist.RealCohesion.RealPathDescent fe pe pt
  using (Unique-Boolean-Real-Path-Descent)

 module _ {@♭ 𝓥 : Universe}
          (@♭ P : subuniverse 𝓤₁ 𝓥)
          (@♭ P-is-reflective : subuniverse-is-reflective P)
          (@♭ P-is-ℝ-null : (X : 𝓤₁ ̇ )
           → subuniverse-contains P X ↔ is-null ℝ X)
          (@♭ cem : Crisp-EM 𝓤₁)
          (@♭ continuity : Crisp-Real-Continuity)
          (@♭ descent : Unique-Boolean-Real-Path-Descent 𝓤₁)
          (r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ)
        where

  open import Modal.ReflectiveSubuniverse P P-is-reflective using (○ ; is-modal)
  open import gist.RealCohesion.BooleanCocycleObstruction ua pt P
   P-is-reflective
   using (B₂)

  module _ (B₂-is-modal : is-modal B₂) where

   dyadic-image-shape-is-not-a-set : ¬ is-set (○ dyadic-image)
   dyadic-image-shape-is-not-a-set =
    shape-of-the-dyadic-image-is-not-a-set P P-is-reflective P-is-ℝ-null
     cem continuity descent r♭ 𝟚-is-♭-discrete B₂-is-modal

   not-every-subset-of-ℝ-has-a-set-as-shape
    : ¬ ((A : ℝ → Ω 𝓤₁) → is-set (○ (Σ x ꞉ ℝ , A x holds)))
   not-every-subset-of-ℝ-has-a-set-as-shape =
    subsets-of-ℝ-need-not-have-set-shape P P-is-reflective P-is-ℝ-null
     cem continuity descent r♭ 𝟚-is-♭-discrete B₂-is-modal

   not-every-crisp-subset-of-ℝ-has-a-set-as-shape
    : ¬ ((@♭ A : ℝ → Ω 𝓤₁) → is-set (○ (Σ x ꞉ ℝ , A x holds)))
   not-every-crisp-subset-of-ℝ-has-a-set-as-shape =
    crisp-subsets-of-ℝ-need-not-have-set-shape P P-is-reflective P-is-ℝ-null
     cem continuity descent r♭ 𝟚-is-♭-discrete B₂-is-modal

\end{code}

nLab problem 1 without the continuity hypothesis. The continuity of
crisp functions at crisp points, Crisp-Real-Continuity, follows from
crisp excluded middle and Axiom R♭ (gist.RealCohesion.CrispContinuity),
so the three theorems above hold without it. In
gist.RealCohesion.RealSubsetShape it is a crisp hypothesis, so we need
a crisp proof of it, whereas r♭ is an ordinary hypothesis. Under Axiom
R♭ crisp propositions are ♭-discrete, and the constancy of maps ℝ → Q,
from which the continuity follows, is a crisp proposition, so it has
a crisp proof.

\begin{code}

module _ (@♭ ua : Univalence)
         (@♭ pt : propositional-truncations-exist)
       where

 open import gist.RealCohesion.RealSubsetShape ua pt
  using (fe ; pe ; dyadic-image ;
         shape-of-the-dyadic-image-is-not-a-set ;
         subsets-of-ℝ-need-not-have-set-shape ;
         crisp-subsets-of-ℝ-need-not-have-set-shape)
 open import UF.SubtypeClassifier using (Ω ; _holds)
 open import UF.Subsingletons-FunExt using (Π₃-is-prop)
 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import gist.RealCohesion.RealPathDescent fe pe pt
  using (Unique-Boolean-Real-Path-Descent)
 open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q ; Q-is-set)
 import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭ as FCD
 import gist.RealCohesion.CrispContinuity fe pe pt as CC
 import gist.RealCohesion.Constancy fe pe pt as Con

 Constancy : 𝓤₁ ̇
 Constancy = Con.Constancy

 Constancy-is-prop : is-prop Constancy
 Constancy-is-prop = Con.Constancy-is-prop

 module _ {@♭ 𝓥 : Universe}
          (@♭ P : subuniverse 𝓤₁ 𝓥)
          (@♭ P-is-reflective : subuniverse-is-reflective P)
          (@♭ P-is-ℝ-null : (X : 𝓤₁ ̇ )
           → subuniverse-contains P X ↔ is-null ℝ X)
          (@♭ cem : Crisp-EM 𝓤₁)
          (@♭ descent : Unique-Boolean-Real-Path-Descent 𝓤₁)
          (r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ)
        where

  open import Modal.ReflectiveSubuniverse P P-is-reflective using (○ ; is-modal)
  open import gist.RealCohesion.BooleanCocycleObstruction ua pt P
   P-is-reflective
   using (B₂)

  crisp-constancy : ♭ Constancy
  crisp-constancy = inverse ♭-counit
                     (FCD.crisp-props-are-♭-discrete r♭ 𝟚-is-♭-discrete
                       Constancy Constancy-is-prop)
                     (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete)

  module _ (B₂-is-modal : is-modal B₂) where

   dyadic-image-shape-is-not-a-set-without-continuity
    : ¬ is-set (○ dyadic-image)
   dyadic-image-shape-is-not-a-set-without-continuity = γ crisp-constancy
    where
     γ : ♭ Constancy → ¬ is-set (○ dyadic-image)
     γ (ν ^♭) =
      shape-of-the-dyadic-image-is-not-a-set P P-is-reflective P-is-ℝ-null
                 cem (CC.crisp-real-continuity cem ν) descent r♭ 𝟚-is-♭-discrete
                 B₂-is-modal

   not-every-subset-of-ℝ-has-a-set-as-shape-without-continuity
    : ¬ ((A : ℝ → Ω 𝓤₁) → is-set (○ (Σ x ꞉ ℝ , A x holds)))
   not-every-subset-of-ℝ-has-a-set-as-shape-without-continuity =
    γ crisp-constancy
    where
     γ : ♭ Constancy → ¬ ((A : ℝ → Ω 𝓤₁) → is-set (○ (Σ x ꞉ ℝ , A x holds)))
     γ (ν ^♭) =
      subsets-of-ℝ-need-not-have-set-shape P P-is-reflective P-is-ℝ-null
                 cem (CC.crisp-real-continuity cem ν) descent r♭ 𝟚-is-♭-discrete
                 B₂-is-modal

   not-every-crisp-subset-of-ℝ-has-a-set-as-shape-without-continuity
    : ¬ ((@♭ A : ℝ → Ω 𝓤₁) → is-set (○ (Σ x ꞉ ℝ , A x holds)))
   not-every-crisp-subset-of-ℝ-has-a-set-as-shape-without-continuity =
    γ crisp-constancy
    where
     γ : ♭ Constancy → ¬ ((@♭ A : ℝ → Ω 𝓤₁) → is-set (○ (Σ x ꞉ ℝ , A x holds)))
     γ (ν ^♭) =
      crisp-subsets-of-ℝ-need-not-have-set-shape P P-is-reflective P-is-ℝ-null
                 cem (CC.crisp-real-continuity cem ν) descent r♭ 𝟚-is-♭-discrete
                 B₂-is-modal

\end{code}

nLab problem 4. Crispness can be removed from Shulman's approximate
intermediate value theorem [1, Theorem 11.4] assuming only Axiom R♭,
besides function extensionality, propositional extensionality and
propositional truncations: for f : ℝ → ℝ and p q a b : ℝ, none of
them crisp, with p < q, f a < q and p < f b, there merely is x with
p < f x < q. This is Theorem E of the proof note by Claude Fable 5.2
cited in gist.RealCohesion.ApproximateIVT, which proves it from Axiom
R♭, crisp-ap-^♭ and the ♭-discreteness of 𝟚.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import Notation.Order
 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import DedekindReals.Order fe pe pt
 import gist.RealCohesion.ApproximateIVT fe pe pt crisp-ap-^♭ as AIVT
 open PropositionalTruncation pt

 approximate-IVT
  : Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (f : ℝ → ℝ) (p q a b : ℝ)
  → p < q
  → f a < q
  → p < f b
  → ∃ x ꞉ ℝ , (p < f x) × (f x < q)
 approximate-IVT r♭ = AIVT.approximate-IVT r♭ 𝟚-is-♭-discrete

\end{code}

Axiom T in Shulman's §11. The continuity of crisp functions at crisp
points, Crisp-Real-Continuity, and Shulman's Theorem 11.2 for crisp
witnesses, assuming only crisp excluded middle and Axiom R♭, besides
function extensionality, propositional extensionality and
propositional truncations (gist.RealCohesion.CrispContinuity and
gist.RealCohesion.CrispExactIVT, with crisp-ap-^♭ and the
♭-discreteness of 𝟚 discharged). Shulman's versions also assume
Axiom T.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import Notation.Order
 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import DedekindReals.Order fe pe pt
 open import gist.RealCohesion.CrispRealAnalysis fe pe pt
  using (Crisp-Real-Continuity)
 open import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭
  using (maps-from-ℝ-to-Q-are-constant)
 import gist.RealCohesion.CrispContinuity fe pe pt as CC
 import gist.RealCohesion.CrispExactIVT fe pe pt as EIVT
 import gist.RealCohesion.Constancy fe pe pt as Con
 open PropositionalTruncation pt

 module _ (ν : Con.Constancy) where

  crisp-functions-are-continuous-without-T-from-constancy
   : (@♭ cem : Crisp-EM 𝓤₁)
   → Crisp-Real-Continuity
  crisp-functions-are-continuous-without-T-from-constancy cem =
   CC.crisp-real-continuity cem ν

  crisp-exact-IVT-without-T-from-constancy
   : (@♭ cem : Crisp-EM 𝓤₁)
   → (@♭ f : ℝ → ℝ) (@♭ c a b : ℝ)
   → f a < c → c < f b
   → ∃ x ꞉ ℝ , f x ＝ c
  crisp-exact-IVT-without-T-from-constancy cem = EIVT.crisp-exact-IVT cem ν

 crisp-functions-are-continuous-without-T
  : (@♭ cem : Crisp-EM 𝓤₁)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → Crisp-Real-Continuity
 crisp-functions-are-continuous-without-T cem r♭ =
  crisp-functions-are-continuous-without-T-from-constancy
   (maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

 crisp-exact-IVT-without-T
  : (@♭ cem : Crisp-EM 𝓤₁)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (@♭ f : ℝ → ℝ) (@♭ c a b : ℝ)
  → f a < c → c < f b
  → ∃ x ꞉ ℝ , f x ＝ c
 crisp-exact-IVT-without-T cem r♭ =
  crisp-exact-IVT-without-T-from-constancy
   (maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

\end{code}

Rational detection and its consequences. GPT-6 Astra's rational
detection holds assuming only Axiom R♭, besides function
extensionality, propositional extensionality and propositional
truncations (gist.RealCohesion.RationalDetection). It gives the
approximate intermediate value theorem with a rational witness. With
crisp excluded middle, it also gives the continuity of crisp
functions at all points of a neighbourhood, and Shulman's Theorem
11.2 for arbitrary witnesses, both without Axiom T
(gist.RealCohesion.CrispFunctionsEverywhere).

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import Notation.CanonicalMap
 open import Notation.Order
 open import Rationals.Type using (ℚ ; 0ℚ)
 open import DedekindReals.Type fe pe pt
 open import DedekindReals.Order fe pe pt
 open import gist.RealCohesion.RationalPoints fe pe pt using (ιₐ ; ιₐ-is-ι)
 import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭ as FCD
 import gist.RealCohesion.RationalDetection fe pe pt as RD
 import gist.RealCohesion.CrispFunctionsEverywhere fe pe pt as CFE
 import gist.RealCohesion.Constancy fe pe pt as Con
 open PropositionalTruncation pt

 module _ (ν : Con.Constancy) where

  rational-detection-from-constancy
   : (h : ℝ → ℝ) (x : ℝ) → 0ℚ < h x → ∃ q ꞉ ℚ , 0ℚ < h (ι q)
  rational-detection-from-constancy h x l =
   ∥∥-functor γ (RD.rational-detection ν h x l)
   where
    γ : (Σ q ꞉ ℚ , 0ℚ < h (ιₐ q)) → Σ q ꞉ ℚ , 0ℚ < h (ι q)
    γ (q , p) = q , transport (λ - → 0ℚ < h -) (ιₐ-is-ι q) p

  approximate-IVT-with-rational-witness-from-constancy
   : (f : ℝ → ℝ) (p q a b : ℝ)
   → p < q
   → f a < q
   → p < f b
   → ∃ r ꞉ ℚ , (p < f (ι r)) × (f (ι r) < q)
  approximate-IVT-with-rational-witness-from-constancy =
   RD.approximate-IVT-with-rational-witness-from-constancy ν

  crisp-functions-are-continuous-everywhere-without-T-from-constancy
   : (@♭ cem : Crisp-EM 𝓤₁)
   → (@♭ f : ℝ → ℝ) (@♭ t : ℝ) (u v : ℚ)
   → u < f t → f t < v
   → CFE.Holds-Near-Everywhere (λ s → (u < f s) × (f s < v)) t
  crisp-functions-are-continuous-everywhere-without-T-from-constancy cem =
   CFE.crisp-functions-are-continuous-everywhere cem ν

  exact-IVT-without-T-from-constancy
   : (@♭ cem : Crisp-EM 𝓤₁)
   → (@♭ f : ℝ → ℝ) (@♭ c : ℝ) (a b : ℝ)
   → f a < c → c < f b
   → ∃ x ꞉ ℝ , f x ＝ c
  exact-IVT-without-T-from-constancy cem = CFE.exact-IVT cem ν

 rational-detection
  : Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (h : ℝ → ℝ) (x : ℝ) → 0ℚ < h x → ∃ q ꞉ ℚ , 0ℚ < h (ι q)
 rational-detection r♭ =
  rational-detection-from-constancy
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete)

 approximate-IVT-with-rational-witness
  : Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (f : ℝ → ℝ) (p q a b : ℝ)
  → p < q
  → f a < q
  → p < f b
  → ∃ r ꞉ ℚ , (p < f (ι r)) × (f (ι r) < q)
 approximate-IVT-with-rational-witness r♭ =
  approximate-IVT-with-rational-witness-from-constancy
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete)

 crisp-functions-are-continuous-everywhere-without-T
  : (@♭ cem : Crisp-EM 𝓤₁)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (@♭ f : ℝ → ℝ) (@♭ t : ℝ) (u v : ℚ)
  → u < f t → f t < v
  → CFE.Holds-Near-Everywhere (λ s → (u < f s) × (f s < v)) t
 crisp-functions-are-continuous-everywhere-without-T cem r♭ =
  crisp-functions-are-continuous-everywhere-without-T-from-constancy
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

 exact-IVT-without-T
  : (@♭ cem : Crisp-EM 𝓤₁)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (@♭ f : ℝ → ℝ) (@♭ c : ℝ) (a b : ℝ)
  → f a < c → c < f b
  → ∃ x ꞉ ℝ , f x ＝ c
 exact-IVT-without-T cem r♭ =
  exact-IVT-without-T-from-constancy
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

\end{code}

Shulman's Corollary 11.6 without Axiom T. Assuming crisp excluded
middle and Axiom R♭, besides function extensionality, propositional
extensionality and propositional truncations, the canonical map
♭ (ℝ → ℝ) → (♭ ℝ → ♭ ℝ) is an embedding whose image consists of the
ε-δ continuous maps, so that ♭ (ℝ → ℝ) is equivalent to the type of
ε-δ continuous maps ♭ ℝ → ♭ ℝ (gist.RealCohesion.FlatRealFunctions,
with crisp-ap-^♭ and the ♭-discreteness of 𝟚 and of ♭ ℝ discharged).
That the canonical map is an embedding, and that crisp functions are
determined by their values at crisp points, needs only Axiom R♭.
Shulman's version also assumes Axiom T, and deduces injectivity from
the concreteness of ℝ, which is stated with ♯.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import UF.Embeddings using (is-embedding)
 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import gist.RealCohesion.CrispUniformContinuity fe pe pt
  using (is-ε-δ-continuous)
 import gist.RealCohesion.FlatRealFunctions fe pe pt crisp-ap-^♭ as FRF
 import gist.RealCohesion.Constancy fe pe pt as Con

 crisp-real-functions-are-determined-by-crisp-points-from-constancy
  : Con.Constancy
  → (@♭ F G : ℝ → ℝ) → ((@♭ x : ℝ) → F x ＝ G x) → F ＝ G
 crisp-real-functions-are-determined-by-crisp-points-from-constancy =
  FRF.crisp-functions-agreeing-at-crisp-points-are-equal

 crisp-real-functions-are-determined-by-crisp-points
  : Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (@♭ F G : ℝ → ℝ) → ((@♭ x : ℝ) → F x ＝ G x) → F ＝ G
 crisp-real-functions-are-determined-by-crisp-points r♭ =
  crisp-real-functions-are-determined-by-crisp-points-from-constancy
   (FRF.maps-from-ℝ-to-Q-are-constant' r♭ 𝟚-is-♭-discrete)

 canonical-map-is-an-embedding
  : Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → is-embedding (FRF.♭-action {𝓤₁} {𝓤₁} {ℝ} {ℝ})
 canonical-map-is-an-embedding r♭ = FRF.♭-action-is-embedding r♭ 𝟚-is-♭-discrete

 Shulman-Corollary-11-6-without-T
  : (@♭ cem : Crisp-EM 𝓤₁)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → is-embedding (FRF.♭-action {𝓤₁} {𝓤₁} {ℝ} {ℝ})
  × ((h : ♭ ℝ → ♭ ℝ) → fiber FRF.♭-action h ↔ is-ε-δ-continuous h)
 Shulman-Corollary-11-6-without-T cem r♭ =
  FRF.Shulman-Corollary-11-6 r♭ 𝟚-is-♭-discrete ♭-is-♭-discrete cem

 crisp-real-functions-are-the-continuous-maps
  : (@♭ cem : Crisp-EM 𝓤₁)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → ♭ (ℝ → ℝ) ≃ (Σ h ꞉ (♭ ℝ → ♭ ℝ) , is-ε-δ-continuous h)
 crisp-real-functions-are-the-continuous-maps cem r♭ =
  FRF.crisp-functions-are-the-continuous-maps r♭ 𝟚-is-♭-discrete ♭-is-♭-discrete
   cem

\end{code}

Axiom T relative to the native ♯. gist.RealCohesion.AxiomTObstruction
takes the sharp modality as a parameter S : Sharp-Modality. For the
native ♯ (gist.RealCohesion.NativeSharp) its results need no
assumption about ♯: under crisp excluded middle, Axiom T gives the
analytic Markov principle, and a dense family of reals that are not
not positive, but not all positive, refutes Axiom T, as do the five
conditions of gist.RealCohesion.AnalyticMarkovObstruction. Axiom T itself
remains a hypothesis. The names are those of
gist.RealCohesion.AxiomTObstruction. Two of them are targets of
gist.RealCohesion.BrouwerStatements: the analytic Markov principle for
apartness, which is Shulman's Theorem 8.32 without Axiom C1
(Target-8-32), and Lemma 4.1 of the write-up (Target-4-1).

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import MLTT.List hiding ([_])
 open import UF.SubtypeClassifier using (Ω)
 open import Notation.Order
 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import DedekindReals.Order fe pe pt
 open import gist.RealCohesion.NativeSharp using (native-sharp)
 open import gist.RealCohesion.AnalyticMarkovObstruction fe pe pt
  using (Analytic-Markov ; Five-Conditions)
 open import gist.RealCohesion.BrouwerStatements fe pe pt
  using (Target-4-1 ; Target-8-32)
 import gist.RealCohesion.AxiomTObstruction fe pe pt native-sharp as ATO

 Axiom-T : 𝓤₁ ̇
 Axiom-T = ATO.Axiom-T

 Axiom-T-gives-analytic-Markov : Crisp-EM 𝓤₀ → Axiom-T → Analytic-Markov
 Axiom-T-gives-analytic-Markov = ATO.Axiom-T-gives-analytic-Markov

 Axiom-T-gives-analytic-Markov-for-apartness : Target-8-32 native-sharp
 Axiom-T-gives-analytic-Markov-for-apartness =
  ATO.Axiom-T-gives-analytic-Markov-for-apartness

 Axiom-T-gives-positive-terms-are-codiscrete : Target-4-1 native-sharp
 Axiom-T-gives-positive-terms-are-codiscrete =
  ATO.Axiom-T-gives-positive-terms-are-codiscrete

 dense-positive-family-refutes-Axiom-T
  : Crisp-EM 𝓤₀
  → {𝓤 : Universe}
    (X : 𝓤 ̇ )
    (t : X → ℝ)
  → ((x : X) → ¬¬ (0ℝ < t x))
  → ¬ ((x : X) → 0ℝ < t x)
  → ¬ Axiom-T
 dense-positive-family-refutes-Axiom-T =
  ATO.dense-positive-family-refutes-Axiom-T

 five-conditions-refute-Axiom-T
  : Crisp-EM 𝓤₀
  → {𝓤 𝓥 : Universe}
    {X : 𝓤 ̇ }
    {t : X → ℝ}
    {B : X → List 𝟚 → Ω 𝓥}
  → Five-Conditions X t B
  → ¬ Axiom-T
 five-conditions-refute-Axiom-T = ATO.five-conditions-refute-Axiom-T

\end{code}

Shulman's Theorem 11.7 without crisp excluded middle: Axiom R♭ alone
refutes the analytic lesser limited principle of omniscience, which
says that every real number is ≤ 0 or ≥ 0 (gist.RealCohesion.AnalyticLLPO,
with crisp-ap-^♭ and the ♭-discreteness of 𝟚 discharged). This is
Theorem 7.10 of the write-up, stated as the target Target-7-10 of
Claude Fable 5.2's starter module gist.RealCohesion.BrouwerStatements,
which is identical to it. Shulman's version also assumes crisp
excluded middle.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import gist.RealCohesion.BrouwerStatements fe pe pt
  using (Analytic-LLPO ; Target-7-10)
 import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭ as FCD
 import gist.RealCohesion.AnalyticLLPO fe pe pt as LLPO
 import gist.RealCohesion.Constancy fe pe pt as Con

 constancy-refutes-analytic-LLPO : Con.Constancy → ¬ Analytic-LLPO
 constancy-refutes-analytic-LLPO = LLPO.analytic-LLPO-fails

 R♭-refutes-analytic-LLPO : Target-7-10
 R♭-refutes-analytic-LLPO r♭ =
  constancy-refutes-analytic-LLPO
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete)

\end{code}

Sequential hitting from Axiom R♭ alone
(gist.RealCohesion.FunctionalHitting, with crisp-ap-^♭ and the
♭-discreteness of 𝟚 discharged). Theorem 7.4 of the write-up, for ℝⁿ
with the supremum norm, is R♭-gives-sequential-hitting, and its form
for functionals on X → ℝ, which the write-up states in the remark
after the theorem, is
R♭-gives-positive-sequential-hitting-for-functionals. The target
Target-hitting of gist.RealCohesion.BrouwerStatements, with the
hypothesis 1 ≤ h a, and the closed half-lines of the blueprint
addendum are stated with the types of that module.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import gist.RealCohesion.BrouwerStatements fe pe pt
  using (Closed-Half-Lines-Are-Sequentially-Closed ; Target-hitting ;
         Sequential-Hitting-For-Functionals)
 import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭ as FCD
 import gist.RealCohesion.FunctionalHitting fe pe pt as FH
 import gist.RealCohesion.Constancy fe pe pt as Con

 module _ (ν : Con.Constancy) where

  constancy-gives-sequential-hitting : FH.Sequential-Hitting-In-ℝ^
  constancy-gives-sequential-hitting = FH.sequential-hitting-in-ℝ^ ν

  constancy-gives-positive-sequential-hitting-for-functionals
   : (𝓥 : Universe)
   → FH.Positive-Sequential-Hitting-For-Functionals 𝓥
  constancy-gives-positive-sequential-hitting-for-functionals 𝓥 =
   FH.positive-sequential-hitting-for-functionals ν {𝓥}

  constancy-gives-sequential-hitting-for-functionals
   : (𝓥 : Universe) → Sequential-Hitting-For-Functionals 𝓥
  constancy-gives-sequential-hitting-for-functionals 𝓥 =
   FH.sequential-hitting-for-functionals ν {𝓥}

  constancy-gives-closed-half-lines
   : (𝓥 : Universe)
   → Closed-Half-Lines-Are-Sequentially-Closed 𝓥
  constancy-gives-closed-half-lines 𝓥 =
   FH.closed-half-lines-are-sequentially-closed ν {𝓥}

 R♭-gives-sequential-hitting
  : Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → FH.Sequential-Hitting-In-ℝ^
 R♭-gives-sequential-hitting r♭ =
  constancy-gives-sequential-hitting
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete)

 R♭-gives-positive-sequential-hitting-for-functionals
  : (𝓥 : Universe)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → FH.Positive-Sequential-Hitting-For-Functionals 𝓥
 R♭-gives-positive-sequential-hitting-for-functionals 𝓥 r♭ =
  constancy-gives-positive-sequential-hitting-for-functionals
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) 𝓥

 R♭-gives-sequential-hitting-for-functionals
  : (𝓥 : Universe) → Target-hitting 𝓥
 R♭-gives-sequential-hitting-for-functionals 𝓥 r♭ =
  constancy-gives-sequential-hitting-for-functionals
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) 𝓥

 R♭-gives-closed-half-lines
  : (𝓥 : Universe)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → Closed-Half-Lines-Are-Sequentially-Closed 𝓥
 R♭-gives-closed-half-lines 𝓥 r♭ =
  constancy-gives-closed-half-lines
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) 𝓥

\end{code}

Kuhn's cubical lemma for n = 0, 1 and 2 (gist.RealCohesion.KuhnLemma),
stated with the type Kuhn-Lemma of gist.RealCohesion.BrouwerStatements.
Both modules take the statement from gist.RealCohesion.KuhnStatement,
by typed aliases, so their functions bit are equal by refl
(bits-agree), and each result of the
first module has the type of the second. Until the consolidation of
13 November 2026 the two modules defined bit separately, bits-agree
was proved by function extensionality, and the results were
transported along it; the name bits-agree and its type are kept.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import gist.RealCohesion.BrouwerStatements fe pe pt
  using (bit ; Kuhn-Lemma)
 import gist.RealCohesion.KuhnLemma as K
 import gist.RealCohesion.KuhnLemmaGeneral as KG

 bits-agree : K.bit ＝ bit
 bits-agree = refl

 kuhn-lemma-0 : Kuhn-Lemma 0
 kuhn-lemma-0 = K.kuhn-lemma-0

 kuhn-lemma-1 : Kuhn-Lemma 1
 kuhn-lemma-1 = K.kuhn-lemma-1

 kuhn-lemma-2 : Kuhn-Lemma 2
 kuhn-lemma-2 = K.kuhn-lemma-2 fe

\end{code}

Kuhn's lemma in every dimension, the last item of gate G14, by Claude
Fable 5.2's route, revision 3, which GPT-6 Astra audited
(gist.RealCohesion.KuhnCounting and gist.RealCohesion.KuhnLemmaGeneral),
in the same two forms: kuhn-lemma-for-bit, with the type Kuhn-Lemma of
gist.RealCohesion.KuhnLemma, which gate G27 uses, and kuhn-lemma, with
that of gist.RealCohesion.BrouwerStatements; since the consolidation
the two types are the same up to unfolding. With it, every theorem below
that is stated in every dimension relative to Kuhn's lemma holds
without that hypothesis. Each such theorem is followed by its form
…-in-every-dimension (for the cube form of Shulman's Theorem 12.6 from
crisp excluded middle: R♭-gives-Target-12-6-cube-from-LEM), which has
no Kuhn argument, also not inside the targets Target-3-7-crisp,
Target-3-7-sharp and Target-4-3 of gist.RealCohesion.BrouwerStatements:
their aliases include one, so these forms spell the statement out
without it. Their other hypotheses, their modalities and their
conclusions are those of the conditional forms, which are kept.

\begin{code}

 kuhn-lemma-for-bit : (n : ℕ) → K.Kuhn-Lemma n
 kuhn-lemma-for-bit = KG.kuhn-lemma fe

 kuhn-lemma : (n : ℕ) → Kuhn-Lemma n
 kuhn-lemma n = KG.kuhn-lemma fe n

\end{code}

The crisp fixed point on the cube, Corollary 3.7 of the write-up in
cube form (gist.RealCohesion.CubeFixedPoint, with crisp-ap-^♭ and the
♭-discreteness of 𝟚 discharged). R♭-gives-crisp-cube-fixed-points and
R♭-gives-sharp-cube-fixed-points are the targets Target-3-7-crisp and
Target-3-7-sharp of gist.RealCohesion.BrouwerStatements, the second
for the native ♯ of gist.RealCohesion.NativeSharp. Their hypothesis
Kuhn-Lemma n is passed unchanged to gist.RealCohesion.CubeFixedPoint,
whose statement of Kuhn's lemma, that of gist.RealCohesion.KuhnLemma,
is the same (bits-agree above). With Kuhn's lemma for n = 0 and n = 1,
both forms hold in dimensions 0 and 1 from crisp excluded middle and
Axiom R♭ alone, and the square follows below. The Euclidean ball in
place of the cube is gate G14, and so is Kuhn's lemma for general n,
which is discharged in the forms …-in-every-dimension.

\begin{code}

 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import gist.RealCohesion.BrouwerStatements fe pe pt
  using (Crisp-Cube-Fixed-Point ; Sharp-Cube-Fixed-Point ;
         crisp-fixed-points-give-sharp-fixed-points ; Target-3-7-crisp ;
          Target-3-7-sharp ;
         crisp-retracts-of-the-cube-have-fixed-points ;
         retracts-of-the-cube-have-sharp-fixed-points)
 open import gist.RealCohesion.NativeSharp using (native-sharp)
 import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭ as FCD
 import gist.RealCohesion.CubeFixedPoint fe pe pt as CFP
 import gist.RealCohesion.Constancy fe pe pt as Con

 module _ (ν : Con.Constancy) where

  constancy-gives-crisp-cube-fixed-points
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → (@♭ kuhn : Kuhn-Lemma n)
   → Crisp-Cube-Fixed-Point n
  constancy-gives-crisp-cube-fixed-points n cem kuhn =
   CFP.crisp-cube-fixed-point cem ν {n} kuhn

  constancy-gives-sharp-cube-fixed-points
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → (@♭ kuhn : Kuhn-Lemma n)
   → Sharp-Cube-Fixed-Point native-sharp n
  constancy-gives-sharp-cube-fixed-points n cem kuhn =
   crisp-fixed-points-give-sharp-fixed-points native-sharp n
    (constancy-gives-crisp-cube-fixed-points n cem kuhn)

  constancy-gives-crisp-cube-fixed-points-in-every-dimension
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → Crisp-Cube-Fixed-Point n
  constancy-gives-crisp-cube-fixed-points-in-every-dimension n cem =
   constancy-gives-crisp-cube-fixed-points n cem (kuhn-lemma n)

  constancy-gives-sharp-cube-fixed-points-in-every-dimension
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → Sharp-Cube-Fixed-Point native-sharp n
  constancy-gives-sharp-cube-fixed-points-in-every-dimension n cem =
   constancy-gives-sharp-cube-fixed-points n cem (kuhn-lemma n)

  constancy-gives-crisp-fixed-points-in-dimension-0
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Crisp-Cube-Fixed-Point 0
  constancy-gives-crisp-fixed-points-in-dimension-0 cem =
   CFP.crisp-cube-fixed-point cem ν K.kuhn-lemma-0

  constancy-gives-crisp-fixed-points-in-dimension-1
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Crisp-Cube-Fixed-Point 1
  constancy-gives-crisp-fixed-points-in-dimension-1 cem =
   CFP.crisp-cube-fixed-point cem ν K.kuhn-lemma-1

  constancy-gives-sharp-fixed-points-in-dimension-0
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Sharp-Cube-Fixed-Point native-sharp 0
  constancy-gives-sharp-fixed-points-in-dimension-0 cem =
   crisp-fixed-points-give-sharp-fixed-points native-sharp 0
    (constancy-gives-crisp-fixed-points-in-dimension-0 cem)

  constancy-gives-sharp-fixed-points-in-dimension-1
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Sharp-Cube-Fixed-Point native-sharp 1
  constancy-gives-sharp-fixed-points-in-dimension-1 cem =
   crisp-fixed-points-give-sharp-fixed-points native-sharp 1
    (constancy-gives-crisp-fixed-points-in-dimension-1 cem)

 R♭-gives-crisp-cube-fixed-points : (@♭ n : ℕ) → Target-3-7-crisp n
 R♭-gives-crisp-cube-fixed-points n cem r♭ =
  constancy-gives-crisp-cube-fixed-points
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) n cem

 R♭-gives-sharp-cube-fixed-points : (@♭ n : ℕ) → Target-3-7-sharp native-sharp n
 R♭-gives-sharp-cube-fixed-points n cem r♭ =
  constancy-gives-sharp-cube-fixed-points
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) n cem

 R♭-gives-crisp-cube-fixed-points-in-every-dimension
  : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → Crisp-Cube-Fixed-Point n
 R♭-gives-crisp-cube-fixed-points-in-every-dimension n cem r♭ =
  constancy-gives-crisp-cube-fixed-points-in-every-dimension
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) n cem

 R♭-gives-sharp-cube-fixed-points-in-every-dimension
  : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → Sharp-Cube-Fixed-Point native-sharp n
 R♭-gives-sharp-cube-fixed-points-in-every-dimension n cem r♭ =
  constancy-gives-sharp-cube-fixed-points-in-every-dimension
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) n cem

 R♭-gives-crisp-fixed-points-in-dimension-0
  : (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → Crisp-Cube-Fixed-Point 0
 R♭-gives-crisp-fixed-points-in-dimension-0 cem r♭ =
  constancy-gives-crisp-fixed-points-in-dimension-0
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

 R♭-gives-crisp-fixed-points-in-dimension-1
  : (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → Crisp-Cube-Fixed-Point 1
 R♭-gives-crisp-fixed-points-in-dimension-1 cem r♭ =
  constancy-gives-crisp-fixed-points-in-dimension-1
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

 R♭-gives-sharp-fixed-points-in-dimension-0
  : (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → Sharp-Cube-Fixed-Point native-sharp 0
 R♭-gives-sharp-fixed-points-in-dimension-0 cem r♭ =
  constancy-gives-sharp-fixed-points-in-dimension-0
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

 R♭-gives-sharp-fixed-points-in-dimension-1
  : (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → Sharp-Cube-Fixed-Point native-sharp 1
 R♭-gives-sharp-fixed-points-in-dimension-1 cem r♭ =
  constancy-gives-sharp-fixed-points-in-dimension-1
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

\end{code}

Approximate fixed points on the cube, Theorem 4.3 of the write-up in
cube form (gist.RealCohesion.ApproximateCubeFixedPoint, with
crisp-ap-^♭ and the ♭-discreteness of 𝟚 discharged), as the target
Target-4-3 of gist.RealCohesion.BrouwerStatements for the native ♯,
with its hypothesis Kuhn-Lemma n passed on unchanged as above; and in
dimensions 0 and 1 from crisp excluded middle, Axiom R♭
and Axiom T alone; and in every dimension, with Kuhn's lemma
discharged. The Euclidean ball in place of the cube is gate G14.

\begin{code}

 open import gist.RealCohesion.BrouwerStatements fe pe pt
  using (Approximate-Cube-Fixed-Point ; Target-4-3)
 import gist.RealCohesion.ApproximateCubeFixedPoint fe pe pt as ACFP
 import gist.RealCohesion.AxiomTObstruction fe pe pt native-sharp as ATO

 module _ (ν : Con.Constancy) where

  constancy-and-T-give-approximate-cube-fixed-points
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → ATO.Axiom-T
   → (@♭ kuhn : Kuhn-Lemma n)
   → Approximate-Cube-Fixed-Point n
  constancy-and-T-give-approximate-cube-fixed-points n cem T kuhn =
   ACFP.cube-approximate-fixed-point native-sharp cem ν T {n} kuhn

  constancy-and-T-give-approximate-cube-fixed-points-in-every-dimension
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → ATO.Axiom-T
   → Approximate-Cube-Fixed-Point n
  constancy-and-T-give-approximate-cube-fixed-points-in-every-dimension n cem
   T =
   constancy-and-T-give-approximate-cube-fixed-points n cem T (kuhn-lemma n)

  constancy-and-T-give-approximate-fixed-points-in-dimension-0
   : (@♭ cem : Crisp-EM 𝓤₀)
   → ATO.Axiom-T
   → Approximate-Cube-Fixed-Point 0
  constancy-and-T-give-approximate-fixed-points-in-dimension-0 cem T =
   ACFP.cube-approximate-fixed-point native-sharp cem ν T K.kuhn-lemma-0

  constancy-and-T-give-approximate-fixed-points-in-dimension-1
   : (@♭ cem : Crisp-EM 𝓤₀)
   → ATO.Axiom-T
   → Approximate-Cube-Fixed-Point 1
  constancy-and-T-give-approximate-fixed-points-in-dimension-1 cem T =
   ACFP.cube-approximate-fixed-point native-sharp cem ν T K.kuhn-lemma-1

 R♭-and-T-give-approximate-cube-fixed-points : (@♭ n : ℕ)
                                             → Target-4-3 native-sharp n
 R♭-and-T-give-approximate-cube-fixed-points n cem r♭ =
  constancy-and-T-give-approximate-cube-fixed-points
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) n cem

 R♭-and-T-give-approximate-cube-fixed-points-in-every-dimension
  : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → ATO.Axiom-T
  → Approximate-Cube-Fixed-Point n
 R♭-and-T-give-approximate-cube-fixed-points-in-every-dimension n cem r♭ =
  constancy-and-T-give-approximate-cube-fixed-points-in-every-dimension
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) n cem

 R♭-and-T-give-approximate-fixed-points-in-dimension-0
  : (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → ATO.Axiom-T
  → Approximate-Cube-Fixed-Point 0
 R♭-and-T-give-approximate-fixed-points-in-dimension-0 cem r♭ =
  constancy-and-T-give-approximate-fixed-points-in-dimension-0
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

 R♭-and-T-give-approximate-fixed-points-in-dimension-1
  : (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → ATO.Axiom-T
  → Approximate-Cube-Fixed-Point 1
 R♭-and-T-give-approximate-fixed-points-in-dimension-1 cem r♭ =
  constancy-and-T-give-approximate-fixed-points-in-dimension-1
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

\end{code}

The square: Corollary 3.7, in both forms, and Theorem 4.3 for the
square [-1,1]², with Kuhn's lemma for n = 2 discharged. This is the
dimension of Shulman's Theorem 12.4 and Corollary 12.5, here for the
square in place of the disc, with the supremum norm, and without his
Axiom T and univalence (gate G13 of the blueprint addendum).

\begin{code}

 module _ (ν : Con.Constancy) where

  constancy-gives-crisp-fixed-points-in-dimension-2
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Crisp-Cube-Fixed-Point 2
  constancy-gives-crisp-fixed-points-in-dimension-2 cem =
   CFP.crisp-cube-fixed-point cem ν (K.kuhn-lemma-2 fe)

  constancy-gives-sharp-fixed-points-in-dimension-2
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Sharp-Cube-Fixed-Point native-sharp 2
  constancy-gives-sharp-fixed-points-in-dimension-2 cem =
   crisp-fixed-points-give-sharp-fixed-points native-sharp 2
    (constancy-gives-crisp-fixed-points-in-dimension-2 cem)

  constancy-and-T-give-approximate-fixed-points-in-dimension-2
   : (@♭ cem : Crisp-EM 𝓤₀)
   → ATO.Axiom-T
   → Approximate-Cube-Fixed-Point 2
  constancy-and-T-give-approximate-fixed-points-in-dimension-2 cem T =
   ACFP.cube-approximate-fixed-point native-sharp cem ν T (K.kuhn-lemma-2 fe)

 R♭-gives-crisp-fixed-points-in-dimension-2
  : (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → Crisp-Cube-Fixed-Point 2
 R♭-gives-crisp-fixed-points-in-dimension-2 cem r♭ =
  constancy-gives-crisp-fixed-points-in-dimension-2
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

 R♭-gives-sharp-fixed-points-in-dimension-2
  : (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → Sharp-Cube-Fixed-Point native-sharp 2
 R♭-gives-sharp-fixed-points-in-dimension-2 cem r♭ =
  constancy-gives-sharp-fixed-points-in-dimension-2
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

 R♭-and-T-give-approximate-fixed-points-in-dimension-2
  : (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → ATO.Axiom-T
  → Approximate-Cube-Fixed-Point 2
 R♭-and-T-give-approximate-fixed-points-in-dimension-2 cem r♭ =
  constancy-and-T-give-approximate-fixed-points-in-dimension-2
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

\end{code}

The Euclidean ball: Corollary 3.7 of the write-up for the ball Dⁿ, in
both forms (gate G14, step E2). The write-up's Dⁿ is
{x : ℝⁿ | |x| ≤ 1}; here it is written {x : ℝⁿ | ‖x‖² ≤ 1}, the same
set, without square roots (gist.RealCohesion.EuclideanBall). It is a
retract of the cube by crisp maps, so it inherits the fixed points of
the cube by crisp-retracts-of-the-cube-have-fixed-points and
retracts-of-the-cube-have-sharp-fixed-points of
gist.RealCohesion.BrouwerStatements. As for the cube, Kuhn's lemma in
dimension n is a hypothesis of the first forms; it is discharged in the
forms …-in-every-dimension, and for n = 2 below. For
n = 2 these are Shulman's Theorem 12.4 and Corollary 12.5 for the disc,
from crisp excluded middle and Axiom R♭, without his Axiom T and
univalence.

\begin{code}

 import gist.RealCohesion.EuclideanBall fe pe pt as EB
 import gist.CohesiveApartness.Sharp as NS
 open PropositionalTruncation pt using (Exists)

 module _ (ν : Con.Constancy) where

  constancy-gives-crisp-fixed-points-on-the-ball
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → (@♭ kuhn : Kuhn-Lemma n)
   → (@♭ f : EB.Ball n → EB.Ball n) → ∃ x ꞉ EB.Ball n , f x ＝ x
  constancy-gives-crisp-fixed-points-on-the-ball n cem kuhn =
   crisp-retracts-of-the-cube-have-fixed-points n (EB.Ball n) EB.ball-to-cube
    EB.cube-to-ball
    EB.ball-is-a-retract-of-the-cube
     (constancy-gives-crisp-cube-fixed-points ν n cem kuhn)

  constancy-gives-sharp-fixed-points-on-the-ball
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → (@♭ kuhn : Kuhn-Lemma n)
   → (f : EB.Ball n → EB.Ball n) → NS.♯ (∃ x ꞉ EB.Ball n , f x ＝ x)
  constancy-gives-sharp-fixed-points-on-the-ball n cem kuhn =
   retracts-of-the-cube-have-sharp-fixed-points native-sharp n (EB.Ball n)
    EB.ball-to-cube
    EB.cube-to-ball EB.ball-is-a-retract-of-the-cube
    (constancy-gives-crisp-cube-fixed-points ν n cem kuhn)

  constancy-gives-crisp-fixed-points-on-the-ball-in-every-dimension
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → (@♭ f : EB.Ball n → EB.Ball n) → ∃ x ꞉ EB.Ball n , f x ＝ x
  constancy-gives-crisp-fixed-points-on-the-ball-in-every-dimension n cem =
   constancy-gives-crisp-fixed-points-on-the-ball n cem (kuhn-lemma n)

  constancy-gives-sharp-fixed-points-on-the-ball-in-every-dimension
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → (f : EB.Ball n → EB.Ball n) → NS.♯ (∃ x ꞉ EB.Ball n , f x ＝ x)
  constancy-gives-sharp-fixed-points-on-the-ball-in-every-dimension n cem =
   constancy-gives-sharp-fixed-points-on-the-ball n cem (kuhn-lemma n)

  constancy-gives-crisp-fixed-points-on-the-disc
   : (@♭ cem : Crisp-EM 𝓤₀)
   → (@♭ f : EB.Ball 2 → EB.Ball 2) → ∃ x ꞉ EB.Ball 2 , f x ＝ x
  constancy-gives-crisp-fixed-points-on-the-disc cem =
   crisp-retracts-of-the-cube-have-fixed-points 2 (EB.Ball 2) EB.ball-to-cube
    EB.cube-to-ball
    EB.ball-is-a-retract-of-the-cube
     (constancy-gives-crisp-fixed-points-in-dimension-2 ν cem)

  constancy-gives-sharp-fixed-points-on-the-disc
   : (@♭ cem : Crisp-EM 𝓤₀)
   → (f : EB.Ball 2 → EB.Ball 2) → NS.♯ (∃ x ꞉ EB.Ball 2 , f x ＝ x)
  constancy-gives-sharp-fixed-points-on-the-disc cem =
   retracts-of-the-cube-have-sharp-fixed-points native-sharp 2 (EB.Ball 2)
    EB.ball-to-cube
    EB.cube-to-ball EB.ball-is-a-retract-of-the-cube
    (constancy-gives-crisp-fixed-points-in-dimension-2 ν cem)

 R♭-gives-crisp-fixed-points-on-the-ball
  : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (@♭ kuhn : Kuhn-Lemma n)
  → (@♭ f : EB.Ball n → EB.Ball n) → ∃ x ꞉ EB.Ball n , f x ＝ x
 R♭-gives-crisp-fixed-points-on-the-ball n cem r♭ =
  constancy-gives-crisp-fixed-points-on-the-ball
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) n cem

 R♭-gives-sharp-fixed-points-on-the-ball
  : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (@♭ kuhn : Kuhn-Lemma n)
  → (f : EB.Ball n → EB.Ball n) → NS.♯ (∃ x ꞉ EB.Ball n , f x ＝ x)
 R♭-gives-sharp-fixed-points-on-the-ball n cem r♭ =
  constancy-gives-sharp-fixed-points-on-the-ball
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) n cem

 R♭-gives-crisp-fixed-points-on-the-ball-in-every-dimension
  : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (@♭ f : EB.Ball n → EB.Ball n) → ∃ x ꞉ EB.Ball n , f x ＝ x
 R♭-gives-crisp-fixed-points-on-the-ball-in-every-dimension n cem r♭ =
  constancy-gives-crisp-fixed-points-on-the-ball-in-every-dimension
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) n cem

 R♭-gives-sharp-fixed-points-on-the-ball-in-every-dimension
  : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (f : EB.Ball n → EB.Ball n) → NS.♯ (∃ x ꞉ EB.Ball n , f x ＝ x)
 R♭-gives-sharp-fixed-points-on-the-ball-in-every-dimension n cem r♭ =
  constancy-gives-sharp-fixed-points-on-the-ball-in-every-dimension
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) n cem

 R♭-gives-crisp-fixed-points-on-the-disc
  : (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (@♭ f : EB.Ball 2 → EB.Ball 2) → ∃ x ꞉ EB.Ball 2 , f x ＝ x
 R♭-gives-crisp-fixed-points-on-the-disc cem r♭ =
  constancy-gives-crisp-fixed-points-on-the-disc
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

 R♭-gives-sharp-fixed-points-on-the-disc
  : (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (f : EB.Ball 2 → EB.Ball 2) → NS.♯ (∃ x ꞉ EB.Ball 2 , f x ＝ x)
 R♭-gives-sharp-fixed-points-on-the-disc cem r♭ =
  constancy-gives-sharp-fixed-points-on-the-disc
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

\end{code}

Theorem 4.3 of the write-up for the ball (gate G14, step E3): from
crisp excluded middle, Axiom R♭ and Axiom T, every f : Dⁿ → Dⁿ, not
necessarily crisp, has for every rational ε > 0 a rational point r of
Dⁿ with ‖f r - r‖² < ε², that is, |f r - r| < ε. It comes from the cube
form, through the retraction of gist.RealCohesion.EuclideanBall, which
is nonexpansive (part E of Codex's audit). Kuhn's lemma in dimension n
is a hypothesis of the first form, discharged in every dimension in the
second and for the disc.

\begin{code}

 module _ (ν : Con.Constancy) where

  constancy-and-T-give-approximate-fixed-points-on-the-ball
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → ATO.Axiom-T
   → (@♭ kuhn : Kuhn-Lemma n)
   → EB.Approximate-Fixed-Points-On-The-Ball n
  constancy-and-T-give-approximate-fixed-points-on-the-ball n cem T kuhn =
   EB.approximate-fixed-points-on-the-ball
    (constancy-and-T-give-approximate-cube-fixed-points ν n cem T kuhn)

  constancy-and-T-give-approximate-fixed-points-on-the-ball-in-every-dimension
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → ATO.Axiom-T
   → EB.Approximate-Fixed-Points-On-The-Ball n
  constancy-and-T-give-approximate-fixed-points-on-the-ball-in-every-dimension
   n cem T =
   constancy-and-T-give-approximate-fixed-points-on-the-ball n cem T
    (kuhn-lemma n)

  constancy-and-T-give-approximate-fixed-points-on-the-disc
   : (@♭ cem : Crisp-EM 𝓤₀)
   → ATO.Axiom-T
   → EB.Approximate-Fixed-Points-On-The-Ball 2
  constancy-and-T-give-approximate-fixed-points-on-the-disc cem T =
   EB.approximate-fixed-points-on-the-ball
    (constancy-and-T-give-approximate-fixed-points-in-dimension-2 ν cem T)

 R♭-and-T-give-approximate-fixed-points-on-the-ball
  : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → ATO.Axiom-T
  → (@♭ kuhn : Kuhn-Lemma n)
  → EB.Approximate-Fixed-Points-On-The-Ball n
 R♭-and-T-give-approximate-fixed-points-on-the-ball n cem r♭ =
  constancy-and-T-give-approximate-fixed-points-on-the-ball
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) n cem

 R♭-and-T-give-approximate-fixed-points-on-the-ball-in-every-dimension
  : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → ATO.Axiom-T
  → EB.Approximate-Fixed-Points-On-The-Ball n
 R♭-and-T-give-approximate-fixed-points-on-the-ball-in-every-dimension
  n cem r♭ =
  constancy-and-T-give-approximate-fixed-points-on-the-ball-in-every-dimension
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) n cem

 R♭-and-T-give-approximate-fixed-points-on-the-disc
  : (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → ATO.Axiom-T
  → EB.Approximate-Fixed-Points-On-The-Ball 2
 R♭-and-T-give-approximate-fixed-points-on-the-disc cem r♭ =
  constancy-and-T-give-approximate-fixed-points-on-the-disc
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

\end{code}

Shulman's Lemma 12.3 (gate G14, step E4), from crisp excluded middle
for 𝓤₀ and Axiom T, without his Axiom C1, and in every dimension: if
some f : Dⁿ → Dⁿ, not necessarily crisp, has no fixed point, then Dⁿ
retracts onto the sphere Sⁿ⁻¹ = {x : ℝⁿ | ‖x‖² = 1}
(gist.RealCohesion.EuclideanSphere). The two axioms are used only
through the analytic Markov principle, Axiom-T-gives-analytic-Markov
above, which is Shulman's Theorem 8.32 without C1. The forms
…-literal-Lemma-12-3…, added on 13 November 2026, conclude with a
retraction of the inclusion sphere-to-ball
(ES.Literal-Lemma-12-3-for-the-ball), which the proof constructs; for
n = 2 this is his Lemma 12.3 as he states it, with C1 removed (Remark
3.8 of the write-up; part B of GPT-6 Astra's audit of 12 November
2026). The first two forms, with the same hypotheses, conclude with
the type-level retract retract (Sphere n) of (Ball n), the consequence
that forgets that the section is the inclusion.

\begin{code}

 import gist.RealCohesion.EuclideanSphere fe pe pt as ES

 LEM-and-T-give-Lemma-12-3
  : Crisp-EM 𝓤₀ → ATO.Axiom-T → (n : ℕ) → ES.Lemma-12-3-for-the-ball n
 LEM-and-T-give-Lemma-12-3 cem T =
  ES.Analytic-Markov-gives-Lemma-12-3 (ATO.Axiom-T-gives-analytic-Markov cem T)

 LEM-and-T-give-Lemma-12-3-for-the-disc
  : Crisp-EM 𝓤₀ → ATO.Axiom-T → ES.Lemma-12-3-for-the-ball 2
 LEM-and-T-give-Lemma-12-3-for-the-disc cem T =
  LEM-and-T-give-Lemma-12-3 cem T 2

 LEM-and-T-give-literal-Lemma-12-3
  : Crisp-EM 𝓤₀ → ATO.Axiom-T → (n : ℕ)
  → ES.Literal-Lemma-12-3-for-the-ball n
 LEM-and-T-give-literal-Lemma-12-3 cem T =
  ES.Analytic-Markov-gives-literal-Lemma-12-3
   (ATO.Axiom-T-gives-analytic-Markov cem T)

 LEM-and-T-give-literal-Lemma-12-3-for-the-disc
  : Crisp-EM 𝓤₀ → ATO.Axiom-T → ES.Literal-Lemma-12-3-for-the-ball 2
 LEM-and-T-give-literal-Lemma-12-3-for-the-disc cem T =
  LEM-and-T-give-literal-Lemma-12-3 cem T 2

\end{code}

The targets of Claude Fable 5.2's second addendum, stated in
gist.RealCohesion.ShulmanWeakeningsStatements: gate G16, and the
bridges of its §2 to theorems proved above.

 * Strong extensionality, Lemma 7.12 of the write-up
   (gist.RealCohesion.StrongExtensionality), and rational detection in
   n variables (gist.RealCohesion.RationalDetection), from Axiom R♭.
   Both are new.

 * Rational detection in one variable and the exact intermediate value
   theorem, in the words of the starter module: its hypotheses
   ∃ x , 0 < h x and ∃ a , f a < c are eliminated, and 0ℝ < y is
   converted to 0ℚ < y and back.

 * Shulman's Theorem 11.5 and Corollary 11.6 in his words, as
   Shulman-11-5 and Shulman-11-6 of the starter module. Continuity by
   rational intervals and by TypeTopology's rational balls is converted
   to the strict ε-δ form of the starter module
   (gist.RealCohesion.ContinuityForms). The canonical map is an
   embedding, so it is injective; its fibres give the image of the
   starter module; and the starter's ♭-apply₁ is the map ♭-action of
   gist.RealCohesion.FlatRealFunctions.

The library's theorems assume Crisp-EM 𝓤₁, where the targets
Target-3-5, Target-11-5 and Target-11-6 of the starter module assume
Crisp-EM 𝓤₀. So the last three statements below assume Crisp-EM 𝓤₁.
The same holds for crisp-functions-are-continuous-without-T above,
which otherwise has the type of the target
Target-crisp-real-continuity.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import Fin.Type
 open import UF.Subsingletons-FunExt using (Π-is-prop)
 open import Notation.CanonicalMap
 open import Notation.Order
 open import Rationals.Type using (ℚ ; 0ℚ)
 open import DedekindReals.Type fe pe pt
 open import DedekindReals.Order fe pe pt
 open import gist.RealCohesion.RationalPoints fe pe pt using (ιₐ ; ιₐ-is-ι)
 open import gist.RealCohesion.SequentialHitting fe pe pt
  using (positive-from-rational)
 open import gist.RealCohesion.FunctionalHitting fe pe pt
  using (rational-from-positive)
 open import gist.RealCohesion.BrouwerStatements fe pe pt
  using (ℝ^ ; rational-point)
 open import UF.Embeddings using (embeddings-are-lc ; is-embedding)
 open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt
  using (Target-strong-extensionality ; Target-7-6 ; Target-7-6-in-dimension ;
          Crisp-Exact-IVT ;
         Shulman-11-5 ; Shulman-11-6 ; ♭-apply₁ ; is-♭-ε-δ-continuous ;
         Strongly-Extensional ; Rational-Detection ;
         Rational-Detection-In-Dimension)
 open import gist.RealCohesion.CrispUniformContinuity fe pe pt
  using (is-ε-δ-continuous ; being-ε-δ-continuous-is-prop)
 import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭ as FCD
 import gist.RealCohesion.RationalDetection fe pe pt as RD
 import gist.RealCohesion.StrongExtensionality fe pe pt as SE
 import gist.RealCohesion.CrispFunctionsEverywhere fe pe pt as CFE
 import gist.RealCohesion.FlatRealFunctions fe pe pt crisp-ap-^♭ as FRF
 import gist.RealCohesion.ContinuityForms fe pe pt as CF
 import gist.RealCohesion.Constancy fe pe pt as Con
 open PropositionalTruncation pt

 module _ (ν : Con.Constancy) where

  constancy-gives-strong-extensionality
   : (f : ℝ → ℝ) → Strongly-Extensional f
  constancy-gives-strong-extensionality = SE.strong-extensionality ν

  constancy-gives-rational-detection : Rational-Detection
  constancy-gives-rational-detection h = ∥∥-rec ∃-is-prop γ
   where
    γ : (Σ x ꞉ ℝ , 0ℝ < h x) → ∃ q ꞉ ℚ , 0ℝ < h (ι q)
    γ (x , l) = ∥∥-functor δ
                 (RD.rational-detection ν h x (rational-from-positive (h x) l))
     where
      δ : (Σ q ꞉ ℚ , 0ℚ < h (ιₐ q)) → Σ q ꞉ ℚ , 0ℝ < h (ι q)
      δ (q , m) = q , positive-from-rational (h (ι q))
                       (transport (λ - → 0ℚ < h -) (ιₐ-is-ι q) m)

  constancy-gives-rational-detection-in-dimension
   : (n : ℕ) → Rational-Detection-In-Dimension n
  constancy-gives-rational-detection-in-dimension n h = ∥∥-rec ∃-is-prop γ
   where
    γ : (Σ x ꞉ ℝ^ n , 0ℝ < h x) → ∃ q ꞉ (Fin n → ℚ) , 0ℝ < h (rational-point q)
    γ (x , l) = ∥∥-functor δ
                 (RD.rational-detection-in-dimension ν
                   n h x (rational-from-positive (h x) l))
     where
      δ : (Σ q ꞉ (Fin n → ℚ) , 0ℚ < h (λ i → ιₐ (q i)))
        → Σ q ꞉ (Fin n → ℚ) , 0ℝ < h (rational-point q)
      δ (q , m) = q , positive-from-rational (h (rational-point q))
                       (transport (λ - → 0ℚ < h -)
                         (dfunext fe (λ i → ιₐ-is-ι (q i))) m)

  constancy-gives-crisp-exact-IVT
   : (@♭ cem : Crisp-EM 𝓤₁)
   → Crisp-Exact-IVT
  constancy-gives-crisp-exact-IVT cem f c =
   ∥∥-rec (Π-is-prop fe (λ _ → ∃-is-prop)) γ
   where
    γ : (Σ a ꞉ ℝ , f a < c) → (∃ b ꞉ ℝ , c < f b) → ∃ x ꞉ ℝ , f x ＝ c
    γ (a , l) = ∥∥-rec ∃-is-prop δ
     where
      δ : (Σ b ꞉ ℝ , c < f b) → ∃ x ꞉ ℝ , f x ＝ c
      δ (b , m) = CFE.exact-IVT cem ν f c a b l m

  constancy-gives-Shulman-11-5
   : (@♭ cem : Crisp-EM 𝓤₁)
   → Shulman-11-5
  constancy-gives-Shulman-11-5 cem f a =
   CF.interval-gives-strict id f a
    (CFE.crisp-functions-are-continuous-everywhere cem ν f a)

 R♭-gives-strong-extensionality : Target-strong-extensionality
 R♭-gives-strong-extensionality r♭ =
  constancy-gives-strong-extensionality
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete)

 R♭-gives-rational-detection : Target-7-6
 R♭-gives-rational-detection r♭ =
  constancy-gives-rational-detection
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete)

 R♭-gives-rational-detection-in-dimension : (n : ℕ) → Target-7-6-in-dimension n
 R♭-gives-rational-detection-in-dimension n r♭ =
  constancy-gives-rational-detection-in-dimension
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) n

 R♭-gives-crisp-exact-IVT
  : (@♭ cem : Crisp-EM 𝓤₁)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → Crisp-Exact-IVT
 R♭-gives-crisp-exact-IVT cem r♭ =
  constancy-gives-crisp-exact-IVT
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

 R♭-gives-Shulman-11-5
  : (@♭ cem : Crisp-EM 𝓤₁)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → Shulman-11-5
 R♭-gives-Shulman-11-5 cem r♭ =
  constancy-gives-Shulman-11-5
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

 ♭-apply₁-is-♭-action : ♭-apply₁ ＝ FRF.♭-action
 ♭-apply₁-is-♭-action = dfunext fe γ
  where
   γ : (u : ♭ (ℝ → ℝ)) → ♭-apply₁ u ＝ FRF.♭-action u
   γ (f ^♭) = dfunext fe δ
    where
     δ : (x : ♭ ℝ) → ♭-apply₁ (f ^♭) x ＝ FRF.♭-action (f ^♭) x
     δ (x ^♭) = refl

\end{code}

The form of R♭-gives-Shulman-11-6, from Axiom C1 for an ordinary family
of generators and a strictly rising generator path in ℝ, merely (W3 of
Claude Fable 5.2's consolidation plan of 13 November 2026, released by
GPT-6 Astra; gist.RealCohesion.TheoremsFromC1 states it with its type
written out). The theorem under Axiom R♭ is its instance for the one
generator ℝ, whose identity map rises from 0 to 1.

\begin{code}

 module _ {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
          (nc : ∥ Con.Rising-Generator-Path R ∥)
        where

  Shulman-11-6-under-C1
   : (@♭ cem : Crisp-EM 𝓤₁)
   → Shulman-11-6
  Shulman-11-6-under-C1 cem = I , II
   where
    C : is-embedding (FRF.♭-action {𝓤₁} {𝓤₁} {ℝ} {ℝ})
      × ((h : ♭ ℝ → ♭ ℝ) → fiber FRF.♭-action h ↔ is-ε-δ-continuous h)
    C = FRF.under-C1.Shulman-Corollary-11-6 R c1 𝟚-is-♭-discrete
         ♭-is-♭-discrete nc cem

    I : (f g : ♭ (ℝ → ℝ)) → ♭-apply₁ f ＝ ♭-apply₁ g → f ＝ g
    I f g e = embeddings-are-lc FRF.♭-action (pr₁ C)
               (transport (λ - → - f ＝ - g) ♭-apply₁-is-♭-action e)

    II : (h : ♭ ℝ → ♭ ℝ)
       → (∃ f ꞉ ♭ (ℝ → ℝ) , ♭-apply₁ f ＝ h) ↔ is-♭-ε-δ-continuous h
    II h = III , IV
     where
      V : fiber FRF.♭-action h ↔ is-ε-δ-continuous h
      V = pr₂ C h

      III : (∃ f ꞉ ♭ (ℝ → ℝ) , ♭-apply₁ f ＝ h) → is-♭-ε-δ-continuous h
      III t x = CF.ball-gives-strict ♭-counit (λ y → ♭-counit (h y)) x (VI x)
       where
        VI : is-ε-δ-continuous h
        VI = ∥∥-rec (being-ε-δ-continuous-is-prop h)
              (λ (f , e) →
                pr₁ V (f , transport (λ - → - f ＝ h) ♭-apply₁-is-♭-action e)) t

      IV : is-♭-ε-δ-continuous h → ∃ f ꞉ ♭ (ℝ → ℝ) , ♭-apply₁ f ＝ h
      IV c = ∣ VII (pr₂ V
        (λ x → CF.strict-gives-ball ♭-counit (λ y → ♭-counit (h y)) x (c x))) ∣
       where
        VII : fiber FRF.♭-action h → Σ f ꞉ ♭ (ℝ → ℝ) , ♭-apply₁ f ＝ h
        VII (f , e) =
         f , transport (λ - → - f ＝ h) (♭-apply₁-is-♭-action ⁻¹) e

 R♭-gives-Shulman-11-6
  : (@♭ cem : Crisp-EM 𝓤₁)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → Shulman-11-6
 R♭-gives-Shulman-11-6 cem r♭ =
  Shulman-11-6-under-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
   (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
   Con.identity-of-ℝ-rises cem

\end{code}

Shulman's Theorem 11.5 from Axiom R♭ alone, Theorem 7.14 of the
write-up's revision of 12 November (gate G23 of the second addendum;
gist.RealCohesion.CrispFunctionsAreContinuous, with crisp-ap-^♭ and the
♭-discreteness of 𝟚 discharged). It is stated in Shulman's words, as
the target Target-11-5-from-R♭-alone of the starter module, by the
conversion of gist.RealCohesion.ContinuityForms from rational
intervals to ε and δ. It gives the targets Target-11-5 and
Target-crisp-real-continuity with their types, since crisp excluded
middle is no longer needed, and so it supersedes
R♭-gives-Shulman-11-5 above. Two parts of Shulman's Corollary 11.6 for
the map ♭-apply₁ of the starter module also hold from Axiom R♭ alone:
it is injective (canonical-map-is-an-embedding above), and its values
are ε-δ continuous.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import UF.Embeddings using (embeddings-are-lc)
 open import Notation.Order
 open import Rationals.Type using (ℚ)
 open import DedekindReals.Type fe pe pt
 open import DedekindReals.Order fe pe pt
 open import gist.RealCohesion.CrispRealAnalysis fe pe pt
  using (Crisp-Real-Continuity)
 open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt
  using
   (Target-11-5-from-R♭-alone ; Target-11-5 ; Target-crisp-real-continuity ;
    Shulman-11-5 ; ♭-apply₁ ; is-♭-ε-δ-continuous)
 import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭ as FCD
 import gist.RealCohesion.FlatRealFunctions fe pe pt crisp-ap-^♭ as FRF
 import gist.RealCohesion.ContinuityForms fe pe pt as CF
 import gist.RealCohesion.CrispFunctionsAreContinuous fe pe pt crisp-ap-^♭ as
  CFAC
 import gist.RealCohesion.Constancy fe pe pt as Con
 open PropositionalTruncation pt

\end{code}

The forms of R♭-gives-Shulman-11-5-from-R♭-alone,
R♭-gives-crisp-real-continuity, R♭-gives-♭-apply₁-is-injective and
R♭-gives-continuous-values, from Axiom C1 for an ordinary family of
generators and a strictly rising generator path in ℝ, merely (W3 of
Claude Fable 5.2's consolidation plan of 13 November 2026, released by
GPT-6 Astra; gist.RealCohesion.TheoremsFromC1 states them with their
types written out). The theorems under Axiom R♭ are their instances
for the one generator ℝ, whose identity map rises from 0 to 1.

\begin{code}

 module _ {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
          (nc : ∥ Con.Rising-Generator-Path R ∥)
        where

  private
   module Cont = CFAC.continuity-under-C1 R c1 𝟚-is-♭-discrete nc

  Shulman-11-5-under-C1 : Shulman-11-5
  Shulman-11-5-under-C1 f a =
   CF.interval-gives-strict id f a (Cont.crisp-functions-are-continuous f a)

  crisp-real-continuity-under-C1 : Crisp-Real-Continuity
  crisp-real-continuity-under-C1 f t u v l m =
   ∥∥-functor γ (Cont.crisp-functions-are-continuous f t u v l m)
   where
    γ : (Σ (r , r') ꞉ ℚ × ℚ , (r < t) × (t < r')
                            ×
                            ((x : ℝ) → r < x → x < r' → (u < f x) × (f x < v)))
      → Σ (r , r') ꞉ ℚ × ℚ , (r < t) × (t < r')
                           ×
                           ((@♭ s : ℝ) → r < s → s < r' → (u < f s) × (f s < v))
    γ ((r , r') , k , k' , h) = (r , r') , k , k' , (λ s → h s)

  ♭-apply₁-is-injective-under-C1
   : (f g : ♭ (ℝ → ℝ)) → ♭-apply₁ f ＝ ♭-apply₁ g → f ＝ g
  ♭-apply₁-is-injective-under-C1 f g e =
   embeddings-are-lc FRF.♭-action
    (FRF.under-C1.♭-action-is-embedding R c1 𝟚-is-♭-discrete nc)
    (transport (λ - → - f ＝ - g) (♭-apply₁-is-♭-action fe pe pt) e)

  continuous-values-under-C1
   : (F : ♭ (ℝ → ℝ)) → is-♭-ε-δ-continuous (♭-apply₁ F)
  continuous-values-under-C1 (f ^♭) (x ^♭) =
   CF.interval-gives-strict ♭-counit (λ y → ♭-counit (♭-apply₁ (f ^♭) y))
    (x ^♭) I
   where
    I : CF.Interval-Continuous ♭-counit (λ y → ♭-counit (♭-apply₁ (f ^♭) y))
        (x ^♭)
    I u v l m = ∥∥-functor γ (Cont.crisp-functions-are-continuous f x u v l m)
     where
      γ : (Σ (r , r') ꞉ ℚ × ℚ , (r < x) × (x < r')
                              ×
                              ((z : ℝ) → r < z → z < r'
                                       → (u < f z) × (f z < v)))
        → Σ (r , r') ꞉ ℚ × ℚ , (r < x) × (x < r')
                             × ((y : ♭ ℝ) → r < ♭-counit y → ♭-counit y < r'
                                          → (u < ♭-counit (♭-apply₁ (f ^♭) y))
                                          × (♭-counit (♭-apply₁ (f ^♭) y) < v))
      γ ((r , r') , k , k' , h) = (r , r') , k , k' , δ
       where
        δ : (y : ♭ ℝ) → r < ♭-counit y → ♭-counit y < r'
          → (u < ♭-counit (♭-apply₁ (f ^♭) y))
          × (♭-counit (♭-apply₁ (f ^♭) y) < v)
        δ (y ^♭) = h y

 R♭-gives-Shulman-11-5-from-R♭-alone : Target-11-5-from-R♭-alone
 R♭-gives-Shulman-11-5-from-R♭-alone r♭ =
  Shulman-11-5-under-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
   (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
   Con.identity-of-ℝ-rises

 R♭-gives-Target-11-5 : Target-11-5
 R♭-gives-Target-11-5 cem = R♭-gives-Shulman-11-5-from-R♭-alone

 R♭-gives-crisp-real-continuity
  : Singly-Generated-Punctual-Cohesion ℝ 0ℝ → Crisp-Real-Continuity
 R♭-gives-crisp-real-continuity r♭ =
  crisp-real-continuity-under-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
   (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
   Con.identity-of-ℝ-rises

 R♭-gives-Target-crisp-real-continuity : Target-crisp-real-continuity
 R♭-gives-Target-crisp-real-continuity cem = R♭-gives-crisp-real-continuity

 R♭-gives-♭-apply₁-is-injective
  : Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (f g : ♭ (ℝ → ℝ)) → ♭-apply₁ f ＝ ♭-apply₁ g → f ＝ g
 R♭-gives-♭-apply₁-is-injective r♭ =
  ♭-apply₁-is-injective-under-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
   (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
   Con.identity-of-ℝ-rises

 R♭-gives-continuous-values
  : Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (F : ♭ (ℝ → ℝ)) → is-♭-ε-δ-continuous (♭-apply₁ F)
 R♭-gives-continuous-values r♭ =
  continuous-values-under-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
   (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
   Con.identity-of-ℝ-rises

\end{code}

The n-variable form of Shulman's Theorem 11.5 from Axiom R♭ alone,
Theorem 7.17 of the write-up's revision of 12 November, by GPT-6 Astra
(gate G24 of the second addendum;
gist.RealCohesion.CrispFunctionsOfSeveralVariables, with crisp-ap-^♭
and the ♭-discreteness of 𝟚 discharged). It is stated as the target
Target-3-4-from-R♭-alone of the starter module, through the conversion
of gist.RealCohesion.ContinuityForms from boxes to ε and δ. By
Target-3-4-follows of the starter module it gives the target
Target-3-4, Remark 3.4 of the write-up with its crisp excluded middle:
this is gate G18, which the second addendum calls a corollary of G24.
As a corollary, the values of the canonical map ♭ (ℝⁿ → ℝ) → (♭ ℝⁿ → ♭ ℝ)
are ε-δ continuous, from Axiom R♭ alone: the second part of the
target of gate G20, for every crisp n.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import Notation.Order
 open import Rationals.Type using (ℚ ; 0ℚ)
 open import Rationals.Order
 open import DedekindReals.Type fe pe pt
 open import DedekindReals.Order fe pe pt
 open import gist.RealCohesion.BrouwerStatements fe pe pt using (ℝ^)
 open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt
  using (Target-3-4-from-R♭-alone ; Target-3-4 ; Target-3-4-follows ; ♭-apply ;
         Remark-3-4 ;
         ♭-apply-has-continuous-values ; _is-coordinatewise-within_of_ ;
         _is-strictly-within_of_)
 import gist.RealCohesion.ContinuityForms fe pe pt as CF
 import gist.RealCohesion.CrispFunctionsOfSeveralVariables fe pe pt crisp-ap-^♭
  as CFSV
 import gist.RealCohesion.Constancy fe pe pt as Con
 open PropositionalTruncation pt

\end{code}

The forms of R♭-gives-Remark-3-4-from-R♭-alone and
R♭-gives-continuous-values-in-dimension, from Axiom C1 for an ordinary
family of generators and a strictly rising generator path in ℝ, merely
(W3 of Claude Fable 5.2's consolidation plan of 13 November 2026,
released by GPT-6 Astra; gist.RealCohesion.TheoremsFromC1 states them
with their types written out). The theorems under Axiom R♭ are their
instances for the one generator ℝ, whose identity map rises from 0
to 1.

\begin{code}

 module _ {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
          (nc : ∥ Con.Rising-Generator-Path R ∥)
        where

  private
   module Cont = CFSV.continuity-under-C1 R c1 𝟚-is-♭-discrete nc

  Remark-3-4-under-C1 : (@♭ n : ℕ) → Remark-3-4 n
  Remark-3-4-under-C1 n F p =
   CF.box-gives-coordinatewise-strict F p
    (Cont.crisp-functions-of-several-variables-are-continuous n F p)

  continuous-values-in-dimension-under-C1
   : (@♭ n : ℕ) → ♭-apply-has-continuous-values n
  continuous-values-in-dimension-under-C1 n (f ^♭) (x ^♭) ε o =
   ∥∥-functor γ (Remark-3-4-under-C1 n f x ε o)
   where
    γ : (Σ δ ꞉ ℚ , (0ℚ < δ)
                 × ((y : ℝ^ n) → y is-coordinatewise-within δ of x
                               → f y is-strictly-within ε of f x))
      → Σ δ ꞉ ℚ , (0ℚ < δ)
                × ((y : ♭ (ℝ^ n)) → ♭-counit y is-coordinatewise-within δ of x
                                  → ♭-counit (♭-apply (f ^♭) y)
                                     is-strictly-within ε of f x)
    γ (δ , p , h) = δ , p , θ
     where
      θ : (y : ♭ (ℝ^ n)) → ♭-counit y is-coordinatewise-within δ of x
        → ♭-counit (♭-apply (f ^♭) y) is-strictly-within ε of f x
      θ (y ^♭) b = h y b

 R♭-gives-Remark-3-4-from-R♭-alone : (@♭ n : ℕ) → Target-3-4-from-R♭-alone n
 R♭-gives-Remark-3-4-from-R♭-alone n r♭ =
  Remark-3-4-under-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
   (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
   Con.identity-of-ℝ-rises n

 R♭-gives-Target-3-4 : (@♭ n : ℕ) → Target-3-4 n
 R♭-gives-Target-3-4 n =
  Target-3-4-follows n (R♭-gives-Remark-3-4-from-R♭-alone n)

 R♭-gives-continuous-values-in-dimension
  : (@♭ n : ℕ) → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → ♭-apply-has-continuous-values n
 R♭-gives-continuous-values-in-dimension n r♭ =
  continuous-values-in-dimension-under-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
   (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
   Con.identity-of-ℝ-rises n

\end{code}

The first part of Theorem 3.3 in n variables from Axiom R♭ alone (gate
G20 of the second addendum; gist.RealCohesion.FlatFunctionsOfSeveralVariables,
with crisp-ap-^♭ and the ♭-discreteness of 𝟚 discharged): the
canonical map ♭ (ℝⁿ → ℝ) → (♭ ℝⁿ → ♭ ℝ) is injective. With the
continuity of its values above, this is the target
Target-3-3-embedding-and-continuity-from-R♭-alone of the starter
module. The starter's ♭-apply and the module's ♭-apply' are the same
map.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import Fin.Type using (Fin)
 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt
  using (♭-apply ; ♭-apply-is-injective ;
          Target-3-3-embedding-and-continuity-from-R♭-alone)
 import gist.RealCohesion.FlatFunctionsOfSeveralVariables fe pe pt crisp-ap-^♭
  as FFSV
 import gist.RealCohesion.Constancy fe pe pt as Con
 open PropositionalTruncation pt using (∥_∥)

 ♭-apply-is-♭-apply' : {@♭ n : ℕ} → ♭-apply {n} ＝ FFSV.♭-apply' {n}
 ♭-apply-is-♭-apply' {n} = dfunext fe γ
  where
   γ : (F : ♭ ((Fin n → ℝ) → ℝ)) → ♭-apply F ＝ FFSV.♭-apply' F
   γ (F ^♭) = dfunext fe δ
    where
     δ : (x : ♭ (Fin n → ℝ)) → ♭-apply (F ^♭) x ＝ FFSV.♭-apply' (F ^♭) x
     δ (x ^♭) = refl

\end{code}

The form of R♭-gives-♭-apply-is-injective, from Axiom C1 for an
ordinary family of generators and a strictly rising generator path in
ℝ, merely (W3 of Claude Fable 5.2's consolidation plan of 13 November
2026, released by GPT-6 Astra; gist.RealCohesion.TheoremsFromC1 states
it with its type written out). The theorem under Axiom R♭ is its
instance for the one generator ℝ, whose identity map rises from 0 to 1.

\begin{code}

 module _ {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
          (nc : ∥ Con.Rising-Generator-Path R ∥)
        where

  ♭-apply-is-injective-under-C1 : (@♭ n : ℕ) → ♭-apply-is-injective n
  ♭-apply-is-injective-under-C1 n F G e =
   FFSV.under-C1.♭-apply-is-injective' R c1 𝟚-is-♭-discrete nc F G
    (transport (λ h → h F ＝ h G) ♭-apply-is-♭-apply' e)

 R♭-gives-♭-apply-is-injective
  : (@♭ n : ℕ) → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → ♭-apply-is-injective n
 R♭-gives-♭-apply-is-injective n r♭ =
  ♭-apply-is-injective-under-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
   (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
   Con.identity-of-ℝ-rises n

 R♭-gives-Target-3-3-embedding-and-continuity
  : (@♭ n : ℕ) → Target-3-3-embedding-and-continuity-from-R♭-alone n
 R♭-gives-Target-3-3-embedding-and-continuity n r♭ =
  R♭-gives-♭-apply-is-injective n r♭ ,
  R♭-gives-continuous-values-in-dimension fe pe pt n r♭

\end{code}

The cube form of Shulman's Theorem 12.6 from crisp excluded middle and
Axiom R♭, the starter's Target-12-6-cube-from-LEM: a crisp self-map of
the cube moves some point by less than ε, in the supremum norm. The
second addendum calls it a corollary of the crisp fixed point, and so
it is: a fixed point moves by nothing. It holds outright in every
dimension (R♭-gives-Target-12-6-cube-from-LEM), with Kuhn's lemma in
every dimension (gate G14); the forms in dimensions 0, 1 and 2 and the
form relative to Kuhn's lemma are kept.
Shulman's own Theorem 12.6, for the disc and from univalence and Axiom
R♭, is gates G25 and G26.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import Fin.Type using (Fin)
 open import Rationals.Type using (ℚ ; 0ℚ)
 open import Rationals.Order
 open import Notation.Order
 open import DedekindReals.Type fe pe pt
 open import DedekindReals.Order fe pe pt
 open import gist.RealCohesion.BrouwerStatements fe pe pt
  using (Cube ; Kuhn-Lemma)
 open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt
  using (Approximate-Fixed-Points-Of-Crisp-Maps ; Target-12-6-cube-from-LEM ;
         _is-coordinatewise-within_of_ ; _is-strictly-within_of_)
 open import gist.RealCohesion.RealLattice fe pe pt using (translate-up)
 import gist.RealCohesion.ContinuityForms fe pe pt as CF
 import gist.RealCohesion.Constancy fe pe pt as Con
 import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭ as FCD
 open PropositionalTruncation pt

 strictly-within-itself : (y : ℝ) (ε : ℚ) → 0ℚ < ε → y is-strictly-within ε of y
 strictly-within-itself y ε l =
  transport (y <_) (CF.plus-ιₐ-is-plus-ι y ε) (translate-up y ε l) ,
  transport (y <_) (CF.plus-ιₐ-is-plus-ι y ε) (translate-up y ε l)

 approximate-from-exact
  : (n : ℕ) (f : Cube n → Cube n) (ε : ℚ) → 0ℚ < ε
  → (∃ x ꞉ Cube n , f x ＝ x)
  → ∃ x ꞉ Cube n , pr₁ (f x) is-coordinatewise-within ε of pr₁ x
 approximate-from-exact n f ε l = ∥∥-functor γ
  where
   γ : (Σ x ꞉ Cube n , f x ＝ x)
     → Σ x ꞉ Cube n , pr₁ (f x) is-coordinatewise-within ε of pr₁ x
   γ (x , e) =
    x , (λ i → transport (λ z → pr₁ z i is-strictly-within ε of pr₁ x i) (e ⁻¹)
                 (strictly-within-itself (pr₁ x i) ε l))

 module _ (ν : Con.Constancy) where

  constancy-gives-approximate-fixed-points-of-crisp-maps
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → (@♭ kuhn : Kuhn-Lemma n)
   → Approximate-Fixed-Points-Of-Crisp-Maps n
  constancy-gives-approximate-fixed-points-of-crisp-maps n cem kuhn f ε l =
   approximate-from-exact n f ε l
    (constancy-gives-crisp-cube-fixed-points fe pe pt ν n cem kuhn f)

  constancy-gives-Target-12-6-cube-from-LEM-in-dimension-0
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Approximate-Fixed-Points-Of-Crisp-Maps 0
  constancy-gives-Target-12-6-cube-from-LEM-in-dimension-0 cem f ε l =
   approximate-from-exact 0 f ε l
    (constancy-gives-crisp-fixed-points-in-dimension-0 fe pe pt ν cem f)

  constancy-gives-Target-12-6-cube-from-LEM-in-dimension-1
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Approximate-Fixed-Points-Of-Crisp-Maps 1
  constancy-gives-Target-12-6-cube-from-LEM-in-dimension-1 cem f ε l =
   approximate-from-exact 1 f ε l
    (constancy-gives-crisp-fixed-points-in-dimension-1 fe pe pt ν cem f)

  constancy-gives-Target-12-6-cube-from-LEM-in-dimension-2
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Approximate-Fixed-Points-Of-Crisp-Maps 2
  constancy-gives-Target-12-6-cube-from-LEM-in-dimension-2 cem f ε l =
   approximate-from-exact 2 f ε l
    (constancy-gives-crisp-fixed-points-in-dimension-2 fe pe pt ν cem f)

  constancy-gives-Target-12-6-cube-from-LEM
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → Approximate-Fixed-Points-Of-Crisp-Maps n
  constancy-gives-Target-12-6-cube-from-LEM n cem =
   constancy-gives-approximate-fixed-points-of-crisp-maps n cem
    (kuhn-lemma fe pe pt n)

 R♭-gives-approximate-fixed-points-of-crisp-maps
  : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (@♭ kuhn : Kuhn-Lemma n)
  → Approximate-Fixed-Points-Of-Crisp-Maps n
 R♭-gives-approximate-fixed-points-of-crisp-maps n cem r♭ =
  constancy-gives-approximate-fixed-points-of-crisp-maps
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) n cem

 R♭-gives-Target-12-6-cube-from-LEM-in-dimension-0 : Target-12-6-cube-from-LEM 0
 R♭-gives-Target-12-6-cube-from-LEM-in-dimension-0 cem r♭ =
  constancy-gives-Target-12-6-cube-from-LEM-in-dimension-0
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

 R♭-gives-Target-12-6-cube-from-LEM-in-dimension-1 : Target-12-6-cube-from-LEM 1
 R♭-gives-Target-12-6-cube-from-LEM-in-dimension-1 cem r♭ =
  constancy-gives-Target-12-6-cube-from-LEM-in-dimension-1
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

 R♭-gives-Target-12-6-cube-from-LEM-in-dimension-2 : Target-12-6-cube-from-LEM 2
 R♭-gives-Target-12-6-cube-from-LEM-in-dimension-2 cem r♭ =
  constancy-gives-Target-12-6-cube-from-LEM-in-dimension-2
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) cem

 R♭-gives-Target-12-6-cube-from-LEM : (@♭ n : ℕ) → Target-12-6-cube-from-LEM n
 R♭-gives-Target-12-6-cube-from-LEM n cem r♭ =
  constancy-gives-Target-12-6-cube-from-LEM
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete) n cem

\end{code}

Theorem 3.3 in n variables, all three parts (gate G21 of the second
addendum): the canonical map ♭ (ℝⁿ → ℝ) → (♭ ℝⁿ → ♭ ℝ) is injective,
its values are continuous, and every continuous map is a value, from
crisp excluded middle for 𝓤₀ and Axiom R♭. The third part is
continuous-maps-are-values' of
gist.RealCohesion.FlatFunctionsOfSeveralVariables, with the
♭-discreteness of 𝟚 and of ♭ ℝ discharged; with the first two parts
above it is the starter's Target-3-3, Theorem 3.3 of the write-up with
the supremum norm, in every crisp dimension.

For n = 1 this gives Shulman's Corollary 11.6 in his words, the
starter's Target-11-6, with crisp excluded middle for 𝓤₀ only; the
bridge R♭-gives-Shulman-11-6 above, through
gist.RealCohesion.FlatRealFunctions, assumes it for 𝓤₁. A map h of one
variable is read as the map y ↦ h (y 𝟎) of ℝ¹, and a function F of
ℝ¹ as the function r ↦ F (λ _ → r) of one variable. Injectivity and
the continuity of the values come from Axiom R♭ alone (gate G23,
above).

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import Fin.Type using (Fin ; 𝟎)
 open import UF.Base using (happly)
 open import UF.Subsingletons-FunExt using (Π-is-prop)
 open import Notation.Order
 open import Rationals.Type using (ℚ ; 0ℚ)
 open import Rationals.Order
 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import gist.RealCohesion.BrouwerStatements fe pe pt using (ℝ^)
 open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt
  using (♭-apply ; is-♭-continuous ; continuous-maps-are-values-of-♭-apply ;
         Target-3-3 ; ♭-apply₁ ; is-♭-ε-δ-continuous ; Shulman-11-6 ;
          Target-11-6 ;
         _is-strictly-within_of_ ; _is-coordinatewise-within_of_)
 import gist.RealCohesion.FlatFunctionsOfSeveralVariables fe pe pt crisp-ap-^♭
  as FFSV
 import gist.RealCohesion.Constancy fe pe pt as Con
 open PropositionalTruncation pt

\end{code}

The form of R♭-gives-continuous-maps-are-values from Axiom C1 for an
ordinary family of generators (W3 of Claude Fable 5.2's consolidation
plan of 13 November 2026, released by GPT-6 Astra;
gist.RealCohesion.TheoremsFromC1 states it with its type written out).
It does not use a rising generator path: maps into ♭ ℝ form a
♭-discrete type, and continuity of a crisp map is a crisp proposition,
by Axiom C1 alone (gist.RealCohesion.FlatFunctionsOfSeveralVariables).
The theorem under Axiom R♭ is its instance for the one generator ℝ.

\begin{code}

 module _ {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R) where

  continuous-maps-are-values-under-C1
   : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
   → continuous-maps-are-values-of-♭-apply n
  continuous-maps-are-values-under-C1 n cem h c =
   γ
    (FFSV.under-C1.continuous-maps-are-values' R c1 𝟚-is-♭-discrete
      ♭-is-♭-discrete cem h c)
   where
    γ : (Σ F ꞉ ♭ ((Fin n → ℝ) → ℝ) , FFSV.♭-apply' F ＝ h)
      → ∃ F ꞉ ♭ (ℝ^ n → ℝ) , ♭-apply F ＝ h
    γ (F , e) = ∣ F , (happly (♭-apply-is-♭-apply' fe pe pt {n}) F ∙ e) ∣

 R♭-gives-continuous-maps-are-values
  : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → continuous-maps-are-values-of-♭-apply n
 R♭-gives-continuous-maps-are-values n cem r♭ =
  continuous-maps-are-values-under-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
   (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭) n cem

 R♭-gives-Target-3-3 : (@♭ n : ℕ) → Target-3-3 n
 R♭-gives-Target-3-3 n cem r♭ =
  R♭-gives-♭-apply-is-injective fe pe pt n r♭ ,
  R♭-gives-continuous-values-in-dimension fe pe pt n r♭ ,
  R♭-gives-continuous-maps-are-values n cem r♭

 one-variable : (♭ ℝ → ♭ ℝ) → ♭ (ℝ^ 1) → ♭ ℝ
 one-variable h (y ^♭) = h ((y 𝟎) ^♭)

 one-variable-is-continuous
  : (h : ♭ ℝ → ♭ ℝ) → is-♭-ε-δ-continuous h → is-♭-continuous (one-variable h)
 one-variable-is-continuous h c (x ^♭) ε l = ∥∥-functor γ (c ((x 𝟎) ^♭) ε l)
  where
   γ : (Σ δ ꞉ ℚ , (0ℚ < δ)
                × ((y : ♭ ℝ) → ♭-counit y is-strictly-within δ of x 𝟎
                             → ♭-counit (h y) is-strictly-within ε of ♭-counit
                                (h ((x 𝟎) ^♭))))
     → Σ δ ꞉ ℚ , (0ℚ < δ)
               × ((y : ♭ (ℝ^ 1)) → ♭-counit y is-coordinatewise-within δ of x
                                 → ♭-counit (one-variable h y)
                                    is-strictly-within ε
                                                               of ♭-counit
                                                                (h ((x 𝟎) ^♭)))
   γ (δ , m , f) = δ , m , φ
    where
     φ : (y : ♭ (ℝ^ 1)) → ♭-counit y is-coordinatewise-within δ of x
       → ♭-counit (one-variable h y) is-strictly-within ε of ♭-counit
          (h ((x 𝟎) ^♭))
     φ (y ^♭) w = f ((y 𝟎) ^♭) (w 𝟎)

 being-♭-ε-δ-continuous-is-prop : (h : ♭ ℝ → ♭ ℝ)
                                → is-prop (is-♭-ε-δ-continuous h)
 being-♭-ε-δ-continuous-is-prop h =
  Π-is-prop fe (λ x → Π-is-prop fe (λ ε → Π-is-prop fe (λ _ → ∃-is-prop)))

\end{code}

The form of R♭-gives-Target-11-6, with crisp excluded middle for 𝓤₀,
from Axiom C1 for an ordinary family of generators and a strictly
rising generator path in ℝ, merely (W3 of Claude Fable 5.2's
consolidation plan of 13 November 2026, released by GPT-6 Astra;
gist.RealCohesion.TheoremsFromC1 states it with its type written out).
The theorem under Axiom R♭ is its instance for the one generator ℝ,
whose identity map rises from 0 to 1.

\begin{code}

 module _ {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
          (nc : ∥ Con.Rising-Generator-Path R ∥)
        where

  Target-11-6-under-C1
   : (@♭ cem : Crisp-EM 𝓤₀)
   → Shulman-11-6
  Target-11-6-under-C1 cem =
   ♭-apply₁-is-injective-under-C1 fe pe pt R c1 nc , (λ h → I h , II h)
   where
    I : (h : ♭ ℝ → ♭ ℝ) → (∃ f ꞉ ♭ (ℝ → ℝ) , ♭-apply₁ f ＝ h)
      → is-♭-ε-δ-continuous h
    I h = ∥∥-rec (being-♭-ε-δ-continuous-is-prop h) γ
     where
      γ : (Σ f ꞉ ♭ (ℝ → ℝ) , ♭-apply₁ f ＝ h) → is-♭-ε-δ-continuous h
      γ (f , e) = transport is-♭-ε-δ-continuous e
                   (continuous-values-under-C1 fe pe pt R c1 nc f)

    II : (h : ♭ ℝ → ♭ ℝ) → is-♭-ε-δ-continuous h
       → ∃ f ꞉ ♭ (ℝ → ℝ) , ♭-apply₁ f ＝ h
    II h c = ∥∥-functor γ
              (continuous-maps-are-values-under-C1 R c1 1 cem (one-variable h)
                (one-variable-is-continuous h c))
     where
      γ : (Σ F ꞉ ♭ (ℝ^ 1 → ℝ) , ♭-apply F ＝ one-variable h)
        → Σ f ꞉ ♭ (ℝ → ℝ) , ♭-apply₁ f ＝ h
      γ ((F ^♭) , e) = ((λ r → F (λ _ → r)) ^♭) , dfunext fe δ
       where
        δ : (x : ♭ ℝ) → ♭-apply₁ ((λ r → F (λ _ → r)) ^♭) x ＝ h x
        δ (x ^♭) = happly e ((λ _ → x) ^♭)

 R♭-gives-Target-11-6 : Target-11-6
 R♭-gives-Target-11-6 cem r♭ =
  Target-11-6-under-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
   (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
   Con.identity-of-ℝ-rises cem

\end{code}

Shulman's Lemma 8.15 with its scope (gate G15 of the blueprint
addendum; gist.RealCohesion.DiscreteSets, by Claude Fable 5.2, with the
♭-discreteness of 𝟚 from the native ♯). Lemma 8.15 is printed for an
arbitrary set: it is discrete, which in real cohesion means ℝ-null, if
and only if it has decidable equality. Here: decidable equality gives
ℝ-nullity under Axiom R♭; the converse holds for crisp sets under crisp
excluded middle; and for sets that need not be crisp the converse is
false under Axiom R♭ (GPT-6 Astra's observation that the printed proof
needs a crisp set, and Astra's example P → 𝟚). Fable's package stated
these three results with --flat-split in a module DiscreteSetsFlatSplit;
at Colin Zwanziger's decision they are stated here, in --safe mode, and
that module is not part of the folder.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import UF.DiscreteAndSeparated using (is-discrete)
 open import gist.RealCohesion.DiscreteSets fe pe pt
  using (discrete-types-are-ℝ-null-under-R♭ ; crisp-ℝ-null-sets-are-discrete ;
         ℝ-null-sets-need-not-be-discrete-under-R♭)

 Lemma-8-15-from-decidable-equality
  : {𝓤 : Universe}
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (A : 𝓤 ̇ ) → is-discrete A → is-null ℝ A
 Lemma-8-15-from-decidable-equality r♭ =
  discrete-types-are-ℝ-null-under-R♭ r♭ 𝟚-is-♭-discrete

 Lemma-8-15-for-crisp-sets
  : {@♭ 𝓤 : Universe}
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → Crisp-EM 𝓤
  → (@♭ A : 𝓤 ̇ ) → @♭ is-set A → is-null ℝ A → is-discrete A
 Lemma-8-15-for-crisp-sets r♭ =
  crisp-ℝ-null-sets-are-discrete r♭ 𝟚-is-♭-discrete

 unrestricted-Lemma-8-15-is-false
  : Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → ¬ ((A : 𝓤₀ ̇ ) → is-set A → is-null ℝ A → is-discrete A)
 unrestricted-Lemma-8-15-is-false r♭ =
  ℝ-null-sets-need-not-be-discrete-under-R♭ r♭ 𝟚-is-♭-discrete

\end{code}

Gate G27 of the second addendum: Shulman's Lemma 12.3 from crisp
excluded middle and Axiom C1, without his Axiom T. The theorem and its
proof are GPT-6 Astra's; the modules are Claude Fable 5.2's
(gist.RealCohesion.BoundaryRetractionFromC1 and its companions), and
Astra's review released them on 12 November 2026.

 * For the square [-1,1]², outright, and for the cube [-1,1]ⁿ⁺¹
   relative to Kuhn's lemma in dimension n + 1, and outright in the
   forms …-in-every-dimension, which discharge it: a self-map without
   a fixed point, not necessarily crisp, gives a retraction of the
   cube onto its boundary, as data.

 * For the disc D², outright, and for the ball Dⁿ⁺¹ relative to Kuhn's
   lemma, and outright in the forms …-in-every-dimension: the same
   with the sphere. The forms …-literal-Lemma-12-3…, added on
   13 November 2026, conclude with a retraction of the inclusion
   sphere-to-ball (Literal-Lemma-12-3-for-the-ball of
   gist.RealCohesion.EuclideanSphere), which the proof constructs; for
   n + 1 = 2 this is Shulman's Lemma 12.3 as he states it. The other
   forms, with the same hypotheses, have the type
   Lemma-12-3-for-the-ball of that module, whose conclusion
   retract (Sphere n) of (Ball n) is the type-level retract
   consequence, which forgets that the section is the inclusion. Step
   E4 of gate G14 proves both forms from crisp excluded middle and
   Axiom T, above.

 * Either ℝ is ♭-discrete, or no self-map of the cube is fixed-point
   free; and from crisp excluded middle for 𝓤₀, Axiom C1 and "ℝ is not
   ♭-discrete", every crisp self-map of the cube, of the ball or of the
   disc has a fixed point, and every self-map sharply has one
   (Shulman's Corollary 12.5 and Theorem 12.4). Axiom R♭ gives Axiom C1
   and that ℝ is not ♭-discrete (R♭-gives-C1,
   R♭-gives-that-ℝ-is-not-♭-discrete).

 * The fixed-point theorems for the cube also hold with Axiom C1 as an
   ordinary hypothesis, and they give the targets Target-3-7-crisp and
   Target-3-7-sharp with their own types, through the codiscreteness
   of crisp propositions under Axiom R♭ or C1
   (gist.RealCohesion.BoundaryRetractionFromC1Targets).

Crisp excluded middle is assumed for 𝓤₀ as a crisp hypothesis, and, in
the lemma and the dichotomy, for 𝓤₁ as an ordinary one, to decide
whether ℝ is ♭-discrete. The family R of generators is crisp, and so
is Axiom C1, except in the four forms
LEM-ordinary-C1-and-ℝ-not-♭-discrete-give-…, where C1 is an ordinary
hypothesis for the crisp family; these C1 forms assume no univalence,
Axiom T or Axiom R♭. The four compatibility exports below,
C1-theorem-gives-Target-3-7-crisp, C1-theorem-gives-Target-3-7-sharp
and their two …-in-every-dimension forms, are not such forms: they
specialize the C1 argument back to the original targets, which take
ordinary Axiom R♭ and crisp excluded middle, and crisp Kuhn's lemma
except in the …-in-every-dimension forms. Each theorem
stated in a dimension relative to Kuhn's lemma is followed by its form
…-in-every-dimension, with Kuhn's lemma discharged (kuhn-lemma-for-bit
and kuhn-lemma above) and the same hypotheses otherwise.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import gist.CohesiveApartness.Sharp using (♯)
 open import gist.RealCohesion.BrouwerStatements fe pe pt
  using (Cube ; Target-3-7-crisp ; Target-3-7-sharp ; Crisp-Cube-Fixed-Point ;
         Sharp-Cube-Fixed-Point)
 open import gist.RealCohesion.NativeSharp using (native-sharp)
 open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt
  using (is-retraction-onto-the-boundary)
 import gist.RealCohesion.KuhnLemma as K
 import gist.RealCohesion.EuclideanBall fe pe pt as EB
 import gist.RealCohesion.EuclideanSphere fe pe pt as ES
 import gist.RealCohesion.BoundaryRetractionFromC1Statements fe pe pt as G27
 import gist.RealCohesion.BoundaryRetractionFromC1Targets fe pe pt as G27T
 import gist.RealCohesion.SphereRetractionFromC1
 open PropositionalTruncation pt using (Exists)

 module _ {@♭ 𝓥 𝓦 : Universe} {@♭ J : 𝓥 ̇ }
          (@♭ R : J → 𝓦 ̇ )
          (@♭ c1 : Axiom-C1 R)
        where

  private
   module SR = gist.RealCohesion.SphereRetractionFromC1 fe pe pt R c1

  LEM-and-C1-give-Lemma-12-3-for-the-square
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → Crisp-EM 𝓤₁
   → (f : Cube 2 → Cube 2)
   → ((x : Cube 2) → ¬ (f x ＝ x))
   → Σ r ꞉ (Cube 2 → Cube 2) , is-retraction-onto-the-boundary r
  LEM-and-C1-give-Lemma-12-3-for-the-square =
   G27.Lemma-12-3-for-the-square-from-LEM-and-C1 R c1

  LEM-and-C1-give-Lemma-12-3-for-the-cube
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → Crisp-EM 𝓤₁
   → {@♭ n : ℕ} (@♭ kuhn : K.Kuhn-Lemma (succ n))
   →
   (Σ f ꞉ (Cube (succ n) → Cube (succ n)) , ((x : Cube (succ n)) → ¬ (f x ＝ x)))
   → Σ r ꞉ (Cube (succ n) → Cube (succ n)) , is-retraction-onto-the-boundary r
  LEM-and-C1-give-Lemma-12-3-for-the-cube =
   G27.Lemma-12-3-for-the-cube-from-LEM-and-C1 R c1

  LEM-and-C1-give-Lemma-12-3-for-the-cube-in-every-dimension
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → Crisp-EM 𝓤₁
   → {@♭ n : ℕ}
   →
   (Σ f ꞉ (Cube (succ n) → Cube (succ n)) , ((x : Cube (succ n)) → ¬ (f x ＝ x)))
   → Σ r ꞉ (Cube (succ n) → Cube (succ n)) , is-retraction-onto-the-boundary r
  LEM-and-C1-give-Lemma-12-3-for-the-cube-in-every-dimension cem₀ cem₁ {n} =
   LEM-and-C1-give-Lemma-12-3-for-the-cube cem₀ cem₁ {n}
    (kuhn-lemma-for-bit fe pe pt (succ n))

  LEM-and-C1-give-Lemma-12-3-for-the-disc
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → Crisp-EM 𝓤₁
   → ES.Lemma-12-3-for-the-ball 2
  LEM-and-C1-give-Lemma-12-3-for-the-disc =
   SR.Lemma-12-3-for-the-disc-as-a-retract

  LEM-and-C1-give-Lemma-12-3-for-the-ball
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → Crisp-EM 𝓤₁
   → {@♭ n : ℕ} (@♭ kuhn : K.Kuhn-Lemma (succ n))
   → ES.Lemma-12-3-for-the-ball (succ n)
  LEM-and-C1-give-Lemma-12-3-for-the-ball =
   SR.Lemma-12-3-for-the-ball-as-a-retract

  LEM-and-C1-give-Lemma-12-3-for-the-ball-in-every-dimension
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → Crisp-EM 𝓤₁
   → {@♭ n : ℕ}
   → ES.Lemma-12-3-for-the-ball (succ n)
  LEM-and-C1-give-Lemma-12-3-for-the-ball-in-every-dimension cem₀ cem₁ {n} =
   LEM-and-C1-give-Lemma-12-3-for-the-ball cem₀ cem₁ {n}
    (kuhn-lemma-for-bit fe pe pt (succ n))

  LEM-and-C1-give-literal-Lemma-12-3-for-the-disc
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → Crisp-EM 𝓤₁
   → ES.Literal-Lemma-12-3-for-the-ball 2
  LEM-and-C1-give-literal-Lemma-12-3-for-the-disc =
   SR.literal-Lemma-12-3-for-the-disc

  LEM-and-C1-give-literal-Lemma-12-3-for-the-ball
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → Crisp-EM 𝓤₁
   → {@♭ n : ℕ} (@♭ kuhn : K.Kuhn-Lemma (succ n))
   → ES.Literal-Lemma-12-3-for-the-ball (succ n)
  LEM-and-C1-give-literal-Lemma-12-3-for-the-ball =
   SR.literal-Lemma-12-3-for-the-ball

  LEM-and-C1-give-literal-Lemma-12-3-for-the-ball-in-every-dimension
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → Crisp-EM 𝓤₁
   → {@♭ n : ℕ}
   → ES.Literal-Lemma-12-3-for-the-ball (succ n)
  LEM-and-C1-give-literal-Lemma-12-3-for-the-ball-in-every-dimension
   cem₀ cem₁ {n} =
   LEM-and-C1-give-literal-Lemma-12-3-for-the-ball cem₀ cem₁ {n}
    (kuhn-lemma-for-bit fe pe pt (succ n))

  LEM-and-C1-give-discrete-or-no-fixed-point-free-maps
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → Crisp-EM 𝓤₁
   → {@♭ n : ℕ} (@♭ kuhn : K.Kuhn-Lemma n)
   → is-♭-discrete ℝ
   + ¬ (Σ f ꞉ (Cube n → Cube n) , ((x : Cube n) → ¬ (f x ＝ x)))
  LEM-and-C1-give-discrete-or-no-fixed-point-free-maps =
   G27.discrete-or-no-fixed-point-free-maps-from-LEM-and-C1 R c1

  LEM-and-C1-give-discrete-or-no-fixed-point-free-maps-in-every-dimension
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → Crisp-EM 𝓤₁
   → {@♭ n : ℕ}
   → is-♭-discrete ℝ
   + ¬ (Σ f ꞉ (Cube n → Cube n) , ((x : Cube n) → ¬ (f x ＝ x)))
  LEM-and-C1-give-discrete-or-no-fixed-point-free-maps-in-every-dimension cem₀
   cem₁ {n} =
   LEM-and-C1-give-discrete-or-no-fixed-point-free-maps cem₀ cem₁ {n}
    (kuhn-lemma-for-bit fe pe pt n)

  LEM-C1-and-ℝ-not-♭-discrete-give-crisp-cube-fixed-points
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → ¬ is-♭-discrete ℝ
   → {@♭ n : ℕ} (@♭ kuhn : K.Kuhn-Lemma n)
   → (@♭ f : Cube n → Cube n) → ∃ x ꞉ Cube n , f x ＝ x
  LEM-C1-and-ℝ-not-♭-discrete-give-crisp-cube-fixed-points =
   G27.crisp-fixed-points-from-LEM-C1-and-ℝ-not-♭-discrete R c1

  LEM-C1-and-ℝ-not-♭-discrete-give-crisp-cube-fixed-points-in-every-dimension
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → ¬ is-♭-discrete ℝ
   → {@♭ n : ℕ}
   → (@♭ f : Cube n → Cube n) → ∃ x ꞉ Cube n , f x ＝ x
  LEM-C1-and-ℝ-not-♭-discrete-give-crisp-cube-fixed-points-in-every-dimension
   cem₀ nd {n} =
   LEM-C1-and-ℝ-not-♭-discrete-give-crisp-cube-fixed-points cem₀ nd {n}
    (kuhn-lemma-for-bit fe pe pt n)

  LEM-C1-and-ℝ-not-♭-discrete-give-sharp-cube-fixed-points
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → ¬ is-♭-discrete ℝ
   → {@♭ n : ℕ} (@♭ kuhn : K.Kuhn-Lemma n)
   → (f : Cube n → Cube n) → ♯ (∃ x ꞉ Cube n , f x ＝ x)
  LEM-C1-and-ℝ-not-♭-discrete-give-sharp-cube-fixed-points =
   G27.sharp-fixed-points-from-LEM-C1-and-ℝ-not-♭-discrete R c1

  LEM-C1-and-ℝ-not-♭-discrete-give-sharp-cube-fixed-points-in-every-dimension
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → ¬ is-♭-discrete ℝ
   → {@♭ n : ℕ}
   → (f : Cube n → Cube n) → ♯ (∃ x ꞉ Cube n , f x ＝ x)
  LEM-C1-and-ℝ-not-♭-discrete-give-sharp-cube-fixed-points-in-every-dimension
   cem₀ nd {n} =
   LEM-C1-and-ℝ-not-♭-discrete-give-sharp-cube-fixed-points cem₀ nd {n}
    (kuhn-lemma-for-bit fe pe pt n)

  LEM-C1-and-ℝ-not-♭-discrete-give-crisp-fixed-points-on-the-ball
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → ¬ is-♭-discrete ℝ
   → {@♭ n : ℕ} (@♭ kuhn : K.Kuhn-Lemma n)
   → (@♭ f : EB.Ball n → EB.Ball n) → ∃ k ꞉ EB.Ball n , f k ＝ k
  LEM-C1-and-ℝ-not-♭-discrete-give-crisp-fixed-points-on-the-ball =
   SR.crisp-fixed-points-on-the-ball-if-ℝ-is-not-♭-discrete

  LEM-C1-and-ℝ-not-♭-discrete-give-crisp-fixed-points-on-the-ball-in-every-dimension
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → ¬ is-♭-discrete ℝ
   → {@♭ n : ℕ}
   → (@♭ f : EB.Ball n → EB.Ball n) → ∃ k ꞉ EB.Ball n , f k ＝ k
  LEM-C1-and-ℝ-not-♭-discrete-give-crisp-fixed-points-on-the-ball-in-every-dimension
   cem₀ nd {n} =
   LEM-C1-and-ℝ-not-♭-discrete-give-crisp-fixed-points-on-the-ball cem₀ nd {n}
    (kuhn-lemma-for-bit fe pe pt n)

  LEM-C1-and-ℝ-not-♭-discrete-give-sharp-fixed-points-on-the-ball
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → ¬ is-♭-discrete ℝ
   → {@♭ n : ℕ} (@♭ kuhn : K.Kuhn-Lemma n)
   → (f : EB.Ball n → EB.Ball n) → ♯ (∃ k ꞉ EB.Ball n , f k ＝ k)
  LEM-C1-and-ℝ-not-♭-discrete-give-sharp-fixed-points-on-the-ball =
   SR.sharp-fixed-points-on-the-ball-if-ℝ-is-not-♭-discrete

  LEM-C1-and-ℝ-not-♭-discrete-give-sharp-fixed-points-on-the-ball-in-every-dimension
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → ¬ is-♭-discrete ℝ
   → {@♭ n : ℕ}
   → (f : EB.Ball n → EB.Ball n) → ♯ (∃ k ꞉ EB.Ball n , f k ＝ k)
  LEM-C1-and-ℝ-not-♭-discrete-give-sharp-fixed-points-on-the-ball-in-every-dimension
   cem₀ nd {n} =
   LEM-C1-and-ℝ-not-♭-discrete-give-sharp-fixed-points-on-the-ball cem₀ nd {n}
    (kuhn-lemma-for-bit fe pe pt n)

  LEM-C1-and-ℝ-not-♭-discrete-give-crisp-fixed-points-on-the-disc
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → ¬ is-♭-discrete ℝ
   → (@♭ f : EB.Ball 2 → EB.Ball 2) → ∃ k ꞉ EB.Ball 2 , f k ＝ k
  LEM-C1-and-ℝ-not-♭-discrete-give-crisp-fixed-points-on-the-disc =
   SR.crisp-fixed-points-on-the-disc-if-ℝ-is-not-♭-discrete

  LEM-C1-and-ℝ-not-♭-discrete-give-sharp-fixed-points-on-the-disc
   : (@♭ cem₀ : Crisp-EM 𝓤₀)
   → ¬ is-♭-discrete ℝ
   → (f : EB.Ball 2 → EB.Ball 2) → ♯ (∃ k ꞉ EB.Ball 2 , f k ＝ k)
  LEM-C1-and-ℝ-not-♭-discrete-give-sharp-fixed-points-on-the-disc =
   SR.sharp-fixed-points-on-the-disc-if-ℝ-is-not-♭-discrete

  C1-gives-separators-make-ℝ-♭-discrete
   : (e : ℝ → 𝟚) (a b : ℝ) → e a ≠ e b → is-♭-discrete ℝ
  C1-gives-separators-make-ℝ-♭-discrete = G27.separators-make-ℝ-♭-discrete R c1

  C1-gives-♯𝟘-is-empty : ♯ (𝟘 {𝓤₀}) → 𝟘 {𝓤₀}
  C1-gives-♯𝟘-is-empty = G27.♯𝟘-is-empty-from-C1 R c1

  C1-gives-♭-detects-emptiness
   : {@♭ 𝓣 : Universe} (@♭ A : 𝓣 ̇ ) → ¬ ♭ A → ¬ A
  C1-gives-♭-detects-emptiness = G27.♭-detects-emptiness-from-C1 R c1

 module _ {@♭ 𝓥 𝓦 : Universe} {@♭ J : 𝓥 ̇ }
          (@♭ R : J → 𝓦 ̇ )
        where

  LEM-ordinary-C1-and-ℝ-not-♭-discrete-give-crisp-cube-fixed-points
   : Axiom-C1 R
   → (@♭ cem₀ : Crisp-EM 𝓤₀)
   → ¬ is-♭-discrete ℝ
   → {@♭ n : ℕ} (@♭ kuhn : K.Kuhn-Lemma n)
   → (@♭ f : Cube n → Cube n) → ∃ x ꞉ Cube n , f x ＝ x
  LEM-ordinary-C1-and-ℝ-not-♭-discrete-give-crisp-cube-fixed-points =
   G27T.crisp-fixed-points-from-LEM-ordinary-C1-and-ℝ-not-♭-discrete R

  LEM-ordinary-C1-and-ℝ-not-♭-discrete-give-crisp-cube-fixed-points-in-every-dimension
   : Axiom-C1 R
   → (@♭ cem₀ : Crisp-EM 𝓤₀)
   → ¬ is-♭-discrete ℝ
   → {@♭ n : ℕ}
   → (@♭ f : Cube n → Cube n) → ∃ x ꞉ Cube n , f x ＝ x
  LEM-ordinary-C1-and-ℝ-not-♭-discrete-give-crisp-cube-fixed-points-in-every-dimension
   c1 cem₀ nd {n} =
   LEM-ordinary-C1-and-ℝ-not-♭-discrete-give-crisp-cube-fixed-points c1 cem₀ nd
    {n}
    (kuhn-lemma-for-bit fe pe pt n)

  LEM-ordinary-C1-and-ℝ-not-♭-discrete-give-sharp-cube-fixed-points
   : Axiom-C1 R
   → (@♭ cem₀ : Crisp-EM 𝓤₀)
   → ¬ is-♭-discrete ℝ
   → {@♭ n : ℕ} (@♭ kuhn : K.Kuhn-Lemma n)
   → (f : Cube n → Cube n) → ♯ (∃ x ꞉ Cube n , f x ＝ x)
  LEM-ordinary-C1-and-ℝ-not-♭-discrete-give-sharp-cube-fixed-points =
   G27T.sharp-fixed-points-from-LEM-ordinary-C1-and-ℝ-not-♭-discrete R

  LEM-ordinary-C1-and-ℝ-not-♭-discrete-give-sharp-cube-fixed-points-in-every-dimension
   : Axiom-C1 R
   → (@♭ cem₀ : Crisp-EM 𝓤₀)
   → ¬ is-♭-discrete ℝ
   → {@♭ n : ℕ}
   → (f : Cube n → Cube n) → ♯ (∃ x ꞉ Cube n , f x ＝ x)
  LEM-ordinary-C1-and-ℝ-not-♭-discrete-give-sharp-cube-fixed-points-in-every-dimension
   c1 cem₀ nd {n} =
   LEM-ordinary-C1-and-ℝ-not-♭-discrete-give-sharp-cube-fixed-points c1 cem₀ nd
    {n}
    (kuhn-lemma-for-bit fe pe pt n)

 C1-theorem-gives-Target-3-7-crisp : (@♭ n : ℕ) → Target-3-7-crisp n
 C1-theorem-gives-Target-3-7-crisp = G27T.C1-theorem-gives-Target-3-7-crisp

 C1-theorem-gives-Target-3-7-sharp : (@♭ n : ℕ)
                                   → Target-3-7-sharp native-sharp n
 C1-theorem-gives-Target-3-7-sharp = G27T.C1-theorem-gives-Target-3-7-sharp

 C1-theorem-gives-crisp-cube-fixed-points-in-every-dimension
  : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → Crisp-Cube-Fixed-Point n
 C1-theorem-gives-crisp-cube-fixed-points-in-every-dimension n cem r♭ =
  C1-theorem-gives-Target-3-7-crisp n cem r♭ (kuhn-lemma fe pe pt n)

 C1-theorem-gives-sharp-cube-fixed-points-in-every-dimension
  : (@♭ n : ℕ) (@♭ cem : Crisp-EM 𝓤₀)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → Sharp-Cube-Fixed-Point native-sharp n
 C1-theorem-gives-sharp-cube-fixed-points-in-every-dimension n cem r♭ =
  C1-theorem-gives-Target-3-7-sharp n cem r♭ (kuhn-lemma fe pe pt n)

 module _ (@♭ r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ) where

  R♭-gives-C1 : Axiom-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
  R♭-gives-C1 = G27.R♭-gives-C1 r♭

  R♭-gives-that-ℝ-is-not-♭-discrete : ¬ is-♭-discrete ℝ
  R♭-gives-that-ℝ-is-not-♭-discrete = G27.R♭-gives-that-ℝ-is-not-♭-discrete r♭

\end{code}

Shulman's Theorem 12.6 for the square (gate G25), from univalence and
Axiom R♭, which are his hypotheses: every crisp self-map of the square
moves some point by less than any rational ε > 0 in each coordinate.
It is the target Target-12-6-cube of
gist.RealCohesion.ShulmanWeakeningsStatements. The proof is that of
Fable's note on Theorem 12.6, revision 2, which GPT-6 Astra audited on
12 November 2026: it replaces Shulman's shape modality, circle and van
Kampen theorem by a double cover of the punctured plane and a collapse
along a proposition (gist.RealCohesion.ApproximateBrouwerSquare).

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt
  using (Target-12-6-cube)
 import gist.RealCohesion.ApproximateBrouwerSquare fe pe pt as ABS

 UA-and-R♭-give-Target-12-6-cube : Target-12-6-cube
 UA-and-R♭-give-Target-12-6-cube = ABS.UA-and-R♭-give-Target-12-6-cube

\end{code}

The exact intermediate value theorem for crisp functions without Axiom
T, from crisp excluded middle for 𝓤₀: the target Target-3-5, which had
no proof with its own type (crisp-exact-IVT above assumes crisp
excluded middle for 𝓤₁). It follows from a weaker hypothesis, a choice
of x ≤ y or y ≤ x for crisp reals, by the bisection of Claude Fable
5.2's gist.RealCohesion.CrispExactIVTFromTotalOrder, with the continuity
of crisp functions from Axiom R♭ alone and the constancy of maps from ℝ
to the finite chain quotient. The three statements and their proofs are
Fable's (the scratch module Target35Check, 12 November 2026).

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import UF.Subsingletons-FunExt using (Π-is-prop)
 open import Notation.Order
 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import DedekindReals.Order fe pe pt
 open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt
  using (R♭ ; Crisp-Exact-IVT ; Target-3-5)
 open import gist.RealCohesion.CrispExactIVTFromTotalOrder fe pe pt
  using (Crisp-Order-Is-Total ; Crisp-Order-Is-Decidable ;
          crisp-EM-gives-decidable-order ;
         decidable-order-gives-total-order ; exact-IVT-from-total-order)
 import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭ as FCD
 import gist.RealCohesion.Constancy fe pe pt as Con
 open PropositionalTruncation pt

\end{code}

The form of R♭-gives-crisp-exact-IVT-from-total-order, from Axiom C1
for an ordinary family of generators and a strictly rising generator
path in ℝ, merely (W3 of Claude Fable 5.2's consolidation plan of 13
November 2026, released by GPT-6 Astra;
gist.RealCohesion.TheoremsFromC1 states it with its type written out).
The theorem under Axiom R♭ is its instance for the one generator ℝ,
whose identity map rises from 0 to 1.

\begin{code}

 module _ {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
          (nc : ∥ Con.Rising-Generator-Path R ∥)
        where

  crisp-exact-IVT-from-total-order-under-C1
   : (@♭ total : Crisp-Order-Is-Total) → Crisp-Exact-IVT
  crisp-exact-IVT-from-total-order-under-C1 total f c =
   ∥∥-rec (Π-is-prop fe (λ _ → ∃-is-prop)) γ
   where
    γ : (Σ a ꞉ ℝ , f a < c) → (∃ b ꞉ ℝ , c < f b) → ∃ x ꞉ ℝ , f x ＝ c
    γ (a , l) = ∥∥-rec ∃-is-prop δ
     where
      δ : (Σ b ꞉ ℝ , c < f b) → ∃ x ꞉ ℝ , f x ＝ c
      δ (b , m) =
       exact-IVT-from-total-order
        (crisp-real-continuity-under-C1 fe pe pt R c1 nc)
        (FCD.under-C1.constancy-from-C1-and-NC R c1 𝟚-is-♭-discrete nc)
        total f c a b l m

 R♭-gives-crisp-exact-IVT-from-total-order
  : (@♭ total : Crisp-Order-Is-Total) → R♭ → Crisp-Exact-IVT
 R♭-gives-crisp-exact-IVT-from-total-order total r♭ =
  crisp-exact-IVT-from-total-order-under-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
   (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
   Con.identity-of-ℝ-rises total

 R♭-gives-crisp-exact-IVT-from-decidable-order
  : (@♭ d : Crisp-Order-Is-Decidable) → R♭ → Crisp-Exact-IVT
 R♭-gives-crisp-exact-IVT-from-decidable-order d =
  R♭-gives-crisp-exact-IVT-from-total-order
   (decidable-order-gives-total-order d)

 R♭-gives-Target-3-5 : Target-3-5
 R♭-gives-Target-3-5 cem =
  R♭-gives-crisp-exact-IVT-from-decidable-order
   (crisp-EM-gives-decidable-order cem)

\end{code}

Shulman's Theorem 12.6 as he states it, for the round disc with the
Euclidean norm (gate G26), from univalence and Axiom R♭: for every
crisp f : D² → D² and real ε > 0 there is x : D² with ‖f x - x‖² < ε²,
that is, |f x - x| < ε; and the same for rational ε > 0, from which the
form for real ε follows through a positive rational below ε. The form
for rational ε follows from the square
(gate G25) through the retraction onto the disc, which does not increase
distances (gist.RealCohesion.ApproximateBrouwerDisc, Corollary 4 of
Fable's note).

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt using (R♭)
 import gist.RealCohesion.ApproximateBrouwerDisc fe pe pt as ABD

 UA-and-R♭-give-approximate-fixed-points-on-the-disc
  : Univalence → R♭ → ABD.Approximate-Fixed-Points-Of-Crisp-Maps-Of-The-Disc
 UA-and-R♭-give-approximate-fixed-points-on-the-disc =
  ABD.UA-and-R♭-give-approximate-fixed-points-on-the-disc

 UA-and-R♭-give-approximate-fixed-points-on-the-disc-for-real-ε
  : Univalence → R♭
  → ABD.Approximate-Fixed-Points-Of-Crisp-Maps-Of-The-Disc-For-Real-ε
 UA-and-R♭-give-approximate-fixed-points-on-the-disc-for-real-ε =
  ABD.UA-and-R♭-give-approximate-fixed-points-on-the-disc-for-real-ε

\end{code}
