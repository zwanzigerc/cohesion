Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Shulman's Theorem 12.6 for the square, from univalence and Axiom R♭
(gate G25), by the proof of Fable's note [1], revision 2, which GPT-6
Astra audited on 12 November 2026.

Shulman's Theorem 12.6 [2], tagged UA and R♭: for a crisp
f :: D² → D² and ε > 0 there is x : D² with |f x - x| < ε. The target
Target-12-6-cube of gist.RealCohesion.ShulmanWeakeningsStatements is
its form for the square [-1,1]² with the coordinatewise distance, from
univalence and Axiom R♭ as ordinary hypotheses; it is proved here
(UA-and-R♭-give-Target-12-6-cube). Shulman's proof uses the shape
modality as a higher inductive type, the circle and the van Kampen
theorem; the note replaces them by a double cover of the punctured
plane (gist.RealCohesion.DoubleCover) and by collapsing a set along a
proposition (gist.RealCohesion.Collapse). No multiplication of reals
occurs (gist.RealCohesion.SquareEstimates).

 * Lemma 2 of the note (module classifier). For a crisp proposition Q,
   let M be 𝟚 collapsed along Q, and K the type of types merely
   equivalent to M. Under univalence and R♭, every map from ℝ to K is
   constant. M is ♭-discrete as a crisp quotient of the ♭-discrete set
   𝟚 + Q (gist.RealCohesion.CrispQuotients); the identity types of K
   are, by univalence, types of equivalences into types merely
   equivalent to M, so maps from ℝ to them are constant, and they are
   ♭-discrete by R♭; K is connected, so it is ♭-discrete by Lemma 1
   (gist.RealCohesion.DiscreteConnectedTypes), and R♭ applies.

 * The theorem for crisp f and a crisp rational ε with 0 < ε < 1
   (module square). With η = ε/2, δ = ε/4 and c = 1 - η, let g be f
   between the clamps to [-1,1] and to [-c,c], U the points where some
   coordinate of z - g z exceeds δ in absolute value, V those where
   every coordinate is below η, and Q = ∥V∥, a crisp proposition. A
   point of V gives the fixed point wanted. For z in U, the double
   cover over z - g z has two elements; F z collapses (U z) × (that
   cover) along Q; so F z is merely equivalent to M, also for z in V,
   where both are contractible, and F is a map from ℝ² to K, constant
   in each variable. Transporting along these identifications, the
   two sections of the cover on each of the lines x = ±2, y = ±2 give
   constant maps into F 0, which agree at the corners, except that the
   cover is twisted at the corner (2 , -2). Going round, the classes of
   the two sections at (2 , 0) agree, which the collapse allows only if
   Q holds.

 * The target, for every rational ε > 0: a smaller crisp rational
   below 1 is a crisp representative of min(ε , 1/2), and the
   statement for it gives the statement for ε.

Since the consolidation of 13 November 2026, by Claude Opus 5.5 (W4 of
Claude Fable 5.2's consolidation plan [3], after GPT-6 Astra's
independent review [4]), Lemma 2 is proved under Axiom C1 for an
ordinary family of pointed generators and univalence (module
classifier.under-C1): with "null for every generator" in place of
"ℝ-null", the same steps make K ♭-discrete, without a rising path; then
a crisp ♭-discrete type, which need not be a set, is ℝ-null if some map
from a generator to ℝ rises strictly, merely
(gist.RealCohesion.HigherTransfer). The proof for the square is stated
once, from the two constancy statements that Lemma 2 gives
(square.proof-from-constancy), and the theorem for every rational ε
once, from the theorem for small crisp rationals ε
(approximate-fixed-points-from-small-crisp-ε). The theorem under
univalence and Axiom R♭ keeps its name and type and is the instance for
the one generator ℝ; the theorem under univalence, Axiom C1 and a
merely rising generator path is Target-12-6-cube-under-C1.

[1] Claude Fable 5.2. Note: Shulman's approximate Brouwer theorem (12.6)
    without the shape modality. Revision 2, 12 November 2026, audited
    by GPT-6 Astra.
    references/F11-shulman-12-6-rev2.md

[2] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer Science
    28(6), 2018. https://arxiv.org/abs/1509.07584v3

[3] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, Section 4.5, as incorporated by
    its addendum 01, Section 3, and released by GPT-6 Astra.
    references/F02-consolidation-plan.md

[4] GPT-6 Astra. W4 independent mathematical review, 13 November 2026.
    references/A13-w4-review.txt

\begin{code}

{-# OPTIONS --safe --without-K --cohesion --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Univalence
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.ApproximateBrouwerSquare
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Fin.Type
open import MLTT.Two-Properties using (zero-is-not-one ; one-is-not-zero)
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import UF.Embeddings using (pr₁-is-embedding ; embedding-gives-embedding')
open import UF.Equiv
open import UF.Equiv-FunExt using (being-equiv-is-prop'')
open import UF.EquivalenceExamples using (singleton-≃)
open import UF.Sets
open import UF.Sets-Properties using (equiv-to-set ; being-set-is-prop)
open import UF.Subsingletons-FunExt
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import Rationals.MinMax using (min ; min≤ ; min≤')
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Addition fe pe pt using () renaming (_+_ to _+ᵗ_)
open import gist.CohesiveApartness.CrispInduction
 using (crisp-ap-^♭ ; 𝟚-is-♭-discrete)
open import gist.RealCohesion.RationalArithmetic using (half ; min-is-positive)
open import gist.RealCohesion.RationalProducts
 using (minus-one-is-negation ; minus-one-is-negative)
open import gist.RealCohesion.RationalPoints fe pe pt using (ιₐ ; ιₐ-is-ι)
open import gist.RealCohesion.RealOrder fe pe pt using (ℝ<-gives-≤)
open import gist.RealCohesion.RealLattice fe pe pt
 using (_+_ ; -_ ; +-is-+ᵗ ; clamp ; clamp-is-above-lo ; clamp-is-below-hi ;
         clamp-inside)
open import gist.RealCohesion.CrispRationals
 using (ℚ-has-crisp-representatives ; crisp-elim)
open import gist.RealCohesion.FinVectors using (Fin-pair)
open import gist.RealCohesion.CrispQuotients fe pe pt crisp-ap-^♭
 using (crisp-quotients-are-♭-discrete)
open import gist.RealCohesion.DiscreteConnectedTypes pt
 using (connected-crisp-types-are-♭-discrete)
open import gist.RealCohesion.Constancy fe pe pt using (Rising-Generator-Path)
import gist.RealCohesion.PunctualCohesion fe as PC
import gist.RealCohesion.HigherTransfer fe pe pt as HT
open import gist.RealCohesion.Collapse fe pe pt
open import gist.RealCohesion.DoubleCover fe pe pt
open import gist.RealCohesion.SquareEstimates fe pe pt
 using (margin-or-inside ; positive-from-margin ; negative-from-margin ;
         within-weakens ;
        module square-estimates)
open import gist.RealCohesion.BrouwerStatements fe pe pt using (Cube ; in-cube)
open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt
 using (R♭ ; Approximate-Fixed-Points-Of-Crisp-Maps ; Target-12-6-cube ;
        _is-coordinatewise-within_of_ ; _is-strictly-within_of_)

open PropositionalTruncation pt

\end{code}

The forward half of Axiom R♭ under Axiom C1 for an ordinary family R
of pointed generators, with a strictly rising generator path in ℝ,
merely (gate 4 of W4 [3]): a crisp ♭-discrete type is null for every
generator, by Axiom C0, and so null for ℝ, by
gist.RealCohesion.HigherTransfer. The type need not be a set.

\begin{code}

module ℝ-nullness-under-C1
        {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
        (nc : ∥ Rising-Generator-Path R ∥)
       where

 open Axiom-C1 c1

 crisp-♭-discrete-types-are-ℝ-null
  : {@♭ 𝓣 : Universe} (@♭ A : 𝓣 ̇ ) → is-♭-discrete A → is-null ℝ A
 crisp-♭-discrete-types-are-ℝ-null A d =
  HT.nullness-transfers-along-a-rising-generator-path R
   (lr-implication (axiom-C0 A) d) nc

 maps-into-crisp-♭-discrete-types-are-constant
  : {@♭ 𝓣 : Universe} (@♭ A : 𝓣 ̇ ) → is-♭-discrete A
  → (h : ℝ → A) (s : ℝ) → h s ＝ h 0ℝ
 maps-into-crisp-♭-discrete-types-are-constant A d =
  lr-implication (null-iff-maps-are-constant fe ℝ 0ℝ A)
   (crisp-♭-discrete-types-are-ℝ-null A d)

\end{code}

Lemma 2 of the note: the classifying type of 𝟚 collapsed along a crisp
proposition is ℝ-null, under univalence and Axiom R♭.

\begin{code}

module classifier {@♭ 𝓥 : Universe} (@♭ Q : 𝓥 ̇ ) (@♭ Q-is-prop : is-prop Q)
                where

 M : (𝓤₀ ⊔ 𝓥) ⁺ ̇
 M = Collapse 𝟚 Q-is-prop

 K : (𝓤₀ ⊔ 𝓥) ⁺ ⁺ ̇
 K = Σ X ꞉ (𝓤₀ ⊔ 𝓥) ⁺ ̇ , ∥ X ≃ M ∥

 k₀ : K
 k₀ = M , ∣ ≃-refl M ∣

\end{code}

The steps, under Axiom C1 for an ordinary family R of pointed
generators and univalence, without a rising generator path (gate 3 of
W4, steps a to e of GPT-6 Astra's review [4, Section 3]): maps from a
generator to 𝟚, and hence to 𝟚 + Q, are constant, so 𝟚 + Q is
♭-discrete by Axiom C0; so is its crisp quotient M; maps from a
generator to a type merely equivalent to M are constant; so are maps
from a generator to an identity type of K, by univalence, and the
identity types of K between crisp points are ♭-discrete by Axiom C0;
and K, being connected, is ♭-discrete by Lemma 1. Axiom C0 is applied
only to crisp types. With a strictly rising generator path in ℝ,
merely, maps from ℝ to K, or to a type merely equivalent to M, are
constant, since K and M are crisp and ♭-discrete (gate 4).

\begin{code}

 module under-C1 {𝓥' 𝓦 : Universe} {J : 𝓥' ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
                 (ua : Univalence)
               where

  open Axiom-C1 c1

  generator-maps-to-𝟚-are-constant
   : (j : J) (h : R j → 𝟚) (s : R j) → h s ＝ h (base-point j)
  generator-maps-to-𝟚-are-constant =
   PC.generator-maps-are-constant R c1 𝟚 𝟚-is-♭-discrete

  generator-maps-to-𝟚+Q-are-constant
   : (j : J) (h : R j → 𝟚 ∔ Q) (s : R j) → h s ＝ h (base-point j)
  generator-maps-to-𝟚+Q-are-constant j h s =
   γ (h s) (h (base-point j)) refl refl
   where
    side value : 𝟚 ∔ Q → 𝟚
    side (inl _) = ₀
    side (inr _) = ₁
    value (inl b) = b
    value (inr _) = ₀

    c : (k : R j → 𝟚) → k s ＝ k (base-point j)
    c k = generator-maps-to-𝟚-are-constant j k s

    γ : (u v : 𝟚 ∔ Q) → h s ＝ u → h (base-point j) ＝ v
      → h s ＝ h (base-point j)
    γ (inl a) (inl b) e e' = e ∙ ap inl I ∙ e' ⁻¹
     where
      I : a ＝ b
      I = ap value e ⁻¹ ∙ c (value ∘ h) ∙ ap value e'
    γ (inr p) (inr q) e e' = e ∙ ap inr (Q-is-prop p q) ∙ e' ⁻¹
    γ (inl a) (inr q) e e' =
     𝟘-elim (zero-is-not-one (ap side e ⁻¹ ∙ c (side ∘ h) ∙ ap side e'))
    γ (inr p) (inl b) e e' =
     𝟘-elim (one-is-not-zero (ap side e ⁻¹ ∙ c (side ∘ h) ∙ ap side e'))

  crisp-props-are-♭-discrete
   : {@♭ 𝓣 : Universe} (@♭ P : 𝓣 ̇ ) → @♭ is-prop P → is-♭-discrete P
  crisp-props-are-♭-discrete P i = PC.crisp-propositions-are-♭-discrete R c1 P i

  𝟚+Q-is-♭-discrete : is-♭-discrete (𝟚 ∔ Q)
  𝟚+Q-is-♭-discrete =
   PC.types-null-for-the-generators-are-♭-discrete R c1 (𝟚 ∔ Q)
    generator-maps-to-𝟚+Q-are-constant

  M-is-♭-discrete : is-♭-discrete M
  M-is-♭-discrete =
   crisp-quotients-are-♭-discrete crisp-props-are-♭-discrete (𝟚 ∔ Q)
    (collapse-eqrel 𝟚 Q-is-prop) 𝟚+Q-is-♭-discrete

  classified-types-are-sets : (X : (𝓤₀ ⊔ 𝓥) ⁺ ̇ ) → ∥ X ≃ M ∥ → is-set X
  classified-types-are-sets X =
   ∥∥-rec (being-set-is-prop fe)
    (λ e → equiv-to-set e (collapse-is-set 𝟚 Q-is-prop))

  generator-maps-to-classified-types-are-constant
   : (X : (𝓤₀ ⊔ 𝓥) ⁺ ̇ ) → ∥ X ≃ M ∥
   → (j : J) (h : R j → X) (s : R j) → h s ＝ h (base-point j)
  generator-maps-to-classified-types-are-constant X t j h s =
   ∥∥-rec (classified-types-are-sets X t) γ t
   where
    γ : X ≃ M → h s ＝ h (base-point j)
    γ e = equivs-are-lc ⌜ e ⌝ ⌜ e ⌝-is-equiv
           (PC.generator-maps-are-constant R c1 M M-is-♭-discrete j
             (⌜ e ⌝ ∘ h) s)

  generator-maps-to-identifications-of-K-are-constant
   : (a b : K) (j : J) (g : R j → a ＝ b) (s : R j) → g s ＝ g (base-point j)
  generator-maps-to-identifications-of-K-are-constant (X , σ) (Y , σ') j g s =
   equivs-are-lc φ φ-is-equiv II
   where
    φ : (X , σ) ＝ (Y , σ') → X ≃ Y
    φ p = idtoeq X Y (ap pr₁ p)

    φ-is-equiv : is-equiv φ
    φ-is-equiv = ∘-is-equiv
                  (embedding-gives-embedding' pr₁
                    (pr₁-is-embedding (λ _ → ∥∥-is-prop))
                    (X , σ) (Y , σ'))
                  (ua _ X Y)

    II : φ (g s) ＝ φ (g (base-point j))
    II = to-subtype-＝ (being-equiv-is-prop'' fe)
          (dfunext fe
            (λ x → generator-maps-to-classified-types-are-constant Y σ' j
                    (λ s' → ⌜ φ (g s') ⌝ x) s))

  K-is-♭-discrete : is-♭-discrete K
  K-is-♭-discrete =
   connected-crisp-types-are-♭-discrete k₀ connected crisp-identifications
   where
    connected : (x : K) → ∥ x ＝ k₀ ∥
    connected (X , σ) =
     ∥∥-functor (λ e → to-subtype-＝ (λ _ → ∥∥-is-prop) (eqtoid (ua _) X M e)) σ

    crisp-identifications : (@♭ a b : K) → is-♭-discrete (a ＝ b)
    crisp-identifications a b =
     PC.types-null-for-the-generators-are-♭-discrete R c1 (a ＝ b)
      (generator-maps-to-identifications-of-K-are-constant a b)

  generator-maps-to-K-are-constant
   : (j : J) (h : R j → K) (s : R j) → h s ＝ h (base-point j)
  generator-maps-to-K-are-constant =
   PC.generator-maps-are-constant R c1 K K-is-♭-discrete

  module _ (nc : ∥ Rising-Generator-Path R ∥) where

   private
    module N = ℝ-nullness-under-C1 R c1 nc

   maps-to-classified-types-are-constant
    : (X : (𝓤₀ ⊔ 𝓥) ⁺ ̇ ) → ∥ X ≃ M ∥ → (h : ℝ → X) (s : ℝ) → h s ＝ h 0ℝ
   maps-to-classified-types-are-constant X t h s =
    ∥∥-rec (classified-types-are-sets X t) γ t
    where
     γ : X ≃ M → h s ＝ h 0ℝ
     γ e = equivs-are-lc ⌜ e ⌝ ⌜ e ⌝-is-equiv
            (N.maps-into-crisp-♭-discrete-types-are-constant M M-is-♭-discrete
              (⌜ e ⌝ ∘ h) s)

   maps-to-K-are-constant : (h : ℝ → K) (s : ℝ) → h s ＝ h 0ℝ
   maps-to-K-are-constant =
    N.maps-into-crisp-♭-discrete-types-are-constant K K-is-♭-discrete

\end{code}

Under Axiom R♭ and univalence, the instance for the one generator ℝ,
pointed by 0, with the names and types of the module before the
consolidation of 13 November 2026. No rising path is needed here,
since ℝ is the generator.

\begin{code}

 module _ (ua : Univalence) (r♭ : R♭) where

  private
   module G = under-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
               (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
               ua

  maps-to-𝟚-are-constant : (h : ℝ → 𝟚) (s : ℝ) → h s ＝ h 0ℝ
  maps-to-𝟚-are-constant = G.generator-maps-to-𝟚-are-constant ⋆

  maps-to-𝟚+Q-are-constant : (h : ℝ → 𝟚 ∔ Q) (s : ℝ) → h s ＝ h 0ℝ
  maps-to-𝟚+Q-are-constant = G.generator-maps-to-𝟚+Q-are-constant ⋆

  crisp-props-are-♭-discrete
   : {@♭ 𝓣 : Universe} (@♭ P : 𝓣 ̇ ) → @♭ is-prop P → is-♭-discrete P
  crisp-props-are-♭-discrete = G.crisp-props-are-♭-discrete

  M-is-♭-discrete : is-♭-discrete M
  M-is-♭-discrete = G.M-is-♭-discrete

  classified-types-are-sets : (X : (𝓤₀ ⊔ 𝓥) ⁺ ̇ ) → ∥ X ≃ M ∥ → is-set X
  classified-types-are-sets = G.classified-types-are-sets

  maps-to-classified-types-are-constant
   : (X : (𝓤₀ ⊔ 𝓥) ⁺ ̇ ) → ∥ X ≃ M ∥ → (h : ℝ → X) (s : ℝ) → h s ＝ h 0ℝ
  maps-to-classified-types-are-constant X t =
   G.generator-maps-to-classified-types-are-constant X t ⋆

  identifications-of-K-are-constant
   : (a b : K) (g : ℝ → a ＝ b) (s : ℝ) → g s ＝ g 0ℝ
  identifications-of-K-are-constant a b =
   G.generator-maps-to-identifications-of-K-are-constant a b ⋆

  K-is-♭-discrete : is-♭-discrete K
  K-is-♭-discrete = G.K-is-♭-discrete

  maps-to-K-are-constant : (h : ℝ → K) (s : ℝ) → h s ＝ h 0ℝ
  maps-to-K-are-constant = G.generator-maps-to-K-are-constant ⋆

\end{code}

The theorem for a crisp self-map f of the square and a crisp rational ε.
Points of the plane are pairs of reals.

\begin{code}

module square (@♭ f : Cube 2 → Cube 2) (@♭ ε : ℚ) where

 η δ c : ℚ
 η = half ε
 δ = half η
 c = 1ℚ ℚ- η

 lo hi : ℝ
 lo = ιₐ (ℚ- c)
 hi = ιₐ c

 minus-one-≤-one : embedding-ℚ-to-ℝ -1ℚ ≤ 1ℝ
 minus-one-≤-one = ℝ<-gives-≤ (embedding-ℚ-to-ℝ -1ℚ) 1ℝ
                    (embedding-preserves-order -1ℚ 1ℚ
                      (ℚ<-trans -1ℚ 0ℚ 1ℚ minus-one-is-negative 0<1))

 clamp-one : ℝ → ℝ
 clamp-one = clamp (embedding-ℚ-to-ℝ -1ℚ) 1ℝ

 to-cube : ℝ → ℝ → Cube 2
 to-cube z₁ z₂ = (λ i → clamp-one (Fin-pair z₁ z₂ i)) ,
                 (λ i → clamp-is-above-lo (embedding-ℚ-to-ℝ -1ℚ) 1ℝ
                         (Fin-pair z₁ z₂ i) ,
                        clamp-is-below-hi (embedding-ℚ-to-ℝ -1ℚ) 1ℝ
                         (Fin-pair z₁ z₂ i)
                         minus-one-≤-one)

 t₁ t₂ g₁ g₂ w₁ w₂ : ℝ → ℝ → ℝ
 t₁ z₁ z₂ = pr₁ (f (to-cube z₁ z₂)) 𝟎
 t₂ z₁ z₂ = pr₁ (f (to-cube z₁ z₂)) 𝟏
 g₁ z₁ z₂ = clamp lo hi (t₁ z₁ z₂)
 g₂ z₁ z₂ = clamp lo hi (t₂ z₁ z₂)
 w₁ z₁ z₂ = z₁ + (- g₁ z₁ z₂)
 w₂ z₁ z₂ = z₂ + (- g₂ z₁ z₂)

 Margin : ℝ → ℝ → Side → 𝓤₀ ̇
 Margin z₁ z₂ east  = g₁ z₁ z₂ + ιₐ δ < z₁
 Margin z₁ z₂ north = g₂ z₁ z₂ + ιₐ δ < z₂
 Margin z₁ z₂ west  = z₁ + ιₐ δ < g₁ z₁ z₂
 Margin z₁ z₂ south = z₂ + ιₐ δ < g₂ z₁ z₂

 U V : ℝ → ℝ → 𝓤₀ ̇
 U z₁ z₂ = ∃ i ꞉ Side , Margin z₁ z₂ i
 V z₁ z₂ = ((z₁ < g₁ z₁ z₂ + ιₐ η) × (g₁ z₁ z₂ < z₁ + ιₐ η))
         × ((z₂ < g₂ z₁ z₂ + ιₐ η) × (g₂ z₁ z₂ < z₂ + ιₐ η))

 Q : 𝓤₁ ̇
 Q = ∃ z₁ ꞉ ℝ , Σ z₂ ꞉ ℝ , V z₁ z₂

 Q-is-prop : is-prop Q
 Q-is-prop = ∃-is-prop

 B : ℝ → ℝ → 𝓤₀ ̇
 B z₁ z₂ = U z₁ z₂ × Cover (w₁ z₁ z₂) (w₂ z₁ z₂)

 F : ℝ → ℝ → 𝓤₂ ̇
 F z₁ z₂ = Collapse (B z₁ z₂) Q-is-prop

 open classifier Q Q-is-prop

 module proof-from-constancy
         (maps-to-K-are-constant' : (h : ℝ → K) (s : ℝ) → h s ＝ h 0ℝ)
         (maps-to-classified-types-are-constant'
           : (X : (𝓤₀ ⊔ 𝓤₁) ⁺ ̇ ) → ∥ X ≃ M ∥
           → (h : ℝ → X) (s : ℝ) → h s ＝ h 0ℝ)
         (ε-positive : 0ℚ < ε)
         (ε-below-one : ε < 1ℚ)
        where

  open square-estimates ε ε-positive ε-below-one
   using (δ-positive ; δ-below-η ; clamp-bounds ; east-margin ; west-margin ;
          inside-gives-cube ; within-from-inside)

  U-or-V : (z₁ z₂ : ℝ) → U z₁ z₂ ∨ V z₁ z₂
  U-or-V z₁ z₂ = ∥∥-rec ∨-is-prop γ
                  (binary-choice (binary-choice A₁ B₁) (binary-choice A₂ B₂))
   where
    A₁ : (g₁ z₁ z₂ + ιₐ δ < z₁) ∨ (z₁ < g₁ z₁ z₂ + ιₐ η)
    A₁ = margin-or-inside z₁ (g₁ z₁ z₂) δ η δ-below-η

    B₁ : (z₁ + ιₐ δ < g₁ z₁ z₂) ∨ (g₁ z₁ z₂ < z₁ + ιₐ η)
    B₁ = margin-or-inside (g₁ z₁ z₂) z₁ δ η δ-below-η

    A₂ : (g₂ z₁ z₂ + ιₐ δ < z₂) ∨ (z₂ < g₂ z₁ z₂ + ιₐ η)
    A₂ = margin-or-inside z₂ (g₂ z₁ z₂) δ η δ-below-η

    B₂ : (z₂ + ιₐ δ < g₂ z₁ z₂) ∨ (g₂ z₁ z₂ < z₂ + ιₐ η)
    B₂ = margin-or-inside (g₂ z₁ z₂) z₂ δ η δ-below-η

    γ : (((g₁ z₁ z₂ + ιₐ δ < z₁) ∔ (z₁ < g₁ z₁ z₂ + ιₐ η))
         × ((z₁ + ιₐ δ < g₁ z₁ z₂) ∔ (g₁ z₁ z₂ < z₁ + ιₐ η)))
      × (((g₂ z₁ z₂ + ιₐ δ < z₂) ∔ (z₂ < g₂ z₁ z₂ + ιₐ η))
         × ((z₂ + ιₐ δ < g₂ z₁ z₂) ∔ (g₂ z₁ z₂ < z₂ + ιₐ η)))
      → U z₁ z₂ ∨ V z₁ z₂
    γ ((inl m , _) , _)                       = ∣ inl ∣ east , m ∣ ∣
    γ ((inr _ , inl m) , _)                   = ∣ inl ∣ west , m ∣ ∣
    γ ((inr _ , inr _) , (inl m , _))         = ∣ inl ∣ north , m ∣ ∣
    γ ((inr _ , inr _) , (inr _ , inl m))     = ∣ inl ∣ south , m ∣ ∣
    γ ((inr a , inr b) , (inr a' , inr b'))   = ∣ inr ((a , b) , (a' , b')) ∣

  margin-gives-half-plane
   : (z₁ z₂ : ℝ) (i : Side) → Margin z₁ z₂ i
   → Half-Plane (w₁ z₁ z₂) (w₂ z₁ z₂) i
  margin-gives-half-plane z₁ z₂ east  m =
   positive-from-margin z₁ (g₁ z₁ z₂) δ δ-positive m
  margin-gives-half-plane z₁ z₂ north m =
   positive-from-margin z₂ (g₂ z₁ z₂) δ δ-positive m
  margin-gives-half-plane z₁ z₂ west  m =
   negative-from-margin z₁ (g₁ z₁ z₂) δ δ-positive m
  margin-gives-half-plane z₁ z₂ south m =
   negative-from-margin z₂ (g₂ z₁ z₂) δ δ-positive m

  B-≃-Cover : (z₁ z₂ : ℝ) → U z₁ z₂ → B z₁ z₂ ≃ Cover (w₁ z₁ z₂) (w₂ z₁ z₂)
  B-≃-Cover z₁ z₂ u = qinveq pr₂ ((λ e → u , e) , I , (λ e → refl))
   where
    I : (b : B z₁ z₂) → (u , pr₂ b) ＝ b
    I (u' , e) = to-×-＝ (∃-is-prop u u') refl

  F-classified : (z₁ z₂ : ℝ) → ∥ F z₁ z₂ ≃ M ∥
  F-classified z₁ z₂ = ∥∥-rec ∥∥-is-prop γ (U-or-V z₁ z₂)
   where
    γ : U z₁ z₂ ∔ V z₁ z₂ → ∥ F z₁ z₂ ≃ M ∥
    γ (inl u) = ∥∥-functor δ' u
     where
      δ' : (Σ i ꞉ Side , Margin z₁ z₂ i) → F z₁ z₂ ≃ M
      δ' (i , m) = collapse-≃ Q-is-prop
                    (B-≃-Cover z₁ z₂ u
                     ● Cover-≃-𝟚 (w₁ z₁ z₂) (w₂ z₁ z₂) i
                      (margin-gives-half-plane z₁ z₂ i m))
    γ (inr v) = ∣ singleton-≃ (collapse-is-singleton (B z₁ z₂) Q-is-prop q)
                              (collapse-is-singleton 𝟚 Q-is-prop q) ∣
     where
      q : Q
      q = ∣ z₁ , z₂ , v ∣

  F' : ℝ → ℝ → K
  F' z₁ z₂ = F z₁ z₂ , F-classified z₁ z₂

  F'-is-constant : (z₁ z₂ : ℝ) → F' z₁ z₂ ＝ F' 0ℝ 0ℝ
  F'-is-constant z₁ z₂ = maps-to-K-are-constant' (λ s → F' s z₂) z₁
                       ∙ maps-to-K-are-constant' (λ s → F' 0ℝ s) z₂

  Ψ : (z₁ z₂ : ℝ) → F z₁ z₂ ≃ F 0ℝ 0ℝ
  Ψ z₁ z₂ = idtoeq (F z₁ z₂) (F 0ℝ 0ℝ) (ap pr₁ (F'-is-constant z₁ z₂))

  constant-along : (l : ℝ → F 0ℝ 0ℝ) (a b : ℝ) → l a ＝ l b
  constant-along l a b =
   maps-to-classified-types-are-constant' (F 0ℝ 0ℝ) (F-classified 0ℝ 0ℝ) l a
   ∙ maps-to-classified-types-are-constant' (F 0ℝ 0ℝ) (F-classified 0ℝ 0ℝ) l b
      ⁻¹

\end{code}

The four lines and the corners.

\begin{code}

  P N : ℝ
  P = ιₐ (1ℚ ℚ+ 1ℚ)
  N = ιₐ (ℚ- (1ℚ ℚ+ 1ℚ))

  east-line : (t : ℝ) → Margin P t east
  east-line t = east-margin (g₁ P t) (pr₂ (clamp-bounds (t₁ P t)))

  north-line : (t : ℝ) → Margin t P north
  north-line t = east-margin (g₂ t P) (pr₂ (clamp-bounds (t₂ t P)))

  west-line : (t : ℝ) → Margin N t west
  west-line t = west-margin (g₁ N t) (pr₁ (clamp-bounds (t₁ N t)))

  south-line : (t : ℝ) → Margin t N south
  south-line t = west-margin (g₂ t N) (pr₁ (clamp-bounds (t₂ t N)))

  point : (z₁ z₂ : ℝ) (i : Side) → Margin z₁ z₂ i → 𝟚 → F z₁ z₂
  point z₁ z₂ i m b =
   collapse-η (B z₁ z₂) Q-is-prop
    (∣ i , m
     ∣ , τ (w₁ z₁ z₂) (w₂ z₁ z₂) i (margin-gives-half-plane z₁ z₂ i m) b)

  seen : (z₁ z₂ : ℝ) (i : Side) → Margin z₁ z₂ i → 𝟚 → F 0ℝ 0ℝ
  seen z₁ z₂ i m b = ⌜ Ψ z₁ z₂ ⌝ (point z₁ z₂ i m b)

  corner : (z₁ z₂ : ℝ) (i j : Side) (mi : Margin z₁ z₂ i) (mj : Margin z₁ z₂ j)
           (b : 𝟚)
         → seen z₁ z₂ i mi b ＝ seen z₁ z₂ j mj (transition i j b)
  corner z₁ z₂ i j mi mj b =
   ap (λ e → ⌜ Ψ z₁ z₂ ⌝ (collapse-η (B z₁ z₂) Q-is-prop e))
    (to-×-＝ (∃-is-prop ∣ i , mi ∣ ∣ j , mj ∣)
      (τ-change (w₁ z₁ z₂) (w₂ z₁ z₂) i j
        (margin-gives-half-plane z₁ z₂ i mi)
         (margin-gives-half-plane z₁ z₂ j mj) b))

  east-sees north-sees west-sees south-sees : 𝟚 → ℝ → F 0ℝ 0ℝ
  east-sees  b t = seen P t east  (east-line t)  b
  north-sees b t = seen t P north (north-line t) b
  west-sees  b t = seen N t west  (west-line t)  b
  south-sees b t = seen t N south (south-line t) b

  round-the-square : east-sees ₀ 0ℝ ＝ east-sees ₁ 0ℝ
  round-the-square =
     constant-along (east-sees ₀) 0ℝ P
   ∙ corner P P east north (east-line P) (north-line P) ₀
   ∙ constant-along (north-sees ₀) P N
   ∙ corner N P north west (north-line N) (west-line P) ₀
   ∙ constant-along (west-sees ₀) P N
   ∙ corner N N west south (west-line N) (south-line N) ₀
   ∙ constant-along (south-sees ₀) N P
   ∙ corner P N south east (south-line P) (east-line N) ₀
   ∙ constant-along (east-sees ₁) N 0ℝ

  Q-holds : Q
  Q-holds = ∥∥-rec Q-is-prop γ
             (collapse-η-reflects (B P 0ℝ) Q-is-prop
               (∣ east , east-line 0ℝ ∣ , τ (w₁ P 0ℝ) (w₂ P 0ℝ) east h ₀)
               (∣ east , east-line 0ℝ ∣ , τ (w₁ P 0ℝ) (w₂ P 0ℝ) east h ₁)
               (equivs-are-lc ⌜ Ψ P 0ℝ ⌝ ⌜ Ψ P 0ℝ ⌝-is-equiv round-the-square))
   where
    h : Half-Plane (w₁ P 0ℝ) (w₂ P 0ℝ) east
    h = margin-gives-half-plane P 0ℝ east (east-line 0ℝ)

    γ : ((∣ east , east-line 0ℝ ∣ , τ (w₁ P 0ℝ) (w₂ P 0ℝ) east h ₀)
         ＝ (∣ east , east-line 0ℝ ∣ , τ (w₁ P 0ℝ) (w₂ P 0ℝ) east h ₁)) ∔ Q
      → Q
    γ (inl d) = 𝟘-elim (τ-is-injective (w₁ P 0ℝ) (w₂ P 0ℝ) east h (ap pr₂ d))
    γ (inr q) = q

\end{code}

A point of V is the point wanted.

\begin{code}

  from-in-cube : {y : ℝ} → (embedding-ℚ-to-ℝ -1ℚ ≤ y) × (y ≤ 1ℝ)
               → (ιₐ (ℚ- 1ℚ) ≤ y) × (y ≤ ιₐ 1ℚ)
  from-in-cube {y} (k , k') =
   transport (_≤ y) {embedding-ℚ-to-ℝ -1ℚ} {ιₐ (ℚ- 1ℚ)}
    ((ιₐ-is-ι (ℚ- 1ℚ) ∙ ap ι (minus-one-is-negation ⁻¹)) ⁻¹) k ,
   transport (y ≤_) {1ℝ} {ιₐ 1ℚ} (ιₐ-is-ι 1ℚ ⁻¹) k'

  to-in-cube : {y : ℝ} → (ιₐ (ℚ- 1ℚ) ≤ y) × (y ≤ ιₐ 1ℚ)
             → (embedding-ℚ-to-ℝ -1ℚ ≤ y) × (y ≤ 1ℝ)
  to-in-cube {y} (k , k') =
   transport (_≤ y) {ιₐ (ℚ- 1ℚ)} {embedding-ℚ-to-ℝ -1ℚ}
    (ιₐ-is-ι (ℚ- 1ℚ) ∙ ap ι (minus-one-is-negation ⁻¹)) k ,
   transport (y ≤_) {ιₐ 1ℚ} {1ℝ} (ιₐ-is-ι 1ℚ) k'

  Within : Cube 2 → 𝓤₀ ̇
  Within x =
   (i : Fin 2) → (pr₁ (f x) i < pr₁ x i + ιₐ ε) × (pr₁ x i < pr₁ (f x) i + ιₐ ε)

  approximate-fixed-point : ∃ x ꞉ Cube 2 , Within x
  approximate-fixed-point = ∥∥-functor γ Q-holds
   where
    γ : (Σ z₁ ꞉ ℝ , Σ z₂ ꞉ ℝ , V z₁ z₂) → Σ x ꞉ Cube 2 , Within x
    γ (z₁ , z₂ , ((a₁ , b₁) , (a₂ , b₂))) = x , within
     where
      in-cube-z : in-cube (Fin-pair z₁ z₂)
      in-cube-z 𝟎             = to-in-cube (inside-gives-cube z₁ (g₁ z₁ z₂)
                                  (pr₁ (clamp-bounds (t₁ z₁ z₂)))
                                  (pr₂ (clamp-bounds (t₁ z₁ z₂))) a₁ b₁)
      in-cube-z 𝟏             = to-in-cube (inside-gives-cube z₂ (g₂ z₁ z₂)
                                  (pr₁ (clamp-bounds (t₂ z₁ z₂)))
                                  (pr₂ (clamp-bounds (t₂ z₁ z₂))) a₂ b₂)
      in-cube-z (suc (suc i)) = 𝟘-elim i

      x : Cube 2
      x = Fin-pair z₁ z₂ , in-cube-z

      same : to-cube z₁ z₂ ＝ x
      same = to-subtype-＝
              (λ y →
                Π-is-prop fe (λ i → ×-is-prop (≤-is-prop _ _) (≤-is-prop _ _)))
              (dfunext fe
                (λ i → clamp-inside (embedding-ℚ-to-ℝ -1ℚ) 1ℝ (Fin-pair z₁ z₂ i)
                        (pr₁ (in-cube-z i)) (pr₂ (in-cube-z i))))

      moved : (i : Fin 2) → clamp lo hi (pr₁ (f (to-cube z₁ z₂)) i)
                            ＝ clamp lo hi (pr₁ (f x) i)
      moved i = ap (λ y → clamp lo hi (pr₁ (f y) i)) same

      within : Within x
      within 𝟎 =
       within-from-inside z₁ (pr₁ (f x) 𝟎) (pr₁ (from-in-cube (pr₂ (f x) 𝟎)))
                  (pr₂ (from-in-cube (pr₂ (f x) 𝟎)))
                  (transport (λ y → z₁ < y + ιₐ η) (moved 𝟎) a₁)
                  (transport (λ y → y < z₁ + ιₐ η) (moved 𝟎) b₁)
      within 𝟏 =
       within-from-inside z₂ (pr₁ (f x) 𝟏) (pr₁ (from-in-cube (pr₂ (f x) 𝟏)))
                  (pr₂ (from-in-cube (pr₂ (f x) 𝟏)))
                  (transport (λ y → z₂ < y + ιₐ η) (moved 𝟏) a₂)
                  (transport (λ y → y < z₂ + ιₐ η) (moved 𝟏) b₂)
      within (suc (suc i)) = 𝟘-elim i

\end{code}

The proof under univalence and Axiom R♭, with the names and types of
the module before the consolidation of 13 November 2026, as explicitly
typed aliases; and under univalence, Axiom C1 for an ordinary family of
generators and a strictly rising generator path in ℝ, merely, as a
module application of proof-from-constancy.

\begin{code}

 module proof (ua : Univalence) (r♭ : R♭) (ε-positive : 0ℚ < ε)
              (ε-below-one : ε < 1ℚ) where

  private
   module Pf = proof-from-constancy (maps-to-K-are-constant ua r♭)
                (maps-to-classified-types-are-constant ua r♭) ε-positive
                ε-below-one

  U-or-V : (z₁ z₂ : ℝ) → U z₁ z₂ ∨ V z₁ z₂
  U-or-V = Pf.U-or-V

  margin-gives-half-plane
   : (z₁ z₂ : ℝ) (i : Side) → Margin z₁ z₂ i
   → Half-Plane (w₁ z₁ z₂) (w₂ z₁ z₂) i
  margin-gives-half-plane = Pf.margin-gives-half-plane

  B-≃-Cover : (z₁ z₂ : ℝ) → U z₁ z₂ → B z₁ z₂ ≃ Cover (w₁ z₁ z₂) (w₂ z₁ z₂)
  B-≃-Cover = Pf.B-≃-Cover

  F-classified : (z₁ z₂ : ℝ) → ∥ F z₁ z₂ ≃ M ∥
  F-classified = Pf.F-classified

  F' : ℝ → ℝ → K
  F' = Pf.F'

  F'-is-constant : (z₁ z₂ : ℝ) → F' z₁ z₂ ＝ F' 0ℝ 0ℝ
  F'-is-constant = Pf.F'-is-constant

  Ψ : (z₁ z₂ : ℝ) → F z₁ z₂ ≃ F 0ℝ 0ℝ
  Ψ = Pf.Ψ

  constant-along : (l : ℝ → F 0ℝ 0ℝ) (a b : ℝ) → l a ＝ l b
  constant-along = Pf.constant-along

  P N : ℝ
  P = Pf.P
  N = Pf.N

  east-line : (t : ℝ) → Margin P t east
  east-line = Pf.east-line

  north-line : (t : ℝ) → Margin t P north
  north-line = Pf.north-line

  west-line : (t : ℝ) → Margin N t west
  west-line = Pf.west-line

  south-line : (t : ℝ) → Margin t N south
  south-line = Pf.south-line

  point : (z₁ z₂ : ℝ) (i : Side) → Margin z₁ z₂ i → 𝟚 → F z₁ z₂
  point = Pf.point

  seen : (z₁ z₂ : ℝ) (i : Side) → Margin z₁ z₂ i → 𝟚 → F 0ℝ 0ℝ
  seen = Pf.seen

  corner : (z₁ z₂ : ℝ) (i j : Side) (mi : Margin z₁ z₂ i) (mj : Margin z₁ z₂ j)
           (b : 𝟚)
         → seen z₁ z₂ i mi b ＝ seen z₁ z₂ j mj (transition i j b)
  corner = Pf.corner

  east-sees north-sees west-sees south-sees : 𝟚 → ℝ → F 0ℝ 0ℝ
  east-sees = Pf.east-sees
  north-sees = Pf.north-sees
  west-sees = Pf.west-sees
  south-sees = Pf.south-sees

  round-the-square : east-sees ₀ 0ℝ ＝ east-sees ₁ 0ℝ
  round-the-square = Pf.round-the-square

  Q-holds : Q
  Q-holds = Pf.Q-holds

  from-in-cube : {y : ℝ} → (embedding-ℚ-to-ℝ -1ℚ ≤ y) × (y ≤ 1ℝ)
               → (ιₐ (ℚ- 1ℚ) ≤ y) × (y ≤ ιₐ 1ℚ)
  from-in-cube = Pf.from-in-cube

  to-in-cube : {y : ℝ} → (ιₐ (ℚ- 1ℚ) ≤ y) × (y ≤ ιₐ 1ℚ)
             → (embedding-ℚ-to-ℝ -1ℚ ≤ y) × (y ≤ 1ℝ)
  to-in-cube = Pf.to-in-cube

  Within : Cube 2 → 𝓤₀ ̇
  Within = Pf.Within

  approximate-fixed-point : ∃ x ꞉ Cube 2 , Within x
  approximate-fixed-point = Pf.approximate-fixed-point

 module proof-under-C1
         {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
         (ua : Univalence) (nc : ∥ Rising-Generator-Path R ∥) =
  proof-from-constancy (under-C1.maps-to-K-are-constant R c1 ua nc)
   (under-C1.maps-to-classified-types-are-constant R c1 ua nc)

\end{code}

The target: univalence and Axiom R♭ give approximate fixed points of
crisp self-maps of the square, for every rational ε > 0. Its proof
uses the theorem for crisp rationals ε with 0 < ε < 1 only, so it is
stated for any proof of that; the theorem under univalence, Axiom C1
and a merely rising generator path is the other instance.

\begin{code}

Approximate-Fixed-Points-For-Small-Crisp-ε : 𝓤₁ ̇
Approximate-Fixed-Points-For-Small-Crisp-ε =
   (@♭ f : Cube 2 → Cube 2) (@♭ e : ℚ)
 → 0ℚ < e → e < 1ℚ
 → ∃ x ꞉ Cube 2 , ((i : Fin 2) → (pr₁ (f x) i < pr₁ x i + ιₐ e)
                                × (pr₁ x i < pr₁ (f x) i + ιₐ e))

approximate-fixed-points-from-small-crisp-ε
 : Approximate-Fixed-Points-For-Small-Crisp-ε
 → Approximate-Fixed-Points-Of-Crisp-Maps 2
approximate-fixed-points-from-small-crisp-ε small f ε ε-positive =
 ∥∥-functor convert
  (crisp-elim ℚ-has-crisp-representatives V h ε' ε'-positive ε'-below-one)
 where
  ε' : ℚ
  ε' = min ε 1/2

  ε'-positive : 0ℚ < ε'
  ε'-positive = min-is-positive ε 1/2 ε-positive 0<1/2

  ε'-below-one : ε' < 1ℚ
  ε'-below-one = ℚ≤-<-trans ε' 1/2 1ℚ (min≤' ε 1/2) 1/2<1

  V : ℚ → 𝓤₁ ̇
  V e = 0ℚ < e → e < 1ℚ
      → ∃ x ꞉ Cube 2 , ((i : Fin 2) → (pr₁ (f x) i < pr₁ x i + ιₐ e)
                                     × (pr₁ x i < pr₁ (f x) i + ιₐ e))

  h : (@♭ e : ℚ) → V e
  h e p q = small f e p q

  to-target : {u v : ℝ} → u < v + ιₐ ε → u < v +ᵗ embedding-ℚ-to-ℝ ε
  to-target {u} {v} =
   transport (u <_) (+-is-+ᵗ v (ιₐ ε) ∙ ap (v +ᵗ_) (ιₐ-is-ι ε))

  convert : (Σ x ꞉ Cube 2 , ((i : Fin 2) → (pr₁ (f x) i < pr₁ x i + ιₐ ε')
                                         × (pr₁ x i < pr₁ (f x) i + ιₐ ε')))
          → Σ x ꞉ Cube 2 , pr₁ (f x) is-coordinatewise-within ε of pr₁ x
  convert (x , w) =
   x , λ i → to-target (within-weakens _ _ ε' ε (min≤ ε 1/2) (pr₁ (w i))) ,
                              to-target (within-weakens _ _ ε' ε (min≤ ε 1/2)
                                          (pr₂ (w i)))

UA-and-R♭-give-Target-12-6-cube : Target-12-6-cube
UA-and-R♭-give-Target-12-6-cube ua r♭ =
 approximate-fixed-points-from-small-crisp-ε
  (λ f e → square.proof.approximate-fixed-point f e ua r♭)

Target-12-6-cube-under-C1
 : {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) → Axiom-C1 R
 → Univalence
 → ∥ Rising-Generator-Path R ∥
 → Approximate-Fixed-Points-Of-Crisp-Maps 2
Target-12-6-cube-under-C1 R c1 ua nc =
 approximate-fixed-points-from-small-crisp-ε
  (λ f e → square.proof-under-C1.approximate-fixed-point f e R c1 ua nc)

\end{code}
