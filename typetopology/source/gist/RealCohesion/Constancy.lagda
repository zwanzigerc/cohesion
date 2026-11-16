Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), in the consolidation that
followed the final audits: step K5 and the transfer lemma of W1 of
Claude Fable 5.2's plan [1], as corrected by its addendum [2] and
released by GPT-6 Astra [3]. See the AI disclosure in
gist.RealCohesion.index.

Constancy of maps out of ℝ, without modalities
----------------------------------------------

 * Constancy: every map from ℝ to the quotient Q of levels by finite
   chains (gist.RealCohesion.FiniteChainQuotient) is constant. It is a
   proposition (Constancy-is-prop). The hitting chain and the
   fixed-point theorems use Axiom R♭ only through it.

 * Maps-From-ℝ-To-𝟚-Are-Constant: every map from ℝ to 𝟚 is constant,
   in the form "k u ＝ k v for all u and v".

 * Rising-Generator-Path R, for a family R : J → 𝓦 of types: a map g
   from some R j to ℝ with g x < g y for some x and y in R j. This is
   the hypothesis NC of "C1 + NC in place of R♭", as data; the
   statements that use it take its propositional truncation. For the
   one generator ℝ of Axiom R♭, the identity rises from 0 to 1
   (identity-of-ℝ-rises); the R♭ instances of the modules with a
   general C1 pass this.

 * The transfer lemma for sets (module transfer): let S be a type with
   a point s₀, and A a set such that every map S → A is constant. If
   some g : S → ℝ has g x < g y, then every map e : ℝ → A is constant
   (constancy-transfers-along-a-strict-rise). For C rational, let P C
   say that e s ＝ e t whenever s ≤ t ≤ s + C. Choose rationals p < q
   strictly between g x and g y. Then P (q - p) holds: for
   s ≤ t ≤ s + (q - p), the map τ ↦ clamp s t (s + (τ - p)) sends g x
   to s and g y to t, and its composite with g and e is a map from S
   to A, hence constant. P is closed under addition of nonnegative
   constants, so P N holds for every rational N ≥ 0, by halving N
   until it is below q - p and doubling back; and two reals have a
   common rational lower bound. Neither multiplication nor division of
   real numbers is used. The rationals are chosen inside the
   elimination of truncations into e a ＝ e b, which is a proposition
   because A is a set.

The module uses no modality and no excluded middle, and imports only
modules of the Agda 2.8 comparison closure, so that the closure of
gist.RealCohesion.FlatSplit can contain it.

Sources. Constancy and Constancy-is-prop were defined, by Claude Opus
5.5, both in gist.RealCohesion.FlatSplit (lines 299–303 of the frozen
delivery r3) and in gist.RealCohesion.Theorems (lines 274–278), which
now name them by typed aliases. Maps-From-ℝ-To-𝟚-Are-Constant is that
of gist.RealCohesion.BoundaryRetractionFromC1 (line 318–319 there),
which names it by a typed alias. (gist.RealCohesion.DiscreteSets
defines a type of the same name in the form "k x ＝ k 0", which is not
definitionally this one, so it keeps its own definition.) The transfer
lemma is the module separator of
gist.RealCohesion.BoundaryRetractionFromC1 (lines 386–516 there, by
Claude Fable 5.2, in Fable's form of GPT-6 Astra's argument), with a
pointed type S and a set A in place of a generator and 𝟚, as in
Fable's scratch check ConstancyTransferCheck.lagda (SHA-256 21c2dc24…,
in the companion of [1]), whose code is used here with the module
made a named module and its last lemma named; the module separator now
names these lemmas by typed aliases.

[1] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, step K5 and Section 4.1.
    references/F02-consolidation-plan.md

[2] Claude Fable 5.2. Addendum 01 to the consolidation plan,
    13 November 2026, Section 1.
    references/F03-consolidation-plan-addendum-01.md

[3] GPT-6 Astra. Consolidation implementation, second release,
    13 November 2026.
    references/A27-consolidation-release-02.txt

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.Constancy
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Notation.Order
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import UF.Base hiding (_≈_)
open import UF.Sets
open import UF.Subsingletons-FunExt using (Π₃-is-prop)
open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q ; Q-is-set)
open import gist.RealCohesion.RationalArithmetic
 using (half ; add-difference ; minus-plus ; module halving-sequence)
open import gist.RealCohesion.RationalLimits fe pe pt
 using (module halving-sequence-bounds)
open import gist.RealCohesion.RationalPoints fe pe pt using (ιₐ)
open import gist.RealCohesion.RealLattice fe pe pt
 using (min ; clamp ; clamp-below ; clamp-above ; ≤-min ; min-≤-left ;
        min-≤-right ; below-min ; below-min-left ; below-min-right ; _+_ ;
        sum-≤ ; plus-zero ; translate-twice ; translate-above ;
        translate-below ; translate-strict ; below-translate⁻¹ ; ιₐ-sum ;
        ιₐ-≤-ιₐ ; <-gives-≤-ιₐ ; >-gives-ιₐ-≤)
open import gist.RealCohesion.RealOrder fe pe pt
 using (ℝ≤-refl ; cuts-are-ordered)

open PropositionalTruncation pt

Constancy : 𝓤₁ ̇
Constancy = (k : ℝ → Q) (u v : ℝ) → k u ＝ k v

Constancy-is-prop : is-prop Constancy
Constancy-is-prop = Π₃-is-prop fe (λ k u v → Q-is-set)

Maps-From-ℝ-To-𝟚-Are-Constant : 𝓤₁ ̇
Maps-From-ℝ-To-𝟚-Are-Constant = (k : ℝ → 𝟚) (u v : ℝ) → k u ＝ k v

Rising-Generator-Path : {𝓥 𝓦 : Universe} {J : 𝓥 ̇ }
                      → (J → 𝓦 ̇ ) → 𝓥 ⊔ 𝓦 ⊔ 𝓤₁ ̇
Rising-Generator-Path {𝓥} {𝓦} {J} R =
 Σ j ꞉ J , Σ g ꞉ (R j → ℝ) , Σ x ꞉ R j , Σ y ꞉ R j , g x < g y

identity-of-ℝ-rises : ∥ Rising-Generator-Path (λ (_ : 𝟙 {𝓤₀}) → ℝ) ∥
identity-of-ℝ-rises = ∣ ⋆ , id , 0ℝ , 1ℝ , ℝ-zero-less-than-one ∣

\end{code}

The transfer lemma for sets.

\begin{code}

module transfer
        {𝓥 𝓣 : Universe} {S : 𝓥 ̇ } (s₀ : S) {A : 𝓣 ̇ }
        (A-is-set : is-set A)
        (S-maps-are-constant : (h : S → A) (r : S) → h r ＝ h s₀)
        (g : S → ℝ) (x y : S)
        (e : ℝ → A)
       where

 P : ℚ → 𝓤₁ ⊔ 𝓣 ̇
 P C = (s t : ℝ) → s ≤ t → t ≤ (s + ιₐ C) → e s ＝ e t

 ≤-translate : (s : ℝ) (C : ℚ) → 0ℚ ≤ C → s ≤ (s + ιₐ C)
 ≤-translate s C l =
  transport (λ - → - ≤ (s + ιₐ C)) (plus-zero s)
   (sum-≤ s s (ιₐ 0ℚ) (ιₐ C) (ℝ≤-refl s) (ιₐ-≤-ιₐ 0ℚ C l))

 ≤-min-translate : (u v z : ℝ) (C : ℚ)
                 → z ≤ (u + ιₐ C) → z ≤ (v + ιₐ C) → z ≤ (min u v + ιₐ C)
 ≤-min-translate u v z C k k' r l =
  transport (λ - → r < (min u v + ιₐ -)) (ℚ-minus-minus C ⁻¹)
   (translate-strict (min u v) r (ℚ- C)
     (below-min u v (r ℚ+ (ℚ- C))
       (below-translate⁻¹ u r (ℚ- C)
         (transport (λ - → r < (u + ιₐ -)) (ℚ-minus-minus C) (k r l)))
       (below-translate⁻¹ v r (ℚ- C)
         (transport (λ - → r < (v + ιₐ -)) (ℚ-minus-minus C) (k' r l)))))

 P-is-monotone : (C C' : ℚ) → C' ≤ C → P C → P C'
 P-is-monotone C C' l h s t k k' =
  h s t k (ℝ≤-trans t (s + ιₐ C') (s + ιₐ C) k'
            (sum-≤ s s (ιₐ C') (ιₐ C) (ℝ≤-refl s) (ιₐ-≤-ιₐ C' C l)))

 P-is-additive : (C C' : ℚ) → 0ℚ ≤ C → 0ℚ ≤ C' → P C → P C' → P (C ℚ+ C')
 P-is-additive C C' l l' h h' s t k k' = h s m I II ∙ h' m t III IV
  where
   m : ℝ
   m = min t (s + ιₐ C)

   I : s ≤ m
   I = ≤-min t (s + ιₐ C) s k (≤-translate s C l)

   II : m ≤ (s + ιₐ C)
   II = min-≤-right t (s + ιₐ C)

   III : m ≤ t
   III = min-≤-left t (s + ιₐ C)

   IV : t ≤ (m + ιₐ C')
   IV = ≤-min-translate t (s + ιₐ C) t C' (≤-translate t C' l')
         (transport (λ - → t ≤ -) (translate-twice s C C' ⁻¹) k')

 module _ (p q : ℚ) (l₁ : g x < p) (l₂ : q < g y) where

  base : P (q ℚ- p)
  base s t k k' = ap e (I ⁻¹) ∙ (III x ∙ III y ⁻¹) ∙ ap e II
   where
    F : ℝ → ℝ
    F τ = clamp s t (s + (τ + ιₐ (ℚ- p)))

    I : F (g x) ＝ s
    I = clamp-below s t (s + (g x + ιₐ (ℚ- p)))
         (transport (λ - → (s + (g x + ιₐ (ℚ- p))) ≤ -) (plus-zero s)
           (sum-≤ s s (g x + ιₐ (ℚ- p)) (ιₐ 0ℚ) (ℝ≤-refl s)
             (translate-below (g x) 0ℚ p
               (transport (λ - → g x < -) (ℚ-zero-left-neutral p ⁻¹) l₁))))

    II : F (g y) ＝ t
    II = clamp-above s t (s + (g y + ιₐ (ℚ- p))) k
          (ℝ≤-trans t (s + ιₐ (q ℚ- p)) (s + (g y + ιₐ (ℚ- p))) k'
            (sum-≤ s s (ιₐ (q ℚ- p)) (g y + ιₐ (ℚ- p)) (ℝ≤-refl s)
              (translate-above (g y) (q ℚ- p) p
                (transport (λ - → - < g y) (minus-plus q p ⁻¹) l₂))))

    III : (r : S) → e (F (g r)) ＝ e (F (g s₀))
    III = S-maps-are-constant (λ r → e (F (g r)))

 all-constants : (c : ℚ) → 0ℚ < c → P c → (N : ℚ) → 0ℚ ≤ N → P N
 all-constants c l h N l' =
  climb (pr₁ σ) (P-is-monotone c (z (pr₁ σ))
                  (ℚ<-coarser-than-≤ (z (pr₁ σ)) c (pr₂ σ)) h)
  where
   z : ℕ → ℚ
   z 0        = N
   z (succ n) = half (z n)

   open halving-sequence z (λ n → refl)
   open nonneg l'
   open halving-sequence-bounds z (λ n → refl) N l' (ℚ≤-refl N)

   σ : Σ n ꞉ ℕ , z n < c
   σ = becomes-small c l

   climb : (k : ℕ) → P (z k) → P (z 0)
   climb 0        h' = h'
   climb (succ k) h' =
    climb k (transport P (doubled k)
              (P-is-additive (z (succ k)) (z (succ k))
                (is-nonneg (succ k)) (is-nonneg (succ k)) h' h'))

 hub : ((N : ℚ) → 0ℚ ≤ N → P N)
     → (a : ℝ) (L U : ℚ) → L < a → a < U → e (ιₐ L) ＝ e a
 hub φ a L U l l' =
  φ (U ℚ- L)
    (ℚ≤-difference-positive L U
      (ℚ<-coarser-than-≤ L U (cuts-are-ordered a L U l l')))
    (ιₐ L) a (>-gives-ιₐ-≤ a L l)
    (transport (λ - → a ≤ -)
      ((ιₐ-sum L (U ℚ- L) ∙ ap ιₐ (add-difference L U)) ⁻¹)
      (<-gives-≤-ιₐ a U l'))

 constancy-transfers-along-a-strict-rise : g x < g y → (a b : ℝ) → e a ＝ e b
 constancy-transfers-along-a-strict-rise l a b = ∥∥-rec A-is-set γ₁ l
  where
   γ₁ : (Σ p ꞉ ℚ , (g x < p) × (p < g y)) → e a ＝ e b
   γ₁ (p , l₁ , l₂) =
    ∥∥-rec A-is-set γ₂
     (rounded-left-b (lower-cut-of (g y)) (rounded-from-real-L (g y)) p l₂)
    where
     γ₂ : (Σ q ꞉ ℚ , (p < q) × (q < g y)) → e a ＝ e b
     γ₂ (q , m , l₃) = ∥∥-rec A-is-set γ₃ (inhabited-from-real-L (min a b))
      where
       φ : (N : ℚ) → 0ℚ ≤ N → P N
       φ = all-constants (q ℚ- p) (ℚ<-difference-positive p q m)
            (base p q l₁ l₃)

       γ₃ : (Σ L ꞉ ℚ , L < min a b) → e a ＝ e b
       γ₃ (L , k) = ∥∥-rec A-is-set γ₄ (inhabited-from-real-R a)
        where
         γ₄ : (Σ U ꞉ ℚ , a < U) → e a ＝ e b
         γ₄ (U , k₁) = ∥∥-rec A-is-set γ₅ (inhabited-from-real-R b)
          where
           γ₅ : (Σ U' ꞉ ℚ , b < U') → e a ＝ e b
           γ₅ (U' , k₂) = hub φ a L U (below-min-left a b L k) k₁ ⁻¹
                        ∙ hub φ b L U' (below-min-right a b L k) k₂

\end{code}
