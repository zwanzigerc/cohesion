Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

The n-variable form of Shulman's Theorem 11.5 from Axiom R♭ alone:
Theorem 7.17 of the write-up [1], by GPT-6 Astra; gate G24 of Claude
Fable 5.2's second addendum [2].

The exact statement. Theorem 7.17 of [1]: assume Axiom R♭; let n be a
crisp natural number, and let F :: ℝⁿ → ℝ and a :: ℝⁿ be crisp. For
every ε > 0 there is δ > 0 such that |F x - F a| < ε for every x : ℝⁿ
with |x - a| < δ, in the supremum norm. It is Remark 3.4 of [1]
without crisp excluded middle.

The formal statement, crisp-functions-of-several-variables-are-continuous,
is the same with rational bounds in place of ε: for rationals
u < F a < v there is a rational r > 0 such that u < F x < v for every
x, crisp or not, whose coordinates are strictly within r of those of
a. gist.RealCohesion.Theorems states it as Remark-3-4 of
gist.RealCohesion.ShulmanWeakeningsStatements.

The proof is Astra's transfer [1, proof of Theorem 7.17], with the curve
in the form of gist.RealCohesion.DigitCurve.

 1. G t = F (a + P t - c), for the curve P with 2n + 1 coordinates of
    which the first n are used, and c the box centre, is a crisp
    function of one variable, and G (1/4) = F a.

 2. Theorem 7.14 (gist.RealCohesion.CrispFunctionsAreContinuous) at the
    crisp point 1/4 gives a rational interval (r₁ , r₂) around 1/4 on
    which u₁ < G < v₁, for rationals u < u₁ < F a < v₁ < v.

 3. Take k with 2⁻ᵏ below 1/4 - r₁ and r₂ - 1/4, and the radius r of
    the box of level k. For x within r of a, locatedness gives
    u < F x < v, or F x < u₁, or v₁ < F x. In the second case the
    function y ↦ u₁ - F (a + y - c) is positive at the point
    c + x - a of the box, so, by detection along the curve, it is
    positive at P t for a rational t within 2⁻ᵏ of 1/4. Then t lies in
    (r₁ , r₂), so u₁ < G t, while the positivity says G t < u₁. The
    third case is the same with v₁.

The centre is 1/4 rather than Astra's 1/(3ⁿ + 1), and the cells are
intervals around 1/3 and 2/3 rather than dyadic cells around 1/3; see
gist.RealCohesion.DigitCodes and gist.RealCohesion.DigitCells. The
function G and the translations are defined before Axiom R♭ is
assumed, from crisp data only, so that G is crisp.

Since the consolidation of 13 November 2026, by Claude Opus 5.5 (W3 of
[3]), the proof is carried out under Axiom C1 for an ordinary family of
pointed generators, the ♭-discreteness of 𝟚 and a strictly rising
generator path in ℝ, merely (module continuity-under-C1), with Theorem
7.14 in the same generality. Axiom R♭ is the case of the one generator
ℝ, whose identity map rises from 0 to 1, and
crisp-functions-of-several-variables-are-continuous keeps its type
under Axiom R♭.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, revision of 12 November 2026, Theorem 7.17
    and Remark 3.4.
    references/C04-write-up-2026-11-12.tex

[2] Claude Fable 5.2. Second addendum to the formalization plan,
    revision 4 of 12 November 2026, §3, G24.
    references/F13b-second-addendum-rev4-as-amended.md

[3] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, Section 4.3, as corrected by
    its addendum 01 and released by GPT-6 Astra.
    references/F02-consolidation-plan.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.CrispFunctionsOfSeveralVariables
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ crisp-ap-^♭ : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } {@♭ x y : A}
                        → @♭ x ＝ y → x ^♭ ＝ y ^♭)
       where

open import Fin.Type using (Fin)
open import Notation.Order
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.RationalArithmetic
 using (half ; half-is-positive ; sum-minus-first)
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealOrder fe pe pt using (cuts-are-ordered)
open import gist.RealCohesion.RealLattice fe pe pt
 using (ℚ<ℝ-is-prop ; ℝ<ℚ-is-prop ; ιₐ-sum ; translate-twice ; plus-zero ;
         zero-plus ;
        minus-plus-cancel ; below-sum⁻¹ ; sum-below ; below-sum ; neg-below ;
         below-neg ;
        <-from-difference ; <-gives-positive-difference)
 renaming (_+_ to _ℝ+_ ; -_ to ℝ-_)
open import gist.RealCohesion.RealLimits fe pe pt using (ρ-becomes-small)
open import gist.RealCohesion.RealBalls fe pe pt
 using (minₐ ; minₐ-≤-left ; minₐ-≤-right ; minₐ-is-positive)
open import gist.RealCohesion.RationalDetection fe pe pt
 using (translate-upper ; translate-lower)
open import gist.RealCohesion.ContinuityForms fe pe pt using (Strictly-Close)
open import gist.RealCohesion.DigitCodes using (pow½ ; close ; dbl ; below-dbl)
open import gist.RealCohesion.DigitCells
 using
  (radius ; radius-is-positive ; close-gives-interval ; index ; index-bound ;
   box-centre ; box-radius)
open import gist.RealCohesion.DigitCurve fe pe pt
 using (P ; in-box ; P-at-centre ; curve-detection)
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭ as FCD
import gist.RealCohesion.CrispFunctionsAreContinuous fe pe pt crisp-ap-^♭ as
 CFAC
open import gist.RealCohesion.Constancy fe pe pt
 using (Rising-Generator-Path ; identity-of-ℝ-rises)

open PropositionalTruncation pt

\end{code}

Step 1: the translations, and the crisp function G of one variable.

\begin{code}

translate : {n : ℕ} → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ
translate a y j = (y j ℝ+ ιₐ (ℚ- box-centre (index j))) ℝ+ a j

inverse-translate : {n : ℕ} → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ
inverse-translate a x j = (x j ℝ+ (ℝ- a j)) ℝ+ ιₐ (box-centre (index j))

curve-function : (n : ℕ) → ((Fin n → ℝ) → ℝ) → (Fin n → ℝ) → ℝ → ℝ
curve-function n F a t = F (translate a (λ j → P (dbl n) (index j) t))

cancel-centre : (y : ℝ) (c : ℚ) → (y ℝ+ ιₐ c) ℝ+ ιₐ (ℚ- c) ＝ y
cancel-centre y c =
 translate-twice y c (ℚ- c) ∙ ap (λ q → y ℝ+ ιₐ q) (ℚ-inverse-sum-to-zero c)
                  ∙ plus-zero y

translate-of-box-centre : {n : ℕ} (a : Fin n → ℝ)
                        → translate a (λ j → ιₐ (box-centre (index j))) ＝ a
translate-of-box-centre a = dfunext fe γ
 where
  γ : (j : _) → translate a (λ j' → ιₐ (box-centre (index j'))) j ＝ a j
  γ j = ap (_ℝ+ a j) (ιₐ-sum (box-centre (index j)) (ℚ- box-centre (index j))
                      ∙ ap ιₐ (ℚ-inverse-sum-to-zero (box-centre (index j))))
      ∙ zero-plus (a j)

translate-of-inverse : {n : ℕ} (a x : Fin n → ℝ)
                     → translate a (inverse-translate a x) ＝ x
translate-of-inverse a x = dfunext fe γ
 where
  γ : (j : _) → translate a (inverse-translate a x) j ＝ x j
  γ j = ap (_ℝ+ a j) (cancel-centre (x j ℝ+ (ℝ- a j)) (box-centre (index j)))
      ∙ minus-plus-cancel (x j) (a j)

curve-function-at-centre : (n : ℕ) (F : (Fin n → ℝ) → ℝ) (a : Fin n → ℝ)
                         → curve-function n F a (ιₐ 1/4) ＝ F a
curve-function-at-centre n F a =
 ap (λ y → F (translate a y))
  (dfunext fe
    (λ j → P-at-centre n (index j) (below-dbl n (index j) (index-bound j))))
 ∙ ap F (translate-of-box-centre a)

\end{code}

Points strictly within r of a correspond to points of the box of
radius r around the box centre.

\begin{code}

difference-below : (x a : ℝ) (r : ℚ) → x < a ℝ+ ιₐ r
                 → ∃ t ꞉ ℚ , (x ℝ+ (ℝ- a) < t) × (t < r)
difference-below x a r = ∥∥-rec ∃-is-prop γ
 where
  γ : (Σ q ꞉ ℚ , (x < q) × (q < a ℝ+ ιₐ r))
    → ∃ t ꞉ ℚ , (x ℝ+ (ℝ- a) < t) × (t < r)
  γ (q , l , m) = ∥∥-functor δ (below-sum⁻¹ a (ιₐ r) q m)
   where
    δ : (Σ (s , t) ꞉ ℚ × ℚ , (s < a) × (t < ιₐ r) × (q ＝ s ℚ+ t))
      → Σ t ꞉ ℚ , (x ℝ+ (ℝ- a) < t) × (t < r)
    δ ((s , t) , o , o' , e) =
     t , transport (x ℝ+ (ℝ- a) <_) (ap (_ℚ- s) e ∙ sum-minus-first s t)
          (sum-below x (ℝ- a) q (ℚ- s) l (neg-below a s o)) ,
     ιₐ-lower⁻¹ t r o'

difference-above : (x a : ℝ) (r : ℚ) → a < x ℝ+ ιₐ r
                 → ∃ t ꞉ ℚ , (t < x ℝ+ (ℝ- a)) × ((ℚ- r) < t)
difference-above x a r = ∥∥-rec ∃-is-prop γ
 where
  γ : (Σ q ꞉ ℚ , (a < q) × (q < x ℝ+ ιₐ r))
    → ∃ t ꞉ ℚ , (t < x ℝ+ (ℝ- a)) × ((ℚ- r) < t)
  γ (q , l , m) = ∥∥-functor δ (below-sum⁻¹ x (ιₐ r) q m)
   where
    δ : (Σ (s , t) ꞉ ℚ × ℚ , (s < x) × (t < ιₐ r) × (q ＝ s ℚ+ t))
      → Σ t' ꞉ ℚ , (t' < x ℝ+ (ℝ- a)) × ((ℚ- r) < t')
    δ ((s , t) , o , o' , e) =
     (ℚ- t) ,
     transport (_< x ℝ+ (ℝ- a)) I
      (below-sum x (ℝ- a) s (ℚ- q) o (below-neg a q l)) ,
     ℚ<-swap t r (ιₐ-lower⁻¹ t r o')
     where
      I : s ℚ+ (ℚ- q) ＝ ℚ- t
      I = ap (λ q' → s ℚ+ (ℚ- q')) e
        ∙ ap (s ℚ+_) (ℚ-minus-dist s t ⁻¹)
        ∙ ℚ+-assoc s (ℚ- s) (ℚ- t) ⁻¹
        ∙ ap (_ℚ+ (ℚ- t)) (ℚ-inverse-sum-to-zero s)
        ∙ ℚ-zero-left-neutral (ℚ- t)

inverse-is-in-box : {n : ℕ} (k : ℕ) (a x : Fin n → ℝ)
                  → ((j : Fin n) → Strictly-Close (box-radius k) (x j) (a j))
                  → in-box k (inverse-translate a x)
inverse-is-in-box k a x b j = lower , upper
 where
  c r : ℚ
  c = box-centre (index j)
  r = box-radius k

  lower : ιₐ (c ℚ- r) < inverse-translate a x j
  lower = ∥∥-functor γ (difference-above (x j) (a j) r (pr₂ (b j)))
   where
    γ : (Σ t ꞉ ℚ , (t < x j ℝ+ (ℝ- a j)) × ((ℚ- r) < t))
      → Σ q ꞉ ℚ , (ιₐ (c ℚ- r) < q) × (q < inverse-translate a x j)
    γ (t , o , o') = t ℚ+ c ,
                     ιₐ-upper (c ℚ- r) (t ℚ+ c)
                      (transport (_< t ℚ+ c) (ℚ+-comm (ℚ- r) c)
                        (ℚ<-addition-preserves-order (ℚ- r) t c o')) ,
                     translate-lower (x j ℝ+ (ℝ- a j)) t c o

  upper : inverse-translate a x j < ιₐ (c ℚ+ r)
  upper = ∥∥-functor γ (difference-below (x j) (a j) r (pr₁ (b j)))
   where
    γ : (Σ t ꞉ ℚ , (x j ℝ+ (ℝ- a j) < t) × (t < r))
      → Σ q ꞉ ℚ , (inverse-translate a x j < q) × (q < ιₐ (c ℚ+ r))
    γ (t , o , o') = t ℚ+ c ,
                     translate-upper (x j ℝ+ (ℝ- a j)) t c o ,
                     ιₐ-lower (t ℚ+ c) (c ℚ+ r)
                      (transport (t ℚ+ c <_) (ℚ+-comm r c)
                        (ℚ<-addition-preserves-order t r c o'))

\end{code}

Comparisons with embedded rationals.

\begin{code}

below-ιₐ : (y : ℝ) (q : ℚ) → y < q → y < ιₐ q
below-ιₐ y q l =
 ∥∥-functor γ (rounded-right-b (upper-cut-of y) (rounded-from-real-R y) q l)
 where
  γ : (Σ q' ꞉ ℚ , (q' < q) × (y < q')) → Σ q' ꞉ ℚ , (y < q') × (q' < ιₐ q)
  γ (q' , k , l') = q' , l' , ιₐ-lower q' q k

above-ιₐ : (y : ℝ) (q : ℚ) → q < y → ιₐ q < y
above-ιₐ y q l = ∥∥-functor γ (rounded-left-d y q l)
 where
  γ : (Σ q' ꞉ ℚ , (q < q') × (q' < y)) → Σ q' ꞉ ℚ , (ιₐ q < q') × (q' < y)
  γ (q' , k , l') = q' , ιₐ-upper q q' k , l'

not-above-and-below-ιₐ : (y : ℝ) (q : ℚ) → q < y → y < ιₐ q → 𝟘
not-above-and-below-ιₐ y q l m = ∥∥-rec 𝟘-is-prop γ m
 where
  γ : (Σ q' ꞉ ℚ , (y < q') × (q' < ιₐ q)) → 𝟘
  γ (q' , k , k') = ℚ<-irrefl q (ℚ<-trans q q' q (cuts-are-ordered y q q' l k)
                                   (ιₐ-lower⁻¹ q' q k'))

not-below-and-above-ιₐ : (y : ℝ) (q : ℚ) → y < q → ιₐ q < y → 𝟘
not-below-and-above-ιₐ y q l m = ∥∥-rec 𝟘-is-prop γ m
 where
  γ : (Σ q' ꞉ ℚ , (ιₐ q < q') × (q' < y)) → 𝟘
  γ (q' , k , k') = ℚ<-irrefl q (ℚ<-trans q q' q (ιₐ-upper⁻¹ q q' k)
                                   (cuts-are-ordered y q' q k' l))

\end{code}

Choosing the level k: 2⁻ᵏ below the distances from 1/4 to the ends of
an interval. The rationals are arguments or bound by patterns, never
local definitions, as gist.RealCohesion.RealBalls recommends.

\begin{code}

choose-level : (r₁ r₂ : ℚ) → r₁ < 1/4 → 1/4 < r₂
             → Σ k ꞉ ℕ , (pow½ k < 1/4 ℚ- r₁) × (pow½ k < r₂ ℚ- 1/4)
choose-level r₁ r₂ l m =
 γ (ρ-becomes-small (minₐ (1/4 ℚ- r₁) (r₂ ℚ- 1/4))
     (minₐ-is-positive (1/4 ℚ- r₁) (r₂ ℚ- 1/4)
       (ℚ<-difference-positive r₁ 1/4 l) (ℚ<-difference-positive 1/4 r₂ m)))
 where
  γ : (Σ k' ꞉ ℕ , pow½ (succ k') < minₐ (1/4 ℚ- r₁) (r₂ ℚ- 1/4))
    → Σ k ꞉ ℕ , (pow½ k < 1/4 ℚ- r₁) × (pow½ k < r₂ ℚ- 1/4)
  γ (k' , s) = succ k' ,
               ℚ<-≤-trans (pow½ (succ k')) (minₐ (1/4 ℚ- r₁) (r₂ ℚ- 1/4))
                (1/4 ℚ- r₁) s
                (minₐ-≤-left (1/4 ℚ- r₁) (r₂ ℚ- 1/4)) ,
               ℚ<-≤-trans (pow½ (succ k')) (minₐ (1/4 ℚ- r₁) (r₂ ℚ- 1/4))
                (r₂ ℚ- 1/4) s
                (minₐ-≤-right (1/4 ℚ- r₁) (r₂ ℚ- 1/4))

near-the-centre : (r₁ r₂ : ℚ) (k : ℕ) → pow½ k < 1/4 ℚ- r₁ → pow½ k < r₂ ℚ- 1/4
                → (t : ℚ) → close (pow½ k) t 1/4 → (r₁ < ιₐ t) × (ιₐ t < r₂)
near-the-centre r₁ r₂ k s₁ s₂ t c =
 ιₐ-lower r₁ t (pr₁ (close-gives-interval (pow½ k) t 1/4 r₁ r₂ c s₁ s₂)) ,
 ιₐ-upper t r₂ (pr₂ (close-gives-interval (pow½ k) t 1/4 r₁ r₂ c s₁ s₂))

\end{code}

Steps 2 and 3, for the function G = curve-function n F a.

\begin{code}

module _ (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v)
         (n : ℕ)
         (F : (Fin n → ℝ) → ℝ)
         (a : Fin n → ℝ)
         (u₁ v₁ r₁ r₂ : ℚ)
         (k : ℕ)
         (h : (t : ℝ) → r₁ < t → t < r₂
            → (u₁ < curve-function n F a t) × (curve-function n F a t < v₁))
         (near : (t : ℚ) → close (pow½ k) t 1/4 → (r₁ < ιₐ t) × (ιₐ t < r₂))
         (x : Fin n → ℝ)
         (b : (j : Fin n) → Strictly-Close (box-radius k) (x j) (a j))
       where

 private
  w₀-is-in-box : in-box k (inverse-translate a x)
  w₀-is-in-box = inverse-is-in-box k a x b

  at-w₀ : F (translate a (inverse-translate a x)) ＝ F x
  at-w₀ = ap F (translate-of-inverse a x)

 not-below : F x < u₁ → 𝟘
 not-below q = ∥∥-rec 𝟘-is-prop γ
                (curve-detection ν n k (λ y → ιₐ u₁ ℝ+ (ℝ- F (translate a y)))
                  (inverse-translate a x) w₀-is-in-box
                  (<-gives-positive-difference (ιₐ u₁)
                    (F (translate a (inverse-translate a x)))
                    (transport (_< ιₐ u₁) (at-w₀ ⁻¹) (below-ιₐ (F x) u₁ q))))
  where
   γ : (Σ t ꞉ ℚ , close (pow½ k) t 1/4
                × (0ℝ < ιₐ u₁
                   ℝ+ (ℝ- F (translate a (λ j → P (dbl n) (index j) (ιₐ t))))))
     → 𝟘
   γ (t , c , pos) =
    not-above-and-below-ιₐ (curve-function n F a (ιₐ t)) u₁
     (pr₁ (h (ιₐ t) (pr₁ (near t c)) (pr₂ (near t c))))
     (<-from-difference (ιₐ u₁) (curve-function n F a (ιₐ t)) pos)

 not-above : v₁ < F x → 𝟘
 not-above q = ∥∥-rec 𝟘-is-prop γ
                (curve-detection ν n k (λ y → F (translate a y) ℝ+ (ℝ- ιₐ v₁))
                  (inverse-translate a x) w₀-is-in-box
                  (<-gives-positive-difference
                    (F (translate a (inverse-translate a x))) (ιₐ v₁)
                    (transport (ιₐ v₁ <_) (at-w₀ ⁻¹) (above-ιₐ (F x) v₁ q))))
  where
   γ : (Σ t ꞉ ℚ , close (pow½ k) t 1/4
                × (0ℝ < F (translate a (λ j → P (dbl n) (index j) (ιₐ t)))
                   ℝ+ (ℝ- ιₐ v₁)))
     → 𝟘
   γ (t , c , pos) =
    not-below-and-above-ιₐ (curve-function n F a (ιₐ t)) v₁
     (pr₂ (h (ιₐ t) (pr₁ (near t c)) (pr₂ (near t c))))
     (<-from-difference (curve-function n F a (ιₐ t)) (ιₐ v₁) pos)

 within-bounds : (u v : ℚ) → u < u₁ → v₁ < v → (u < F x) × (F x < v)
 within-bounds u v o p =
  ∥∥-rec (×-is-prop (ℚ<ℝ-is-prop u (F x)) (ℝ<ℚ-is-prop (F x) v)) γ
                          (binary-choice (ℝ-locatedness (F x) u u₁ o)
                            (ℝ-locatedness (F x) v₁ v p))
  where
   γ : ((u < F x) ∔ (F x < u₁)) × ((v₁ < F x) ∔ (F x < v))
     → (u < F x) × (F x < v)
   γ (inl q , inr q') = q , q'
   γ (inr q , _)      = 𝟘-elim (not-below q)
   γ (inl _ , inl q') = 𝟘-elim (not-above q')

\end{code}

The theorem, under Axiom C1 for an ordinary family of generators and
the propositional truncation of a strictly rising generator path in ℝ,
which give the constancy of maps ℝ → Q
(gist.RealCohesion.FiniteChainDiscreteness) and the continuity in one
variable (gist.RealCohesion.CrispFunctionsAreContinuous); Axiom R♭ is
the instance below.

\begin{code}

module continuity-under-C1
        {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
        (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
        (nc : ∥ Rising-Generator-Path R ∥)
       where

 private
  ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v
  ν = FCD.under-C1.constancy-from-C1-and-NC R c1 𝟚-is-♭-discrete nc

 crisp-functions-of-several-variables-are-continuous
  : (@♭ n : ℕ) (@♭ F : (Fin n → ℝ) → ℝ) (@♭ a : Fin n → ℝ) (u v : ℚ)
  → u < F a → F a < v
  → ∃ r ꞉ ℚ , (0ℚ < r)
            × ((x : Fin n → ℝ) → ((j : Fin n) → Strictly-Close r (x j) (a j))
                               → (u < F x) × (F x < v))
 crisp-functions-of-several-variables-are-continuous n F a u v l m =
  ∥∥-rec ∃-is-prop γ
   (binary-choice (rounded-left-d (F a) u l)
                  (rounded-right-b (upper-cut-of (F a))
                    (rounded-from-real-R (F a)) v m))
  where
   γ : (Σ u₁ ꞉ ℚ , (u < u₁) × (u₁ < F a)) × (Σ v₁ ꞉ ℚ , (v₁ < v) × (F a < v₁))
     → ∃ r ꞉ ℚ , (0ℚ < r)
               × ((x : Fin n → ℝ) → ((j : Fin n) → Strictly-Close r (x j) (a j))
                                  → (u < F x) × (F x < v))
   γ ((u₁ , o , o') , (v₁ , p , p')) =
    ∥∥-functor δ
     (CFAC.continuity-under-C1.crisp-functions-are-continuous R c1
       𝟚-is-♭-discrete nc
       (curve-function n F a) (ιₐ 1/4)
       u₁ v₁ (transport (u₁ <_) (curve-function-at-centre n F a ⁻¹) o')
             (transport (_< v₁) (curve-function-at-centre n F a ⁻¹) p'))
    where
     δ : (Σ (r₁ , r₂) ꞉ ℚ × ℚ , (r₁ < ιₐ 1/4) × (ιₐ 1/4 < r₂)
                              × ((t : ℝ) → r₁ < t → t < r₂
                                         → (u₁ < curve-function n F a t)
                                         × (curve-function n F a t < v₁)))
       → Σ r ꞉ ℚ , (0ℚ < r)
                 ×
                 ((x : Fin n → ℝ) → ((j : Fin n) → Strictly-Close r (x j) (a j))
                                  → (u < F x) × (F x < v))
     δ ((r₁ , r₂) , k₁ , k₂ , h) =
      ε (choose-level r₁ r₂ (ιₐ-lower⁻¹ r₁ 1/4 k₁) (ιₐ-upper⁻¹ 1/4 r₂ k₂))
      where
       ε : (Σ k ꞉ ℕ , (pow½ k < 1/4 ℚ- r₁) × (pow½ k < r₂ ℚ- 1/4))
         → Σ r ꞉ ℚ , (0ℚ < r)
                   × ((x : Fin n → ℝ)
                      → ((j : Fin n) → Strictly-Close r (x j) (a j))
                                      → (u < F x) × (F x < v))
       ε (k , s₁ , s₂) =
        box-radius k , half-is-positive (radius k) (radius-is-positive k) ,
        (λ x b → within-bounds ν n F a u₁ v₁ r₁ r₂ k h
                  (near-the-centre r₁ r₂ k s₁ s₂) x b
                  u v o p)

\end{code}

Under Axiom R♭: the instance for the one generator ℝ, whose identity
map rises from 0 to 1, with the name and type of the module before the
consolidation of 13 November 2026.

\begin{code}

module _ (r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ)
         (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
       where

 crisp-functions-of-several-variables-are-continuous
  : (@♭ n : ℕ) (@♭ F : (Fin n → ℝ) → ℝ) (@♭ a : Fin n → ℝ) (u v : ℚ)
  → u < F a → F a < v
  → ∃ r ꞉ ℚ , (0ℚ < r)
            × ((x : Fin n → ℝ) → ((j : Fin n) → Strictly-Close r (x j) (a j))
                               → (u < F x) × (F x < v))
 crisp-functions-of-several-variables-are-continuous =
  continuity-under-C1.crisp-functions-of-several-variables-are-continuous
   (λ (_ : 𝟙 {𝓤₀}) → ℝ)
   (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
   𝟚-is-♭-discrete identity-of-ℝ-rises

\end{code}
