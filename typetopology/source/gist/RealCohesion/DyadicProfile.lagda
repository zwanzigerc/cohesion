Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 26 October 2026. See the AI disclosure in
gist.RealCohesion.index. The function is the dyadic witness proposed
in GPT-6 Astra's gameplan (25 October 2026) [2] for the counterexample of
the research notes [1, Section 5], by Claude Opus.

A 1-Lipschitz rational function that oscillates at 0.

We construct f : ℚ → ℚ with

  f y = max (0 , |y| - 1)               for |y| ≥ 5/32,
          + max (0 , 1/16 - ||y| - 1/4|)
  f y = - f (2 y) / 2                   for |y| ≤ 5/32,

so that f has a ramp beyond ±1, a bump of height 1/16 centred at ±1/4,
and below 5/32 the copies of this bump scaled by (- 1/2)ⁿ, centred at
±2⁻ⁿ⁻², with alternating signs. Between the bumps f is 0, on the
plateaux ±[5/16 , 1] and ±[5 · 2⁻ⁿ⁻⁵ , 3 · 2⁻ⁿ⁻⁴].

The construction is a recursion with fuel: H m keeps the first m + 1
bumps, and f y = ramp y + H (den y) y, where den y is the denominator of
y. The fuel is enough, because the bumps of level at least den y are
smaller than |y| ≥ 1 / den y. Every H m is 1-Lipschitz, because the
bumps of consecutive levels have separated supports, and hence so is
f. We make f abstract and export the characteristic properties listed
above, together with f 0 ＝ f 1 ＝ 0 and f (- y) ＝ f y.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, draft of 25 October 2026.
    references/C01-write-up-2026-10-25.tex

[2] GPT-6 Astra. Gameplan for Opus: a subset of the Dedekind reals
    whose shape is not a set, 25 October 2026.
    references/A32-subset-shape-gameplan.md

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.DyadicProfile
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Integers.Addition renaming (_+_ to _ℤ+_) hiding (_-_)
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Order
open import Integers.Type hiding (abs)
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Notation.Order
open import UF.Base
open import Rationals.Abs
open import Rationals.Addition
open import Rationals.Fractions
open import Rationals.FractionsOrder
open import Rationals.FractionsOperations renaming (abs to 𝔽-abs)
 hiding (_+_ ; _*_ ; -_)
open import Rationals.Limits fe pe pt
open import Rationals.MinMax
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Type
open import gist.RealCohesion.RationalArithmetic
open import gist.RealCohesion.RationalLimits fe pe pt
open import gist.RealCohesion.RationalLipschitz

\end{code}

Constants and their order.

\begin{code}

1/16 3/16 5/16 5/32 : ℚ
1/16 = toℚ (pos 1 , 15)
3/16 = toℚ (pos 3 , 15)
5/16 = toℚ (pos 5 , 15)
5/32 = toℚ (pos 5 , 31)

5/32≤3/16 : 5/32 ≤ 3/16
5/32≤3/16 = 16 , refl

3/16≤1/4 : 3/16 ≤ 1/4
3/16≤1/4 = 4 , refl

1/4≤5/16 : 1/4 ≤ 5/16
1/4≤5/16 = 4 , refl

5/16≤1 : 5/16 ≤ 1ℚ
5/16≤1 = 11 , refl

5/32≤1 : 5/32 ≤ 1ℚ
5/32≤1 = 27 , refl

5/32+5/32 : 5/32 + 5/32 ＝ 5/16
5/32+5/32 = refl

1/16-1/4 : 1/16 - 1/4 ＝ - 3/16
1/16-1/4 = refl

1/16+1/4 : 1/16 + 1/4 ＝ 5/16
1/16+1/4 = refl

half-of-zero : half 0ℚ ＝ 0ℚ
half-of-zero = refl

\end{code}

The ramp and the bump.

\begin{code}

ramp bump : ℚ → ℚ
ramp y = nonneg-part (abs y - 1ℚ)
bump y = nonneg-part (1/16 - abs (abs y - 1/4))

ramp-is-Lipschitz : Lipschitz ramp
ramp-is-Lipschitz =
 ∘-Lipschitz nonneg-part (λ y → abs y - 1ℚ) nonneg-part-is-Lipschitz
  (∘-Lipschitz (λ u → u - 1ℚ) abs (translation-is-Lipschitz (- 1ℚ))
    abs-is-Lipschitz)

bump-is-Lipschitz : Lipschitz bump
bump-is-Lipschitz =
 ∘-Lipschitz nonneg-part (λ y → 1/16 - abs (abs y - 1/4))
  nonneg-part-is-Lipschitz
  (∘-Lipschitz (λ u → 1/16 - u) (λ y → abs (abs y - 1/4))
    (reflection-is-Lipschitz 1/16)
    (∘-Lipschitz abs (λ y → abs y - 1/4) abs-is-Lipschitz
      (∘-Lipschitz (λ u → u - 1/4) abs (translation-is-Lipschitz (- 1/4))
        abs-is-Lipschitz)))

private
 reflect-difference : (c d u : ℚ) → c - (d - u) ＝ u + (c - d)
 reflect-difference c d u = ap (c +_) (ℚ-minus-dist' d u)
                          ∙ ℚ+-assoc c u (- d) ⁻¹
                          ∙ ap (_+ (- d)) (ℚ+-comm c u)
                          ∙ ℚ+-assoc u c (- d)

 reflect-sum : (c d u : ℚ) → c - (u - d) ＝ (c + d) - u
 reflect-sum c d u = ap (c +_) (ℚ-minus-dist' u d) ∙ ℚ+-assoc c d (- u) ⁻¹

 nonpos-difference : (u v : ℚ) → u ≤ v → u - v ≤ 0ℚ
 nonpos-difference u v l = transport (u - v ≤_) (ℚ-inverse-sum-to-zero v)
                            (ℚ≤-addition-preserves-order u v (- v) l)

bump-low : (y : ℚ) → abs y ≤ 1/4 → bump y ＝ nonneg-part (abs y - 3/16)
bump-low y l = ap nonneg-part (ap (λ w → 1/16 - w) (ℚ≤-to-abs' (abs y) 1/4 l)
                               ∙ reflect-difference 1/16 1/4 (abs y)
                               ∙ ap (abs y +_) 1/16-1/4)

bump-high : (y : ℚ) → 1/4 ≤ abs y → bump y ＝ nonneg-part (5/16 - abs y)
bump-high y l = ap nonneg-part (ap (λ w → 1/16 - w)
                                 (abs-comm (abs y) 1/4
                                  ∙ ℚ≤-to-abs' 1/4 (abs y) l)
                                ∙ reflect-sum 1/16 1/4 (abs y)
                                ∙ ap (_- abs y) 1/16+1/4)

bump-inner : (y : ℚ) → abs y ≤ 3/16 → bump y ＝ 0ℚ
bump-inner y l = bump-low y (ℚ≤-trans (abs y) 3/16 1/4 l 3/16≤1/4)
               ∙ nonneg-part-of-nonpos (abs y - 3/16)
                  (nonpos-difference (abs y) 3/16 l)

bump-rising : (y : ℚ) → 3/16 ≤ abs y → abs y ≤ 1/4 → bump y ＝ abs y - 3/16
bump-rising y l l' = bump-low y l'
                   ∙ nonneg-part-of-nonneg (abs y - 3/16)
                      (ℚ≤-difference-positive 3/16 (abs y) l)

bump-falling : (y : ℚ) → 1/4 ≤ abs y → abs y ≤ 5/16 → bump y ＝ 5/16 - abs y
bump-falling y l l' = bump-high y l
                    ∙ nonneg-part-of-nonneg (5/16 - abs y)
                       (ℚ≤-difference-positive (abs y) 5/16 l')

bump-outer : (y : ℚ) → 5/16 ≤ abs y → bump y ＝ 0ℚ
bump-outer y l = bump-high y (ℚ≤-trans 1/4 5/16 (abs y) 1/4≤5/16 l)
               ∙ nonneg-part-of-nonpos (5/16 - abs y)
                  (nonpos-difference 5/16 (abs y) l)

ramp-inner : (y : ℚ) → abs y ≤ 1ℚ → ramp y ＝ 0ℚ
ramp-inner y l =
 nonneg-part-of-nonpos (abs y - 1ℚ) (nonpos-difference (abs y) 1ℚ l)

ramp-outer : (y : ℚ) → 1ℚ ≤ abs y → ramp y ＝ abs y - 1ℚ
ramp-outer y l =
 nonneg-part-of-nonneg (abs y - 1ℚ) (ℚ≤-difference-positive 1ℚ (abs y) l)

ramp-is-even : (y : ℚ) → ramp (- y) ＝ ramp y
ramp-is-even y = ap (λ w → nonneg-part (w - 1ℚ)) (ℚ-abs-neg-equals-pos y ⁻¹)

bump-is-even : (y : ℚ) → bump (- y) ＝ bump y
bump-is-even y =
 ap (λ w → nonneg-part (1/16 - abs (w - 1/4))) (ℚ-abs-neg-equals-pos y ⁻¹)

abs-of-double : (y : ℚ) → abs (y + y) ＝ abs y + abs y
abs-of-double y = halves-add-up (abs (y + y)) ⁻¹ ∙ ap₂ _+_ I I
 where
  I : half (abs (y + y)) ＝ abs y
  I = abs-of-half (y + y) ⁻¹ ∙ ap abs (half-of-double y)

double-bound : (c y : ℚ) → c ≤ abs y → c + c ≤ abs (y + y)
double-bound c y l =
 transport (c + c ≤_) (abs-of-double y ⁻¹) (ℚ≤-adding c (abs y) c (abs y) l l)

double-bound' : (c y : ℚ) → abs y ≤ c → abs (y + y) ≤ c + c
double-bound' c y l =
 transport (_≤ c + c) (abs-of-double y ⁻¹) (ℚ≤-adding (abs y) c (abs y) c l l)

double-is-larger : (y : ℚ) → abs y ≤ abs (y + y)
double-is-larger y = transport (abs y ≤_) (abs-of-double y ⁻¹)
                      (ℚ≤-addition-preserves-order'' (abs y) (abs y)
                        (ℚ-abs-is-positive y))

\end{code}

Some closed computations, used to avoid relying on computation inside
larger expressions.

\begin{code}

bump-at-zero : bump 0ℚ ＝ 0ℚ
bump-at-zero = refl

ramp-at-zero : ramp 0ℚ ＝ 0ℚ
ramp-at-zero = refl

zero-plus-zero : 0ℚ + 0ℚ ＝ 0ℚ
zero-plus-zero = refl

zero-minus-half-of-zero : 0ℚ - half 0ℚ ＝ 0ℚ
zero-minus-half-of-zero = refl

negated-half-of-zero : - half 0ℚ ＝ 0ℚ
negated-half-of-zero = refl

\end{code}

The approximations H m, with the bumps of levels 0 , … , m. We make H
abstract, and use its defining equations explicitly: the type checker
should never have to unfold H inside rational arithmetic, which is very
expensive.

\begin{code}

abstract
 H : ℕ → ℚ → ℚ
 H 0        y = bump y
 H (succ m) y = bump y - half (H m (y + y))

 H-zero : (y : ℚ) → H 0 y ＝ bump y
 H-zero y = refl

 H-succ : (m : ℕ) (y : ℚ) → H (succ m) y ＝ bump y - half (H m (y + y))
 H-succ m y = refl

H-outer : (m : ℕ) (y : ℚ) → 5/16 ≤ abs y → H m y ＝ 0ℚ
H-outer 0        y l = H-zero y ∙ bump-outer y l
H-outer (succ m) y l =
   H-succ m y
 ∙ ap₂-at (λ (a b : ℚ) → a - half b) (bump y) 0ℚ (H m (y + y)) 0ℚ
     (bump-outer y l) (H-outer m (y + y) X)
 ∙ zero-minus-half-of-zero
 where
  X : 5/16 ≤ abs (y + y)
  X = ℚ≤-trans 5/16 (abs y) (abs (y + y)) l (double-is-larger y)

H-at-zero : (m : ℕ) → H m 0ℚ ＝ 0ℚ
H-at-zero 0        = H-zero 0ℚ ∙ bump-at-zero
H-at-zero (succ m) =
   H-succ m 0ℚ
 ∙ ap-at (λ (w : ℚ) → bump 0ℚ - half (H m w)) (0ℚ + 0ℚ) 0ℚ zero-plus-zero
 ∙ ap₂-at (λ (a b : ℚ) → a - half b) (bump 0ℚ) 0ℚ (H m 0ℚ) 0ℚ bump-at-zero
    (H-at-zero m)
 ∙ zero-minus-half-of-zero

H-is-even : (m : ℕ) (y : ℚ) → H m (- y) ＝ H m y
H-is-even 0        y = H-zero (- y) ∙ bump-is-even y ∙ H-zero y ⁻¹
H-is-even (succ m) y =
   H-succ m (- y)
 ∙ ap₂-at (λ (a b : ℚ) → a - half b) (bump (- y)) (bump y) (H m ((- y) + (- y)))
    (H m (y + y))
     (bump-is-even y) X
 ∙ H-succ m y ⁻¹
 where
  X : H m ((- y) + (- y)) ＝ H m (y + y)
  X = ap-at (H m) ((- y) + (- y)) (- (y + y)) (ℚ-minus-dist y y)
      ∙ H-is-even m (y + y)

H-is-Lipschitz : (m : ℕ) → Lipschitz (H m)
H-is-Lipschitz 0        = Lipschitz-ext (H 0) bump H-zero bump-is-Lipschitz
H-is-Lipschitz (succ m) =
 Lipschitz-ext (H (succ m)) (λ y → bump y + (- half (H m (y + y)))) (H-succ m) γ
 where
  ψ : ℚ → ℚ
  ψ y = - half (H m (y + y))

  ψ-is-Lipschitz : Lipschitz ψ
  ψ-is-Lipschitz =
   ∘-Lipschitz -_ (λ y → half (H m (y + y))) negation-is-Lipschitz
                    (rescaling-is-Lipschitz (H m) (H-is-Lipschitz m))

  bump-vanishes : (y : ℚ) → abs y ≤ 5/32 → bump y ＝ 0ℚ
  bump-vanishes y l = bump-inner y (ℚ≤-trans (abs y) 5/32 3/16 l 5/32≤3/16)

  ψ-vanishes : (y : ℚ) → 5/32 ≤ abs y → ψ y ＝ 0ℚ
  ψ-vanishes y l =
   ap-at (λ (w : ℚ) → - half w) (H m (y + y)) 0ℚ (H-outer m (y + y) X)
                 ∙ negated-half-of-zero
   where
    X : 5/16 ≤ abs (y + y)
    X = transport-at (λ (w : ℚ) → w ≤ abs (y + y)) (5/32 + 5/32) 5/16 5/32+5/32
         (double-bound 5/32 y l)

  γ : Lipschitz (λ y → bump y + ψ y)
  γ = glued-is-Lipschitz bump ψ 5/32 bump-is-Lipschitz ψ-is-Lipschitz
       bump-vanishes ψ-vanishes

\end{code}

Stabilization. The bumps of level greater than m vanish at |y| ≥ 5 /
2ᵐ⁺⁵. The thresholds are abstract, for the same reason as H.

\begin{code}

abstract
 threshold : ℕ → ℚ
 threshold 0        = 5/32
 threshold (succ m) = half (threshold m)

 threshold-zero : threshold 0 ＝ 5/32
 threshold-zero = refl

 threshold-succ : (m : ℕ) → threshold (succ m) ＝ half (threshold m)
 threshold-succ m = refl

\end{code}

The thresholds form a halving sequence, so their lemmas are instances
of halving-sequence (gist.RealCohesion.RationalArithmetic) and
halving-sequence-bounds (gist.RealCohesion.RationalLimits).

\begin{code}

private
 module threshold-sequence =
  halving-sequence.positive threshold threshold-succ
   (transport-at (λ (w : ℚ) → 0ℚ < w) 5/32 (threshold 0) (threshold-zero ⁻¹)
     (4 , refl))

 module threshold-bounds =
  halving-sequence-bounds threshold threshold-succ 1ℚ (1 , refl)
   (transport-at (λ (w : ℚ) → w ≤ 1ℚ) 5/32 (threshold 0) (threshold-zero ⁻¹)
     (27 , refl))

open halving-sequence threshold threshold-succ
 using () renaming (doubled to threshold-doubled) public
open threshold-sequence
 using ()
 renaming
  (is-positive to threshold-is-positive ; is-nonneg to threshold-is-nonneg ;
   decreases to threshold-decreases ; shift to threshold-decreases')
 public
open threshold-bounds using ()
 renaming (becomes-small to threshold-becomes-small) public

threshold-at-most-first : (m : ℕ) → threshold m ≤ 5/32
threshold-at-most-first m =
 transport-at (λ (w : ℚ) → threshold m ≤ w) (threshold 0) 5/32
                             threshold-zero (threshold-sequence.at-most-first m)

threshold-bound : (m : ℕ) → threshold m ≤ (⟨2/3⟩^ m)
threshold-bound m =
 transport-at (λ (w : ℚ) → threshold m ≤ w) ((⟨2/3⟩^ m) * 1ℚ) (⟨2/3⟩^ m)
                     (ℚ-mult-right-id (⟨2/3⟩^ m)) (threshold-bounds.bound m)

H-stable : (m : ℕ) (y : ℚ) → threshold m ≤ abs y → H (succ m) y ＝ H m y
H-stable 0 y l =
   H-succ 0 y
 ∙ ap-at (λ (w : ℚ) → bump y - half w) (H 0 (y + y)) 0ℚ
    (H-zero (y + y) ∙ bump-outer (y + y) X)
 ∙ ap-at (λ (w : ℚ) → bump y - w) (half 0ℚ) 0ℚ half-of-zero
 ∙ minus-zero (bump y)
 ∙ H-zero y ⁻¹
 where
  l' : 5/32 ≤ abs y
  l' = transport-at (λ (w : ℚ) → w ≤ abs y) (threshold 0) 5/32 threshold-zero l

  X : 5/16 ≤ abs (y + y)
  X = transport-at (λ (w : ℚ) → w ≤ abs (y + y)) (5/32 + 5/32) 5/16 5/32+5/32
       (double-bound 5/32 y l')
H-stable (succ m) y l =
   H-succ (succ m) y
 ∙ ap-at (λ (w : ℚ) → bump y - half w) (H (succ m) (y + y)) (H m (y + y))
    (H-stable m (y + y) X)
 ∙ H-succ m y ⁻¹
 where
  X : threshold m ≤ abs (y + y)
  X = transport-at (λ (w : ℚ) → w ≤ abs (y + y))
       (threshold (succ m) + threshold (succ m))
       (threshold m) (threshold-doubled m)
        (double-bound (threshold (succ m)) y l)

H-stable-top : (m : ℕ) (y : ℚ) → 5/32 ≤ abs y → H m y ＝ bump y
H-stable-top 0        y l = H-zero y
H-stable-top (succ m) y l =
 H-stable m y
  (ℚ≤-trans (threshold m) 5/32 (abs y) (threshold-at-most-first m) l)
 ∙ H-stable-top m y l

\end{code}

The fuel. For a nonzero rational y with denominator d, we have
1 / d ≤ |y|, and the threshold at d is at most (2/3)ᵈ ≤ 1 / d.

\begin{code}

abstract
 den : ℚ → ℕ
 den ((x , a) , _) = succ a

 private
  one-over-denominator : (q : ℚ) → ¬ (q ＝ 0ℚ) → ⟨1/sn⟩ (den q) ≤ abs q
  one-over-denominator q@((x , a) , p) ν =
   toℚ-≤ (pos 1 , a) (𝔽-abs (x , a)) (γ x refl)
   where
    I : (k : ℕ) → pos 1 ℤ* pos (succ a) ≤ pos (succ k) ℤ* pos (succ a)
    I k = positive-multiplication-preserves-order' (pos 1) (pos (succ k))
           (pos (succ a)) ⋆
           (k , ℤ+-comm (pos 1) (pos k))

    γ : (z : ℤ) → z ＝ x → (pos 1 , a) 𝔽≤ 𝔽-abs (x , a)
    γ (pos 0)        e = 𝟘-elim (ν (numerator-zero-is-zero q (e ⁻¹)))
    γ (pos (succ k)) e = transport (λ w → (pos 1 , a) 𝔽≤ 𝔽-abs (w , a)) e (I k)
    γ (negsucc k)    e = transport (λ w → (pos 1 , a) 𝔽≤ 𝔽-abs (w , a)) e (I k)

 den-bound : (y : ℚ) → ¬ (y ＝ 0ℚ) → threshold (den y) ≤ abs y
 den-bound y@((x , a) , p) ν =
  ℚ≤-trans (threshold (succ a)) (⟨2/3⟩^ (succ a)) (abs y)
   (threshold-bound (succ a))
   (ℚ≤-trans (⟨2/3⟩^ (succ a)) (⟨1/sn⟩ (succ a)) (abs y)
     (⟨1/sn⟩-bounds-⟨2/3⟩ (succ a))
     (one-over-denominator y ν))

H-stable-from-den : (y : ℚ) → ¬ (y ＝ 0ℚ) → (k : ℕ)
                  → H (den y ℕ+ k) y ＝ H (den y) y
H-stable-from-den y ν 0        = refl
H-stable-from-den y ν (succ k) =
 H-stable (den y ℕ+ k) y
  (ℚ≤-trans (threshold (den y ℕ+ k)) (threshold (den y)) (abs y)
    (threshold-decreases' (den y) k) (den-bound y ν))
 ∙ H-stable-from-den y ν k

\end{code}

The function f, and its properties.

\begin{code}

abstract
 f : ℚ → ℚ
 f y = ramp y + H (den y) y

 private
  f-as : (y : ℚ) (k : ℕ) → f y ＝ ramp y + H (den y ℕ+ k) y
  f-as y k = ap-at (λ (w : ℚ) → ramp y + w) (H (den y) y) (H (den y ℕ+ k) y)
              (γ (ℚ-is-discrete y 0ℚ))
   where
    γ : (y ＝ 0ℚ) ∔ ¬ (y ＝ 0ℚ) → H (den y) y ＝ H (den y ℕ+ k) y
    γ (inl e) = I (den y) ∙ I (den y ℕ+ k) ⁻¹
     where
      I : (n : ℕ) → H n y ＝ 0ℚ
      I n = transport-at (λ (w : ℚ) → H n w ＝ 0ℚ) 0ℚ y (e ⁻¹) (H-at-zero n)
    γ (inr ν) = H-stable-from-den y ν k ⁻¹

 f-is-Lipschitz : Lipschitz f
 f-is-Lipschitz x y =
  transport₂ (λ a b → abs (a - b) ≤ abs (x - y)) (I ⁻¹) (II ⁻¹) IV
  where
   K : ℕ
   K = den x ℕ+ den y

   I : f x ＝ ramp x + H K x
   I = f-as x (den y)

   II' : f y ＝ ramp y + H (den y ℕ+ den x) y
   II' = f-as y (den x)

   II'' : ramp y + H (den y ℕ+ den x) y ＝ ramp y + H K y
   II'' = ap-at (λ (n : ℕ) → ramp y + H n y) (den y ℕ+ den x) K
           (addition-commutativity (den y) (den x))

   II : f y ＝ ramp y + H K y
   II = II' ∙ II''

   outer : (z : ℚ) → 1ℚ ≤ abs z → H K z ＝ 0ℚ
   outer z l = H-outer K z (ℚ≤-trans 5/16 1ℚ (abs z) 5/16≤1 l)

   III : Lipschitz (λ z → ramp z + H K z)
   III = glued-is-Lipschitz ramp (H K) 1ℚ ramp-is-Lipschitz (H-is-Lipschitz K)
          ramp-inner outer

   IV : abs ((ramp x + H K x) - (ramp y + H K y)) ≤ abs (x - y)
   IV = III x y

 f-top : (y : ℚ) → 5/32 ≤ abs y → f y ＝ ramp y + bump y
 f-top y l = ap-at (λ (w : ℚ) → ramp y + w) (H (den y) y) (bump y)
              (H-stable-top (den y) y l)

 f-self-similar : (y : ℚ) → abs y ≤ 5/32 → f y ＝ - half (f (y + y))
 f-self-similar y l = I ∙ II ∙ III'
  where
   K : ℕ
   K = den y ℕ+ den (y + y)

   abs-y≤1 : abs y ≤ 1ℚ
   abs-y≤1 = ℚ≤-trans (abs y) 5/32 1ℚ l 5/32≤1

   abs-y≤3/16 : abs y ≤ 3/16
   abs-y≤3/16 = ℚ≤-trans (abs y) 5/32 3/16 l 5/32≤3/16

   abs-2y≤5/16 : abs (y + y) ≤ 5/16
   abs-2y≤5/16 =
    transport-at (λ (w : ℚ) → abs (y + y) ≤ w) (5/32 + 5/32) 5/16 5/32+5/32
                  (double-bound' 5/32 y l)

   abs-2y≤1 : abs (y + y) ≤ 1ℚ
   abs-2y≤1 = ℚ≤-trans (abs (y + y)) 5/16 1ℚ abs-2y≤5/16 5/16≤1

   Z : ℚ
   Z = half (H K (y + y))

   I₀ : f y ＝ ramp y + H (succ K) y
   I₀ = f-as y (succ (den (y + y)))

   I₁ : ramp y + H (succ K) y ＝ ramp y + (bump y - Z)
   I₁ = ap-at (λ (w : ℚ) → ramp y + w) (H (succ K) y) (bump y - Z) (H-succ K y)

   I : f y ＝ ramp y + (bump y - Z)
   I = I₀ ∙ I₁

   II₀ : ramp y + (bump y - Z) ＝ 0ℚ + (0ℚ - Z)
   II₀ = ap₂-at (λ (a b : ℚ) → a + (b - Z)) (ramp y) 0ℚ (bump y) 0ℚ
          (ramp-inner y abs-y≤1) (bump-inner y abs-y≤3/16)

   II₁ : 0ℚ + (0ℚ - Z) ＝ - Z
   II₁ = ℚ-zero-left-neutral (0ℚ - Z) ∙ zero-minus Z

   II : ramp y + (bump y - Z) ＝ - Z
   II = II₀ ∙ II₁

   III₀ : f (y + y) ＝ ramp (y + y) + H (den (y + y) ℕ+ den y) (y + y)
   III₀ = f-as (y + y) (den y)

   III₁ : ramp (y + y) + H (den (y + y) ℕ+ den y) (y + y) ＝ 0ℚ + H K (y + y)
   III₁ = ap₂-at (λ (a : ℚ) (n : ℕ) → a + H n (y + y)) (ramp (y + y)) 0ℚ
           (den (y + y) ℕ+ den y) K
           (ramp-inner (y + y) abs-2y≤1)
            (addition-commutativity (den (y + y)) (den y))

   III : f (y + y) ＝ H K (y + y)
   III = III₀ ∙ III₁ ∙ ℚ-zero-left-neutral (H K (y + y))

   III' : - Z ＝ - half (f (y + y))
   III' = ap-at (λ (w : ℚ) → - half w) (f (y + y)) (H K (y + y)) III ⁻¹

 f-is-even : (y : ℚ) → f (- y) ＝ f y
 f-is-even y = I ∙ II ∙ III
  where
   I : f (- y) ＝ ramp (- y) + H (den (- y) ℕ+ den y) (- y)
   I = f-as (- y) (den y)

   H' : H (den (- y) ℕ+ den y) (- y) ＝ H (den y ℕ+ den (- y)) y
   H' = H-is-even (den (- y) ℕ+ den y) y
      ∙ ap-at (λ (n : ℕ) → H n y) (den (- y) ℕ+ den y) (den y ℕ+ den (- y))
         (addition-commutativity (den (- y)) (den y))

   II : ramp (- y) + H (den (- y) ℕ+ den y) (- y) ＝ ramp y
      + H (den y ℕ+ den (- y)) y
   II = ap₂-at _+_ (ramp (- y)) (ramp y) (H (den (- y) ℕ+ den y) (- y))
         (H (den y ℕ+ den (- y)) y)
         (ramp-is-even y) H'

   III : ramp y + H (den y ℕ+ den (- y)) y ＝ f y
   III = f-as y (den (- y)) ⁻¹

 f-at-zero : f 0ℚ ＝ 0ℚ
 f-at-zero = I ∙ zero-plus-zero
  where
   I : ramp 0ℚ + H (den 0ℚ) 0ℚ ＝ 0ℚ + 0ℚ
   I =
    ap₂-at _+_ (ramp 0ℚ) 0ℚ (H (den 0ℚ) 0ℚ) 0ℚ ramp-at-zero (H-at-zero (den 0ℚ))

 f-at-one : f 1ℚ ＝ 0ℚ
 f-at-one = f-top 1ℚ 5/32≤abs1 ∙ ramp-plus-bump-at-one
  where
   5/32≤abs1 : 5/32 ≤ abs 1ℚ
   5/32≤abs1 = 27 , refl

   ramp-plus-bump-at-one : ramp 1ℚ + bump 1ℚ ＝ 0ℚ
   ramp-plus-bump-at-one = refl

\end{code}
