Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 26 October 2026. See the AI disclosure in
gist.RealCohesion.index.

The shape of the dyadic profile f of gist.RealCohesion.DyadicProfile,
level by level.

Level k consists of the plateau [threshold k , hi k], which is
[5 · 2⁻ᵏ⁻⁵ , 3 · 2⁻ᵏ⁻⁴], and the bump of level k, which rises from hi k
to its centre cen k = 2⁻ᵏ⁻² and falls to 2 · threshold k, the left end
of the plateau of level k - 1. The bump has the sign sgn k = (-1)ᵏ. We
prove, for rationals, that f is 0 on the plateaux and linear with slope
±1 on the halves of the bumps, by induction on k from the
self-similarity f y = - f (2 y) / 2, and the corresponding facts on the
negative side from f (- y) = f y. The outer plateau is [5/16 , 1],
followed by the ramp f y = y - 1.

As in gist.RealCohesion.DyadicProfile, the level constants are abstract,
and identifications in rational arithmetic are given with explicit
endpoints.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.DyadicLevels
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Integers.Type hiding (abs)
open import Notation.Order
open import UF.Base
open import Rationals.Abs
open import Rationals.Addition
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Type
open import gist.RealCohesion.DyadicProfile fe pe pt
open import gist.RealCohesion.RationalArithmetic

\end{code}

The levels.

\begin{code}

abstract
 hi cen : ℕ → ℚ
 hi 0        = 3/16
 hi (succ k) = half (hi k)

 cen 0        = 1/4
 cen (succ k) = half (cen k)

 hi-zero : hi 0 ＝ 3/16
 hi-zero = refl

 hi-succ : (k : ℕ) → hi (succ k) ＝ half (hi k)
 hi-succ k = refl

 cen-zero : cen 0 ＝ 1/4
 cen-zero = refl

 cen-succ : (k : ℕ) → cen (succ k) ＝ half (cen k)
 cen-succ k = refl

sgn : ℕ → 𝟚
sgn 0        = ₁
sgn (succ k) = opposite (sgn k)

\end{code}

hi and cen are halving sequences, so their lemmas are instances of
halving-sequence (gist.RealCohesion.RationalArithmetic), and they are
ordered with the thresholds by halving-sequences-are-ordered.

\begin{code}

private
 module hi-sequence =
  halving-sequence.positive hi hi-succ
   (transport-at (λ (w : ℚ) → 0ℚ < w) 3/16 (hi 0) (hi-zero ⁻¹) (2 , refl))

 module cen-sequence =
  halving-sequence.positive cen cen-succ
   (transport-at (λ (w : ℚ) → 0ℚ < w) 1/4 (cen 0) (cen-zero ⁻¹) (0 , refl))

open halving-sequence hi hi-succ using () renaming (doubled to hi-doubled)
 public
open halving-sequence cen cen-succ using () renaming (doubled to cen-doubled)
 public
open hi-sequence
 using () renaming (is-positive to hi-is-positive ; decreases to hi-decreases)
  public
open cen-sequence
 using () renaming (is-positive to cen-is-positive ; decreases to cen-decreases)
  public

threshold<hi : (k : ℕ) → threshold k < hi k
threshold<hi = halving-sequences-are-ordered threshold hi threshold-succ hi-succ
                (transport₂-at _<_ 5/32 (threshold 0) 3/16 (hi 0)
                  (threshold-zero ⁻¹) (hi-zero ⁻¹) (15 , refl))

hi<cen : (k : ℕ) → hi k < cen k
hi<cen = halving-sequences-are-ordered hi cen hi-succ cen-succ
          (transport₂-at _<_ 3/16 (hi 0) 1/4 (cen 0) (hi-zero ⁻¹) (cen-zero ⁻¹)
            (3 , refl))

cen-succ<threshold : (k : ℕ) → cen (succ k) < threshold k
cen-succ<threshold =
 halving-sequences-are-ordered (cen ∘ succ) threshold (cen-succ ∘ succ)
  threshold-succ
  (transport₂-at _<_ (half 1/4) (cen 1) 5/32 (threshold 0)
    (ap-at half 1/4 (cen 0) (cen-zero ⁻¹) ∙ cen-succ 0 ⁻¹)
    (threshold-zero ⁻¹) (7 , refl))

threshold≤hi : (k : ℕ) → threshold k ≤ hi k
threshold≤hi k = ℚ<-coarser-than-≤ (threshold k) (hi k) (threshold<hi k)

cen-succ≤threshold : (k : ℕ) → cen (succ k) ≤ threshold k
cen-succ≤threshold k =
 ℚ<-coarser-than-≤ (cen (succ k)) (threshold k) (cen-succ<threshold k)

hi-succ≤5/32 : (k : ℕ) → hi (succ k) ≤ 5/32
hi-succ≤5/32 0        = transport-at (λ (w : ℚ) → w ≤ 5/32) (half 3/16) (hi 1)
                         (ap-at half 3/16 (hi 0) (hi-zero ⁻¹) ∙ hi-succ 0 ⁻¹)
                          (64 , refl)
hi-succ≤5/32 (succ k) = ℚ≤-trans (hi (succ (succ k))) (hi (succ k)) 5/32
                         (hi-decreases (succ k)) (hi-succ≤5/32 k)

cen-succ≤5/32 : (k : ℕ) → cen (succ k) ≤ 5/32
cen-succ≤5/32 k =
 ℚ≤-trans (cen (succ k)) (threshold k) 5/32 (cen-succ≤threshold k)
                   (threshold-at-most-first k)

\end{code}

Order facts.

\begin{code}

private
 double-≤ : (a y : ℚ) → a ≤ y → a + a ≤ y + y
 double-≤ a y l = ℚ≤-adding a y a y l l

 nonneg-from : (a y : ℚ) → 0ℚ < a → a ≤ y → 0ℚ ≤ y
 nonneg-from a y l m = ℚ≤-trans 0ℚ a y (ℚ<-coarser-than-≤ 0ℚ a l) m

 small-abs : (a y b : ℚ) → 0ℚ < a → a ≤ y → y ≤ b → b ≤ 5/32 → abs y ≤ 5/32
 small-abs a y b l m n o = transport-at (λ (w : ℚ) → w ≤ 5/32) y (abs y)
                            (abs-of-pos-is-pos y (nonneg-from a y l m) ⁻¹)
                            (ℚ≤-trans y b 5/32 n o)

 abs-of-large : (y : ℚ) → 5/32 ≤ y → abs y ＝ y
 abs-of-large y l = abs-of-pos-is-pos y (nonneg-from 5/32 y (4 , refl) l)

 large-abs : (y : ℚ) → 5/32 ≤ y → 5/32 ≤ abs y
 large-abs y l =
  transport-at (λ (w : ℚ) → 5/32 ≤ w) y (abs y) (abs-of-large y l ⁻¹) l

\end{code}

The top level, from f y ＝ ramp y + bump y for |y| ≥ 5/32.

\begin{code}

top-formula : (y : ℚ) → 5/32 ≤ y → y ≤ 1ℚ → f y ＝ bump y
top-formula y l l' = f-top y (large-abs y l)
                   ∙ ap-at (λ (w : ℚ) → w + bump y) (ramp y) 0ℚ (ramp-inner y X)
                   ∙ ℚ-zero-left-neutral (bump y)
 where
  X : abs y ≤ 1ℚ
  X = transport-at (λ (w : ℚ) → w ≤ 1ℚ) y (abs y) (abs-of-large y l ⁻¹) l'

flat-0 : (y : ℚ) → threshold 0 ≤ y → y ≤ hi 0 → f y ＝ 0ℚ
flat-0 y l l' = top-formula y l₀ (ℚ≤-trans y 3/16 1ℚ l₀' (13 , refl))
              ∙ bump-inner y (transport-at (λ (w : ℚ) → w ≤ 3/16) y (abs y)
                               (abs-of-large y l₀ ⁻¹) l₀')
 where
  l₀ : 5/32 ≤ y
  l₀ = transport-at (λ (w : ℚ) → w ≤ y) (threshold 0) 5/32 threshold-zero l

  l₀' : y ≤ 3/16
  l₀' = transport-at (λ (w : ℚ) → y ≤ w) (hi 0) 3/16 hi-zero l'

rising-0 : (y : ℚ) → hi 0 ≤ y → y ≤ cen 0 → f y ＝ signed (sgn 0) (y - hi 0)
rising-0 y l l' = top-formula y l₁ (ℚ≤-trans y 1/4 1ℚ l₀' (3 , refl))
                ∙ bump-rising y
                   (transport-at (λ (w : ℚ) → 3/16 ≤ w) y (abs y) (I ⁻¹) l₀)
                                (transport-at (λ (w : ℚ) → w ≤ 1/4) y (abs y)
                                  (I ⁻¹) l₀')
                ∙ ap-at (λ (w : ℚ) → w - 3/16) (abs y) y I
                ∙ ap-at (λ (w : ℚ) → y - w) 3/16 (hi 0) (hi-zero ⁻¹)
 where
  l₀ : 3/16 ≤ y
  l₀ = transport-at (λ (w : ℚ) → w ≤ y) (hi 0) 3/16 hi-zero l

  l₀' : y ≤ 1/4
  l₀' = transport-at (λ (w : ℚ) → y ≤ w) (cen 0) 1/4 cen-zero l'

  l₁ : 5/32 ≤ y
  l₁ = ℚ≤-trans 5/32 3/16 y 5/32≤3/16 l₀

  I : abs y ＝ y
  I = abs-of-large y l₁

double-threshold-0 : threshold 0 + threshold 0 ＝ 5/16
double-threshold-0 =
 ap₂-at _+_ (threshold 0) 5/32 (threshold 0) 5/32 threshold-zero threshold-zero
                   ∙ 5/32+5/32

bump-falls-0 : (y : ℚ) → cen 0 ≤ y → y ≤ threshold 0 + threshold 0
             → f y ＝ signed (sgn 0) ((threshold 0 + threshold 0) - y)
bump-falls-0 y l l' = top-formula y l₁ (ℚ≤-trans y 5/16 1ℚ l₀' 5/16≤1)
                    ∙ bump-falling y
                       (transport-at (λ (w : ℚ) → 1/4 ≤ w) y (abs y) (I ⁻¹) l₀)
                                     (transport-at (λ (w : ℚ) → w ≤ 5/16) y
                                       (abs y) (I ⁻¹) l₀')
                    ∙ ap-at (λ (w : ℚ) → 5/16 - w) (abs y) y I
                    ∙ ap-at (λ (w : ℚ) → w - y) 5/16 (threshold 0 + threshold 0)
                       (double-threshold-0 ⁻¹)
 where
  l₀ : 1/4 ≤ y
  l₀ = transport-at (λ (w : ℚ) → w ≤ y) (cen 0) 1/4 cen-zero l

  l₀' : y ≤ 5/16
  l₀' = transport-at (λ (w : ℚ) → y ≤ w) (threshold 0 + threshold 0) 5/16
         double-threshold-0 l'

  l₁ : 5/32 ≤ y
  l₁ = ℚ≤-trans 5/32 1/4 y (ℚ≤-trans 5/32 3/16 1/4 5/32≤3/16 3/16≤1/4) l₀

  I : abs y ＝ y
  I = abs-of-large y l₁

outer-flat : (y : ℚ) → 5/16 ≤ y → y ≤ 1ℚ → f y ＝ 0ℚ
outer-flat y l l' = top-formula y l₁ l'
                  ∙ bump-outer y (transport-at (λ (w : ℚ) → 5/16 ≤ w) y (abs y)
                                   (abs-of-large y l₁ ⁻¹) l)
 where
  l₁ : 5/32 ≤ y
  l₁ = ℚ≤-trans 5/32 5/16 y (80 , refl) l

outer-ramp : (y : ℚ) → 1ℚ ≤ y → f y ＝ signed ₁ (y - 1ℚ)
outer-ramp y l = f-top y (large-abs y l₁)
               ∙ ap₂-at _+_ (ramp y) (y - 1ℚ) (bump y) 0ℚ
                  (ramp-outer y
                    (transport-at (λ (w : ℚ) → 1ℚ ≤ w) y (abs y) (I ⁻¹) l)
                   ∙ ap-at (λ (w : ℚ) → w - 1ℚ) (abs y) y I)
                  (bump-outer y
                    (transport-at (λ (w : ℚ) → 5/16 ≤ w) y (abs y) (I ⁻¹)
                      (ℚ≤-trans 5/16 1ℚ y 5/16≤1 l)))
               ∙ ℚ-zero-right-neutral (y - 1ℚ)
 where
  l₁ : 5/32 ≤ y
  l₁ = ℚ≤-trans 5/32 1ℚ y 5/32≤1 l

  I : abs y ＝ y
  I = abs-of-large y l₁

\end{code}

All levels, by induction. The induction step is the same for the three
kinds of piece: for y in [lo' , hi'], with lo' positive and hi' at most
5/32, the self-similarity of f gives f y from f (y + y), and y + y lies
in [lo' + lo' , hi' + hi'].

\begin{code}

private
 step : (y v lo hi lo' hi' : ℚ)
      → lo' + lo' ＝ lo → hi' + hi' ＝ hi
      → 0ℚ < lo' → hi' ≤ 5/32
      → lo' ≤ y → y ≤ hi'
      → (lo ≤ y + y → y + y ≤ hi → f (y + y) ＝ v)
      → f y ＝ - half v
 step y v lo hi lo' hi' e e' p b l l' g =
    f-self-similar y (small-abs lo' y hi' p l l' b)
  ∙ ap-at (λ (w : ℚ) → - half w) (f (y + y)) v
     (g (transport-at (λ (w : ℚ) → w ≤ y + y) (lo' + lo') lo e
          (double-≤ lo' y l))
        (transport-at (λ (w : ℚ) → y + y ≤ w) (hi' + hi') hi e'
          (double-≤ y hi' l')))

flat : (k : ℕ) (y : ℚ) → threshold k ≤ y → y ≤ hi k → f y ＝ 0ℚ
flat 0        y l l' = flat-0 y l l'
flat (succ k) y l l' =
   step y 0ℚ (threshold k) (hi k) (threshold (succ k)) (hi (succ k))
    (threshold-doubled k) (hi-doubled k) (threshold-is-positive (succ k))
     (hi-succ≤5/32 k)
    l l' (flat k (y + y))
 ∙ negated-half-of-zero

rising : (k : ℕ) (y : ℚ) → hi k ≤ y → y ≤ cen k
       → f y ＝ signed (sgn k) (y - hi k)
rising 0        y l l' = rising-0 y l l'
rising (succ k) y l l' =
   step y (signed (sgn k) ((y + y) - hi k)) (hi k) (cen k) (hi (succ k))
    (cen (succ k))
    (hi-doubled k) (cen-doubled k) (hi-is-positive (succ k)) (cen-succ≤5/32 k)
    l l' (rising k (y + y))
 ∙ negated-half-of-signed (sgn k) ((y + y) - hi k)
 ∙ ap-at (signed (sgn (succ k))) (half ((y + y) - hi k)) (y - hi (succ k)) D
 where
  D : half ((y + y) - hi k) ＝ y - hi (succ k)
  D = half-of-difference-of-double y (hi k)
    ∙ ap-at (λ (w : ℚ) → y - w) (half (hi k)) (hi (succ k)) (hi-succ k ⁻¹)

bump-falls : (k : ℕ) (z : ℚ) → cen k ≤ z → z ≤ threshold k + threshold k
           → f z ＝ signed (sgn k) ((threshold k + threshold k) - z)

falling : (k : ℕ) (y : ℚ) → cen (succ k) ≤ y → y ≤ threshold k
        → f y ＝ signed (sgn (succ k)) (threshold k - y)

bump-falls 0        z m m' = bump-falls-0 z m m'
bump-falls (succ k) z m m' =
   falling k z m
    (transport-at (λ (w : ℚ) → z ≤ w) (threshold (succ k) + threshold (succ k))
      (threshold k) (threshold-doubled k) m')
 ∙ ap-at (λ (w : ℚ) → signed (sgn (succ k)) (w - z)) (threshold k)
    (threshold (succ k) + threshold (succ k)) (threshold-doubled k ⁻¹)

falling k y l l' =
   step y (signed (sgn k) ((threshold k + threshold k) - (y + y)))
    (cen k) (threshold k + threshold k) (cen (succ k)) (threshold k)
    (cen-doubled k) refl (cen-is-positive (succ k)) (threshold-at-most-first k)
    l l' (bump-falls k (y + y))
 ∙ negated-half-of-signed (sgn k) ((threshold k + threshold k) - (y + y))
 ∙ ap-at (signed (sgn (succ k))) (half ((threshold k + threshold k) - (y + y)))
    (threshold k - y) D
 where
  D : half ((threshold k + threshold k) - (y + y)) ＝ threshold k - y
  D = half-of-difference-from-double (threshold k + threshold k) y
    ∙ ap-at (λ (w : ℚ) → w - y) (half (threshold k + threshold k)) (threshold k)
       (half-of-double (threshold k))

\end{code}

The negative side, from f (- y) ＝ f y.

\begin{code}

private
 mirror : (a b y : ℚ) → - b ≤ y → y ≤ - a → (a ≤ - y) × (- y ≤ b)
 mirror a b y l l' =
  transport-at (λ (w : ℚ) → w ≤ - y) (- (- a)) a (ℚ-minus-minus a ⁻¹)
                      (ℚ≤-swap y (- a) l') ,
                     transport-at (λ (w : ℚ) → - y ≤ w) (- (- b)) b
                      (ℚ-minus-minus b ⁻¹)
                      (ℚ≤-swap (- b) y l)

 even : (y : ℚ) → f y ＝ f (- y)
 even y =
  transport-at (λ (w : ℚ) → f w ＝ f (- y)) (- (- y)) y (ℚ-minus-minus y ⁻¹)
           (f-is-even (- y))

 swap-difference : (a y : ℚ) → (- y) - a ＝ (- a) - y
 swap-difference a y = ℚ+-comm (- y) (- a)

 cross-difference : (a y : ℚ) → a - (- y) ＝ y - (- a)
 cross-difference a y =
  ap-at (λ (w : ℚ) → a + w) (- (- y)) y (ℚ-minus-minus y ⁻¹)
                      ∙ ℚ+-comm a y
                      ∙ ap-at (λ (w : ℚ) → y + w) a (- (- a)) (ℚ-minus-minus a)

flat⁻ : (k : ℕ) (y : ℚ) → - hi k ≤ y → y ≤ - threshold k → f y ＝ 0ℚ
flat⁻ k y l l' =
 even y ∙ flat k (- y) (pr₁ (mirror (threshold k) (hi k) y l l'))
                                       (pr₂
                                         (mirror (threshold k) (hi k) y l l'))

rising⁻ : (k : ℕ) (y : ℚ) → - cen k ≤ y → y ≤ - hi k
        → f y ＝ signed (sgn k) ((- hi k) - y)
rising⁻ k y l l' = even y
                 ∙ rising k (- y) (pr₁ (mirror (hi k) (cen k) y l l'))
                                  (pr₂ (mirror (hi k) (cen k) y l l'))
                 ∙ ap-at (signed (sgn k)) ((- y) - hi k) ((- hi k) - y)
                    (swap-difference (hi k) y)

falling⁻ : (k : ℕ) (y : ℚ) → - threshold k ≤ y → y ≤ - cen (succ k)
         → f y ＝ signed (sgn (succ k)) (y - (- threshold k))
falling⁻ k y l l' = even y
                  ∙ falling k (- y)
                     (pr₁ (mirror (cen (succ k)) (threshold k) y l l'))
                                    (pr₂ (mirror (cen (succ k)) (threshold k) y
                                           l l'))
                  ∙ ap-at (signed (sgn (succ k))) (threshold k - (- y))
                     (y - (- threshold k))
                     (cross-difference (threshold k) y)

bump-falls⁻ : (k : ℕ) (y : ℚ) → - (threshold k + threshold k) ≤ y → y ≤ - cen k
            → f y ＝ signed (sgn k) (y - (- (threshold k + threshold k)))
bump-falls⁻ k y l l' = even y
                     ∙ bump-falls k (- y)
                     (pr₁ (mirror (cen k) (threshold k + threshold k) y l l'))
                                          (pr₂ (mirror (cen k)
                                            (threshold k + threshold k) y l l'))
                     ∙ ap-at (signed (sgn k))
                        ((threshold k + threshold k) - (- y))
                        (y - (- (threshold k + threshold k)))
                        (cross-difference (threshold k + threshold k) y)

outer-flat⁻ : (y : ℚ) → - 1ℚ ≤ y → y ≤ - 5/16 → f y ＝ 0ℚ
outer-flat⁻ y l l' = even y ∙ outer-flat (- y) (pr₁ (mirror 5/16 1ℚ y l l'))
                                               (pr₂ (mirror 5/16 1ℚ y l l'))

outer-ramp⁻ : (y : ℚ) → y ≤ - 1ℚ → f y ＝ signed ₁ ((- 1ℚ) - y)
outer-ramp⁻ y l = even y
                ∙ outer-ramp (- y)
                   (transport-at (λ (w : ℚ) → w ≤ - y) (- (- 1ℚ)) 1ℚ
                     (ℚ-minus-minus 1ℚ ⁻¹) (ℚ≤-swap y (- 1ℚ) l))
                ∙ swap-difference 1ℚ y

\end{code}
