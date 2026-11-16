Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 26 October 2026. See the AI disclosure in
gist.RealCohesion.index.

Elementary rational arithmetic used by the real-analytic modules:
halving, telescoping sums of differences, and absolute values.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.RealCohesion.RationalArithmetic where

open import MLTT.Spartan renaming (_+_ to _∔_)
open import MLTT.Two-Properties using (complement)
open import Integers.Type using (pos)
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Order using (_≤ℕ_ ; ≤-+ ; Order-ℕ-ℕ)
open import Notation.Order
open import UF.Base
open import Rationals.Abs
open import Rationals.Addition
open import Rationals.MinMax
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Type

\end{code}

Halving.

\begin{code}

half : ℚ → ℚ
half d = d * 1/2

halves-add-up : (d : ℚ) → half d + half d ＝ d
halves-add-up d = ℚ-distributivity d 1/2 1/2 ⁻¹
                ∙ ap (d *_) 1/2+1/2
                ∙ ℚ-mult-right-id d

add-two-halves : (x d : ℚ) → x + half d + half d ＝ x + d
add-two-halves x d = ℚ+-assoc x (half d) (half d) ∙ ap (x +_) (halves-add-up d)

half-of-double : (y : ℚ) → half (y + y) ＝ y
half-of-double y = ℚ-distributivity' 1/2 y y ∙ ℚ-into-half y ⁻¹

half-of-difference : (a b : ℚ) → half (a - b) ＝ half a - half b
half-of-difference a b = ℚ-distributivity' 1/2 a (- b)
                       ∙ ap (half a +_) (ℚ-negation-dist-over-mult b 1/2)

half-of-negation : (a : ℚ) → half (- a) ＝ - half a
half-of-negation a = ℚ-negation-dist-over-mult a 1/2

1/2≤2/3 : 1/2 ≤ 2/3
1/2≤2/3 = 1 , refl

1/2≤1 : 1/2 ≤ 1ℚ
1/2≤1 = 1 , refl

0≤1/2 : 0ℚ ≤ 1/2
0≤1/2 = ℚ<-coarser-than-≤ 0ℚ 1/2 0<1/2

two : ℚ
two = toℚ (pos 2 , 0)

two-is-nonneg : 0ℚ ≤ two
two-is-nonneg = ℚ≤-trans 0ℚ 1ℚ two (ℚ<-coarser-than-≤ 0ℚ 1ℚ 0<1)
                 (ℚ≤-addition-preserves-order'' 1ℚ 1ℚ
                   (ℚ<-coarser-than-≤ 0ℚ 1ℚ 0<1))

minus-one-plus-two : -1ℚ + two ＝ 1ℚ
minus-one-plus-two = refl

half-is-nonneg : (d : ℚ) → 0ℚ ≤ d → 0ℚ ≤ half d
half-is-nonneg d l = ℚ≤-pos-multiplication-preserves-order d 1/2 l 0≤1/2

half-is-positive : (d : ℚ) → 0ℚ < d → 0ℚ < half d
half-is-positive = halving-preserves-order

half-is-less : (d : ℚ) → 0ℚ < d → half d < d
half-is-less d l = transport (_< d) (ℚ*-comm 1/2 d) (half-of-pos-is-less d l)

half-is-at-most : (d : ℚ) → 0ℚ ≤ d → half d ≤ d
half-is-at-most d l = transport₂ _≤_ (ℚ*-comm 1/2 d) (ℚ-mult-left-id d)
                       (ℚ≤-pos-multiplication-preserves-order' 1/2 1ℚ d 1/2≤1 l)

half-is-monotone : (a b : ℚ) → a ≤ b → half a ≤ half b
half-is-monotone a b l = ℚ≤-pos-multiplication-preserves-order' a b 1/2 l 0≤1/2

half-is-strictly-monotone : (a b : ℚ) → a < b → half a < half b
half-is-strictly-monotone a b l =
 ℚ<-pos-multiplication-preserves-order' a b 1/2 l 0<1/2

\end{code}

A sequence with R (a n) (a (n + 1)) for every n has R (a m) (a k)
whenever m ≤ k, for a reflexive and transitive relation R.

\begin{code}

monotone-from-steps : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } (R : X → X → 𝓥 ̇ )
                    → ((x : X) → R x x)
                    → ((x y z : X) → R x y → R y z → R x z)
                    → (a : ℕ → X)
                    → ((n : ℕ) → R (a n) (a (succ n)))
                    → (m k : ℕ) → m ≤ℕ k → R (a m) (a k)
monotone-from-steps R r t a s 0        0        _ = r (a 0)
monotone-from-steps R r t a s 0        (succ k) _ =
 t (a 0) (a k) (a (succ k)) (monotone-from-steps R r t a s 0 k ⋆) (s k)
monotone-from-steps R r t a s (succ m) 0        l = 𝟘-elim l
monotone-from-steps R r t a s (succ m) (succ k) l =
 monotone-from-steps R r t (a ∘ succ) (s ∘ succ) m k l

\end{code}

Halving sequences, with x (n + 1) ＝ half (x n): ρ of
gist.RealCohesion.RealLimits, the thresholds and levels of
gist.RealCohesion.DyadicProfile and DyadicLevels, and the lengths of
the intervals of gist.RealCohesion.CrispConnectedness. Their bounds by
powers of 2/3 are in gist.RealCohesion.RationalLimits.

\begin{code}

module halving-sequence
        (x : ℕ → ℚ)
        (x-succ : (n : ℕ) → x (succ n) ＝ half (x n))
       where

 doubled : (n : ℕ) → x (succ n) + x (succ n) ＝ x n
 doubled n = ap (λ w → w + w) (x-succ n) ∙ halves-add-up (x n)

 module nonneg (x-zero-is-nonneg : 0ℚ ≤ x 0) where

  is-nonneg : (n : ℕ) → 0ℚ ≤ x n
  is-nonneg 0        = x-zero-is-nonneg
  is-nonneg (succ n) =
   transport (0ℚ ≤_) (x-succ n ⁻¹) (half-is-nonneg (x n) (is-nonneg n))

  decreases : (n : ℕ) → x (succ n) ≤ x n
  decreases n =
   transport (_≤ x n) (x-succ n ⁻¹) (half-is-at-most (x n) (is-nonneg n))

  antitone : (j k : ℕ) → j ≤ℕ k → x k ≤ x j
  antitone = monotone-from-steps (λ u v → v ≤ u) ℚ≤-refl
              (λ u v w p q → ℚ≤-trans w v u q p) x decreases

  at-most-first : (n : ℕ) → x n ≤ x 0
  at-most-first n = antitone 0 n ⋆

  shift : (m k : ℕ) → x (m +ℕ k) ≤ x m
  shift m k = antitone m (m +ℕ k) (≤-+ m k)

 module positive (x-zero-is-positive : 0ℚ < x 0) where

  open nonneg (ℚ<-coarser-than-≤ 0ℚ (x 0) x-zero-is-positive) public

  is-positive : (n : ℕ) → 0ℚ < x n
  is-positive 0        = x-zero-is-positive
  is-positive (succ n) = transport (0ℚ <_) (x-succ n ⁻¹)
                          (half-is-positive (x n) (is-positive n))

  strictly-decreases : (n : ℕ) → x (succ n) < x n
  strictly-decreases n = transport (_< x n) (x-succ n ⁻¹)
                          (half-is-less (x n) (is-positive n))

halving-sequences-are-ordered : (x y : ℕ → ℚ)
                              → ((n : ℕ) → x (succ n) ＝ half (x n))
                              → ((n : ℕ) → y (succ n) ＝ half (y n))
                              → x 0 < y 0
                              → (n : ℕ) → x n < y n
halving-sequences-are-ordered x y x-succ y-succ l 0        = l
halving-sequences-are-ordered x y x-succ y-succ l (succ n) =
 transport₂ _<_ (x-succ n ⁻¹) (y-succ n ⁻¹)
  (half-is-strictly-monotone (x n) (y n)
    (halving-sequences-are-ordered x y x-succ y-succ l n))

abs-of-half : (v : ℚ) → abs (half v) ＝ half (abs v)
abs-of-half v = abs-mult v 1/2 ⁻¹ ∙ ap (abs v *_) (abs-of-pos-is-pos' 1/2 0<1/2)

\end{code}

Bisection of a rational interval [x , x + d] with d ≥ 0: halve ₀ x d
and halve ₁ x d are the left ends of its lower and its upper half,
each of length half d. Used by gist.RealCohesion.CrispConnectedness
and gist.RealCohesion.CrispBolzanoWeierstrass.

\begin{code}

halve : 𝟚 → ℚ → ℚ → ℚ
halve ₀ x d = x
halve ₁ x d = x + half d

halving-shrinks : (x d : ℚ) → 0ℚ ≤ d → x + half d ≤ x + d
halving-shrinks x d l = transport₂ _≤_ (ℚ+-comm (half d) x) (ℚ+-comm d x)
                         (ℚ≤-addition-preserves-order (half d) d x
                           (half-is-at-most d l))

halve-grows : (b : 𝟚) (x d : ℚ) → 0ℚ ≤ d → x ≤ halve b x d
halve-grows ₀ x d l = ℚ≤-refl x
halve-grows ₁ x d l =
 ℚ≤-addition-preserves-order'' x (half d) (half-is-nonneg d l)

halve-shrinks : (b : 𝟚) (x d : ℚ) → 0ℚ ≤ d → halve b x d + half d ≤ x + d
halve-shrinks ₀ x d l = halving-shrinks x d l
halve-shrinks ₁ x d l =
 transport (_≤ x + d) (add-two-halves x d ⁻¹) (ℚ≤-refl (x + d))

\end{code}

Multiples of a rational unit. They were in gist.RealCohesion.Quantizers,
which re-exports them. They are here, in a module without parameters,
so that gist.RealCohesion.RationalGrid, which defines the grid points
of the cube with them, needs no parameters either: see there.

\begin{code}

abstract
 mult : ℚ → ℕ → ℚ
 mult e 0        = 0ℚ
 mult e (succ n) = mult e n + e

 mult-zero : (e : ℚ) → mult e 0 ＝ 0ℚ
 mult-zero e = refl

 mult-succ : (e : ℚ) (n : ℕ) → mult e (succ n) ＝ mult e n + e
 mult-succ e n = refl

 mult-add : (e : ℚ) (a b : ℕ) → mult e (a +ℕ b) ＝ mult e a + mult e b
 mult-add e a 0        = ℚ-zero-right-neutral (mult e a) ⁻¹
 mult-add e a (succ b) =
  ap (_+ e) (mult-add e a b) ∙ ℚ+-assoc (mult e a) (mult e b) e

 mult-nonneg : (e : ℚ) → 0ℚ ≤ e → (n : ℕ) → 0ℚ ≤ mult e n
 mult-nonneg e l 0        = ℚ≤-refl 0ℚ
 mult-nonneg e l (succ n) = transport (_≤ mult e n + e) (ℚ-zero-left-neutral 0ℚ)
                             (ℚ≤-adding 0ℚ (mult e n) 0ℚ e (mult-nonneg e l n)
                               l)

 mult-mono : (e : ℚ) → 0ℚ ≤ e → (a b : ℕ) → a ≤ b → mult e a ≤ mult e b
 mult-mono e l 0        b        _ = mult-nonneg e l b
 mult-mono e l (succ a) 0        k = 𝟘-elim k
 mult-mono e l (succ a) (succ b) k =
  ℚ≤-addition-preserves-order (mult e a) (mult e b) e
                                      (mult-mono e l a b k)

 mult-one : (e : ℚ) → mult e 1 ＝ e
 mult-one e = ℚ-zero-left-neutral e

 mult-half : (e : ℚ) (a : ℕ) → mult (half e) (a +ℕ a) ＝ mult e a
 mult-half e 0        = refl
 mult-half e (succ a) =
  ap (λ - → mult (half e) - + half e) (succ-left a a)
  ∙ ℚ+-assoc (mult (half e) (a +ℕ a)) (half e) (half e)
  ∙ ap₂ _+_ (mult-half e a) (halves-add-up e)

\end{code}

Decidability of the order.

\begin{code}

ℚ≤-decide : (p q : ℚ) → is-decidable (p ≤ q)
ℚ≤-decide p q = γ (ℚ-dichotomous' q p)
 where
  γ : (q < p) ∔ (p ≤ q) → is-decidable (p ≤ q)
  γ (inl l) = inr (λ m → ℚ<-irrefl q (ℚ<-≤-trans q p q l m))
  γ (inr m) = inl m

\end{code}

Sums and differences.

\begin{code}

add-difference : (p q : ℚ) → p + (q - p) ＝ q
add-difference p q = ap (p +_) (ℚ+-comm q (- p))
                   ∙ ℚ+-assoc p (- p) q ⁻¹
                   ∙ ap (_+ q) (ℚ-inverse-sum-to-zero p)
                   ∙ ℚ-zero-left-neutral q

minus-zero : (p : ℚ) → p - 0ℚ ＝ p
minus-zero p = ap (p +_) (ℚ-minus-zero-is-zero ⁻¹) ∙ ℚ-zero-right-neutral p

zero-minus : (p : ℚ) → 0ℚ - p ＝ - p
zero-minus p = ℚ-zero-left-neutral (- p)

telescope : (p q r : ℚ) → (q - p) + (r - q) ＝ r - p
telescope p q r = ℚ+-comm (q - p) (r - q)
                ∙ ℚ+-assoc r (- q) (q - p)
                ∙ ap (r +_) (ℚ+-assoc (- q) q (- p) ⁻¹
                             ∙ ap (_+ (- p)) (ℚ-inverse-sum-to-zero' q)
                             ∙ ℚ-zero-left-neutral (- p))

difference-of-translates : (a b c : ℚ) → (a + c) - (b + c) ＝ a - b
difference-of-translates a b c =
   ap ((a + c) +_) (ℚ-minus-dist b c ⁻¹)
 ∙ ℚ+-assoc a c ((- b) + (- c))
 ∙ ap (a +_) (ℚ+-assoc c (- b) (- c) ⁻¹
              ∙ ap (_+ (- c)) (ℚ+-comm c (- b))
              ∙ ℚ+-assoc (- b) c (- c)
              ∙ ap ((- b) +_) (ℚ-inverse-sum-to-zero c)
              ∙ ℚ-zero-right-neutral (- b))

difference-of-negations : (a b : ℚ) → (- a) - (- b) ＝ - (a - b)
difference-of-negations a b = ℚ-minus-dist a (- b)

difference-of-reflections : (c a b : ℚ) → (c - a) - (c - b) ＝ b - a
difference-of-reflections c a b =
   ap (_- (c - b)) (ℚ+-comm c (- a))
 ∙ ap (((- a) + c) +_) (ℚ-minus-dist c (- b) ⁻¹)
 ∙ ℚ+-assoc (- a) c ((- c) + (- (- b)))
 ∙ ap ((- a) +_) (ℚ+-assoc c (- c) (- (- b)) ⁻¹
                  ∙ ap (_+ (- (- b))) (ℚ-inverse-sum-to-zero c)
                  ∙ ℚ-zero-left-neutral (- (- b))
                  ∙ ℚ-minus-minus b ⁻¹)
 ∙ ℚ+-comm (- a) b

\end{code}

The nonnegative part of a rational number.

\begin{code}

nonneg-part : ℚ → ℚ
nonneg-part d = max 0ℚ d

nonneg-part-is-nonneg : (d : ℚ) → 0ℚ ≤ nonneg-part d
nonneg-part-is-nonneg d = max≤ 0ℚ d

nonneg-part-of-nonneg : (d : ℚ) → 0ℚ ≤ d → nonneg-part d ＝ d
nonneg-part-of-nonneg d l = ≤-to-max 0ℚ d l ⁻¹

nonneg-part-of-nonpos : (d : ℚ) → d ≤ 0ℚ → nonneg-part d ＝ 0ℚ
nonneg-part-of-nonpos d l = max-comm 0ℚ d ∙ ≤-to-max d 0ℚ l ⁻¹

nonneg-part-of-positive : (d : ℚ) → 0ℚ < d → nonneg-part d ＝ d
nonneg-part-of-positive d l = nonneg-part-of-nonneg d (ℚ<-coarser-than-≤ 0ℚ d l)

\end{code}

Moving a summand across an inequality.

\begin{code}

sum-minus-first : (a b : ℚ) → (a + b) - a ＝ b
sum-minus-first a b = ap (_- a) (ℚ+-comm a b) ∙ ℚ-inverse-intro'' b a ⁻¹

plus-minus : (p ε : ℚ) → (p + ε) - ε ＝ p
plus-minus p ε = ℚ-inverse-intro'' p ε ⁻¹

minus-plus : (p ε : ℚ) → (p - ε) + ε ＝ p
minus-plus p ε = ℚ-inverse-intro'''' p ε ⁻¹

neg-is-negative : (r : ℚ) → 0ℚ < r → - r < 0ℚ
neg-is-negative r l =
 transport (- r <_) (ℚ-minus-zero-is-zero ⁻¹) (ℚ<-swap 0ℚ r l)

<-sub-right : (u v w : ℚ) → u + w < v → u < v - w
<-sub-right u v w = ℚ<-subtraction-preserves-order''' u w v

<-add-right : (u v w : ℚ) → u < v - w → u + w < v
<-add-right = ℚ<-subtraction-preserves-order''

≤-sub-right : (u v w : ℚ) → u + w ≤ v → u ≤ v - w
≤-sub-right u v w l = transport (_≤ v - w) (ℚ-inverse-intro'' u w ⁻¹)
                       (ℚ≤-addition-preserves-order (u + w) v (- w) l)

≤-add-right : (u v w : ℚ) → u ≤ v - w → u + w ≤ v
≤-add-right u v w l = transport (u + w ≤_) (ℚ-inverse-intro'''' v w ⁻¹)
                       (ℚ≤-addition-preserves-order u (v - w) w l)

<-move-left : (u v w : ℚ) → u < v + w → u - w < v
<-move-left u v w l = transport (u - w <_) (ℚ-inverse-intro'' v w ⁻¹)
                       (ℚ<-addition-preserves-order u (v + w) (- w) l)

<-move-right : (u v w : ℚ) → u - w < v → u < v + w
<-move-right u v w l = transport (_< v + w) (ℚ-inverse-intro'''' u w ⁻¹)
                        (ℚ<-addition-preserves-order (u - w) v w l)

ball-gives-abs : (x x₀ ε : ℚ) → x₀ - ε < x → x < x₀ + ε → abs (x - x₀) < ε
ball-gives-abs x x₀ ε a b = ℚ<-to-abs (x - x₀) ε (I , II)
 where
  I : - ε < x - x₀
  I = transport (_< x - x₀) (sum-minus-first x₀ (- ε))
       (ℚ<-addition-preserves-order (x₀ - ε) x (- x₀) a)

  II : x - x₀ < ε
  II = transport (x - x₀ <_) (sum-minus-first x₀ ε)
        (ℚ<-addition-preserves-order x (x₀ + ε) (- x₀) b)

abs-gives-ball : (y y₀ ε : ℚ) → abs (y - y₀) < ε → (y₀ - ε < y) × (y < y₀ + ε)
abs-gives-ball y y₀ ε l = I , II
 where
  bounds : (- ε < y - y₀) × (y - y₀ < ε)
  bounds = ℚ-abs-<-unpack (y - y₀) ε l

  I : y₀ - ε < y
  I = transport₂ _<_ (ℚ+-comm (- ε) y₀) (ℚ-inverse-intro'''' y y₀ ⁻¹)
       (ℚ<-addition-preserves-order (- ε) (y - y₀) y₀ (pr₁ bounds))

  II : y < y₀ + ε
  II = transport₂ _<_ (ℚ-inverse-intro'''' y y₀ ⁻¹) (ℚ+-comm ε y₀)
        (ℚ<-addition-preserves-order (y - y₀) ε y₀ (pr₂ bounds))

min-is-positive : (p q : ℚ) → 0ℚ < p → 0ℚ < q → 0ℚ < min p q
min-is-positive p q l m = γ (decide-min p q)
 where
  γ : (min p q ＝ p) ∔ (min p q ＝ q) → 0ℚ < min p q
  γ (inl e) = transport (0ℚ <_) (e ⁻¹) l
  γ (inr e) = transport (0ℚ <_) (e ⁻¹) m

\end{code}

Signed values: signed ₁ v is v and signed ₀ v is - v.

\begin{code}

opposite : 𝟚 → 𝟚
opposite = complement

signed : 𝟚 → ℚ → ℚ
signed ₀ v = - v
signed ₁ v = v

signed-involutive : (σ : 𝟚) (v : ℚ) → signed σ (signed σ v) ＝ v
signed-involutive ₀ v = ℚ-minus-minus v ⁻¹
signed-involutive ₁ v = refl

\end{code}

Negated halves of signed values.

\begin{code}

negated-half-of-signed : (σ : 𝟚) (v : ℚ)
                       → - half (signed σ v) ＝ signed (opposite σ) (half v)
negated-half-of-signed ₀ v =
 ap -_ (half-of-negation v) ∙ ℚ-minus-minus (half v) ⁻¹
negated-half-of-signed ₁ v = refl

half-of-difference-of-double : (y c : ℚ) → half ((y + y) - c) ＝ y - half c
half-of-difference-of-double y c =
 half-of-difference (y + y) c ∙ ap (_- half c) (half-of-double y)

half-of-difference-from-double : (c y : ℚ) → half (c - (y + y)) ＝ half c - y
half-of-difference-from-double c y = half-of-difference c (y + y)
                                   ∙ ap (λ w → half c - w) (half-of-double y)

\end{code}

Congruence and transport with explicit endpoints. When the endpoints of
an identification are left implicit, Agda may try to infer them by
unifying arithmetic expressions with metavariables, which unfolds the
arithmetic of the rationals and can exhaust memory; we use these
versions in arithmetic-heavy proofs.

\begin{code}

ap-at : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (x x' : X) → x ＝ x'
      → f x ＝ f x'
ap-at f x x' = ap f

ap₂-at : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z)
         (x x' : X) (y y' : Y) → x ＝ x' → y ＝ y' → f x y ＝ f x' y'
ap₂-at f x x' y y' = ap₂ f

transport-at : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x x' : X) → x ＝ x'
             → A x → A x'
transport-at A x x' = transport A

transport₂-at : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X → Y → 𝓦 ̇ )
                (x x' : X) (y y' : Y) → x ＝ x' → y ＝ y' → A x y → A x' y'
transport₂-at A x x' y y' = transport₂ A

\end{code}

The difference of the ends of an interval widened by d at both ends. It
was in gist.RealCohesion.CrispUniformContinuityOnBoxes, which
re-exports it.

\begin{code}

widened-difference : (x y d : ℚ) → (y + d) - (x - d) ＝ (y - x) + (d + d)
widened-difference x y d =
 (y + d) - (x - d)       ＝⟨ ap ((y + d) +_) I ⟩
 (y + d) + ((- x) + d)   ＝⟨ ℚ+-assoc y d ((- x) + d) ⟩
 y + (d + ((- x) + d))   ＝⟨ ap (y +_) II ⟩
 y + ((- x) + (d + d))   ＝⟨ ℚ+-assoc y (- x) (d + d) ⁻¹ ⟩
 (y - x) + (d + d)       ∎
 where
  I : - (x - d) ＝ (- x) + d
  I = ℚ-minus-dist' x d ∙ ℚ+-comm d (- x)

  II : d + ((- x) + d) ＝ (- x) + (d + d)
  II = ℚ+-assoc d (- x) d ⁻¹ ∙ ap (_+ d) (ℚ+-comm d (- x)) ∙ ℚ+-assoc (- x) d d

\end{code}
