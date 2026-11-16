Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Vectors of rationals: sums, inner products and squared norms, and the
nonexpansiveness of the retraction x ↦ x / max(1 , ‖x‖²) onto the ball,
in squared form (gate G14, step E3).

The proof of nonexpansiveness is the one of Codex's audit of
12 November 2026 (part D), for rationals, whose order is decidable.
With s = ‖x‖², t = ‖y‖², c = ⟨x , y⟩ and d = ‖x - y‖² = s + t - 2c:

 * if s ≤ 1 and t ≤ 1, the retraction fixes x and y;

 * if 1 ≤ s and 1 ≤ t, the squared distance of the images is
   d / (s t) ≤ d;

 * if s ≤ 1 ≤ t, d minus the squared distance of the images is
   (t - 1) (1 / t) (t + 1 - 2c), and t + 1 - 2c = d + 1 - s ≥ 0;

 * the last case is symmetric.

The module has no parameters, so that Agda does not unfold the
arithmetic of its closed terms where it is used.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.RealCohesion.RationalVectors where

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.Order
open import UF.Base
open import Fin.Type
open import Rationals.Type
open import Rationals.Addition
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order
open import gist.RealCohesion.RationalProducts
 using (rational-squares-are-nonneg ; reciprocal ; max-one ; max-one-≥-one ;
        reciprocal-times-max-one ; reciprocal-of-at-most-one ;
         reciprocal-≤-one ;
        reciprocal-is-nonneg ; left-multiplication-preserves-≤ ;
         reciprocal-times-self ;
        reciprocal-is-positive)
open import gist.RealCohesion.RationalArithmetic using (minus-plus)

\end{code}

Sums, inner products and squared norms.

\begin{code}

vsum : {n : ℕ} → (Fin n → ℚ) → ℚ
vsum {0}      v = 0ℚ
vsum {succ n} v = v 𝟎 + vsum (v ∘ suc)

inner : {n : ℕ} → (Fin n → ℚ) → (Fin n → ℚ) → ℚ
inner x y = vsum (λ i → x i * y i)

norm² : {n : ℕ} → (Fin n → ℚ) → ℚ
norm² x = inner x x

vsum-ext : {n : ℕ} (u v : Fin n → ℚ) → ((i : Fin n) → u i ＝ v i)
         → vsum u ＝ vsum v
vsum-ext {0}      u v e = refl
vsum-ext {succ n} u v e = ap₂ _+_ (e 𝟎) (vsum-ext (u ∘ suc) (v ∘ suc) (e ∘ suc))

four-rearrange : (a b c d : ℚ) → (a + b) + (c + d) ＝ (a + c) + (b + d)
four-rearrange a b c d =
 (a + b) + (c + d) ＝⟨ ℚ+-assoc a b (c + d) ⟩
 a + (b + (c + d)) ＝⟨ ap (a +_) (ℚ+-assoc b c d ⁻¹) ⟩
 a + ((b + c) + d) ＝⟨ ap (λ z → a + (z + d)) (ℚ+-comm b c) ⟩
 a + ((c + b) + d) ＝⟨ ap (a +_) (ℚ+-assoc c b d) ⟩
 a + (c + (b + d)) ＝⟨ ℚ+-assoc a c (b + d) ⁻¹ ⟩
 (a + c) + (b + d) ∎

vsum-add : {n : ℕ} (u v : Fin n → ℚ) → vsum (λ i → u i + v i) ＝ vsum u + vsum v
vsum-add {0}      u v = ℚ-zero-left-neutral 0ℚ ⁻¹
vsum-add {succ n} u v =
 ap ((u 𝟎 + v 𝟎) +_) (vsum-add (u ∘ suc) (v ∘ suc))
 ∙ four-rearrange (u 𝟎) (v 𝟎) (vsum (u ∘ suc)) (vsum (v ∘ suc))

vsum-scale : {n : ℕ} (a : ℚ) (v : Fin n → ℚ) → vsum (λ i → a * v i) ＝ a * vsum v
vsum-scale {0}      a v = ℚ-zero-right-is-zero a ⁻¹
vsum-scale {succ n} a v =
 ap (a * v 𝟎 +_) (vsum-scale a (v ∘ suc))
 ∙ ℚ-distributivity a (v 𝟎) (vsum (v ∘ suc)) ⁻¹

vsum-neg : {n : ℕ} (v : Fin n → ℚ) → vsum (λ i → - v i) ＝ - vsum v
vsum-neg {0}      v = ℚ-minus-zero-is-zero
vsum-neg {succ n} v =
 ap ((- v 𝟎) +_) (vsum-neg (v ∘ suc)) ∙ ℚ-minus-dist (v 𝟎) (vsum (v ∘ suc))

vsum-sub : {n : ℕ} (u v : Fin n → ℚ) → vsum (λ i → u i - v i) ＝ vsum u - vsum v
vsum-sub u v = vsum-add u (λ i → - v i) ∙ ap (vsum u +_) (vsum-neg v)

vsum-is-nonneg : {n : ℕ} (v : Fin n → ℚ) → ((i : Fin n) → 0ℚ ≤ v i)
               → 0ℚ ≤ vsum v
vsum-is-nonneg {0}      v h = ℚ≤-refl 0ℚ
vsum-is-nonneg {succ n} v h =
 transport (_≤ vsum {succ n} v) {0ℚ + 0ℚ} {0ℚ} (ℚ-zero-left-neutral 0ℚ)
  (ℚ≤-adding 0ℚ (v 𝟎) 0ℚ (vsum (v ∘ suc)) (h 𝟎)
    (vsum-is-nonneg (v ∘ suc) (h ∘ suc)))

norm²-is-nonneg : {n : ℕ} (x : Fin n → ℚ) → 0ℚ ≤ norm² x
norm²-is-nonneg x =
 vsum-is-nonneg (λ i → x i * x i) (λ i → rational-squares-are-nonneg (x i))

\end{code}

The expansion of ‖x - y‖², and the squared norms and inner products of
scaled vectors.

\begin{code}

square-of-difference : (a b : ℚ)
                     → (a - b) * (a - b) ＝ (a * a + b * b) - (a * b + a * b)
square-of-difference a b =
 (a - b) * (a - b)
  ＝⟨ ℚ-distributivity' (a - b) a (- b) ⟩
 a * (a - b) + (- b) * (a - b)               ＝⟨ ap₂ _+_ I II ⟩
 (a * a - a * b) + ((- (b * a)) + b * b)
  ＝⟨ ap ((a * a - a * b) +_) (ℚ+-comm (- (b * a)) (b * b)) ⟩
 (a * a - a * b) + (b * b - b * a)
  ＝⟨ four-rearrange (a * a) (- (a * b)) (b * b) (- (b * a)) ⟩
 (a * a + b * b) + ((- (a * b)) - b * a)     ＝⟨ ap ((a * a + b * b) +_) III ⟩
 (a * a + b * b) - (a * b + a * b)           ∎
 where
  I : a * (a - b) ＝ a * a - a * b
  I =
   ℚ-distributivity a a (- b) ∙ ap (a * a +_) (ℚ-negation-dist-over-mult' a b)

  II : (- b) * (a - b) ＝ (- (b * a)) + b * b
  II = (- b) * (a - b)               ＝⟨ ℚ-negation-dist-over-mult b (a - b) ⟩
       - (b * (a - b))
        ＝⟨ ap -_ (ℚ-distributivity b a (- b)
            ∙ ap (b * a +_) (ℚ-negation-dist-over-mult' b b)) ⟩
       - (b * a - b * b)             ＝⟨ ℚ-minus-dist (b * a) (- (b * b)) ⁻¹ ⟩
       (- (b * a)) + (- (- (b * b)))
        ＝⟨ ap ((- (b * a)) +_) (ℚ-minus-minus (b * b) ⁻¹) ⟩
       (- (b * a)) + b * b           ∎

  III : (- (a * b)) - b * a ＝ - (a * b + a * b)
  III =
   (- (a * b)) + (- (b * a)) ＝⟨ ap (λ z → (- (a * b)) + (- z)) (ℚ*-comm b a) ⟩
        (- (a * b)) + (- (a * b)) ＝⟨ ℚ-minus-dist (a * b) (a * b) ⟩
        - (a * b + a * b)         ∎

norm²-of-difference
 : {n : ℕ} (x y : Fin n → ℚ)
 → norm² (λ i → x i - y i) ＝ (norm² x + norm² y) - (inner x y + inner x y)
norm²-of-difference x y =
 vsum-ext (λ i → (x i - y i) * (x i - y i))
  (λ i → (x i * x i + y i * y i) - (x i * y i + x i * y i))
  (λ i → square-of-difference (x i) (y i))
 ∙ vsum-sub (λ i → x i * x i + y i * y i) (λ i → x i * y i + x i * y i)
 ∙ ap₂ _-_ (vsum-add (λ i → x i * x i) (λ i → y i * y i))
           (vsum-add (λ i → x i * y i) (λ i → x i * y i))

swap-middle : (a b c d : ℚ) → (a * b) * (c * d) ＝ (a * c) * (b * d)
swap-middle a b c d =
 (a * b) * (c * d) ＝⟨ ℚ*-assoc a b (c * d) ⟩
 a * (b * (c * d)) ＝⟨ ap (a *_) (ℚ*-assoc b c d ⁻¹) ⟩
 a * ((b * c) * d) ＝⟨ ap (λ z → a * (z * d)) (ℚ*-comm b c) ⟩
 a * ((c * b) * d) ＝⟨ ap (a *_) (ℚ*-assoc c b d) ⟩
 a * (c * (b * d)) ＝⟨ ℚ*-assoc a c (b * d) ⁻¹ ⟩
 (a * c) * (b * d) ∎

inner-of-scaled
 : {n : ℕ} (x y : Fin n → ℚ) (α β : ℚ)
 → inner (λ i → x i * α) (λ i → y i * β) ＝ (α * β) * inner x y
inner-of-scaled x y α β =
 vsum-ext (λ i → (x i * α) * (y i * β)) (λ i → (α * β) * (x i * y i))
  (λ i → swap-middle (x i) α (y i) β ∙ ℚ*-comm (x i * y i) (α * β))
 ∙ vsum-scale (α * β) (λ i → x i * y i)

norm²-of-scaled : {n : ℕ} (x : Fin n → ℚ) (α : ℚ)
                → norm² (λ i → x i * α) ＝ (α * α) * norm² x
norm²-of-scaled x α = inner-of-scaled x x α α

\end{code}

Three identities, and an inequality from a nonnegative difference.

\begin{code}

from-difference : (p q : ℚ) → 0ℚ ≤ q - p → p ≤ q
from-difference p q l =
 transport₂ _≤_ {0ℚ + p} {p} {(q - p) + p} {q} (ℚ-zero-left-neutral p)
  (minus-plus q p)
  (ℚ≤-addition-preserves-order 0ℚ (q - p) p l)

translate-difference : (p r q : ℚ) → (p + r) - (p + q) ＝ r - q
translate-difference p r q =
 (p + r) - (p + q)         ＝⟨ ap ((p + r) +_) (ℚ-minus-dist p q ⁻¹) ⟩
 (p + r) + ((- p) + (- q)) ＝⟨ four-rearrange p r (- p) (- q) ⟩
 (p - p) + (r - q)         ＝⟨ ap (_+ (r - q)) (ℚ-inverse-sum-to-zero p) ⟩
 0ℚ + (r - q)              ＝⟨ ℚ-zero-left-neutral (r - q) ⟩
 r - q                     ∎

difference-of-differences : (X Y Z W : ℚ)
                          → (X - Y) - (Z - W) ＝ ((X - Z) - Y) + W
difference-of-differences X Y Z W =
 (X - Y) - (Z - W)     ＝⟨ ap ((X - Y) +_) I ⟩
 (X - Y) + ((- Z) + W) ＝⟨ four-rearrange X (- Y) (- Z) W ⟩
 (X - Z) + ((- Y) + W) ＝⟨ ℚ+-assoc (X - Z) (- Y) W ⁻¹ ⟩
 ((X - Z) - Y) + W     ∎
 where
  I : - (Z - W) ＝ (- Z) + W
  I = ℚ-minus-dist Z (- W) ⁻¹ ∙ ap ((- Z) +_) (ℚ-minus-minus W ⁻¹)

\end{code}

The case 1 ≤ s and 1 ≤ t, with a s = 1 and b t = 1: the left side is
a b d.

\begin{code}

case-both-large
 : (s t c a b : ℚ) → a * s ＝ 1ℚ → b * t ＝ 1ℚ → a * b ≤ 1ℚ
 → 0ℚ ≤ (s + t) - (c + c)
 → ((a * a) * s + (b * b) * t) - ((a * b) * c + (a * b) * c) ≤ (s + t) - (c + c)
case-both-large s t c a b as bt ab≤1 d-is-nonneg =
 transport (_≤ (s + t) - (c + c))
  {(a * b) * ((s + t) - (c + c))}
   {((a * a) * s + (b * b) * t) - ((a * b) * c + (a * b) * c)}
  I II
 where
  aas : (a * a) * s ＝ a
  aas = ℚ*-assoc a a s ∙ ap (a *_) as ∙ ℚ-mult-right-id a

  bbt : (b * b) * t ＝ b
  bbt = ℚ*-assoc b b t ∙ ap (b *_) bt ∙ ℚ-mult-right-id b

  abs' : (a * b) * s ＝ b
  abs' =
   ap (_* s) (ℚ*-comm a b) ∙ ℚ*-assoc b a s ∙ ap (b *_) as ∙ ℚ-mult-right-id b

  abt : (a * b) * t ＝ a
  abt = ℚ*-assoc a b t ∙ ap (a *_) bt ∙ ℚ-mult-right-id a

  III : (a * b) * (s + t) ＝ a + b
  III = ℚ-distributivity (a * b) s t ∙ ap₂ _+_ abs' abt ∙ ℚ+-comm b a

  IV : (a * b) * (- (c + c)) ＝ - ((a * b) * c + (a * b) * c)
  IV = ℚ-negation-dist-over-mult' (a * b) (c + c)
       ∙ ap -_ (ℚ-distributivity (a * b) c c)

  I : (a * b) * ((s + t) - (c + c)) ＝ ((a * a) * s + (b * b) * t)
    - ((a * b) * c + (a * b) * c)
  I = ℚ-distributivity (a * b) (s + t) (- (c + c))
    ∙ ap₂ _+_ III IV
    ∙ ap (λ z → z - ((a * b) * c + (a * b) * c)) (ap₂ _+_ (aas ⁻¹) (bbt ⁻¹))

  II : (a * b) * ((s + t) - (c + c)) ≤ (s + t) - (c + c)
  II = transport ((a * b) * ((s + t) - (c + c)) ≤_)
        {1ℚ * ((s + t) - (c + c))} {(s + t) - (c + c)}
         (ℚ-mult-left-id ((s + t) - (c + c)))
        (ℚ≤-pos-multiplication-preserves-order' (a * b) 1ℚ ((s + t) - (c + c))
          ab≤1 d-is-nonneg)

\end{code}

The case s ≤ 1 ≤ t, with b t = 1: the difference of the two sides is
(t - 1) (b ((t + 1) - 2c)), and (t + 1) - 2c ≥ (s + t) - 2c ≥ 0.

\begin{code}

case-mixed
 : (s t c b : ℚ) → s ≤ 1ℚ → 1ℚ ≤ t → b * t ＝ 1ℚ → 0ℚ ≤ b
 → 0ℚ ≤ (s + t) - (c + c)
 → (s + b) - (b * c + b * c) ≤ (s + t) - (c + c)
case-mixed s t c b s≤1 1≤t bt b-is-nonneg d-is-nonneg =
 from-difference ((s + b) - (b * c + b * c)) ((s + t) - (c + c))
  (transport (0ℚ ≤_) {P} {((s + t) - (c + c)) - ((s + b) - (b * c + b * c))} V
    P-is-nonneg)
 where
  e : ℚ
  e = (t + 1ℚ) - (c + c)

  Q P : ℚ
  Q = b * e
  P = (t - 1ℚ) * Q

  e-is-nonneg : 0ℚ ≤ e
  e-is-nonneg = ℚ≤-trans 0ℚ ((s + t) - (c + c)) e d-is-nonneg
                 (transport (λ z → z - (c + c) ≤ e) {t + s} {s + t}
                   (ℚ+-comm t s)
                   (ℚ≤-addition-preserves-order (t + s) (t + 1ℚ) (- (c + c))
                     (ℚ≤-addition-preserves-order-left s 1ℚ t s≤1)))

  P-is-nonneg : 0ℚ ≤ P
  P-is-nonneg = ℚ≤-pos-multiplication-preserves-order (t - 1ℚ) Q
                 (ℚ≤-difference-positive 1ℚ t 1≤t)
                 (ℚ≤-pos-multiplication-preserves-order b e b-is-nonneg
                   e-is-nonneg)

  tb : t * b ＝ 1ℚ
  tb = ℚ*-comm t b ∙ bt

  I : Q ＝ (1ℚ + b) - (b * c + b * c)
  I = ℚ-distributivity b (t + 1ℚ) (- (c + c))
    ∙ ap₂ _+_ (ℚ-distributivity b t 1ℚ ∙ ap₂ _+_ bt (ℚ-mult-right-id b))
              (ℚ-negation-dist-over-mult' b (c + c)
               ∙ ap -_ (ℚ-distributivity b c c))

  tbc : t * (b * c) ＝ c
  tbc = ℚ*-assoc t b c ⁻¹ ∙ ap (_* c) tb ∙ ℚ-mult-left-id c

  II : t * Q ＝ (t + 1ℚ) - (c + c)
  II = ap (t *_) I
     ∙ ℚ-distributivity t (1ℚ + b) (- (b * c + b * c))
     ∙ ap₂ _+_ (ℚ-distributivity t 1ℚ b ∙ ap₂ _+_ (ℚ-mult-right-id t) tb)
               (ℚ-negation-dist-over-mult' t (b * c + b * c)
                ∙ ap -_ (ℚ-distributivity t (b * c) (b * c) ∙ ap₂ _+_ tbc tbc))

  III : P ＝ ((t + 1ℚ) - (c + c)) - ((1ℚ + b) - (b * c + b * c))
  III = ℚ-distributivity' Q t (- 1ℚ)
      ∙ ap₂ _+_ II
         (ℚ-negation-dist-over-mult 1ℚ Q ∙ ap -_ (ℚ-mult-left-id Q ∙ I))

  IV : (t + 1ℚ) - (1ℚ + b) ＝ (s + t) - (s + b)
  IV = ap (_- (1ℚ + b)) (ℚ+-comm t 1ℚ) ∙ translate-difference 1ℚ t b
     ∙ translate-difference s t b ⁻¹

  V : P ＝ ((s + t) - (c + c)) - ((s + b) - (b * c + b * c))
  V = III
    ∙ difference-of-differences (t + 1ℚ) (c + c) (1ℚ + b) (b * c + b * c)
    ∙ ap (λ z → (z - (c + c)) + (b * c + b * c)) IV
    ∙ difference-of-differences (s + t) (c + c) (s + b) (b * c + b * c) ⁻¹

\end{code}

The scalar inequality, by the four cases, and the nonexpansiveness of
the retraction.

\begin{code}

scalar-nonexpansiveness
 : (s t c : ℚ) → 0ℚ ≤ (s + t) - (c + c)
 → ((reciprocal s * reciprocal s) * s + (reciprocal t * reciprocal t) * t)
   - ((reciprocal s * reciprocal t) * c + (reciprocal s * reciprocal t) * c)
   ≤ (s + t) - (c + c)
scalar-nonexpansiveness s t c d-is-nonneg =
 Cases (ℚ-dichotomous s 1ℚ) small-s large-s
 where
  L : ℚ → ℚ → ℚ
  L a b = ((a * a) * s + (b * b) * t) - ((a * b) * c + (a * b) * c)

  d : ℚ
  d = (s + t) - (c + c)

  one-one : (q : ℚ) → (1ℚ * 1ℚ) * q ＝ q
  one-one q = ap (_* q) (ℚ-mult-left-id 1ℚ) ∙ ℚ-mult-left-id q

  bb : (b q : ℚ) → b * q ＝ 1ℚ → (b * b) * q ＝ b
  bb b q e = ℚ*-assoc b b q ∙ ap (b *_) e ∙ ℚ-mult-right-id b

  both-small : L 1ℚ 1ℚ ＝ d
  both-small = ap₂ (λ u w → u - w) (ap₂ _+_ (one-one s) (one-one t))
                                   (ap₂ _+_ (one-one c) (one-one c))

  small-s : s ≤ 1ℚ → L (reciprocal s) (reciprocal t) ≤ d
  small-s ls =
   transport (_≤ d) {L 1ℚ (reciprocal t)} {L (reciprocal s) (reciprocal t)}
                (ap (λ a → L a (reciprocal t))
                  (reciprocal-of-at-most-one s ls ⁻¹))
                (Cases (ℚ-dichotomous t 1ℚ) I II)
   where
    I : t ≤ 1ℚ → L 1ℚ (reciprocal t) ≤ d
    I lt = transport (_≤ d) {d} {L 1ℚ (reciprocal t)}
            (both-small ⁻¹ ∙ ap (L 1ℚ) (reciprocal-of-at-most-one t lt ⁻¹))
             (ℚ≤-refl d)

    II : 1ℚ ≤ t → L 1ℚ (reciprocal t) ≤ d
    II lt = transport (_≤ d)
             {(s + reciprocal t) - (reciprocal t * c + reciprocal t * c)}
             {L 1ℚ (reciprocal t)} (III ⁻¹)
             (case-mixed s t c (reciprocal t) ls lt (reciprocal-times-self t lt)
               (reciprocal-is-nonneg t) d-is-nonneg)
     where
      III : L 1ℚ (reciprocal t) ＝ (s + reciprocal t)
          - (reciprocal t * c + reciprocal t * c)
      III = ap₂ (λ u w → u - w)
             (ap₂ _+_ (one-one s)
               (bb (reciprocal t) t (reciprocal-times-self t lt)))
             (ap₂ _+_ (ap (_* c) (ℚ-mult-left-id (reciprocal t)))
                      (ap (_* c) (ℚ-mult-left-id (reciprocal t))))

  large-s : 1ℚ ≤ s → L (reciprocal s) (reciprocal t) ≤ d
  large-s ls = Cases (ℚ-dichotomous t 1ℚ) I II
   where
    a : ℚ
    a = reciprocal s

    as : a * s ＝ 1ℚ
    as = reciprocal-times-self s ls

    I : t ≤ 1ℚ → L a (reciprocal t) ≤ d
    I lt = transport (_≤ d) {L a 1ℚ} {L a (reciprocal t)}
            (ap (L a) (reciprocal-of-at-most-one t lt ⁻¹)) IV
     where
      III : L a 1ℚ ＝ (t + a) - (a * c + a * c)
      III = ap₂ (λ u w → u - w) (ap₂ _+_ (bb a s as) (one-one t) ∙ ℚ+-comm a t)
             (ap₂ _+_ (ap (_* c) (ℚ-mult-right-id a))
               (ap (_* c) (ℚ-mult-right-id a)))

      d' : 0ℚ ≤ (t + s) - (c + c)
      d' = transport (λ z → 0ℚ ≤ z - (c + c)) {s + t} {t + s} (ℚ+-comm s t)
            d-is-nonneg

      IV : L a 1ℚ ≤ d
      IV = transport₂ _≤_ {(t + a) - (a * c + a * c)} {L a 1ℚ}
            {(t + s) - (c + c)} {d}
            (III ⁻¹) (ap (_- (c + c)) (ℚ+-comm t s))
            (case-mixed t s c a lt ls as (reciprocal-is-nonneg s) d')

    II : 1ℚ ≤ t → L a (reciprocal t) ≤ d
    II lt = case-both-large s t c a (reciprocal t) as
             (reciprocal-times-self t lt) ab≤1 d-is-nonneg
     where
      ab≤1 : a * reciprocal t ≤ 1ℚ
      ab≤1 = ℚ≤-trans (a * reciprocal t) (reciprocal t) 1ℚ
              (transport (a * reciprocal t ≤_) {1ℚ * reciprocal t}
                {reciprocal t}
                (ℚ-mult-left-id (reciprocal t))
                (ℚ≤-pos-multiplication-preserves-order' a 1ℚ (reciprocal t)
                  (reciprocal-≤-one s)
                  (reciprocal-is-nonneg t)))
              (reciprocal-≤-one t)

retraction-ℚ : {n : ℕ} → (Fin n → ℚ) → (Fin n → ℚ)
retraction-ℚ x i = x i * reciprocal (norm² x)

retraction-ℚ-is-nonexpansive
 : {n : ℕ} (x y : Fin n → ℚ)
 → norm² (λ i → retraction-ℚ x i - retraction-ℚ y i) ≤ norm² (λ i → x i - y i)
retraction-ℚ-is-nonexpansive x y =
 transport₂ _≤_ {L'} {norm² (λ i → retraction-ℚ x i - retraction-ℚ y i)}
  {(s + t) - (c + c)} {norm² (λ i → x i - y i)}
  (I ⁻¹) (norm²-of-difference x y ⁻¹)
  (scalar-nonexpansiveness s t c d-is-nonneg)
 where
  s t c a b : ℚ
  s = norm² x
  t = norm² y
  c = inner x y
  a = reciprocal s
  b = reciprocal t

  L' : ℚ
  L' = ((a * a) * s + (b * b) * t) - ((a * b) * c + (a * b) * c)

  I : norm² (λ i → retraction-ℚ x i - retraction-ℚ y i) ＝ L'
  I = norm²-of-difference (λ i → x i * a) (λ i → y i * b)
    ∙ ap₂ (λ u w → u - w) (ap₂ _+_ (norm²-of-scaled x a) (norm²-of-scaled y b))
                          (ap₂ _+_ (inner-of-scaled x y a b)
                            (inner-of-scaled x y a b))

  d-is-nonneg : 0ℚ ≤ (s + t) - (c + c)
  d-is-nonneg = transport (0ℚ ≤_) {norm² (λ i → x i - y i)} {(s + t) - (c + c)}
                 (norm²-of-difference x y) (norm²-is-nonneg (λ i → x i - y i))

\end{code}

A budget for n coordinates: for ε > 0, the rational δ = ε / (n + 1)
satisfies n δ² < ε². We write n as the sum of n ones (TypeTopology's ℕ-to-ℚ goes
through the integers, and the recursion is what we need).

\begin{code}

sum-of-ones : ℕ → ℚ
sum-of-ones 0        = 0ℚ
sum-of-ones (succ n) = sum-of-ones n + 1ℚ

sum-of-ones-is-nonneg : (n : ℕ) → 0ℚ ≤ sum-of-ones n
sum-of-ones-is-nonneg 0        = ℚ≤-refl 0ℚ
sum-of-ones-is-nonneg (succ n) =
 ℚ≤-trans 0ℚ (sum-of-ones n) (sum-of-ones n + 1ℚ) (sum-of-ones-is-nonneg n)
  (ℚ≤-addition-preserves-order'' (sum-of-ones n) 1ℚ
    (ℚ<-coarser-than-≤ 0ℚ 1ℚ 0<1))

vsum-constant : (n : ℕ) (c : ℚ) → vsum {n} (λ _ → c) ＝ sum-of-ones n * c
vsum-constant 0        c = ℚ-zero-left-is-zero c ⁻¹
vsum-constant (succ n) c =
 c + vsum {n} (λ _ → c) ＝⟨ ap (c +_) (vsum-constant n c) ⟩
 c + sum-of-ones n * c       ＝⟨ ℚ+-comm c (sum-of-ones n * c) ⟩
 sum-of-ones n * c + c
  ＝⟨ ap (sum-of-ones n * c +_) (ℚ-mult-left-id c ⁻¹) ⟩
 sum-of-ones n * c + 1ℚ * c  ＝⟨ ℚ-distributivity' c (sum-of-ones n) 1ℚ ⁻¹ ⟩
 (sum-of-ones n + 1ℚ) * c    ∎

budget : (n : ℕ) (ε : ℚ) → 0ℚ < ε
       → Σ δ ꞉ ℚ , (0ℚ < δ) × (vsum {n} (λ _ → δ * δ) < ε * ε)
budget n ε l = ε * r , δ-is-positive , bound
 where
  N m r : ℚ
  N = sum-of-ones n
  m = N + 1ℚ
  r = reciprocal m

  1≤m : 1ℚ ≤ m
  1≤m = transport (_≤ m) {0ℚ + 1ℚ} {1ℚ} (ℚ-zero-left-neutral 1ℚ)
         (ℚ≤-addition-preserves-order 0ℚ N 1ℚ (sum-of-ones-is-nonneg n))

  rm : r * m ＝ 1ℚ
  rm = reciprocal-times-self m 1≤m

  δ-is-positive : 0ℚ < ε * r
  δ-is-positive =
   ℚ<-pos-multiplication-preserves-order ε r l (reciprocal-is-positive m)

  δδ-is-positive : 0ℚ < (ε * r) * (ε * r)
  δδ-is-positive = ℚ<-pos-multiplication-preserves-order (ε * r) (ε * r)
                    δ-is-positive δ-is-positive

  I : N * ((ε * r) * (ε * r)) < m * ((ε * r) * (ε * r))
  I = ℚ<-pos-multiplication-preserves-order' N m ((ε * r) * (ε * r))
       (ℚ<-addition-preserves-order'' N 1ℚ 0<1) δδ-is-positive

  II : m * ((ε * r) * (ε * r)) ＝ (ε * ε) * r
  II = m * ((ε * r) * (ε * r)) ＝⟨ ap (m *_) (swap-middle ε r ε r) ⟩
       m * ((ε * ε) * (r * r)) ＝⟨ ℚ*-assoc m (ε * ε) (r * r) ⁻¹ ⟩
       (m * (ε * ε)) * (r * r) ＝⟨ ap (_* (r * r)) (ℚ*-comm m (ε * ε)) ⟩
       ((ε * ε) * m) * (r * r) ＝⟨ ℚ*-assoc (ε * ε) m (r * r) ⟩
       (ε * ε) * (m * (r * r)) ＝⟨ ap ((ε * ε) *_) III ⟩
       (ε * ε) * r             ∎
   where
    III : m * (r * r) ＝ r
    III = ℚ*-assoc m r r ⁻¹ ∙ ap (_* r) (ℚ*-comm m r ∙ rm) ∙ ℚ-mult-left-id r

  IV : (ε * ε) * r ≤ ε * ε
  IV =
   transport ((ε * ε) * r ≤_) {(ε * ε) * 1ℚ} {ε * ε} (ℚ-mult-right-id (ε * ε))
        (left-multiplication-preserves-≤ r 1ℚ (ε * ε) (reciprocal-≤-one m)
          (rational-squares-are-nonneg ε))

  bound : vsum {n} (λ _ → (ε * r) * (ε * r)) < ε * ε
  bound = transport (_< ε * ε) {N * ((ε * r) * (ε * r))}
           {vsum {n} (λ _ → (ε * r) * (ε * r))}
           (vsum-constant n ((ε * r) * (ε * r)) ⁻¹)
           (ℚ<-≤-trans (N * ((ε * r) * (ε * r))) (m * ((ε * r) * (ε * r)))
             (ε * ε) I
             (transport (_≤ ε * ε) {(ε * ε) * r} {m * ((ε * r) * (ε * r))}
               (II ⁻¹) IV))

\end{code}
