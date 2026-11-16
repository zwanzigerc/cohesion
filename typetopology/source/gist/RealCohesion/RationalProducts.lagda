Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Bounds for products of rationals, used to extend multiplication to the
reals (gist.RealCohesion.RealMultiplication, gate G14).

If a and c differ by less than δ, and b and d too, then a b and c d
differ by at most δ |d| + |a| δ. So if |a| and |d| are at most M, the
products differ by less than ε as soon as δ (M + M + 1) ≤ ε. The same
bound moves a rational square across no given rational, which the
square root of gate G14, step E4, needs. The module
is parameter-free, so that Agda does not unfold the arithmetic of its
closed terms where it is used.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.RealCohesion.RationalProducts where

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.Order
open import UF.Base
open import Rationals.Abs
open import Rationals.Addition
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Type
open import Rationals.MinMax
open import Fin.Type
open import gist.RealCohesion.RationalArithmetic
 using (telescope ; <-move-left ; <-move-right ; ball-gives-abs ;
         widened-difference ;
        zero-minus ; minus-plus ; nonneg-part ; nonneg-part-of-nonneg ;
         nonneg-part-of-nonpos ;
        abs-gives-ball ; add-difference ; minus-zero ;
         difference-of-reflections)
open import gist.RealCohesion.RationalLipschitz
 using (Lipschitz ; Lipschitz-ext ; ∘-Lipschitz ; translation-is-Lipschitz ;
        nonneg-part-is-Lipschitz)

\end{code}

The difference of two products, and its bound.

\begin{code}

product-difference : (a b c d : ℚ) → a * b - c * d ＝ (a - c) * d + a * (b - d)
product-difference a b c d =
 a * b - c * d                     ＝⟨ telescope (c * d) (a * d) (a * b) ⁻¹ ⟩
 (a * d - c * d) + (a * b - a * d) ＝⟨ ap₂ _+_ I II ⟩
 (a - c) * d + a * (b - d)         ∎
 where
  I : a * d - c * d ＝ (a - c) * d
  I = a * d - c * d     ＝⟨ ap (a * d +_) (ℚ-negation-dist-over-mult c d ⁻¹) ⟩
      a * d + (- c) * d ＝⟨ ℚ-distributivity' d a (- c) ⁻¹ ⟩
      (a - c) * d       ∎

  II : a * b - a * d ＝ a * (b - d)
  II = a * b - a * d     ＝⟨ ap (a * b +_) (ℚ-negation-dist-over-mult' a d ⁻¹) ⟩
       a * b + a * (- d) ＝⟨ ℚ-distributivity a b (- d) ⁻¹ ⟩
       a * (b - d)       ∎

product-difference-bound
 : (a b c d : ℚ)
 → abs (a * b - c * d) ≤ abs (a - c) * abs d + abs a * abs (b - d)
product-difference-bound a b c d =
 transport (_≤ abs (a - c) * abs d + abs a * abs (b - d))
  (ap abs (product-difference a b c d ⁻¹))
  (transport₂ (λ u v → abs ((a - c) * d + a * (b - d)) ≤ u + v)
    (abs-mult (a - c) d ⁻¹) (abs-mult a (b - d) ⁻¹)
    (ℚ-triangle-inequality ((a - c) * d) (a * (b - d))))

\end{code}

Monotonicity of multiplication by a nonnegative rational on the left.

\begin{code}

left-multiplication-preserves-≤ : (p q r : ℚ) → p ≤ q → 0ℚ ≤ r → r * p ≤ r * q
left-multiplication-preserves-≤ p q r l m =
 transport₂ _≤_ (ℚ*-comm p r) (ℚ*-comm q r)
  (ℚ≤-pos-multiplication-preserves-order' p q r l m)

products-are-close
 : (M δ a b c d : ℚ)
 → abs a ≤ M → abs d ≤ M
 → abs (a - c) < δ → abs (b - d) < δ
 → abs (a * b - c * d) ≤ δ * M + M * δ
products-are-close M δ a b c d la ld lac lbd =
 ℚ≤-trans (abs (a * b - c * d)) (abs (a - c) * abs d + abs a * abs (b - d))
  (δ * M + M * δ) (product-difference-bound a b c d)
  (ℚ≤-adding (abs (a - c) * abs d) (δ * M) (abs a * abs (b - d)) (M * δ) I II)
 where
  δ-is-nonneg : 0ℚ ≤ δ
  δ-is-nonneg = ℚ≤-trans 0ℚ (abs (a - c)) δ (ℚ-abs-is-positive (a - c))
                 (ℚ<-coarser-than-≤ (abs (a - c)) δ lac)

  M-is-nonneg : 0ℚ ≤ M
  M-is-nonneg = ℚ≤-trans 0ℚ (abs a) M (ℚ-abs-is-positive a) la

  I : abs (a - c) * abs d ≤ δ * M
  I = ℚ≤-trans (abs (a - c) * abs d) (δ * abs d) (δ * M)
       (ℚ≤-pos-multiplication-preserves-order' (abs (a - c)) δ (abs d)
         (ℚ<-coarser-than-≤ (abs (a - c)) δ lac) (ℚ-abs-is-positive d))
       (left-multiplication-preserves-≤ (abs d) M δ ld δ-is-nonneg)

  II : abs a * abs (b - d) ≤ M * δ
  II = ℚ≤-trans (abs a * abs (b - d)) (M * abs (b - d)) (M * δ)
        (ℚ≤-pos-multiplication-preserves-order' (abs a) M (abs (b - d))
          la (ℚ-abs-is-positive (b - d)))
        (left-multiplication-preserves-≤ (abs (b - d)) δ M
          (ℚ<-coarser-than-≤ (abs (b - d)) δ lbd) M-is-nonneg)

\end{code}

A positive δ with δ M + M δ < ε, for M ≥ 0 and ε > 0: we take
δ = ε / (M + M + 1).

\begin{code}

small-enough : (M ε : ℚ) → 0ℚ ≤ M → 0ℚ < ε
             → Σ δ ꞉ ℚ , (0ℚ < δ) × (δ * M + M * δ < ε)
small-enough M ε lM lε = δ , δ-is-positive , bound
 where
  N : ℚ
  N = M + M + 1ℚ

  M+M-is-nonneg : 0ℚ ≤ M + M
  M+M-is-nonneg = transport (_≤ M + M) (ℚ-zero-left-neutral 0ℚ)
                   (ℚ≤-adding 0ℚ M 0ℚ M lM lM)

  M+M<N : M + M < N
  M+M<N = ℚ<-addition-preserves-order'' (M + M) 1ℚ 0<1

  N-is-positive : 0ℚ < N
  N-is-positive = ℚ≤-<-trans 0ℚ (M + M) N M+M-is-nonneg M+M<N

  N-is-not-zero : ¬ (N ＝ 0ℚ)
  N-is-not-zero = ℚ<-positive-not-zero N N-is-positive

  N⁻¹ : ℚ
  N⁻¹ = ℚ*-inv N N-is-not-zero

  δ : ℚ
  δ = ε * N⁻¹

  δ-is-positive : 0ℚ < δ
  δ-is-positive = ℚ<-pos-multiplication-preserves-order ε N⁻¹ lε
                   (ℚ-inv-preserves-pos N N-is-positive N-is-not-zero)

  I : δ * M + M * δ ＝ (M + M) * δ
  I = δ * M + M * δ ＝⟨ ap (_+ M * δ) (ℚ*-comm δ M) ⟩
      M * δ + M * δ ＝⟨ ℚ-distributivity' δ M M ⁻¹ ⟩
      (M + M) * δ   ∎

  II : N * δ ＝ ε
  II = N * (ε * N⁻¹) ＝⟨ ℚ*-assoc N ε N⁻¹ ⁻¹ ⟩
       N * ε * N⁻¹   ＝⟨ ap (_* N⁻¹) (ℚ*-comm N ε) ⟩
       ε * N * N⁻¹   ＝⟨ ℚ*-assoc ε N N⁻¹ ⟩
       ε * (N * N⁻¹) ＝⟨ ap (ε *_) (ℚ*-inverse-product N N-is-not-zero) ⟩
       ε * 1ℚ        ＝⟨ ℚ-mult-right-id ε ⟩
       ε             ∎

  bound : δ * M + M * δ < ε
  bound = transport₂ _<_ (I ⁻¹) II
           (ℚ<-pos-multiplication-preserves-order' (M + M) N δ M+M<N
             δ-is-positive)

\end{code}

A rational between two others is bounded in absolute value by the sum
of their absolute values.

\begin{code}

between-is-bounded : (a b c : ℚ) → a < c → c < b → abs c ≤ abs a + abs b
between-is-bounded a b c l m = ℚ≤-to-abs c (abs a + abs b) (I , II)
 where
  |a|≤ : abs a ≤ abs a + abs b
  |a|≤ = ℚ≤-addition-preserves-order'' (abs a) (abs b) (ℚ-abs-is-positive b)

  |b|≤ : abs b ≤ abs a + abs b
  |b|≤ = transport (abs b ≤_) (ℚ+-comm (abs b) (abs a))
          (ℚ≤-addition-preserves-order'' (abs b) (abs a) (ℚ-abs-is-positive a))

  I : - (abs a + abs b) ≤ c
  I = ℚ≤-trans (- (abs a + abs b)) (- abs a) c
       (ℚ≤-swap (abs a) (abs a + abs b) |a|≤)
       (ℚ≤-trans (- abs a) a c
         (pr₁ (ℚ-abs-≤-unpack a (abs a) (ℚ≤-refl (abs a))))
         (ℚ<-coarser-than-≤ a c l))

  II : c ≤ abs a + abs b
  II = ℚ≤-trans c b (abs a + abs b) (ℚ<-coarser-than-≤ c b m)
        (ℚ≤-trans b (abs b) (abs a + abs b) (ℚ≤-abs-all b) |b|≤)

\end{code}

Two rationals in an interval of length less than δ differ by less
than δ.

\begin{code}

interval-gives-close : (p q u v δ : ℚ) → p < u → u < q → p < v → v < q
                     → q - p < δ
                     → abs (u - v) < δ
interval-gives-close p q u v δ pu uq pv vq w = ball-gives-abs u v δ I II
 where
  III : (z : ℚ) → p < z → q < δ + z
  III z l = ℚ<-trans q (δ + p) (δ + z) (<-move-right q δ p w)
             (ℚ<-addition-preserves-order''' p z δ l)

  I : v - δ < u
  I = <-move-left v u δ
       (transport (v <_) (ℚ+-comm δ u) (ℚ<-trans v q (δ + u) vq (III u pu)))

  II : u < v + δ
  II = transport (u <_) (ℚ+-comm δ v) (ℚ<-trans u q (δ + v) uq (III v pv))

\end{code}

Bounds from a box. An interval (a' , b') of length less than 1 with
a' < b and a < b' lies in (a - 1 , b + 1), so its points z have
|z| ≤ |a - 1| + |b + 1|. For boxes in ℚ², we add the bounds of the two
coordinates.

\begin{code}

coordinate-bound : ℚ → ℚ → ℚ
coordinate-bound a b = abs (a - 1ℚ) + abs (b + 1ℚ)

coordinate-bound-is-nonneg : (a b : ℚ) → 0ℚ ≤ coordinate-bound a b
coordinate-bound-is-nonneg a b =
 transport (_≤ coordinate-bound a b) (ℚ-zero-left-neutral 0ℚ)
  (ℚ≤-adding 0ℚ (abs (a - 1ℚ)) 0ℚ (abs (b + 1ℚ))
    (ℚ-abs-is-positive (a - 1ℚ)) (ℚ-abs-is-positive (b + 1ℚ)))

short-intervals-are-bounded
 : (a b a' b' z : ℚ)
 → a' < b → a < b' → b' - a' < 1ℚ
 → a' < z → z < b'
 → abs z ≤ coordinate-bound a b
short-intervals-are-bounded a b a' b' z k k' w l l' =
 between-is-bounded (a - 1ℚ) (b + 1ℚ) z I II
 where
  b'<1+a' : b' < 1ℚ + a'
  b'<1+a' = <-move-right b' 1ℚ a' w

  II : z < b + 1ℚ
  II = ℚ<-trans z b' (b + 1ℚ) l'
        (ℚ<-trans b' (1ℚ + a') (b + 1ℚ) b'<1+a'
          (transport (1ℚ + a' <_) (ℚ+-comm 1ℚ b)
            (ℚ<-addition-preserves-order''' a' b 1ℚ k)))

  I : a - 1ℚ < z
  I = ℚ<-trans (a - 1ℚ) a' z
       (ℚ<-trans (a - 1ℚ) (b' - 1ℚ) a'
         (ℚ<-addition-preserves-order a b' (- 1ℚ) k')
         (<-move-left b' a' 1ℚ (transport (b' <_) (ℚ+-comm 1ℚ a') b'<1+a')))
       l

box-bound : (a b : Fin 2 → ℚ) → ℚ
box-bound a b = coordinate-bound (a 𝟎) (b 𝟎) + coordinate-bound (a 𝟏) (b 𝟏)

box-bound-is-nonneg : (a b : Fin 2 → ℚ) → 0ℚ ≤ box-bound a b
box-bound-is-nonneg a b =
 transport (_≤ box-bound a b) (ℚ-zero-left-neutral 0ℚ)
  (ℚ≤-adding 0ℚ (coordinate-bound (a 𝟎) (b 𝟎)) 0ℚ (coordinate-bound (a 𝟏) (b 𝟏))
    (coordinate-bound-is-nonneg (a 𝟎) (b 𝟎))
     (coordinate-bound-is-nonneg (a 𝟏) (b 𝟏)))

coordinate-bound-≤-box-bound
 : (a b : Fin 2 → ℚ) (i : Fin 2) → coordinate-bound (a i) (b i) ≤ box-bound a b
coordinate-bound-≤-box-bound a b 𝟎 =
 ℚ≤-addition-preserves-order'' (coordinate-bound (a 𝟎) (b 𝟎))
  (coordinate-bound (a 𝟏) (b 𝟏))
  (coordinate-bound-is-nonneg (a 𝟏) (b 𝟏))
coordinate-bound-≤-box-bound a b 𝟏 =
 transport (coordinate-bound (a 𝟏) (b 𝟏) ≤_)
  (ℚ+-comm (coordinate-bound (a 𝟏) (b 𝟏)) (coordinate-bound (a 𝟎) (b 𝟎)))
  (ℚ≤-addition-preserves-order'' (coordinate-bound (a 𝟏) (b 𝟏))
    (coordinate-bound (a 𝟎) (b 𝟎))
    (coordinate-bound-is-nonneg (a 𝟎) (b 𝟎)))
coordinate-bound-≤-box-bound a b (suc (suc i)) = 𝟘-elim i

\end{code}

Products at two rational points of a box (a' , b') in ℚ² whose sides
are shorter than δ and than 1, and which meets a box (a , b) in the
sense above, differ by at most δ M + M δ, for M the bound of (a , b).

\begin{code}

products-in-a-short-box
 : (a b a' b' : Fin 2 → ℚ) (δ : ℚ)
 → ((i : Fin 2) → a' i < b i)
 → ((i : Fin 2) → a i < b' i)
 → ((i : Fin 2) → b' i - a' i < 1ℚ)
 → ((i : Fin 2) → b' i - a' i < δ)
 → (u v : Fin 2 → ℚ)
 → ((i : Fin 2) → (a' i < u i) × (u i < b' i))
 → ((i : Fin 2) → (a' i < v i) × (v i < b' i))
 → abs (u 𝟎 * u 𝟏 - v 𝟎 * v 𝟏) ≤ δ * box-bound a b + box-bound a b * δ
products-in-a-short-box a b a' b' δ k k' w₁ w u v mu mv =
 products-are-close (box-bound a b) δ (u 𝟎) (u 𝟏) (v 𝟎) (v 𝟏)
  (bounded u mu 𝟎) (bounded v mv 𝟏) (close 𝟎) (close 𝟏)
 where
  bounded : (z : Fin 2 → ℚ) → ((i : Fin 2) → (a' i < z i) × (z i < b' i))
          → (i : Fin 2) → abs (z i) ≤ box-bound a b
  bounded z m i =
   ℚ≤-trans (abs (z i)) (coordinate-bound (a i) (b i)) (box-bound a b)
    (short-intervals-are-bounded (a i) (b i) (a' i) (b' i) (z i) (k i) (k' i)
      (w₁ i)
      (pr₁ (m i)) (pr₂ (m i)))
    (coordinate-bound-≤-box-bound a b i)

  close : (i : Fin 2) → abs (u i - v i) < δ
  close i = interval-gives-close (a' i) (b' i) (u i) (v i) δ
             (pr₁ (mu i)) (pr₂ (mu i)) (pr₁ (mv i)) (pr₂ (mv i)) (w i)

\end{code}

The interval of radius η around r is shorter than ε if η + η < ε.

\begin{code}

widened-point : (r η ε : ℚ) → η + η < ε → (r + η) - (r - η) < ε
widened-point r η ε l = transport (_< ε) I l
 where
  I : η + η ＝ (r + η) - (r - η)
  I = η + η             ＝⟨ ℚ-zero-left-neutral (η + η) ⁻¹ ⟩
      0ℚ + (η + η)      ＝⟨ ap (_+ (η + η)) (ℚ-inverse-sum-to-zero r ⁻¹) ⟩
      (r - r) + (η + η) ＝⟨ widened-difference r r η ⁻¹ ⟩
      (r + η) - (r - η) ∎

\end{code}

Products of positive rationals are monotone, and squares are
nonnegative.

\begin{code}

products-of-positives-are-monotone
 : (a₀ a₁ c₀ c₁ : ℚ) → 0ℚ < a₀ → 0ℚ < a₁ → a₀ < c₀ → a₁ < c₁ → a₀ * a₁ < c₀ * c₁
products-of-positives-are-monotone a₀ a₁ c₀ c₁ k₀ k₁ l₀ l₁ =
 ℚ<-trans (a₀ * a₁) (c₀ * a₁) (c₀ * c₁)
  (ℚ<-pos-multiplication-preserves-order' a₀ c₀ a₁ l₀ k₁)
  (ℚ<-pos-multiplication-preserves-order'' a₁ c₁ c₀ l₁
    (ℚ<-trans 0ℚ a₀ c₀ k₀ l₀))

rational-squares-are-nonneg : (q : ℚ) → 0ℚ ≤ q * q
rational-squares-are-nonneg q = Cases (ℚ-dichotomous 0ℚ q) I II
 where
  I : 0ℚ ≤ q → 0ℚ ≤ q * q
  I l = ℚ≤-pos-multiplication-preserves-order q q l l

  III : (- q) * (- q) ＝ q * q
  III = (- q) * (- q) ＝⟨ ℚ-negation-dist-over-mult q (- q) ⟩
        - (q * (- q)) ＝⟨ ap -_ (ℚ-negation-dist-over-mult' q q) ⟩
        - (- (q * q)) ＝⟨ ℚ-minus-minus (q * q) ⁻¹ ⟩
        q * q         ∎

  IV : q ≤ 0ℚ → 0ℚ ≤ - q
  IV l = transport (0ℚ ≤_) (zero-minus q) (ℚ≤-difference-positive q 0ℚ l)

  II : q ≤ 0ℚ → 0ℚ ≤ q * q
  II l = transport (0ℚ ≤_) III
          (ℚ≤-pos-multiplication-preserves-order (- q) (- q) (IV l) (IV l))

\end{code}

The reciprocal of max(1 , q), used for the retraction of ℝⁿ onto the
ball (gate G14). It is positive and at most 1, its product with
max(1 , q) is 1, it is 1 where q ≤ 1, and it is 1-Lipschitz: max(1 , _)
is (by gist.RealCohesion.RationalLipschitz), and the reciprocals r a and
r b satisfy r a - r b = r a r b (max(1 , b) - max(1 , a)) with
r a r b ≤ 1. We keep max(1 , _) and the reciprocal abstract, with their
defining facts, so that Agda does not unfold TypeTopology's rational
inverse where they occur.

\begin{code}

abstract
 max-one : ℚ → ℚ
 max-one q = max 1ℚ q

 max-one-≥-one : (q : ℚ) → 1ℚ ≤ max-one q
 max-one-≥-one q = max≤ 1ℚ q

 max-one-≥-self : (q : ℚ) → q ≤ max-one q
 max-one-≥-self q = max≤' 1ℚ q

 max-one-of-at-most-one : (q : ℚ) → q ≤ 1ℚ → max-one q ＝ 1ℚ
 max-one-of-at-most-one q l = max-comm 1ℚ q ∙ ≤-to-max q 1ℚ l ⁻¹

 max-one-of-at-least-one : (q : ℚ) → 1ℚ ≤ q → max-one q ＝ q
 max-one-of-at-least-one q l = ≤-to-max 1ℚ q l ⁻¹

 max-one-is-shifted-nonneg-part : (y : ℚ)
                                → max-one y ＝ nonneg-part (y - 1ℚ) + 1ℚ
 max-one-is-shifted-nonneg-part y = Cases (max-to-≤ 1ℚ y) I II
  where
   I : (1ℚ ≤ y) × (max 1ℚ y ＝ y) → max 1ℚ y ＝ nonneg-part (y - 1ℚ) + 1ℚ
   I (l , e) = e ∙ minus-plus y 1ℚ ⁻¹
             ∙ ap (_+ 1ℚ)
             (nonneg-part-of-nonneg (y - 1ℚ) (ℚ≤-difference-positive 1ℚ y l) ⁻¹)

   II : (y ≤ 1ℚ) × (max 1ℚ y ＝ 1ℚ) → max 1ℚ y ＝ nonneg-part (y - 1ℚ) + 1ℚ
   II (l , e) = e ∙ ℚ-zero-left-neutral 1ℚ ⁻¹
              ∙ ap (_+ 1ℚ) (nonneg-part-of-nonpos (y - 1ℚ) III ⁻¹)
    where
     III : y - 1ℚ ≤ 0ℚ
     III = transport (y - 1ℚ ≤_) {1ℚ - 1ℚ} {0ℚ} (ℚ-inverse-sum-to-zero 1ℚ)
            (ℚ≤-addition-preserves-order y 1ℚ (- 1ℚ) l)

 max-one-is-positive : (q : ℚ) → 0ℚ < max-one q
 max-one-is-positive q = ℚ<-≤-trans 0ℚ 1ℚ (max-one q) 0<1 (max-one-≥-one q)

 reciprocal : ℚ → ℚ
 reciprocal q =
  ℚ*-inv (max-one q) (ℚ<-positive-not-zero (max-one q) (max-one-is-positive q))

 reciprocal-is-positive : (q : ℚ) → 0ℚ < reciprocal q
 reciprocal-is-positive q =
  ℚ-inv-preserves-pos (max-one q) (max-one-is-positive q)
   (ℚ<-positive-not-zero (max-one q) (max-one-is-positive q))

 reciprocal-times-max-one : (q : ℚ) → reciprocal q * max-one q ＝ 1ℚ
 reciprocal-times-max-one q =
  ℚ*-comm (reciprocal q) (max-one q)
  ∙ ℚ*-inverse-product (max-one q)
     (ℚ<-positive-not-zero (max-one q) (max-one-is-positive q))

max-one-is-Lipschitz : Lipschitz max-one
max-one-is-Lipschitz =
 Lipschitz-ext max-one (λ y → nonneg-part (y - 1ℚ) + 1ℚ)
  max-one-is-shifted-nonneg-part
  (∘-Lipschitz (λ z → z + 1ℚ) (λ y → nonneg-part (y - 1ℚ))
    (translation-is-Lipschitz 1ℚ)
    (∘-Lipschitz nonneg-part (λ y → y - 1ℚ) nonneg-part-is-Lipschitz
      (translation-is-Lipschitz (- 1ℚ))))

reciprocal-is-nonneg : (q : ℚ) → 0ℚ ≤ reciprocal q
reciprocal-is-nonneg q =
 ℚ<-coarser-than-≤ 0ℚ (reciprocal q) (reciprocal-is-positive q)

reciprocal-≤-one : (q : ℚ) → reciprocal q ≤ 1ℚ
reciprocal-≤-one q =
 transport₂ _≤_ {reciprocal q * 1ℚ} {reciprocal q} {reciprocal q * max-one q}
  {1ℚ}
  (ℚ-mult-right-id (reciprocal q)) (reciprocal-times-max-one q)
  (left-multiplication-preserves-≤ 1ℚ (max-one q) (reciprocal q)
    (max-one-≥-one q)
    (reciprocal-is-nonneg q))

reciprocal-of-at-most-one : (q : ℚ) → q ≤ 1ℚ → reciprocal q ＝ 1ℚ
reciprocal-of-at-most-one q l =
 reciprocal q             ＝⟨ ℚ-mult-right-id (reciprocal q) ⁻¹ ⟩
 reciprocal q * 1ℚ
  ＝⟨ ap (reciprocal q *_) (max-one-of-at-most-one q l ⁻¹) ⟩
 reciprocal q * max-one q ＝⟨ reciprocal-times-max-one q ⟩
 1ℚ                       ∎

reciprocal-times-self : (q : ℚ) → 1ℚ ≤ q → reciprocal q * q ＝ 1ℚ
reciprocal-times-self q l =
 ap (reciprocal q *_) (max-one-of-at-least-one q l ⁻¹)
  ∙ reciprocal-times-max-one q

reciprocal-bound : (q : ℚ) → q * (reciprocal q * reciprocal q) ≤ 1ℚ
reciprocal-bound q =
 ℚ≤-trans (q * (r * r)) r 1ℚ
  (transport (q * (r * r) ≤_) {max-one q * (r * r)} {r} II I)
   (reciprocal-≤-one q)
 where
  r : ℚ
  r = reciprocal q

  I : q * (r * r) ≤ max-one q * (r * r)
  I = ℚ≤-pos-multiplication-preserves-order' q (max-one q) (r * r)
       (max-one-≥-self q)
       (ℚ≤-pos-multiplication-preserves-order r r (reciprocal-is-nonneg q)
         (reciprocal-is-nonneg q))

  II : max-one q * (r * r) ＝ r
  II = max-one q * (r * r) ＝⟨ ℚ*-assoc (max-one q) r r ⁻¹ ⟩
       max-one q * r * r   ＝⟨ ap (_* r) (ℚ*-comm (max-one q) r) ⟩
       r * max-one q * r   ＝⟨ ap (_* r) (reciprocal-times-max-one q) ⟩
       1ℚ * r              ＝⟨ ℚ-mult-left-id r ⟩
       r                   ∎

reciprocal-is-Lipschitz : Lipschitz reciprocal
reciprocal-is-Lipschitz a b =
 transport (_≤ abs (a - b)) {c * abs (mb - ma)} {abs (ra - rb)} (II ⁻¹) III
 where
  ra rb ma mb c : ℚ
  ra = reciprocal a
  rb = reciprocal b
  ma = max-one a
  mb = max-one b
  c  = ra * rb

  c-is-nonneg : 0ℚ ≤ c
  c-is-nonneg =
   ℚ≤-pos-multiplication-preserves-order ra rb (reciprocal-is-nonneg a)
                 (reciprocal-is-nonneg b)

  c-≤-one : c ≤ 1ℚ
  c-≤-one = ℚ≤-trans c rb 1ℚ
             (transport (c ≤_) {1ℚ * rb} {rb} (ℚ-mult-left-id rb)
               (ℚ≤-pos-multiplication-preserves-order' ra 1ℚ rb
                 (reciprocal-≤-one a)
                 (reciprocal-is-nonneg b)))
             (reciprocal-≤-one b)

  Ia : ra ＝ c * mb
  Ia = ra             ＝⟨ ℚ-mult-right-id ra ⁻¹ ⟩
       ra * 1ℚ        ＝⟨ ap (ra *_) (reciprocal-times-max-one b ⁻¹) ⟩
       ra * (rb * mb) ＝⟨ ℚ*-assoc ra rb mb ⁻¹ ⟩
       c * mb         ∎

  Ib : rb ＝ c * ma
  Ib = rb             ＝⟨ ℚ-mult-right-id rb ⁻¹ ⟩
       rb * 1ℚ        ＝⟨ ap (rb *_) (reciprocal-times-max-one a ⁻¹) ⟩
       rb * (ra * ma) ＝⟨ ℚ*-assoc rb ra ma ⁻¹ ⟩
       rb * ra * ma   ＝⟨ ap (_* ma) (ℚ*-comm rb ra) ⟩
       c * ma         ∎

  I : ra - rb ＝ c * (mb - ma)
  I = ra - rb             ＝⟨ ap₂ _-_ Ia Ib ⟩
      c * mb - c * ma
       ＝⟨ ap (c * mb +_) (ℚ-negation-dist-over-mult' c ma ⁻¹) ⟩
      c * mb + c * (- ma) ＝⟨ ℚ-distributivity c mb (- ma) ⁻¹ ⟩
      c * (mb - ma)       ∎

  II : abs (ra - rb) ＝ c * abs (mb - ma)
  II = ap abs I ∙ abs-mult c (mb - ma) ⁻¹
       ∙ ap (_* abs (mb - ma)) (abs-of-pos-is-pos c c-is-nonneg)

  III : c * abs (mb - ma) ≤ abs (a - b)
  III = ℚ≤-trans (c * abs (mb - ma)) (abs (mb - ma)) (abs (a - b))
         (transport (c * abs (mb - ma) ≤_) {1ℚ * abs (mb - ma)} {abs (mb - ma)}
           (ℚ-mult-left-id (abs (mb - ma)))
           (ℚ≤-pos-multiplication-preserves-order' c 1ℚ (abs (mb - ma)) c-≤-one
             (ℚ-abs-is-positive (mb - ma))))
         (transport (abs (mb - ma) ≤_) {abs (b - a)} {abs (a - b)}
           (abs-comm b a)
           (max-one-is-Lipschitz b a))

\end{code}

An interval (p , q) with p < 1 contains a rational that is at most 1.

\begin{code}

point-at-most-one : (p q : ℚ) → p < q → p < 1ℚ
                  → Σ c ꞉ ℚ , (p < c) × (c < q) × (c ≤ 1ℚ)
point-at-most-one p q l m = Cases (ℚ-dichotomous q 1ℚ) I II
 where
  I : q ≤ 1ℚ → Σ c ꞉ ℚ , (p < c) × (c < q) × (c ≤ 1ℚ)
  I k = γ (ℚ-dense p q l)
   where
    γ : (Σ c ꞉ ℚ , (p < c) × (c < q)) → Σ c ꞉ ℚ , (p < c) × (c < q) × (c ≤ 1ℚ)
    γ (c , a , b) = c , a , b , ℚ≤-trans c q 1ℚ (ℚ<-coarser-than-≤ c q b) k

  II : 1ℚ ≤ q → Σ c ꞉ ℚ , (p < c) × (c < q) × (c ≤ 1ℚ)
  II k = γ (ℚ-dense p 1ℚ m)
   where
    γ : (Σ c ꞉ ℚ , (p < c) × (c < 1ℚ)) → Σ c ꞉ ℚ , (p < c) × (c < q) × (c ≤ 1ℚ)
    γ (c , a , b) = c , a , ℚ<-≤-trans c 1ℚ q b k , ℚ<-coarser-than-≤ c 1ℚ b

\end{code}

Products of negative rationals are monotone too, the other way.

\begin{code}

negation-times-negation : (p q : ℚ) → (- p) * (- q) ＝ p * q
negation-times-negation p q =
 (- p) * (- q) ＝⟨ ℚ-negation-dist-over-mult p (- q) ⟩
 - (p * (- q)) ＝⟨ ap -_ (ℚ-negation-dist-over-mult' p q) ⟩
 - (- (p * q)) ＝⟨ ℚ-minus-minus (p * q) ⁻¹ ⟩
 p * q         ∎

negative-gives-positive : (p : ℚ) → p < 0ℚ → 0ℚ < - p
negative-gives-positive p l =
 transport (0ℚ <_) {0ℚ - p} {(- p)} (zero-minus p)
  (ℚ<-difference-positive p 0ℚ l)

products-of-negatives-are-monotone
 : (b₀ b₁ c₀ c₁ : ℚ) → b₀ < 0ℚ → b₁ < 0ℚ → c₀ < b₀ → c₁ < b₁ → b₀ * b₁ < c₀ * c₁
products-of-negatives-are-monotone b₀ b₁ c₀ c₁ k₀ k₁ l₀ l₁ =
 transport₂ _<_ {(- b₀) * (- b₁)} {b₀ * b₁} {(- c₀) * (- c₁)} {c₀ * c₁}
  (negation-times-negation b₀ b₁) (negation-times-negation c₀ c₁)
  (products-of-positives-are-monotone (- b₀) (- b₁) (- c₀) (- c₁)
    (negative-gives-positive b₀ k₀) (negative-gives-positive b₁ k₁)
    (ℚ<-swap c₀ b₀ l₀) (ℚ<-swap c₁ b₁ l₁))

\end{code}

Squares of rationals beyond 1 or below -1 exceed 1. (An abstract block
for these facts made Agda take minutes; plain definitions check at
once.)

\begin{code}

minus-one-is-negation : -1ℚ ＝ - 1ℚ
minus-one-is-negation = refl

minus-one-is-negative : -1ℚ < 0ℚ
minus-one-is-negative =
 transport₂ _<_ {(- 1ℚ)} {(-1ℚ)} {(- 0ℚ)} {0ℚ} (minus-one-is-negation ⁻¹)
  (ℚ-minus-zero-is-zero ⁻¹) (ℚ<-swap 0ℚ 1ℚ 0<1)

minus-one-squared : -1ℚ * -1ℚ ＝ 1ℚ
minus-one-squared =
 ap₂ _*_ minus-one-is-negation minus-one-is-negation
 ∙ negation-times-negation 1ℚ 1ℚ
 ∙ ℚ-mult-left-id 1ℚ

square-above-one : (q : ℚ) → 1ℚ < q → 1ℚ < q * q
square-above-one q l =
 transport (_< q * q) {1ℚ * 1ℚ} {1ℚ} (ℚ-mult-left-id 1ℚ)
  (products-of-positives-are-monotone 1ℚ 1ℚ q q 0<1 0<1 l l)

square-below-minus-one : (q : ℚ) → q < -1ℚ → 1ℚ < q * q
square-below-minus-one q l =
 transport (_< q * q) {(-1ℚ * -1ℚ)} {1ℚ} minus-one-squared
  (products-of-negatives-are-monotone -1ℚ -1ℚ q q minus-one-is-negative
    minus-one-is-negative l l)

\end{code}

Products of rationals inside a symmetric interval: if |c₀| < M and
|c₁| < M then c₀ c₁ < M M; and rationals in (a , b) are below M in
absolute value if -a ≤ M and b ≤ M.

\begin{code}

abs-below : (a b c M : ℚ) → a < c → c < b → (- a) ≤ M → b ≤ M → abs c < M
abs-below a b c M l m k k' = ℚ<-to-abs c M (I , ℚ<-≤-trans c b M m k')
 where
  I : (- M) < c
  I = transport ((- M) <_) {(- (- c))} {c} (ℚ-minus-minus c ⁻¹)
       (ℚ<-swap (- c) M (ℚ<-≤-trans (- c) (- a) M (ℚ<-swap a c l) k))

products-below-square : (M c₀ c₁ : ℚ) → abs c₀ < M → abs c₁ < M
                      → c₀ * c₁ < M * M
products-below-square M c₀ c₁ l₀ l₁ =
 ℚ≤-<-trans (c₀ * c₁) (abs c₀ * M) (M * M)
  (ℚ≤-trans (c₀ * c₁) (abs c₀ * abs c₁) (abs c₀ * M)
    (transport (c₀ * c₁ ≤_) {abs (c₀ * c₁)} {abs c₀ * abs c₁}
      (abs-mult c₀ c₁ ⁻¹)
      (ℚ≤-abs-all (c₀ * c₁)))
    (left-multiplication-preserves-≤ (abs c₁) M (abs c₀)
      (ℚ<-coarser-than-≤ (abs c₁) M l₁)
      (ℚ-abs-is-positive c₀)))
  (ℚ<-pos-multiplication-preserves-order' (abs c₀) M M l₀
    (ℚ≤-<-trans 0ℚ (abs c₀) M (ℚ-abs-is-positive c₀) l₀))

max-below : (p q b : ℚ) → p < b → q < b → max p q < b
max-below p q b l m = Cases (max-to-≤ p q)
 (λ (_ , e) → transport (_< b) {q} {max p q} (e ⁻¹) m)
 (λ (_ , e) → transport (_< b) {p} {max p q} (e ⁻¹) l)

square-below-square : (M m : ℚ) → 0ℚ ≤ M → M < m → M * M < m * m
square-below-square M m k l =
 ℚ≤-<-trans (M * M) (M * m) (m * m)
  (left-multiplication-preserves-≤ M m M (ℚ<-coarser-than-≤ M m l) k)
  (ℚ<-pos-multiplication-preserves-order' M m m l (ℚ≤-<-trans 0ℚ M m k l))

\end{code}

Squares near a square, for the square root of real numbers
(gist.RealCohesion.RealSquareRoot, gate G14, step E4). A rational
q ≥ 0 with q² < p can be increased, and a rational q > 0 with p < q²
decreased, keeping its square on the same side of p: by
products-are-close, for a step δ from small-enough. And every rational
is at most the square of a positive rational. These are the facts on
rationals that the roundedness and inhabitedness of the cuts of the
square root use. They are abstract, so that Agda does not unfold the
rationals they provide where they are used (agda-unimath's
rounded-below-square-le-ℚ⁺, rounded-above-square-le-ℚ⁺ and square-le-ℚ⁺', in our
own proofs).

\begin{code}

min-above : (p q b : ℚ) → b < p → b < q → b < min p q
min-above p q b l m = Cases (min-to-≤ p q)
 (λ (_ , e) → transport (b <_) {p} {min p q} (e ⁻¹) l)
 (λ (_ , e) → transport (b <_) {q} {min p q} (e ⁻¹) m)

abstract
 negative-rounds-up : (p : ℚ) → p < 0ℚ → Σ p' ꞉ ℚ , (p < p') × (p' < 0ℚ)
 negative-rounds-up p l = ℚ-dense p 0ℚ l

 square-rounds-up : (q p : ℚ) → 0ℚ ≤ q → q * q < p
                  → Σ q' ꞉ ℚ , (q < q') × (q' * q' < p)
 square-rounds-up q p k l = q' , q<q' , bound
  where
   e : ℚ
   e = p - q * q

   e-is-positive : 0ℚ < e
   e-is-positive = ℚ<-difference-positive (q * q) p l

   M : ℚ
   M = q + 1ℚ

   q<M : q < M
   q<M = ℚ<-addition-preserves-order'' q 1ℚ 0<1

   M-is-nonneg : 0ℚ ≤ M
   M-is-nonneg = ℚ≤-trans 0ℚ q M k (ℚ<-coarser-than-≤ q M q<M)

   δ-data : Σ δ ꞉ ℚ , (0ℚ < δ) × (δ * M + M * δ < e)
   δ-data = small-enough M e M-is-nonneg e-is-positive

   δ : ℚ
   δ = pr₁ δ-data

   δ-is-positive : 0ℚ < δ
   δ-is-positive = pr₁ (pr₂ δ-data)

   between : Σ q' ꞉ ℚ , (q < q') × (q' < min (q + δ) M)
   between = ℚ-dense q (min (q + δ) M)
              (min-above (q + δ) M q
                (ℚ<-addition-preserves-order'' q δ δ-is-positive) q<M)

   q' : ℚ
   q' = pr₁ between

   q<q' : q < q'
   q<q' = pr₁ (pr₂ between)

   q'<q+δ : q' < q + δ
   q'<q+δ =
    ℚ<-≤-trans q' (min (q + δ) M) (q + δ) (pr₂ (pr₂ between)) (min≤ (q + δ) M)

   q'<M : q' < M
   q'<M = ℚ<-≤-trans q' (min (q + δ) M) M (pr₂ (pr₂ between)) (min≤' (q + δ) M)

   close : abs (q' - q) < δ
   close = ball-gives-abs q' q δ
            (ℚ<-trans (q - δ) q q'
              (ℚ<-subtraction-preserves-order q δ δ-is-positive) q<q')
            q'<q+δ

   q'-is-nonneg : 0ℚ ≤ q'
   q'-is-nonneg = ℚ≤-trans 0ℚ q q' k (ℚ<-coarser-than-≤ q q' q<q')

   I : abs q' ≤ M
   I = transport (_≤ M) (abs-of-pos-is-pos q' q'-is-nonneg ⁻¹)
        (ℚ<-coarser-than-≤ q' M q'<M)

   II : abs q ≤ M
   II = transport (_≤ M) (abs-of-pos-is-pos q k ⁻¹) (ℚ<-coarser-than-≤ q M q<M)

   III : abs (q' * q' - q * q) < e
   III = ℚ≤-<-trans (abs (q' * q' - q * q)) (δ * M + M * δ) e
          (products-are-close M δ q' q' q q I II close close) (pr₂ (pr₂ δ-data))

   bound : q' * q' < p
   bound = transport (q' * q' <_) (add-difference (q * q) p)
            (pr₂ (abs-gives-ball (q' * q') (q * q) e III))

 square-rounds-down : (q p : ℚ) → 0ℚ < q → p < q * q
                    → Σ q' ꞉ ℚ , (0ℚ < q') × (q' < q) × (p < q' * q')
 square-rounds-down q p k l = q' , q'-is-positive , q'<q , bound
  where
   e : ℚ
   e = q * q - p

   e-is-positive : 0ℚ < e
   e-is-positive = ℚ<-difference-positive p (q * q) l

   q-is-nonneg : 0ℚ ≤ q
   q-is-nonneg = ℚ<-coarser-than-≤ 0ℚ q k

   δ-data : Σ δ ꞉ ℚ , (0ℚ < δ) × (δ * q + q * δ < e)
   δ-data = small-enough q e q-is-nonneg e-is-positive

   δ : ℚ
   δ = pr₁ δ-data

   δ-is-positive : 0ℚ < δ
   δ-is-positive = pr₁ (pr₂ δ-data)

   q-δ<q : q - δ < q
   q-δ<q = ℚ<-subtraction-preserves-order q δ δ-is-positive

   between : Σ q' ꞉ ℚ , (max (q - δ) 0ℚ < q') × (q' < q)
   between = ℚ-dense (max (q - δ) 0ℚ) q (max-below (q - δ) 0ℚ q q-δ<q k)

   q' : ℚ
   q' = pr₁ between

   q'<q : q' < q
   q'<q = pr₂ (pr₂ between)

   q'-is-positive : 0ℚ < q'
   q'-is-positive =
    ℚ≤-<-trans 0ℚ (max (q - δ) 0ℚ) q' (max≤' (q - δ) 0ℚ) (pr₁ (pr₂ between))

   close : abs (q' - q) < δ
   close = ball-gives-abs q' q δ
            (ℚ≤-<-trans (q - δ) (max (q - δ) 0ℚ) q' (max≤ (q - δ) 0ℚ)
              (pr₁ (pr₂ between)))
            (ℚ<-trans q' q (q + δ) q'<q
              (ℚ<-addition-preserves-order'' q δ δ-is-positive))

   I : abs q' ≤ q
   I = transport (_≤ q) (abs-of-pos-is-pos' q' q'-is-positive ⁻¹)
        (ℚ<-coarser-than-≤ q' q q'<q)

   II : abs q ≤ q
   II = transport (_≤ q) (abs-of-pos-is-pos' q k ⁻¹) (ℚ≤-refl q)

   III : abs (q' * q' - q * q) < e
   III = ℚ≤-<-trans (abs (q' * q' - q * q)) (δ * q + q * δ) e
          (products-are-close q δ q' q' q q I II close close) (pr₂ (pr₂ δ-data))

   IV : q * q - e ＝ p
   IV = ap (_- e) (minus-zero (q * q) ⁻¹)
        ∙ difference-of-reflections (q * q) 0ℚ p ∙ minus-zero p

   bound : p < q' * q'
   bound =
    transport (_< q' * q') IV (pr₁ (abs-gives-ball (q' * q') (q * q) e III))

 square-above : (u : ℚ) → Σ m ꞉ ℚ , (0ℚ < m) × (u ≤ m * m)
 square-above u =
  max-one u , max-one-is-positive u ,
  ℚ≤-trans u (max-one u) (max-one u * max-one u) (max-one-≥-self u)
   (transport (_≤ max-one u * max-one u) (ℚ-mult-right-id (max-one u))
     (left-multiplication-preserves-≤ 1ℚ (max-one u) (max-one u)
       (max-one-≥-one u)
       (ℚ<-coarser-than-≤ 0ℚ (max-one u) (max-one-is-positive u))))

\end{code}

The product of a rational q with the reciprocal of max(1 , q) is at most
1, and is 1 where q ≥ 1. They give the inverse of positive real numbers
(gist.RealCohesion.RealReciprocal, gate G14, step E4).

\begin{code}

times-reciprocal-of-at-least-one : (q : ℚ) → 1ℚ ≤ q → q * reciprocal q ＝ 1ℚ
times-reciprocal-of-at-least-one q l =
 ℚ*-comm q (reciprocal q) ∙ reciprocal-times-self q l

times-reciprocal-≤-one : (q : ℚ) → q * reciprocal q ≤ 1ℚ
times-reciprocal-≤-one q = Cases (ℚ-dichotomous q 1ℚ) I II
 where
  I : q ≤ 1ℚ → q * reciprocal q ≤ 1ℚ
  I l = transport (_≤ 1ℚ)
         (ℚ-mult-right-id q ⁻¹ ∙ ap (q *_) (reciprocal-of-at-most-one q l ⁻¹)) l

  II : 1ℚ ≤ q → q * reciprocal q ≤ 1ℚ
  II l =
   transport (_≤ 1ℚ) (times-reciprocal-of-at-least-one q l ⁻¹) (ℚ≤-refl 1ℚ)

\end{code}
