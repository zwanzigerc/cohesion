Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 26 October 2026. See the AI disclosure in
gist.RealCohesion.index.

1-Lipschitz functions on the rationals.

A function f : ℚ → ℚ is 1-Lipschitz if |f x - f y| ≤ |x - y|. Such
functions extend to the reals (gist.RealCohesion.LipschitzExtension).
We record closure properties: compositions, translations, negation,
absolute value, the nonnegative part, the rescaling y ↦ f (2 y) / 2, and
the sum of two 1-Lipschitz functions of which one vanishes on |y| ≤ c
and the other on |y| ≥ c.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.RealCohesion.RationalLipschitz where

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.Order
open import UF.Base
open import Rationals.Abs
open import Rationals.Addition
open import Rationals.MinMax
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Type
open import gist.RealCohesion.RationalArithmetic

Lipschitz : (ℚ → ℚ) → 𝓤₀ ̇
Lipschitz f = (x y : ℚ) → abs (f x - f y) ≤ abs (x - y)

Lipschitz-ext : (f h : ℚ → ℚ) → ((y : ℚ) → f y ＝ h y) → Lipschitz h
              → Lipschitz f
Lipschitz-ext f h e l x y = transport₂ (λ a b → abs (a - b) ≤ abs (x - y))
                             (e x ⁻¹) (e y ⁻¹) (l x y)

\end{code}

Compositions, translations, negation and reflections.

\begin{code}

∘-Lipschitz : (f h : ℚ → ℚ) → Lipschitz f → Lipschitz h
            → Lipschitz (λ y → f (h y))
∘-Lipschitz f h lf lh x y =
 ℚ≤-trans (abs (f (h x) - f (h y))) (abs (h x - h y)) (abs (x - y))
                             (lf (h x) (h y)) (lh x y)

translation-is-Lipschitz : (c : ℚ) → Lipschitz (λ y → y + c)
translation-is-Lipschitz c x y = transport (λ w → abs w ≤ abs (x - y))
                                  (difference-of-translates x y c ⁻¹)
                                  (ℚ≤-refl (abs (x - y)))

negation-is-Lipschitz : Lipschitz (-_)
negation-is-Lipschitz x y = transport (_≤ abs (x - y)) I (ℚ≤-refl (abs (x - y)))
 where
  I : abs (x - y) ＝ abs ((- x) - (- y))
  I = ℚ-abs-neg-equals-pos (x - y) ∙ ap abs (difference-of-negations x y ⁻¹)

reflection-is-Lipschitz : (c : ℚ) → Lipschitz (λ y → c - y)
reflection-is-Lipschitz c x y =
 transport (_≤ abs (x - y)) I (ℚ≤-refl (abs (x - y)))
 where
  I : abs (x - y) ＝ abs ((c - x) - (c - y))
  I = abs-comm x y ∙ ap abs (difference-of-reflections c x y ⁻¹)

\end{code}

The absolute value and the nonnegative part.

\begin{code}

private
 one-side : (u v : ℚ) → abs u - abs v ≤ abs (u - v)
 one-side u v = transport (abs u - abs v ≤_)
                 (ℚ-inverse-intro'' (abs (u - v)) (abs v) ⁻¹)
                 (ℚ≤-addition-preserves-order (abs u) (abs (u - v) + abs v)
                   (- abs v) I)
  where
   I : abs u ≤ abs (u - v) + abs v
   I =
    transport (λ w → abs w ≤ abs (u - v) + abs v) (ℚ-inverse-intro'''' u v ⁻¹)
        (ℚ-triangle-inequality (u - v) v)

abs-is-Lipschitz : Lipschitz abs
abs-is-Lipschitz x y =
 ℚ≤-to-abs (abs x - abs y) (abs (x - y)) (II , one-side x y)
 where
  II : - abs (x - y) ≤ abs x - abs y
  II = transport₂ _≤_ (ap -_ (abs-comm y x)) (ℚ-minus-dist' (abs y) (abs x))
        (ℚ≤-swap (abs y - abs x) (abs (y - x)) (one-side y x))

nonneg-part-is-Lipschitz : Lipschitz nonneg-part
nonneg-part-is-Lipschitz x y = γ (max-to-≤ 0ℚ x) (max-to-≤ 0ℚ y)
 where
  γ : (0ℚ ≤ x) × (max 0ℚ x ＝ x) ∔ (x ≤ 0ℚ) × (max 0ℚ x ＝ 0ℚ)
    → (0ℚ ≤ y) × (max 0ℚ y ＝ y) ∔ (y ≤ 0ℚ) × (max 0ℚ y ＝ 0ℚ)
    → abs (nonneg-part x - nonneg-part y) ≤ abs (x - y)
  γ (inl (_ , e)) (inl (_ , e')) =
   transport₂ (λ a b → abs (a - b) ≤ abs (x - y)) (e ⁻¹) (e' ⁻¹)
    (ℚ≤-refl (abs (x - y)))
  γ (inl (l , e)) (inr (l' , e')) =
   transport₂ (λ a b → abs (a - b) ≤ abs (x - y)) (e ⁻¹) (e' ⁻¹) δ
   where
    δ : abs (x - 0ℚ) ≤ abs (x - y)
    δ = transport (_≤ abs (x - y))
         (abs-of-pos-is-pos x l ⁻¹ ∙ ap abs (minus-zero x ⁻¹))
         (ℚ≤-trans x (x - y) (abs (x - y))
           (ℚ≤-addition-preserves-order'' x (- y) (ℚ≤-swap' y l'))
           (ℚ≤-abs-all (x - y)))
  γ (inr (l , e)) (inl (l' , e')) =
   transport₂ (λ a b → abs (a - b) ≤ abs (x - y)) (e ⁻¹) (e' ⁻¹) δ
   where
    δ : abs (0ℚ - y) ≤ abs (x - y)
    δ = transport₂ _≤_
         (abs-of-pos-is-pos y l' ⁻¹ ∙ ℚ-abs-neg-equals-pos y
          ∙ ap abs (zero-minus y ⁻¹))
         (abs-comm y x)
         (ℚ≤-trans y (y - x) (abs (y - x))
           (ℚ≤-addition-preserves-order'' y (- x) (ℚ≤-swap' x l))
           (ℚ≤-abs-all (y - x)))
  γ (inr (_ , e)) (inr (_ , e')) =
   transport₂ (λ a b → abs (a - b) ≤ abs (x - y)) (e ⁻¹) (e' ⁻¹)
    (transport (_≤ abs (x - y))
      (ℚ-abs-zero ∙ ap abs (ℚ-inverse-sum-to-zero 0ℚ ⁻¹))
      (ℚ-abs-is-positive (x - y)))

\end{code}

Rescaling: if f is 1-Lipschitz, so is y ↦ f (y + y) / 2.

\begin{code}

rescaling-is-Lipschitz : (f : ℚ → ℚ) → Lipschitz f
                       → Lipschitz (λ y → half (f (y + y)))
rescaling-is-Lipschitz f l x y =
 transport₂ _≤_ I II (half-is-monotone (abs (f (x + x) - f (y + y)))
                                          (abs ((x + x) - (y + y)))
                                          (l (x + x) (y + y)))
 where
  I : half (abs (f (x + x) - f (y + y)))
    ＝ abs (half (f (x + x)) - half (f (y + y)))
  I = abs-of-half (f (x + x) - f (y + y)) ⁻¹
    ∙ ap abs (half-of-difference (f (x + x)) (f (y + y)))

  II : half (abs ((x + x) - (y + y))) ＝ abs (x - y)
  II = abs-of-half ((x + x) - (y + y)) ⁻¹
     ∙ ap abs (half-of-difference (x + x) (y + y)
               ∙ ap₂ _-_ (half-of-double x) (half-of-double y))

\end{code}

Gluing. Let φ and ψ be 1-Lipschitz, with φ y ＝ 0 when |y| ≤ c and
ψ y ＝ 0 when |y| ≥ c. Then φ + ψ is 1-Lipschitz: between a point inside
and a point outside the interval [- c , c] there is a point b with
|b| ＝ c, where both functions vanish, and the estimate goes through b.

\begin{code}

module _ (φ ψ : ℚ → ℚ) (c : ℚ)
         (lφ : Lipschitz φ) (lψ : Lipschitz ψ)
         (φ-vanishes : (y : ℚ) → abs y ≤ c → φ y ＝ 0ℚ)
         (ψ-vanishes : (y : ℚ) → c ≤ abs y → ψ y ＝ 0ℚ)
       where

 private
  F : ℚ → ℚ
  F y = φ y + ψ y

  inner : (u : ℚ) → abs u ≤ c → F u ＝ ψ u
  inner u l = ap (_+ ψ u) (φ-vanishes u l) ∙ ℚ-zero-left-neutral (ψ u)

  outer : (u : ℚ) → c ≤ abs u → F u ＝ φ u
  outer u l = ap (φ u +_) (ψ-vanishes u l) ∙ ℚ-zero-right-neutral (φ u)

  through : (u v b : ℚ) → φ b ＝ 0ℚ → ψ b ＝ 0ℚ
          → abs (ψ u - φ v) ≤ abs (u - b) + abs (b - v)
  through u v b e e' =
   ℚ≤-trans (abs (ψ u - φ v)) (abs (ψ u - 0ℚ) + abs (0ℚ - φ v))
    (abs (u - b) + abs (b - v))
    (ℚ-triangle-inequality' (ψ u) 0ℚ (φ v))
    (transport₂
      (λ s t → abs (ψ u - s) + abs (t - φ v) ≤ abs (u - b) + abs (b - v)) e' e
      (ℚ≤-adding (abs (ψ u - ψ b)) (abs (u - b)) (abs (φ b - φ v)) (abs (b - v))
        (lψ u b) (lφ b v)))

  mixed : (u v : ℚ) → abs u ≤ c → c ≤ abs v → abs (F u - F v) ≤ abs (u - v)
  mixed u v lu lv = transport₂ (λ s t → abs (s - t) ≤ abs (u - v))
                     (inner u lu ⁻¹) (outer v lv ⁻¹)
                     (γ (ℚ-dichotomous 0ℚ v))
   where
    c-nonneg : 0ℚ ≤ c
    c-nonneg = ℚ≤-trans 0ℚ (abs u) c (ℚ-abs-is-positive u) lu

    γ : (0ℚ ≤ v) ∔ (v ≤ 0ℚ) → abs (ψ u - φ v) ≤ abs (u - v)
    γ (inl l) = transport (abs (ψ u - φ v) ≤_) (I ∙ ℚ≤-to-abs' u v u≤v ⁻¹)
                 (through u v c (φ-vanishes c c≤c') (ψ-vanishes c c'≤c))
     where
      abs-c : abs c ＝ c
      abs-c = abs-of-pos-is-pos c c-nonneg

      c≤c' : abs c ≤ c
      c≤c' = transport (_≤ c) (abs-c ⁻¹) (ℚ≤-refl c)

      c'≤c : c ≤ abs c
      c'≤c = transport (c ≤_) (abs-c ⁻¹) (ℚ≤-refl c)

      u≤c : u ≤ c
      u≤c = ℚ≤-trans u (abs u) c (ℚ≤-abs-all u) lu

      c≤v : c ≤ v
      c≤v = transport (c ≤_) (abs-of-pos-is-pos v l) lv

      u≤v : u ≤ v
      u≤v = ℚ≤-trans u c v u≤c c≤v

      I : abs (u - c) + abs (c - v) ＝ v - u
      I = ap₂ _+_ (ℚ≤-to-abs' u c u≤c) (ℚ≤-to-abs' c v c≤v) ∙ telescope u c v

    γ (inr l) =
     transport (abs (ψ u - φ v) ≤_) (I ∙ ℚ≤-to-abs' v u v≤u ⁻¹ ∙ abs-comm v u)
                 (through u v (- c) (φ-vanishes (- c) c≤c')
                   (ψ-vanishes (- c) c'≤c))
     where
      abs-c : abs (- c) ＝ c
      abs-c = ℚ-abs-neg-equals-pos c ⁻¹ ∙ abs-of-pos-is-pos c c-nonneg

      c≤c' : abs (- c) ≤ c
      c≤c' = transport (_≤ c) (abs-c ⁻¹) (ℚ≤-refl c)

      c'≤c : c ≤ abs (- c)
      c'≤c = transport (c ≤_) (abs-c ⁻¹) (ℚ≤-refl c)

      abs-v : abs v ＝ - v
      abs-v = ℚ-abs-neg-equals-pos v ∙ abs-of-pos-is-pos (- v) (ℚ≤-swap' v l)

      v≤-c : v ≤ - c
      v≤-c = transport (_≤ - c) (ℚ-minus-minus v ⁻¹)
              (ℚ≤-swap c (- v) (transport (c ≤_) abs-v lv))

      -c≤u : - c ≤ u
      -c≤u = ℚ≤-trans (- c) (- abs u) u (ℚ≤-swap (abs u) c lu) (pr₁ (ℚ-abs-≤ u))

      v≤u : v ≤ u
      v≤u = ℚ≤-trans v (- c) u v≤-c -c≤u

      I : abs (u - (- c)) + abs ((- c) - v) ＝ u - v
      I = ap₂ _+_ (abs-comm u (- c) ∙ ℚ≤-to-abs' (- c) u -c≤u)
                  (abs-comm (- c) v ∙ ℚ≤-to-abs' v (- c) v≤-c)
        ∙ ℚ+-comm (u - (- c)) ((- c) - v)
        ∙ telescope v (- c) u

 glued-is-Lipschitz : Lipschitz (λ y → φ y + ψ y)
 glued-is-Lipschitz x y = γ (ℚ-dichotomous (abs x) c) (ℚ-dichotomous (abs y) c)
  where
   γ : (abs x ≤ c) ∔ (c ≤ abs x) → (abs y ≤ c) ∔ (c ≤ abs y)
     → abs (F x - F y) ≤ abs (x - y)
   γ (inl a) (inl b) = transport₂ (λ s t → abs (s - t) ≤ abs (x - y))
                        (inner x a ⁻¹) (inner y b ⁻¹) (lψ x y)
   γ (inr a) (inr b) = transport₂ (λ s t → abs (s - t) ≤ abs (x - y))
                        (outer x a ⁻¹) (outer y b ⁻¹) (lφ x y)
   γ (inl a) (inr b) = mixed x y a b
   γ (inr a) (inl b) =
    transport₂ _≤_ (abs-comm (F y) (F x)) (abs-comm y x) (mixed y x b a)

\end{code}
