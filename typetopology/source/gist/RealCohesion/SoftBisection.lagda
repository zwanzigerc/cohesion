Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 10 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Soft bisection and the normal form of the approximate intermediate
value theorem (lemmas B1–B6 of revision 3 of the formalization
blueprint [1]). Soft bisection is Claude Fable 5.2's, with GPT-6
Astra's gated reformulation. The two-case conclusion B6 is Fable's,
and it passed Astra's audit.

The normal form. Let g : ℝ → ℝ be any function with g 0 ≤ 1/3 and
2/3 ≤ g 1. If every map ℝ → Q is constant, where Q is the quotient of
levels by finite chains, then 0 < g x < 1 for some x.

 * The cut-off κ y := clamp₀¹ (3 (y - 1/3)) is 0 for y ≤ 1/3 and 1 for
   y ≥ 2/3, and σ y := min y (1 - y) is positive only for 0 < y < 1.
   The gate: for every real y, κ y ＝ 0, or κ y ＝ 1, or 1/4 < σ y, by
   cotransitivity at 1/4 < 1/3 and at 2/3 < 3/4.

 * Soft bisection with G := κ ∘ g: μ 0 := 1/2 and
   μ (n + 1) := μ n + Δ n (G (μ n)), where the step Δ n y is
   1/2 - y clamped to [- ρ (n + 1) , ρ (n + 1)], so that it is
   ρ (n + 1) when G (μ n) ＝ 0 and - ρ (n + 1) when G (μ n) ＝ 1. Put
   l n := μ n - ρ n and u n := μ n + ρ n, and let x⋆ be the limit of μ
   (B1). I n says that G (l n) ＝ 0 and G (u n) ＝ 1. I 0 holds (B2).
   By the gate at μ n, I n gives I (n + 1) or 1/4 < σ (g (μ n)) (B3),
   so for every n, I n holds or some μ k has 1/4 < σ (g (μ k)) (B4),
   which makes μ k a root (B5).

 * By cotransitivity, 1/4 < G x⋆ or G x⋆ < 3/4 (B6). In the first
   case, sequential hitting (gist.RealCohesion.SequentialHitting),
   applied to 4 G at x⋆ and the sequence l (j + 1), gives k with
   G (l (k + 1)) > 0, so I (k + 1) fails and B4 gives a root. In the
   second case the same holds with 4 (1 - G) and u (j + 1).

The step Δ n is a clamp, not 2⁻ⁿ⁻¹ (1 - 2 G (μ n)) as in [1]; only its
values at 0 and 1 and its bounds matter. As elsewhere, there is no
multiplication of reals; κ uses addition three times, and the factor
4 in B6 is two doublings.

[1] Formalization blueprint: the approximate IVT from Axiom R♭.
    Claude Fable 5.2, revision 3, 10 November 2026.
    references/F15-aivt-blueprint-rev3.md
    references/F16-aivt-handoff-rev4.md

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.SoftBisection
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import UF.Powerset
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealLattice fe pe pt
open import gist.RealCohesion.RationalArithmetic using (neg-is-negative)
open import gist.RealCohesion.RealLimits fe pe pt
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
open import gist.RealCohesion.SequentialHitting fe pe pt
 using (module sequential-hitting)

open PropositionalTruncation pt

\end{code}

Rational constants, checked by computation.

\begin{code}

private
 1/4<1/3 : 1/4 < 1/3
 1/4<1/3 = 0 , refl

 2/3<3/4 : 2/3 < 3/4
 2/3<3/4 = 0 , refl

 1/4<3/4 : 1/4 < 3/4
 1/4<3/4 = 7 , refl

 zero-tripled : (0ℚ ℚ+ 0ℚ) ℚ+ 0ℚ ＝ 0ℚ
 zero-tripled = refl

 third-tripled : (1/3 ℚ+ 1/3) ℚ+ 1/3 ＝ 1ℚ
 third-tripled = refl

 two-thirds-minus-a-third : 2/3 ℚ+ (ℚ- 1/3) ＝ 1/3
 two-thirds-minus-a-third = refl

 one-minus-a-quarter : 1ℚ ℚ- 1/4 ＝ 3/4
 one-minus-a-quarter = refl

 one-minus-zero : 1ℚ ℚ- 0ℚ ＝ 1ℚ
 one-minus-zero = refl

\end{code}

Tripling.

\begin{code}

triple : ℝ → ℝ
triple t = (t + t) + t

triple-≤ : (t : ℝ) (c : ℚ) → t ≤ ιₐ c → triple t ≤ ιₐ ((c ℚ+ c) ℚ+ c)
triple-≤ t c k = transport (λ r → triple t ≤ r)
                  (ap (_+ ιₐ c) (ιₐ-sum c c) ∙ ιₐ-sum (c ℚ+ c) c)
                  (sum-≤ (t + t) (ιₐ c + ιₐ c) t (ιₐ c)
                    (sum-≤ t (ιₐ c) t (ιₐ c) k k) k)

triple-≥ : (t : ℝ) (c : ℚ) → ιₐ c ≤ t → ιₐ ((c ℚ+ c) ℚ+ c) ≤ triple t
triple-≥ t c k = transport (λ r → r ≤ triple t)
                  (ap (_+ ιₐ c) (ιₐ-sum c c) ∙ ιₐ-sum (c ℚ+ c) c)
                  (sum-≤ (ιₐ c + ιₐ c) (t + t) (ιₐ c) t
                    (sum-≤ (ιₐ c) t (ιₐ c) t k k) k)

\end{code}

The cut-off κ, the success measure σ, and the gate.

\begin{code}

κ : ℝ → ℝ
κ y = clamp (ιₐ 0ℚ) (ιₐ 1ℚ) (triple (y + ιₐ (ℚ- 1/3)))

σ : ℝ → ℝ
σ y = min y (ιₐ 1ℚ + (- y))

κ-is-zero : (y : ℝ) → y ≤ ιₐ 1/3 → κ y ＝ ιₐ 0ℚ
κ-is-zero y k = clamp-below (ιₐ 0ℚ) (ιₐ 1ℚ) (triple (y + ιₐ (ℚ- 1/3)))
                 (transport (λ r → triple (y + ιₐ (ℚ- 1/3)) ≤ ιₐ r) zero-tripled
                   (triple-≤ (y + ιₐ (ℚ- 1/3)) 0ℚ I))
 where
  I : (y + ιₐ (ℚ- 1/3)) ≤ ιₐ 0ℚ
  I = transport (λ r → (y + ιₐ (ℚ- 1/3)) ≤ r)
       (ιₐ-sum 1/3 (ℚ- 1/3) ∙ ap ιₐ (ℚ-inverse-sum-to-zero 1/3))
       (sum-≤ y (ιₐ 1/3) (ιₐ (ℚ- 1/3)) (ιₐ (ℚ- 1/3)) k (ℝ≤-refl (ιₐ (ℚ- 1/3))))

κ-is-one : (y : ℝ) → ιₐ 2/3 ≤ y → κ y ＝ ιₐ 1ℚ
κ-is-one y k = clamp-above (ιₐ 0ℚ) (ιₐ 1ℚ) (triple (y + ιₐ (ℚ- 1/3)))
                (ιₐ-<-gives-≤ 0ℚ 1ℚ 0<1)
                (transport (λ r → ιₐ r ≤ triple (y + ιₐ (ℚ- 1/3))) third-tripled
                  (triple-≥ (y + ιₐ (ℚ- 1/3)) 1/3 I))
 where
  I : ιₐ 1/3 ≤ (y + ιₐ (ℚ- 1/3))
  I = transport (λ r → r ≤ (y + ιₐ (ℚ- 1/3)))
       (ιₐ-sum 2/3 (ℚ- 1/3) ∙ ap ιₐ two-thirds-minus-a-third)
       (sum-≤ (ιₐ 2/3) y (ιₐ (ℚ- 1/3)) (ιₐ (ℚ- 1/3)) k (ℝ≤-refl (ιₐ (ℚ- 1/3))))

gate : (y : ℝ) → ∥ (κ y ＝ ιₐ 0ℚ) ∔ (κ y ＝ ιₐ 1ℚ) ∔ (1/4 < σ y) ∥
gate y = ∥∥-rec ∥∥-is-prop γ (ℝ-locatedness y 1/4 1/3 1/4<1/3)
 where
  γ : (1/4 < y) ∔ (y < 1/3) → ∥ (κ y ＝ ιₐ 0ℚ) ∔ (κ y ＝ ιₐ 1ℚ) ∔ (1/4 < σ y) ∥
  γ (inr l) = ∣ inl (κ-is-zero y (<-gives-≤-ιₐ y 1/3 l)) ∣
  γ (inl l) = ∥∥-functor δ (ℝ-locatedness y 2/3 3/4 2/3<3/4)
   where
    δ : (2/3 < y) ∔ (y < 3/4) → (κ y ＝ ιₐ 0ℚ) ∔ (κ y ＝ ιₐ 1ℚ) ∔ (1/4 < σ y)
    δ (inl m) = inr (inl (κ-is-one y (>-gives-ιₐ-≤ y 2/3 m)))
    δ (inr m) = inr (inr (below-min y (ιₐ 1ℚ + (- y)) 1/4 l
                           (reflect-strict y 1/4 1ℚ
                             (transport (y <_) (one-minus-a-quarter ⁻¹) m))))

success : (y : ℝ) → 0ℚ < σ y → (0ℚ < y) × (y < 1ℚ)
success y l = below-min-left y (ιₐ 1ℚ + (- y)) 0ℚ l ,
              transport (y <_) one-minus-zero
               (below-reflect⁻¹ y 0ℚ 1ℚ
                 (below-min-right y (ιₐ 1ℚ + (- y)) 0ℚ l))

\end{code}

Soft bisection.

\begin{code}

module soft-bisection
        (g : ℝ → ℝ)
        (g-at-0 : κ (g (ιₐ 0ℚ)) ＝ ιₐ 0ℚ)
        (g-at-1 : κ (g (ιₐ 1ℚ)) ＝ ιₐ 1ℚ)
       where

 G : ℝ → ℝ
 G y = κ (g y)

 private
  ρ-succ-below-a-half : (n : ℕ) → ρ (succ n) < 1/2
  ρ-succ-below-a-half n = ℚ<-≤-trans (ρ (succ n)) (ρ n) 1/2 (ρ-decreases n)
                           (ρ-is-at-most-a-half n)

  -ρ≤ρ : (n : ℕ) → ιₐ (ℚ- ρ n) ≤ ιₐ (ρ n)
  -ρ≤ρ n = ιₐ-<-gives-≤ (ℚ- ρ n) (ρ n)
            (ℚ<-trans (ℚ- ρ n) 0ℚ (ρ n)
              (neg-is-negative (ρ n) (ρ-is-positive n))
              (ρ-is-positive n))

 Δ : ℕ → ℝ → ℝ
 Δ n y = clamp (ιₐ (ℚ- ρ (succ n))) (ιₐ (ρ (succ n))) (ιₐ 1/2 + (- y))

 Δ-at-zero : (n : ℕ) → Δ n (ιₐ 0ℚ) ＝ ιₐ (ρ (succ n))
 Δ-at-zero n =
  clamp-above (ιₐ (ℚ- ρ (succ n))) (ιₐ (ρ (succ n))) (ιₐ 1/2 + (- ιₐ 0ℚ))
                (-ρ≤ρ (succ n))
                (reflect-above (ιₐ 0ℚ) (ρ (succ n)) 1/2
                  (ιₐ-upper 0ℚ (1/2 ℚ- ρ (succ n))
                    (ℚ<-difference-positive (ρ (succ n)) 1/2
                      (ρ-succ-below-a-half n))))

 Δ-at-one : (n : ℕ) → Δ n (ιₐ 1ℚ) ＝ ιₐ (ℚ- ρ (succ n))
 Δ-at-one n =
  clamp-below (ιₐ (ℚ- ρ (succ n))) (ιₐ (ρ (succ n))) (ιₐ 1/2 + (- ιₐ 1ℚ))
               (reflect-below (ιₐ 1ℚ) (ℚ- ρ (succ n)) 1/2
                 (ιₐ-lower (1/2 ℚ- (ℚ- ρ (succ n))) 1ℚ
                   (transport₂ _<_ (ap (1/2 ℚ+_) (ℚ-minus-minus (ρ (succ n))))
                     1/2+1/2
                     (ℚ<-add-left 1/2 (ρ (succ n)) 1/2
                       (ρ-succ-below-a-half n)))))

 Δ-bounds : (n : ℕ) (y : ℝ)
          → (ιₐ (ℚ- ρ (succ n)) ≤ Δ n y) × (Δ n y ≤ ιₐ (ρ (succ n)))
 Δ-bounds n y =
  clamp-is-above-lo (ιₐ (ℚ- ρ (succ n))) (ιₐ (ρ (succ n))) (ιₐ 1/2 + (- y)) ,
                clamp-is-below-hi (ιₐ (ℚ- ρ (succ n))) (ιₐ (ρ (succ n)))
                 (ιₐ 1/2 + (- y))
                 (-ρ≤ρ (succ n))

 μ : ℕ → ℝ
 μ 0        = ιₐ 1/2
 μ (succ n) = μ n + Δ n (G (μ n))

 l u : ℕ → ℝ
 l n = μ n + ιₐ (ℚ- ρ n)
 u n = μ n + ιₐ (ρ n)

 μ-step : (n : ℕ) → within (ρ (succ n)) (μ n) (μ (succ n))
 μ-step n = within-from-bounds (ρ (succ n)) (μ n) (μ (succ n))
             (sum-≤ (μ n) (μ n) (ιₐ (ℚ- ρ (succ n))) (Δ n (G (μ n)))
               (ℝ≤-refl (μ n)) (pr₁ (Δ-bounds n (G (μ n)))))
             (sum-≤ (μ n) (μ n) (Δ n (G (μ n))) (ιₐ (ρ (succ n)))
               (ℝ≤-refl (μ n)) (pr₂ (Δ-bounds n (G (μ n)))))

 open geometric-limit μ μ-step renaming (lim to x⋆ ; lim-within to x⋆-within)

 l-within : (n : ℕ) → within (ρ n) (l n) (μ n)
 l-within n = within-sym (ρ n) (μ n) (l n)
               (within-from-bounds (ρ n) (μ n) (l n) (ℝ≤-refl (l n))
                 (sum-≤ (μ n) (μ n) (ιₐ (ℚ- ρ n)) (ιₐ (ρ n)) (ℝ≤-refl (μ n))
                   (-ρ≤ρ n)))

 u-within : (n : ℕ) → within (ρ n) (u n) (μ n)
 u-within n = within-sym (ρ n) (μ n) (u n)
               (within-from-bounds (ρ n) (μ n) (u n)
                 (sum-≤ (μ n) (μ n) (ιₐ (ℚ- ρ n)) (ιₐ (ρ n)) (ℝ≤-refl (μ n))
                   (-ρ≤ρ n))
                 (ℝ≤-refl (u n)))

 endpoints-converge : (v : ℕ → ℝ)
                    → ((n : ℕ) → within (ρ n) (v n) (μ n))
                    → (j : ℕ) → within (ρ j) (v (succ j)) x⋆
 endpoints-converge v c j =
  transport (λ ε → within ε (v (succ j)) x⋆) (ρ-halves j)
   (within-trans (ρ (succ j)) (ρ (succ j)) (v (succ j)) (μ (succ j)) x⋆
     (c (succ j))
      (within-sym (ρ (succ j)) x⋆ (μ (succ j)) (x⋆-within (succ j))))

\end{code}

The invariant, B2–B5.

\begin{code}

 I : ℕ → 𝓤₁ ̇
 I n = (G (l n) ＝ ιₐ 0ℚ) × (G (u n) ＝ ιₐ 1ℚ)

 I-at-zero : I 0
 I-at-zero =
  (ap G (ιₐ-sum 1/2 (ℚ- 1/2) ∙ ap ιₐ (ℚ-inverse-sum-to-zero 1/2)) ∙ g-at-0) ,
             (ap G (ιₐ-sum 1/2 1/2 ∙ ap ιₐ 1/2+1/2) ∙ g-at-1)

 I-step : (n : ℕ) → I n → ∥ I (succ n) ∔ (1/4 < σ (g (μ n))) ∥
 I-step n i = ∥∥-functor γ (gate (g (μ n)))
  where
   r : ℚ
   r = ρ (succ n)

   γ : (G (μ n) ＝ ιₐ 0ℚ) ∔ (G (μ n) ＝ ιₐ 1ℚ) ∔ (1/4 < σ (g (μ n)))
     → I (succ n) ∔ (1/4 < σ (g (μ n)))
   γ (inl e) = inl ((ap G l-is-μ ∙ e) , (ap G u-is-u ∙ pr₂ i))
    where
     μ-up : μ (succ n) ＝ μ n + ιₐ r
     μ-up = ap (λ y → μ n + Δ n y) e ∙ ap (μ n +_) (Δ-at-zero n)

     l-is-μ : l (succ n) ＝ μ n
     l-is-μ = ap (_+ ιₐ (ℚ- r)) μ-up
            ∙ translate-twice (μ n) r (ℚ- r)
            ∙ ap (λ s → μ n + ιₐ s) (ℚ-inverse-sum-to-zero r)
            ∙ plus-zero (μ n)

     u-is-u : u (succ n) ＝ u n
     u-is-u = ap (_+ ιₐ r) μ-up
            ∙ translate-twice (μ n) r r
            ∙ ap (λ s → μ n + ιₐ s) (ρ-halves n)
   γ (inr (inl e)) = inl ((ap G l-is-l ∙ pr₁ i) , (ap G u-is-μ ∙ e))
    where
     μ-down : μ (succ n) ＝ μ n + ιₐ (ℚ- r)
     μ-down = ap (λ y → μ n + Δ n y) e ∙ ap (μ n +_) (Δ-at-one n)

     u-is-μ : u (succ n) ＝ μ n
     u-is-μ = ap (_+ ιₐ r) μ-down
            ∙ translate-twice (μ n) (ℚ- r) r
            ∙ ap (λ s → μ n + ιₐ s) (ℚ-inverse-sum-to-zero' r)
            ∙ plus-zero (μ n)

     l-is-l : l (succ n) ＝ l n
     l-is-l = ap (_+ ιₐ (ℚ- r)) μ-down
            ∙ translate-twice (μ n) (ℚ- r) (ℚ- r)
            ∙ ap (λ s → μ n + ιₐ s) (ℚ-minus-dist r r ∙ ap ℚ-_ (ρ-halves n))
   γ (inr (inr s)) = inr s

 invariant-or-root : (n : ℕ) → I n ∨ (∃ k ꞉ ℕ , 1/4 < σ (g (μ k)))
 invariant-or-root 0        = ∣ inl I-at-zero ∣
 invariant-or-root (succ n) = ∥∥-rec ∨-is-prop γ (invariant-or-root n)
  where
   γ : I n ∔ (∃ k ꞉ ℕ , 1/4 < σ (g (μ k)))
     → I (succ n) ∨ (∃ k ꞉ ℕ , 1/4 < σ (g (μ k)))
   γ (inl i) = ∥∥-functor δ (I-step n i)
    where
     δ : I (succ n) ∔ (1/4 < σ (g (μ n)))
       → I (succ n) ∔ (∃ k ꞉ ℕ , 1/4 < σ (g (μ k)))
     δ (inl i') = inl i'
     δ (inr s)  = inr ∣ n , s ∣
   γ (inr x) = ∣ inr x ∣

 root-from-failure : (j : ℕ) → ¬ I j → ∃ k ꞉ ℕ , (0ℚ < g (μ k)) × (g (μ k) < 1ℚ)
 root-from-failure j f = ∥∥-rec ∃-is-prop γ (invariant-or-root j)
  where
   γ : I j ∔ (∃ k ꞉ ℕ , 1/4 < σ (g (μ k)))
     → ∃ k ꞉ ℕ , (0ℚ < g (μ k)) × (g (μ k) < 1ℚ)
   γ (inl i) = 𝟘-elim (f i)
   γ (inr x) = ∥∥-functor
                (λ (k , s) → k , success (g (μ k))
                                  (use-rounded-real-L (σ (g (μ k))) 0ℚ 1/4 0<1/4
                                    s))
                x

\end{code}

B6: the conclusion, by sequential hitting at x⋆.

\begin{code}

 module conclusion (ν : (k : ℝ → Q) (a b : ℝ) → k a ＝ k b) where

  root : ∃ k ꞉ ℕ , (0ℚ < g (μ k)) × (g (μ k) < 1ℚ)
  root = ∥∥-rec ∃-is-prop γ (ℝ-locatedness (G x⋆) 1/4 3/4 1/4<3/4)
   where
    γ : (1/4 < G x⋆) ∔ (G x⋆ < 3/4) → ∃ k ꞉ ℕ , (0ℚ < g (μ k)) × (g (μ k) < 1ℚ)
    γ (inl o) = ∥∥-rec ∃-is-prop δ
                 (sequential-hitting.sequential-hitting ν h x⋆
                   (λ j → l (succ j))
                   (endpoints-converge l l-within) h-at-x⋆)
     where
      h : ℝ → ℝ
      h y = double (double (G y))

      h-at-x⋆ : ιₐ 1ℚ ≤ h x⋆
      h-at-x⋆ = >-gives-ιₐ-≤ (h x⋆) 1ℚ
                 (transport (_< h x⋆) 1/2+1/2
                   (below-double (double (G x⋆)) 1/2
                     (transport (_< double (G x⋆)) 1/4+1/4
                       (below-double (G x⋆) 1/4 o))))

      δ : (Σ k ꞉ ℕ , 0ℚ < h (l (succ k)))
        → ∃ k ꞉ ℕ , (0ℚ < g (μ k)) × (g (μ k) < 1ℚ)
      δ (k , p) = root-from-failure (succ k) f
       where
        positive : 0ℚ < G (l (succ k))
        positive = double-is-positive⁻¹ (G (l (succ k)))
                    (double-is-positive⁻¹ (double (G (l (succ k)))) p)

        f : ¬ I (succ k)
        f i =
         ℚ<-irrefl 0ℚ (ιₐ-lower⁻¹ 0ℚ 0ℚ (transport (0ℚ <_) (pr₁ i) positive))

    γ (inr o) = ∥∥-rec ∃-is-prop δ
                 (sequential-hitting.sequential-hitting ν h x⋆
                   (λ j → u (succ j))
                   (endpoints-converge u u-within) h-at-x⋆)
     where
      h : ℝ → ℝ
      h y = double (double (ιₐ 1ℚ + (- G y)))

      h-at-x⋆ : ιₐ 1ℚ ≤ h x⋆
      h-at-x⋆ = >-gives-ιₐ-≤ (h x⋆) 1ℚ
                 (transport (_< h x⋆) 1/2+1/2
                   (below-double (double (ιₐ 1ℚ + (- G x⋆))) 1/2
                     (transport (_< double (ιₐ 1ℚ + (- G x⋆))) 1/4+1/4
                       (below-double (ιₐ 1ℚ + (- G x⋆)) 1/4
                         (reflect-strict (G x⋆) 1/4 1ℚ
                           (transport (G x⋆ <_) (one-minus-a-quarter ⁻¹) o))))))

      δ : (Σ k ꞉ ℕ , 0ℚ < h (u (succ k)))
        → ∃ k ꞉ ℕ , (0ℚ < g (μ k)) × (g (μ k) < 1ℚ)
      δ (k , p) = root-from-failure (succ k) f
       where
        below-one : G (u (succ k)) < 1ℚ
        below-one = transport (G (u (succ k)) <_) one-minus-zero
                     (below-reflect⁻¹ (G (u (succ k))) 0ℚ 1ℚ
                       (double-is-positive⁻¹ (ιₐ 1ℚ + (- G (u (succ k))))
                         (double-is-positive⁻¹
                           (double (ιₐ 1ℚ + (- G (u (succ k))))) p)))

        f : ¬ I (succ k)
        f i =
         ℚ<-irrefl 1ℚ (ιₐ-upper⁻¹ 1ℚ 1ℚ (transport (_< 1ℚ) (pr₂ i) below-one))

\end{code}

The normal form, in the form of the type Normal-Form of the starter
module of the handoff, with TypeTopology's ι, 0ℝ and 1ℝ. The
conversions between ι and ιₐ, and between comparisons with rationals
and the strict order of reals, are separate lemmas.

\begin{code}

normal-form-at-0 : (g : ℝ → ℝ) → g 0ℝ ≤ ι 1/3 → κ (g (ιₐ 0ℚ)) ＝ ιₐ 0ℚ
normal-form-at-0 g k = κ-is-zero (g (ιₐ 0ℚ))
                        (transport₂ _≤_ (ap g (ιₐ-zero-is-0ℝ ⁻¹))
                          (ιₐ-is-ι 1/3 ⁻¹) k)

normal-form-at-1 : (g : ℝ → ℝ) → ι 2/3 ≤ g 1ℝ → κ (g (ιₐ 1ℚ)) ＝ ιₐ 1ℚ
normal-form-at-1 g k' = κ-is-one (g (ιₐ 1ℚ))
                         (transport₂ _≤_ (ιₐ-is-ι 2/3 ⁻¹) (ap g (ιₐ-is-ι 1ℚ ⁻¹))
                           k')

between-0ℝ-and-1ℝ : (y : ℝ) → 0ℚ < y → y < 1ℚ → (0ℝ < y) × (y < 1ℝ)
between-0ℝ-and-1ℝ y m m' =
 ∥∥-functor δ (rounded-left-d y 0ℚ m) ,
 ∥∥-functor δ' (rounded-right-b (upper-cut-of y) (rounded-from-real-R y) 1ℚ m')
 where
  δ : (Σ q ꞉ ℚ , (0ℚ < q) × (q < y)) → Σ q ꞉ ℚ , (0ℝ < q) × (q < y)
  δ (q , o , o') = q , transport (_< q) ιₐ-zero-is-0ℝ (ιₐ-upper 0ℚ q o) , o'

  δ' : (Σ q ꞉ ℚ , (q < 1ℚ) × (y < q)) → Σ q ꞉ ℚ , (y < q) × (q < 1ℝ)
  δ' (q , r , r') = q , r' , transport (q <_) (ιₐ-is-ι 1ℚ) (ιₐ-lower q 1ℚ r)

normal-form : ((k : ℝ → Q) (a b : ℝ) → k a ＝ k b)
            → (g : ℝ → ℝ)
            → g 0ℝ ≤ ι 1/3
            → ι 2/3 ≤ g 1ℝ
            → ∃ x ꞉ ℝ , (0ℝ < g x) × (g x < 1ℝ)
normal-form ν g k k' =
 ∥∥-functor γ (soft-bisection.conclusion.root g (normal-form-at-0 g k)
                (normal-form-at-1 g k') ν)
 where
  μ : ℕ → ℝ
  μ = soft-bisection.μ g (normal-form-at-0 g k) (normal-form-at-1 g k')

  γ : (Σ n ꞉ ℕ , (0ℚ < g (μ n)) × (g (μ n) < 1ℚ))
    → Σ x ꞉ ℝ , (0ℝ < g x) × (g x < 1ℝ)
  γ (n , m , m') = μ n , between-0ℝ-and-1ℝ (g (μ n)) m m'

\end{code}
