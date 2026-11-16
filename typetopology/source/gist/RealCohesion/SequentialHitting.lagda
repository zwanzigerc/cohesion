Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 10 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Sequential hitting (GPT-6 Astra; lemmas H1–H7 of revision 3 of the
formalization blueprint [1]).

Let h : ℝ → ℝ be any function, a any point with 1 ≤ h a, and z any
sequence with z j within 2⁻⁽ʲ⁺¹⁾ of a, none of them crisp. If every
map ℝ → Q is constant, where Q is the quotient of levels by finite
chains (gist.RealCohesion.FiniteChainQuotient), then h is positive at
some z k. This is the positive form of the statement that h cannot
vanish along a convergent sequence and be nonzero at the limit; it
produces an index, which without Markov's principle is more.

The proof runs a soft graph on the alternating sequence q of points
z, a, z, a, … and feeds the outcome to the finite-chain lemma
(gist.RealCohesion.FiniteChainLemma).

 * q n is a for odd n and z (n + 3) for even n, so that q n is within
   hgt n := ρ (n + 3) of a. e n is h (q n) for even n and 0 for odd n.
   v 0 := 0 and v (n + 1) := max (2 v n) (2 e (n + 1)). So v is
   nonnegative and increasing, v (n + 1) ≥ 2 v n, and v n > 0 gives an
   even index where h is positive (H1, H2).

 * w is the limit of clamped steps from a towards q n, with step size
   B n (v n) ∈ [0 , hgt n], where B n is a tent function of height
   hgt n on the band 1/3 < v < 1/2, vanishing outside (1/4 , 2/3). If
   v n is in the band then w ＝ q n: the earlier v m are below 1/4 and
   the later ones above 2/3, so the other steps are zero (H3, the
   plateau identity).

 * By cotransitivity, 1/3 < h w or h w < 2/3 (H4). In the first case
   no even n has v n in the band, since then h w ＝ e n < 1/4; in the
   second no odd n has, since then h w ＝ h a ≥ 1. So, for the
   indices n of the remaining parity p, whether v n < 1/2 or
   1/3 < v n is decidable, and it is monotone in n.

 * The depth c j is this decision at the least index N j ≥ j of
   parity p. It is monotone, and c j ＝ ₀ gives e j < 1/4 for even j
   (H5).

 * ψ is the limit of clamped steps from a towards q j, with step sizes
   C j s, bumps of height ρ (j + 2) on the plateaus of the
   finite-chain lemma, (α j , β j) with α j = 5/8 · 2⁻ʲ and
   β j = 7/8 · 2⁻ʲ. On the plateau of index j ≥ 1, ψ s ＝ q j (H6).

 * Γ := h ∘ ψ is at least 1 on the odd plateaus and, where c j ＝ ₀,
   below 1/4 on the even ones. So A := {Γ < 2/3} misses the odd
   plateaus, D := {1/3 < Γ} misses the even plateaus of depth ₀, and
   A and D cover ℝ. The finite-chain lemma gives j with c j ＝ ₁, so
   1/3 < v (N j), and H2 gives the hit (H7).

The heights, parity and plateaus are in gist.RealCohesion.Plateaus,
and ψ is the plateau path of gist.RealCohesion.PlateauPath, applied to
q; both were first written in this module, which re-exports them, so
that its names are unchanged.

The step functions are clamps rather than products, so no
multiplication of reals is needed, and their slopes are 1, so no
scaling either (gist.RealCohesion.RealLattice). As there, we use
--lossy-unification and the abstract embedding ιₐ.

The indices differ from [1], where q n is z n for even n and the
bumps have slope 8 · 2ʲ. Here the deeper points z (n + 3) let the
bumps have slope 1.

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

module gist.RealCohesion.SequentialHitting
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import MLTT.Two-Properties
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Order hiding (max)
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import UF.Powerset hiding (complement)
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import Rationals.Limits fe pe pt using (⟨1/2⟩^_)
open import DedekindReals.Addition fe pe pt using () renaming (_+_ to _+ᵗ_)
open import gist.RealCohesion.RationalArithmetic
 using (minus-zero ; monotone-from-steps)
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealOrder fe pe pt using (not-below-and-above)
open import gist.RealCohesion.RealLattice fe pe pt
open import gist.RealCohesion.RealLimits fe pe pt
open import gist.RealCohesion.FiniteChainLevels
open import gist.RealCohesion.FiniteChainQuotient fe pe pt
open import gist.RealCohesion.FiniteChainLemma fe pe pt
open import gist.RealCohesion.Plateaus fe pe pt public
open import gist.RealCohesion.PlateauPath fe pe pt using (module plateau-path)
open import gist.RealCohesion.ApproximateIVTStatement fe pe pt
 using (2⁻ ; Sequential-Hitting)

open PropositionalTruncation pt

\end{code}

Rational constants and their comparisons, all checked by computation.

\begin{code}

private
 1/4<1/3 : 1/4 < 1/3
 1/4<1/3 = 0 , refl

 1/3<1/2 : 1/3 < 1/2
 1/3<1/2 = 0 , refl

 1/3<2/3 : 1/3 < 2/3
 1/3<2/3 = 2 , refl

 2/3<1 : 2/3 < 1ℚ
 2/3<1 = 0 , refl

 band-left : ρ 3 ℚ+ 1/4 ≤ 1/3
 band-left = 1 , refl

 band-right : 1/2 ≤ 2/3 ℚ- ρ 3
 band-right = 10 , refl

\end{code}

The data of sequential hitting.

\begin{code}

module sequential-hitting
        (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v)
        (h : ℝ → ℝ)
        (a : ℝ)
        (z : ℕ → ℝ)
        (z-converges : (j : ℕ) → within (ρ j) (z j) a)
        (h-at-a : ιₐ 1ℚ ≤ h a)
       where

\end{code}

H1. The alternating points q, the values e, and the soft graph v.

\begin{code}

 q' : 𝟚 → ℕ → ℝ
 q' ₀ n = z (n +ℕ 3)
 q' ₁ n = a

 q : ℕ → ℝ
 q n = q' (parity n) n

 e' : 𝟚 → ℕ → ℝ
 e' ₀ n = h (z (n +ℕ 3))
 e' ₁ n = ιₐ 0ℚ

 e : ℕ → ℝ
 e n = e' (parity n) n

 v : ℕ → ℝ
 v 0        = ιₐ 0ℚ
 v (succ n) = max (double (v n)) (double (e (succ n)))

 q-is-close : (n : ℕ) → within (hgt n) (q n) a
 q-is-close n = I (parity n)
  where
   I : (b : 𝟚) → within (hgt n) (q' b n) a
   I ₀ = z-converges (n +ℕ 3)
   I ₁ =
    within-refl (hgt n) a (ℚ<-coarser-than-≤ 0ℚ (hgt n) (hgt-is-positive n))

 q-of-odd : (n : ℕ) → parity n ＝ ₁ → q n ＝ a
 q-of-odd n p = ap (λ b → q' b n) p

 h-of-q-of-even : (n : ℕ) → parity n ＝ ₀ → h (q n) ＝ e n
 h-of-q-of-even n p = transport (λ b → h (q' b n) ＝ e' b n) (p ⁻¹) refl

 v-doubles : (n : ℕ) → double (v n) ≤ v (succ n)
 v-doubles n = ≤-max-left (double (v n)) (double (e (succ n)))

 v-above-e : (n : ℕ) → double (e (succ n)) ≤ v (succ n)
 v-above-e n = ≤-max-right (double (v n)) (double (e (succ n)))

 v-is-nonneg : (n : ℕ) → ιₐ 0ℚ ≤ v n
 v-is-nonneg 0        = ℝ≤-refl (ιₐ 0ℚ)
 v-is-nonneg (succ n) = ℝ≤-trans (ιₐ 0ℚ) (v n) (v (succ n)) (v-is-nonneg n)
                         (ℝ≤-trans (v n) (double (v n)) (v (succ n))
                           (nonneg-below-double (v n) (v-is-nonneg n))
                            (v-doubles n))

 v-increases : (n : ℕ) → v n ≤ v (succ n)
 v-increases n = ℝ≤-trans (v n) (double (v n)) (v (succ n))
                  (nonneg-below-double (v n) (v-is-nonneg n)) (v-doubles n)

 v-is-monotone : (k n : ℕ) → k ≤ℕ n → v k ≤ v n
 v-is-monotone =
  monotone-from-steps (λ x y → x ≤ y) ℝ≤-refl ℝ≤-trans v v-increases

 e-below-a-quarter : (n : ℕ) → v (succ n) < 1/2 → e (succ n) < 1/4
 e-below-a-quarter n l =
  double-below⁻¹ (e (succ n)) 1/4
   (transport (double (e (succ n)) <_) (1/4+1/4 ⁻¹)
     (≤-<-trans-ℚ (double (e (succ n))) (v (succ n)) 1/2 (v-above-e n) l))

\end{code}

H2. A positive value of v gives a hit.

\begin{code}

 positive-e-gives-hit : (b : 𝟚) (n : ℕ) → 0ℚ < e' b n → ∃ k ꞉ ℕ , 0ℚ < h (z k)
 positive-e-gives-hit ₀ n l = ∣ n +ℕ 3 , l ∣
 positive-e-gives-hit ₁ n l = 𝟘-elim (ℚ<-irrefl 0ℚ (ιₐ-lower⁻¹ 0ℚ 0ℚ l))

 positive-v-gives-hit : (n : ℕ) → 0ℚ < v n → ∃ k ꞉ ℕ , 0ℚ < h (z k)
 positive-v-gives-hit 0        l = 𝟘-elim (ℚ<-irrefl 0ℚ (ιₐ-lower⁻¹ 0ℚ 0ℚ l))
 positive-v-gives-hit (succ n) l =
  ∥∥-rec ∃-is-prop γ (below-max (double (v n)) (double (e (succ n))) 0ℚ l)
  where
   γ : (0ℚ < double (v n)) ∔ (0ℚ < double (e (succ n)))
     → ∃ k ꞉ ℕ , 0ℚ < h (z k)
   γ (inl k) = positive-v-gives-hit n (double-is-positive⁻¹ (v n) k)
   γ (inr k) = positive-e-gives-hit (parity (succ n)) (succ n)
                (double-is-positive⁻¹ (e (succ n)) k)

\end{code}

The band function B n of height hgt n and its negative B⁻ n.

\begin{code}

 B B⁻ : ℕ → ℝ → ℝ
 B n t = clamp (ιₐ 0ℚ) (ιₐ (hgt n)) (min (t + ιₐ (ℚ- 1/4)) (ιₐ 2/3 + (- t)))
 B⁻ n t = clamp (ιₐ (ℚ- hgt n)) (ιₐ 0ℚ) (max (ιₐ 1/4 + (- t)) (t + ιₐ (ℚ- 2/3)))

 private
  0≤hgt : (n : ℕ) → ιₐ 0ℚ ≤ ιₐ (hgt n)
  0≤hgt n = ιₐ-<-gives-≤ 0ℚ (hgt n) (hgt-is-positive n)

  -hgt≤0 : (n : ℕ) → ιₐ (ℚ- hgt n) ≤ ιₐ 0ℚ
  -hgt≤0 n =
   ιₐ-<-gives-≤ (ℚ- hgt n) 0ℚ (neg-is-negative (hgt n) (hgt-is-positive n))

  above-band-left : (n : ℕ) (t : ℝ) → 1/3 < t → (hgt n ℚ+ 1/4) < t
  above-band-left n t l = use-rounded-real-L' t (hgt n ℚ+ 1/4) 1/3
                           (ℚ≤-trans (hgt n ℚ+ 1/4) (ρ 3 ℚ+ 1/4) 1/3
                             (ℚ≤-addition-preserves-order (hgt n) (ρ 3) 1/4
                               (hgt-is-small n))
                             band-left)
                           l

  below-band-right : (n : ℕ) (t : ℝ) → t < 1/2 → t < 2/3 ℚ- hgt n
  below-band-right n t l = use-rounded-real-R' t 1/2 (2/3 ℚ- hgt n)
                            (ℚ≤-trans 1/2 (2/3 ℚ- ρ 3) (2/3 ℚ- hgt n) band-right
                              (minus-is-antitone 2/3 (hgt n) (ρ 3)
                                (hgt-is-small n)))
                            l

 B-in-band : (n : ℕ) (t : ℝ) → 1/3 < t → t < 1/2 → B n t ＝ ιₐ (hgt n)
 B-in-band n t l l' =
  clamp-above (ιₐ 0ℚ) (ιₐ (hgt n)) (min (t + ιₐ (ℚ- 1/4)) (ιₐ 2/3 + (- t)))
   (0≤hgt n)
   (≤-min (t + ιₐ (ℚ- 1/4)) (ιₐ 2/3 + (- t)) (ιₐ (hgt n))
     (translate-above t (hgt n) 1/4 (above-band-left n t l))
     (reflect-above t (hgt n) 2/3 (below-band-right n t l')))

 B⁻-in-band : (n : ℕ) (t : ℝ) → 1/3 < t → t < 1/2 → B⁻ n t ＝ ιₐ (ℚ- hgt n)
 B⁻-in-band n t l l' =
  clamp-below (ιₐ (ℚ- hgt n)) (ιₐ 0ℚ) (max (ιₐ 1/4 + (- t)) (t + ιₐ (ℚ- 2/3)))
   (max-≤ (ιₐ 1/4 + (- t)) (t + ιₐ (ℚ- 2/3)) (ιₐ (ℚ- hgt n))
     (reflect-below t (ℚ- hgt n) 1/4
       (transport (_< t)
         (ℚ+-comm (hgt n) 1/4 ∙ ap (1/4 ℚ+_) (ℚ-minus-minus (hgt n)))
         (above-band-left n t l)))
     (translate-below t (ℚ- hgt n) 2/3
       (transport (t <_) (ℚ+-comm 2/3 (ℚ- hgt n)) (below-band-right n t l'))))

 B-below-band : (n : ℕ) (t : ℝ) → t < 1/4 → (B n t ＝ ιₐ 0ℚ) × (B⁻ n t ＝ ιₐ 0ℚ)
 B-below-band n t l = I , II
  where
   I : B n t ＝ ιₐ 0ℚ
   I = clamp-below (ιₐ 0ℚ) (ιₐ (hgt n)) (min (t + ιₐ (ℚ- 1/4)) (ιₐ 2/3 + (- t)))
        (ℝ≤-trans (min (t + ιₐ (ℚ- 1/4)) (ιₐ 2/3 + (- t))) (t + ιₐ (ℚ- 1/4))
          (ιₐ 0ℚ)
          (min-≤-left (t + ιₐ (ℚ- 1/4)) (ιₐ 2/3 + (- t)))
          (translate-below t 0ℚ 1/4
            (transport (t <_) (ℚ-zero-left-neutral 1/4 ⁻¹) l)))

   II : B⁻ n t ＝ ιₐ 0ℚ
   II =
    clamp-above (ιₐ (ℚ- hgt n)) (ιₐ 0ℚ) (max (ιₐ 1/4 + (- t)) (t + ιₐ (ℚ- 2/3)))
         (-hgt≤0 n)
         (ℝ≤-trans (ιₐ 0ℚ) (ιₐ 1/4 + (- t))
           (max (ιₐ 1/4 + (- t)) (t + ιₐ (ℚ- 2/3)))
           (reflect-above t 0ℚ 1/4 (transport (t <_) (minus-zero 1/4 ⁻¹) l))
           (≤-max-left (ιₐ 1/4 + (- t)) (t + ιₐ (ℚ- 2/3))))

 B-above-band : (n : ℕ) (t : ℝ) → 2/3 < t → (B n t ＝ ιₐ 0ℚ) × (B⁻ n t ＝ ιₐ 0ℚ)
 B-above-band n t l = I , II
  where
   I : B n t ＝ ιₐ 0ℚ
   I = clamp-below (ιₐ 0ℚ) (ιₐ (hgt n)) (min (t + ιₐ (ℚ- 1/4)) (ιₐ 2/3 + (- t)))
        (ℝ≤-trans (min (t + ιₐ (ℚ- 1/4)) (ιₐ 2/3 + (- t))) (ιₐ 2/3 + (- t))
          (ιₐ 0ℚ)
          (min-≤-right (t + ιₐ (ℚ- 1/4)) (ιₐ 2/3 + (- t)))
          (reflect-below t 0ℚ 2/3 (transport (_< t) (minus-zero 2/3 ⁻¹) l)))

   II : B⁻ n t ＝ ιₐ 0ℚ
   II =
    clamp-above (ιₐ (ℚ- hgt n)) (ιₐ 0ℚ) (max (ιₐ 1/4 + (- t)) (t + ιₐ (ℚ- 2/3)))
         (-hgt≤0 n)
         (ℝ≤-trans (ιₐ 0ℚ) (t + ιₐ (ℚ- 2/3))
           (max (ιₐ 1/4 + (- t)) (t + ιₐ (ℚ- 2/3)))
           (translate-above t 0ℚ 2/3
             (transport (_< t) (ℚ-zero-left-neutral 2/3 ⁻¹) l))
           (≤-max-right (ιₐ 1/4 + (- t)) (t + ιₐ (ℚ- 2/3))))

 B-bounds : (n : ℕ) (t : ℝ)
          → (ιₐ (ℚ- hgt n) ≤ B⁻ n t) × (B⁻ n t ≤ B n t) × (B n t ≤ ιₐ (hgt n))
 B-bounds n t = clamp-is-above-lo (ιₐ (ℚ- hgt n)) (ιₐ 0ℚ) T⁻ ,
                ℝ≤-trans (B⁻ n t) (ιₐ 0ℚ) (B n t)
                 (clamp-is-below-hi (ιₐ (ℚ- hgt n)) (ιₐ 0ℚ) T⁻ (-hgt≤0 n))
                 (clamp-is-above-lo (ιₐ 0ℚ) (ιₐ (hgt n)) T) ,
                clamp-is-below-hi (ιₐ 0ℚ) (ιₐ (hgt n)) T (0≤hgt n)
  where
   T T⁻ : ℝ
   T  = min (t + ιₐ (ℚ- 1/4)) (ιₐ 2/3 + (- t))
   T⁻ = max (ιₐ 1/4 + (- t)) (t + ιₐ (ℚ- 2/3))

\end{code}

H3. The point w, and the plateau identity.

\begin{code}

 W : ℕ → ℝ
 W 0        = a
 W (succ n) =
  clamped-step (W n) (B⁻ (succ n) (v (succ n))) (B (succ n) (v (succ n)))
               (q (succ n))

 W-step : (n : ℕ) → within (ρ (succ n)) (W n) (W (succ n))
 W-step n = within-weaken (hgt (succ n)) (ρ (succ n)) (W n) (W (succ n))
             (hgt-below-ρ (succ n))
             (clamped-step-within (hgt (succ n)) (W n)
               (B⁻ (succ n) (v (succ n))) (B (succ n) (v (succ n))) (q (succ n))
               (pr₁ (B-bounds (succ n) (v (succ n))))
               (pr₁ (pr₂ (B-bounds (succ n) (v (succ n)))))
               (pr₂ (pr₂ (B-bounds (succ n) (v (succ n))))))

 open geometric-limit W W-step
  renaming (lim to w ; lim-of-eventually-constant to w-of)

 plateau-identity : (n : ℕ) → 1/3 < v (succ n) → v (succ n) < 1/2
                  → w ＝ q (succ n)
 plateau-identity n l l' = w-of (q (succ n)) (succ n) after
  where
   v-n-small : v n < 1/4
   v-n-small = double-below⁻¹ (v n) 1/4
                (transport (double (v n) <_) (1/4+1/4 ⁻¹)
                  (≤-<-trans-ℚ (double (v n)) (v (succ n)) 1/2 (v-doubles n)
                    l'))

   before : (k : ℕ) → k ≤ℕ n → W k ＝ a
   before 0        _ = refl
   before (succ k) i =
    clamped-step-of-zero (W k) (B⁻ (succ k) (v (succ k)))
     (B (succ k) (v (succ k)))
     (q (succ k)) (pr₂ vanish) (pr₁ vanish)
    ∙ before k (≤-trans k (succ k) n (≤-succ k) i)
    where
     small : v (succ k) < 1/4
     small =
      ≤-<-trans-ℚ (v (succ k)) (v n) 1/4 (v-is-monotone (succ k) n i) v-n-small

     vanish : (B (succ k) (v (succ k)) ＝ ιₐ 0ℚ)
            × (B⁻ (succ k) (v (succ k)) ＝ ιₐ 0ℚ)
     vanish = B-below-band (succ k) (v (succ k)) small

   at : W (succ n) ＝ q (succ n)
   at = ap
    (λ x → clamped-step x (B⁻ (succ n) (v (succ n))) (B (succ n) (v (succ n)))
            (q (succ n)))
           (before n (≤-refl n))
      ∙ clamped-step-full (hgt (succ n)) a
         (B⁻ (succ n) (v (succ n))) (B (succ n) (v (succ n))) (q (succ n))
         (B⁻-in-band (succ n) (v (succ n)) l l')
          (B-in-band (succ n) (v (succ n)) l l')
         (within-sym (hgt (succ n)) (q (succ n)) a (q-is-close (succ n)))

   v-after-large : (d : ℕ) → 2/3 < v (succ (succ n +ℕ d))
   v-after-large d =
    <-≤-trans-ℚ (v (succ (succ n))) (v (succ (succ n +ℕ d))) 2/3
                      (<-≤-trans-ℚ (double (v (succ n))) (v (succ (succ n))) 2/3
                        (transport (_< double (v (succ n))) 1/3+1/3
                          (below-double (v (succ n)) 1/3 l))
                        (v-doubles (succ n)))
                      (v-is-monotone (succ (succ n)) (succ (succ n +ℕ d))
                        (≤-+ (succ n) d))

   after : (d : ℕ) → W (succ n +ℕ d) ＝ q (succ n)
   after 0        = at
   after (succ d) =
    clamped-step-of-zero (W (succ n +ℕ d))
     (B⁻ (succ (succ n +ℕ d)) (v (succ (succ n +ℕ d))))
     (B (succ (succ n +ℕ d)) (v (succ (succ n +ℕ d))))
     (q (succ (succ n +ℕ d))) (pr₂ vanish) (pr₁ vanish)
    ∙ after d
    where
     vanish : (B (succ (succ n +ℕ d)) (v (succ (succ n +ℕ d))) ＝ ιₐ 0ℚ)
          × (B⁻ (succ (succ n +ℕ d)) (v (succ (succ n +ℕ d))) ＝ ιₐ 0ℚ)
     vanish = B-above-band (succ (succ n +ℕ d)) (v (succ (succ n +ℕ d)))
               (v-after-large d)

\end{code}

H6. The path ψ, which equals q j on the plateau of index j ≥ 1: the
plateau path through q (gist.RealCohesion.PlateauPath).

\begin{code}

 open plateau-path a q q-is-close public

\end{code}

H4–H7, for the remaining parity p: the depth, its properties, and the
application of the finite-chain lemma.

\begin{code}

 private
  N-aux : 𝟚 → 𝟚 → ℕ → ℕ
  N-aux ₀ ₀ j = j
  N-aux ₀ ₁ j = succ j
  N-aux ₁ ₀ j = succ j
  N-aux ₁ ₁ j = j

  N-aux-parity : (p b : 𝟚) (j : ℕ) → parity j ＝ b → parity (N-aux p b j) ＝ p
  N-aux-parity ₀ ₀ j e = e
  N-aux-parity ₀ ₁ j e = ap complement e
  N-aux-parity ₁ ₀ j e = ap complement e
  N-aux-parity ₁ ₁ j e = e

  N-aux-above : (p b : 𝟚) (j : ℕ) → j ≤ℕ N-aux p b j
  N-aux-above ₀ ₀ j = ≤-refl j
  N-aux-above ₀ ₁ j = ≤-succ j
  N-aux-above ₁ ₀ j = ≤-succ j
  N-aux-above ₁ ₁ j = ≤-refl j

  N-aux-below : (p b : 𝟚) (j : ℕ) → N-aux p b j ≤ℕ succ j
  N-aux-below ₀ ₀ j = ≤-succ j
  N-aux-below ₀ ₁ j = ≤-refl j
  N-aux-below ₁ ₀ j = ≤-refl j
  N-aux-below ₁ ₁ j = ≤-succ j

  depth-bit : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ∔ Y → 𝟚
  depth-bit d = bit (cases inr inl d)

  depth-bit-₀ : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (d : X ∔ Y)
              → depth-bit d ＝ ₀ → X
  depth-bit-₀ d = bit-is-₀ (cases inr inl d)

  depth-bit-₁ : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (d : X ∔ Y)
              → depth-bit d ＝ ₁ → Y
  depth-bit-₁ d = bit-is-₁ (cases inr inl d)

 module branch
         (p : 𝟚)
         (no-plateau : (n : ℕ) → parity (succ n) ＝ p
                     → 1/3 < v (succ n) → v (succ n) < 1/2 → 𝟘 {𝓤₀})
        where

  no-plateau' : (n : ℕ) → parity n ＝ p → 1/3 < v n → v n < 1/2 → 𝟘 {𝓤₀}
  no-plateau' 0        _ l _ = ℚ<-irrefl 0ℚ
                                (ℚ<-trans 0ℚ 1/3 0ℚ (0 , refl)
                                  (ιₐ-lower⁻¹ 1/3 0ℚ l))
  no-plateau' (succ n) i l l' = no-plateau n i l l'

  decision-is-prop : (n : ℕ) → parity n ＝ p
                   → is-prop ((v n < 1/2) ∔ (1/3 < v n))
  decision-is-prop n i =
   +-is-prop (ℝ<ℚ-is-prop (v n) 1/2) (ℚ<ℝ-is-prop 1/3 (v n))
                          (λ k k' → no-plateau' n i k' k)

  decide : (n : ℕ) → parity n ＝ p → (v n < 1/2) ∔ (1/3 < v n)
  decide n i =
   ∥∥-rec (decision-is-prop n i) γ (ℝ-locatedness (v n) 1/3 1/2 1/3<1/2)
   where
    γ : (1/3 < v n) ∔ (v n < 1/2) → (v n < 1/2) ∔ (1/3 < v n)
    γ (inl k) = inr k
    γ (inr k) = inl k

  N : ℕ → ℕ
  N j = N-aux p (parity j) j

  N-parity : (j : ℕ) → parity (N j) ＝ p
  N-parity j = N-aux-parity p (parity j) j refl

  N-is-above : (j : ℕ) → j ≤ℕ N j
  N-is-above j = N-aux-above p (parity j) j

  N-increases : (j : ℕ) → N j ≤ℕ N (succ j)
  N-increases j = ≤-trans (N j) (succ j) (N (succ j))
                   (N-aux-below p (parity j) j) (N-is-above (succ j))

  c : ℕ → 𝟚
  c j = depth-bit (decide (N j) (N-parity j))

  c-is-₁ : (j : ℕ) → c j ＝ ₁ → 1/3 < v (N j)
  c-is-₁ j = depth-bit-₁ (decide (N j) (N-parity j))

  c-is-₀ : (j : ℕ) → c j ＝ ₀ → v (N j) < 1/2
  c-is-₀ j = depth-bit-₀ (decide (N j) (N-parity j))

  c-is-monotone : (j : ℕ) → c j ＝ ₁ → c (succ j) ＝ ₁
  c-is-monotone j r =
   ap depth-bit (decision-is-prop (N (succ j)) (N-parity (succ j))
                  (decide (N (succ j)) (N-parity (succ j)))
                  (inr (<-≤-trans-ℚ (v (N j)) (v (N (succ j))) 1/3 (c-is-₁ j r)
                         (v-is-monotone (N j) (N (succ j)) (N-increases j)))))

  e-small-at-depth-zero : (j : ℕ) → c (succ j) ＝ ₀ → e (succ j) < 1/4
  e-small-at-depth-zero j r =
   e-below-a-quarter j
    (≤-<-trans-ℚ (v (succ j)) (v (N (succ j))) 1/2
      (v-is-monotone (succ j) (N (succ j)) (N-is-above (succ j)))
      (c-is-₀ (succ j) r))

  A D : ℝ → 𝓤₀ ̇
  A s = h (ψ s) < 2/3
  D s = 1/3 < h (ψ s)

  cover : (s : ℝ) → A s ∨ D s
  cover s = ∥∥-functor γ (ℝ-locatedness (h (ψ s)) 1/3 2/3 1/3<2/3)
   where
    γ : (1/3 < h (ψ s)) ∔ (h (ψ s) < 2/3) → A s ∔ D s
    γ (inl k) = inr k
    γ (inr k) = inl k

  A-misses-odd-plateaus : (k : ℕ) → c (odd-index k) ＝ ₀
                        → (s : ℝ) → A s
                        → α (odd-index k) < s → s < β (odd-index k) → 𝟘 {𝓤₀}
  A-misses-odd-plateaus k _ s o l l' =
   ιₐ-≤-gives-not-below (h a) 1ℚ h-at-a
    (use-rounded-real-R (h a) 2/3 1ℚ 2/3<1
      (transport (λ x → h x < 2/3) ψ-is-a o))
   where
    i : ℕ
    i = odd-pred k

    on : (α (succ i) < s) × (s < β (succ i))
    on = transport (λ j → (α j < s) × (s < β j)) (odd-index-is-succ k) (l , l')

    ψ-is-a : ψ s ＝ a
    ψ-is-a = ψ-on-plateau i s (pr₁ on) (pr₂ on)
           ∙ q-of-odd (succ i)
              (transport (λ j → parity j ＝ ₁) (odd-index-is-succ k)
                (parity-of-odd-index k))

  D-misses-even-plateaus : (k : ℕ) → c (even-index k) ＝ ₀
                         → (s : ℝ) → D s
                         → α (even-index k) < s → s < β (even-index k) → 𝟘 {𝓤₀}
  D-misses-even-plateaus k r s o l l' =
   not-below-and-above (e (even-index k)) 1/3
    (transport (1/3 <_) h-ψ-is-e o)
    (use-rounded-real-R (e (even-index k)) 1/4 1/3 1/4<1/3
      (e-small-at-depth-zero (odd-index k) r))
   where
    h-ψ-is-e : h (ψ s) ＝ e (even-index k)
    h-ψ-is-e = ap h (ψ-on-plateau (odd-index k) s l l')
             ∙ h-of-q-of-even (even-index k) (parity-of-even-index k)

  open finite-chain-lemma ν c c-is-monotone (ιₐ 0ℚ) (ιₐ 1ℚ) α m β α-below-m
   m-below-β
        m-decreases (λ j → ιₐ-upper 0ℚ (m j) (m-is-positive j))
        (λ j → ιₐ-lower (m j) 1ℚ (m-below-1 j))
        A D (λ s → ℝ<ℚ-is-prop (h (ψ s)) 2/3) (λ s → ℚ<ℝ-is-prop 1/3 (h (ψ s)))
        cover A-misses-odd-plateaus D-misses-even-plateaus

  hit-on-branch : ∃ k ꞉ ℕ , 0ℚ < h (z k)
  hit-on-branch = ∥∥-rec ∃-is-prop γ depth-is-somewhere-₁
   where
    γ : (Σ j ꞉ ℕ , c j ＝ ₁) → ∃ k ꞉ ℕ , 0ℚ < h (z k)
    γ (j , r) = positive-v-gives-hit (N j)
                 (use-rounded-real-L (v (N j)) 0ℚ 1/3 (0 , refl) (c-is-₁ j r))

\end{code}

The two branches, H4, and the conclusion.

\begin{code}

 sequential-hitting : ∃ k ꞉ ℕ , 0ℚ < h (z k)
 sequential-hitting = ∥∥-rec ∃-is-prop γ (ℝ-locatedness (h w) 1/3 2/3 1/3<2/3)
  where
   even-branch : 1/3 < h w
               → (n : ℕ) → parity (succ n) ＝ ₀
               → 1/3 < v (succ n) → v (succ n) < 1/2 → 𝟘 {𝓤₀}
   even-branch o n i l l' =
    not-below-and-above (e (succ n)) 1/3
     (transport (1/3 <_)
       (ap h (plateau-identity n l l') ∙ h-of-q-of-even (succ n) i) o)
     (use-rounded-real-R (e (succ n)) 1/4 1/3 1/4<1/3 (e-below-a-quarter n l'))

   odd-branch : h w < 2/3
              → (n : ℕ) → parity (succ n) ＝ ₁
              → 1/3 < v (succ n) → v (succ n) < 1/2 → 𝟘 {𝓤₀}
   odd-branch o n i l l' =
    ιₐ-≤-gives-not-below (h a) 1ℚ h-at-a
     (use-rounded-real-R (h a) 2/3 1ℚ 2/3<1
       (transport (λ x → h x < 2/3)
         (plateau-identity n l l' ∙ q-of-odd (succ n) i) o))

   γ : (1/3 < h w) ∔ (h w < 2/3) → ∃ k ꞉ ℕ , 0ℚ < h (z k)
   γ (inl o) = branch.hit-on-branch ₀ (even-branch o)
   γ (inr o) = branch.hit-on-branch ₁ (odd-branch o)

\end{code}

The statement Sequential-Hitting of the starter module
gist.RealCohesion.ApproximateIVTStatement. There, z j is within 2⁻ʲ
of a, with distances stated using TypeTopology's sum, and the
conclusion is 0ℝ < h (z j). We apply sequential hitting to the
sequence z ∘ succ, whose terms are within 2⁻⁽ʲ⁺¹⁾ ＝ ρ j of a.

\begin{code}

positive-from-rational : (y : ℝ) → 0ℚ < y → 0ℝ < y
positive-from-rational y m = ∥∥-functor γ (rounded-left-d y 0ℚ m)
 where
  γ : (Σ q ꞉ ℚ , (0ℚ < q) × (q < y)) → Σ q ꞉ ℚ , (0ℝ < q) × (q < y)
  γ (q , o , o') = q , transport (_< q) ιₐ-zero-is-0ℝ (ιₐ-upper 0ℚ q o) , o'

translate-by-2⁻ : (y : ℝ) (n : ℕ) → y + ιₐ (⟨1/2⟩^ n) ＝ y +ᵗ 2⁻ n
translate-by-2⁻ y n = +-is-+ᵗ y (ιₐ (⟨1/2⟩^ n))
                     ∙ ap (y +ᵗ_) (ιₐ-is-ι (⟨1/2⟩^ n))

within-from-starter-bounds : (n : ℕ) (x y : ℝ)
                           → x ≤ (y +ᵗ 2⁻ n)
                           → y ≤ (x +ᵗ 2⁻ n)
                           → within (⟨1/2⟩^ n) x y
within-from-starter-bounds n x y k k' =
 within-from-bound (⟨1/2⟩^ n) y x (transport (x ≤_) (translate-by-2⁻ y n ⁻¹) k)
  ,
 within-from-bound (⟨1/2⟩^ n) x y (transport (y ≤_) (translate-by-2⁻ x n ⁻¹) k')

starter-bounds-from-within : (n : ℕ) (x y : ℝ)
                           → within (⟨1/2⟩^ n) x y
                           → (x ≤ (y +ᵗ 2⁻ n)) × (y ≤ (x +ᵗ 2⁻ n))
starter-bounds-from-within n x y w =
 transport (x ≤_) (translate-by-2⁻ y n)
  (pr₂ (bounds-from-within (⟨1/2⟩^ n) y x (within-sym (⟨1/2⟩^ n) x y w))) ,
 transport (y ≤_) (translate-by-2⁻ x n)
  (pr₂ (bounds-from-within (⟨1/2⟩^ n) x y w))

sequential-hitting-as-stated : ((k : ℝ → Q) (u v : ℝ) → k u ＝ k v)
                             → Sequential-Hitting
sequential-hitting-as-stated ν h a z c l =
 ∥∥-functor γ (sequential-hitting.sequential-hitting ν h a (z ∘ succ) c' l')
 where
  c' : (j : ℕ) → within (ρ j) (z (succ j)) a
  c' j = within-from-starter-bounds (succ j) (z (succ j)) a
          (pr₁ (c (succ j))) (pr₂ (c (succ j)))

  l' : ιₐ 1ℚ ≤ h a
  l' = transport (_≤ h a) (ιₐ-is-ι 1ℚ ⁻¹) l

  γ : (Σ k ꞉ ℕ , 0ℚ < h (z (succ k))) → Σ j ꞉ ℕ , 0ℝ < h (z j)
  γ (k , m) = succ k , positive-from-rational (h (z (succ k))) m

\end{code}
