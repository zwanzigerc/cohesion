Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026. See the AI disclosure in
gist.RealCohesion.index.

The plateau path through an arbitrary sequence (H6 of the
formalization blueprint [1], for arbitrary data, as the blueprint
addendum [2, A2] asks).

Let a be a real number and q a sequence with q n within
hgt n = 2⁻⁽ⁿ⁺⁴⁾ of a. The path ψ is the limit of clamped steps from a
towards q j, with step sizes the bumps C j s, of height 2⁻⁽ʲ⁺³⁾, on
the plateaus (α j , β j) of the finite-chain lemma, where
α j = 5/8 · 2⁻ʲ and β j = 7/8 · 2⁻ʲ. On the plateau of index j ≥ 1,
ψ s ＝ q j.

The path starts at a: ψ 0 ＝ a.

It serves Theorems 7.4 and 7.10 of the write-up (step A2 of the
addendum [2]) as a lemma of their proofs; it is not itself a statement
of the write-up.

It is the path of the proof of sequential hitting
(gist.RealCohesion.SequentialHitting), which applies it to the
alternating sequence a, z (n + 3), a, z (n + 5), …. With the sequence
as a parameter, it also serves the zigzag of Theorem 7.10
(gist.RealCohesion.AnalyticLLPO) and, pointwise, families of sequences
in sequential hitting for functionals
(gist.RealCohesion.FunctionalHitting). The code was first written
inside gist.RealCohesion.SequentialHitting, which now takes it from
here, and the lemma ψ-at-zero was first proved in
gist.RealCohesion.PairHitting.

[1] Formalization blueprint: the approximate IVT from Axiom R♭.
    Claude Fable 5.2, revision 3, 10 November 2026.
    references/F15-aivt-blueprint-rev3.md
    references/F16-aivt-handoff-rev4.md

[2] Formalization blueprint, addendum: Theorem 7.10, Corollary 3.7,
    Theorem 4.3 and Theorem 8.32, revision 3. Claude Fable 5.2,
    11 November 2026.
    references/F14-brouwer-addendum-rev4.md
    (retained as revision 4, which states that it differs from
    revision 3 only by Part F and gate G15)

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.PlateauPath
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Order hiding (max)
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.RationalArithmetic using (minus-zero)
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealLattice fe pe pt
open import gist.RealCohesion.RealLimits fe pe pt
open import gist.RealCohesion.Plateaus fe pe pt
 using
  (hgt ; neg-is-negative ; α ; β ; β-below-double ; ρ-below-α ; ρ-double-below)

open PropositionalTruncation pt

\end{code}

The data: a point a and a sequence q with q n within hgt n of a.

\begin{code}

module plateau-path
        (a : ℝ)
        (q : ℕ → ℝ)
        (q-is-close : (n : ℕ) → within (hgt n) (q n) a)
       where

\end{code}

The bumps C j s and C⁻ j s, of height ρ (j + 2), on the plateau of
index j.

\begin{code}

 C C⁻ : ℕ → ℝ → ℝ
 C j s = clamp (ιₐ 0ℚ) (ιₐ (ρ (succ (succ j))))
          (min (s + ιₐ (ℚ- ρ j)) (ιₐ (ρ j ℚ+ ρ j) + (- s)))
 C⁻ j s = clamp (ιₐ (ℚ- ρ (succ (succ j)))) (ιₐ 0ℚ)
           (max (ιₐ (ρ j) + (- s)) (s + ιₐ (ℚ- (ρ j ℚ+ ρ j))))

 private
  0≤ρ : (j : ℕ) → ιₐ 0ℚ ≤ ιₐ (ρ j)
  0≤ρ j = ιₐ-<-gives-≤ 0ℚ (ρ j) (ρ-is-positive j)

  -ρ≤0 : (j : ℕ) → ιₐ (ℚ- ρ j) ≤ ιₐ 0ℚ
  -ρ≤0 j = ιₐ-<-gives-≤ (ℚ- ρ j) 0ℚ (neg-is-negative (ρ j) (ρ-is-positive j))

 C-on-plateau : (j : ℕ) (s : ℝ) → α j < s → s < β j
              → (C j s ＝ ιₐ (ρ (succ (succ j))))
              × (C⁻ j s ＝ ιₐ (ℚ- ρ (succ (succ j))))
 C-on-plateau j s l l' = I , II
  where
   r : ℚ
   r = ρ (succ (succ j))

   I : C j s ＝ ιₐ r
   I =
    clamp-above (ιₐ 0ℚ) (ιₐ r) (min (s + ιₐ (ℚ- ρ j)) (ιₐ (ρ j ℚ+ ρ j) + (- s)))
        (0≤ρ (succ (succ j)))
        (≤-min (s + ιₐ (ℚ- ρ j)) (ιₐ (ρ j ℚ+ ρ j) + (- s)) (ιₐ r)
          (translate-above s r (ρ j) (transport (_< s) (ℚ+-comm (ρ j) r) l))
          (reflect-above s r (ρ j ℚ+ ρ j) l'))

   II : C⁻ j s ＝ ιₐ (ℚ- r)
   II = clamp-below (ιₐ (ℚ- r)) (ιₐ 0ℚ)
         (max (ιₐ (ρ j) + (- s)) (s + ιₐ (ℚ- (ρ j ℚ+ ρ j))))
         (max-≤ (ιₐ (ρ j) + (- s)) (s + ιₐ (ℚ- (ρ j ℚ+ ρ j))) (ιₐ (ℚ- r))
           (reflect-below s (ℚ- r) (ρ j)
             (transport (_< s) (ap (ρ j ℚ+_) (ℚ-minus-minus r)) l))
           (translate-below s (ℚ- r) (ρ j ℚ+ ρ j)
             (transport (s <_) (ℚ+-comm (ρ j ℚ+ ρ j) (ℚ- r)) l')))

 C-left : (j : ℕ) (s : ℝ) → s < ρ j → (C j s ＝ ιₐ 0ℚ) × (C⁻ j s ＝ ιₐ 0ℚ)
 C-left j s l = I , II
  where
   I : C j s ＝ ιₐ 0ℚ
   I = clamp-below (ιₐ 0ℚ) (ιₐ (ρ (succ (succ j))))
        (min (s + ιₐ (ℚ- ρ j)) (ιₐ (ρ j ℚ+ ρ j) + (- s)))
        (ℝ≤-trans (min (s + ιₐ (ℚ- ρ j)) (ιₐ (ρ j ℚ+ ρ j) + (- s)))
          (s + ιₐ (ℚ- ρ j)) (ιₐ 0ℚ)
          (min-≤-left (s + ιₐ (ℚ- ρ j)) (ιₐ (ρ j ℚ+ ρ j) + (- s)))
          (translate-below s 0ℚ (ρ j)
            (transport (s <_) (ℚ-zero-left-neutral (ρ j) ⁻¹) l)))

   II : C⁻ j s ＝ ιₐ 0ℚ
   II = clamp-above (ιₐ (ℚ- ρ (succ (succ j)))) (ιₐ 0ℚ)
         (max (ιₐ (ρ j) + (- s)) (s + ιₐ (ℚ- (ρ j ℚ+ ρ j))))
         (-ρ≤0 (succ (succ j)))
         (ℝ≤-trans (ιₐ 0ℚ) (ιₐ (ρ j) + (- s))
           (max (ιₐ (ρ j) + (- s)) (s + ιₐ (ℚ- (ρ j ℚ+ ρ j))))
           (reflect-above s 0ℚ (ρ j) (transport (s <_) (minus-zero (ρ j) ⁻¹) l))
           (≤-max-left (ιₐ (ρ j) + (- s)) (s + ιₐ (ℚ- (ρ j ℚ+ ρ j)))))

 C-right : (j : ℕ) (s : ℝ) → (ρ j ℚ+ ρ j) < s
         → (C j s ＝ ιₐ 0ℚ) × (C⁻ j s ＝ ιₐ 0ℚ)
 C-right j s l = I , II
  where
   I : C j s ＝ ιₐ 0ℚ
   I = clamp-below (ιₐ 0ℚ) (ιₐ (ρ (succ (succ j))))
        (min (s + ιₐ (ℚ- ρ j)) (ιₐ (ρ j ℚ+ ρ j) + (- s)))
        (ℝ≤-trans (min (s + ιₐ (ℚ- ρ j)) (ιₐ (ρ j ℚ+ ρ j) + (- s)))
          (ιₐ (ρ j ℚ+ ρ j) + (- s)) (ιₐ 0ℚ)
          (min-≤-right (s + ιₐ (ℚ- ρ j)) (ιₐ (ρ j ℚ+ ρ j) + (- s)))
          (reflect-below s 0ℚ (ρ j ℚ+ ρ j)
            (transport (_< s) (minus-zero (ρ j ℚ+ ρ j) ⁻¹) l)))

   II : C⁻ j s ＝ ιₐ 0ℚ
   II = clamp-above (ιₐ (ℚ- ρ (succ (succ j)))) (ιₐ 0ℚ)
         (max (ιₐ (ρ j) + (- s)) (s + ιₐ (ℚ- (ρ j ℚ+ ρ j))))
         (-ρ≤0 (succ (succ j)))
         (ℝ≤-trans (ιₐ 0ℚ) (s + ιₐ (ℚ- (ρ j ℚ+ ρ j)))
           (max (ιₐ (ρ j) + (- s)) (s + ιₐ (ℚ- (ρ j ℚ+ ρ j))))
           (translate-above s 0ℚ (ρ j ℚ+ ρ j)
             (transport (_< s) (ℚ-zero-left-neutral (ρ j ℚ+ ρ j) ⁻¹) l))
           (≤-max-right (ιₐ (ρ j) + (- s)) (s + ιₐ (ℚ- (ρ j ℚ+ ρ j)))))

 C-bounds : (j : ℕ) (s : ℝ)
          → (ιₐ (ℚ- ρ (succ (succ j))) ≤ C⁻ j s) × (C⁻ j s ≤ C j s)
          × (C j s ≤ ιₐ (ρ (succ (succ j))))
 C-bounds j s = clamp-is-above-lo (ιₐ (ℚ- ρ (succ (succ j)))) (ιₐ 0ℚ) T⁻ ,
                ℝ≤-trans (C⁻ j s) (ιₐ 0ℚ) (C j s)
                 (clamp-is-below-hi (ιₐ (ℚ- ρ (succ (succ j)))) (ιₐ 0ℚ) T⁻
                   (-ρ≤0 (succ (succ j))))
                 (clamp-is-above-lo (ιₐ 0ℚ) (ιₐ (ρ (succ (succ j)))) T) ,
                clamp-is-below-hi (ιₐ 0ℚ) (ιₐ (ρ (succ (succ j)))) T
                 (0≤ρ (succ (succ j)))
  where
   T T⁻ : ℝ
   T  = min (s + ιₐ (ℚ- ρ j)) (ιₐ (ρ j ℚ+ ρ j) + (- s))
   T⁻ = max (ιₐ (ρ j) + (- s)) (s + ιₐ (ℚ- (ρ j ℚ+ ρ j)))

\end{code}

The path ψ, which equals q j on the plateau of index j ≥ 1.

\begin{code}

 Ψ : ℝ → ℕ → ℝ
 Ψ s 0        = a
 Ψ s (succ j) = clamped-step (Ψ s j) (C⁻ (succ j) s) (C (succ j) s) (q (succ j))

 Ψ-step : (s : ℝ) (j : ℕ) → within (ρ (succ j)) (Ψ s j) (Ψ s (succ j))
 Ψ-step s j =
  within-weaken (ρ (succ (succ (succ j)))) (ρ (succ j)) (Ψ s j) (Ψ s (succ j))
               (ρ-shift (succ j) 2)
               (clamped-step-within (ρ (succ (succ (succ j)))) (Ψ s j)
                 (C⁻ (succ j) s) (C (succ j) s) (q (succ j))
                 (pr₁ (C-bounds (succ j) s))
                 (pr₁ (pr₂ (C-bounds (succ j) s)))
                 (pr₂ (pr₂ (C-bounds (succ j) s))))

 ψ : ℝ → ℝ
 ψ s = geometric-limit.lim (Ψ s) (Ψ-step s)

 ψ-on-plateau : (j : ℕ) (s : ℝ) → α (succ j) < s → s < β (succ j)
              → ψ s ＝ q (succ j)
 ψ-on-plateau j s l l' =
  geometric-limit.lim-of-eventually-constant (Ψ s) (Ψ-step s)
                          (q (succ j)) (succ j) after
  where
   s-below-double : s < ρ (succ j) ℚ+ ρ (succ j)
   s-below-double = use-rounded-real-R s (β (succ j)) (ρ (succ j) ℚ+ ρ (succ j))
                     (β-below-double (succ j)) l'

   before : (i : ℕ) → i ≤ℕ j → Ψ s i ＝ a
   before 0        _ = refl
   before (succ i) k =
    clamped-step-of-zero (Ψ s i) (C⁻ (succ i) s) (C (succ i) s) (q (succ i))
     (pr₂ vanish) (pr₁ vanish)
    ∙ before i (≤-trans i (succ i) j (≤-succ i) k)
    where
     vanish : (C (succ i) s ＝ ιₐ 0ℚ) × (C⁻ (succ i) s ＝ ιₐ 0ℚ)
     vanish = C-left (succ i) s
             (use-rounded-real-R' s (ρ (succ j) ℚ+ ρ (succ j)) (ρ (succ i))
               (ρ-double-below (succ i) (succ j) k) s-below-double)

   close : within (ρ (succ (succ (succ j)))) a (q (succ j))
   close = within-sym (ρ (succ (succ (succ j)))) (q (succ j)) a
            (within-weaken (hgt (succ j)) (ρ (succ (succ (succ j))))
              (q (succ j)) a
              (ℚ<-coarser-than-≤ (hgt (succ j)) (ρ (succ (succ (succ j))))
                (ρ-decreases (succ (succ (succ j)))))
              (q-is-close (succ j)))

   at : Ψ s (succ j) ＝ q (succ j)
   at = ap (λ x → clamped-step x (C⁻ (succ j) s) (C (succ j) s) (q (succ j)))
           (before j (≤-refl j))
      ∙ clamped-step-full (ρ (succ (succ (succ j)))) a (C⁻ (succ j) s)
         (C (succ j) s)
         (q (succ j)) (pr₂ (C-on-plateau (succ j) s l l'))
          (pr₁ (C-on-plateau (succ j) s l l'))
         close

   after : (d : ℕ) → Ψ s (succ j +ℕ d) ＝ q (succ j)
   after 0        = at
   after (succ d) =
    clamped-step-of-zero (Ψ s (succ j +ℕ d)) (C⁻ (succ (succ j +ℕ d)) s)
     (C (succ (succ j +ℕ d)) s) (q (succ (succ j +ℕ d))) (pr₂ vanish)
      (pr₁ vanish)
    ∙ after d
    where
     vanish : (C (succ (succ j +ℕ d)) s ＝ ιₐ 0ℚ)
            × (C⁻ (succ (succ j +ℕ d)) s ＝ ιₐ 0ℚ)
     vanish = C-right (succ (succ j +ℕ d)) s
             (use-rounded-real-L s
               (ρ (succ (succ j +ℕ d)) ℚ+ ρ (succ (succ j +ℕ d)))
               (α (succ j))
               (ℚ≤-<-trans (ρ (succ (succ j +ℕ d)) ℚ+ ρ (succ (succ j +ℕ d)))
                 (ρ (succ j))
                 (α (succ j))
                 (ρ-double-below (succ j) (succ (succ j +ℕ d)) (≤-+ (succ j) d))
                 (ρ-below-α (succ j)))
               l)

\end{code}

The path starts at a, because every bump vanishes at 0.

\begin{code}

 Ψ-at-zero : (n : ℕ) → Ψ (ιₐ 0ℚ) n ＝ a
 Ψ-at-zero 0        = refl
 Ψ-at-zero (succ n) = clamped-step-of-zero (Ψ (ιₐ 0ℚ) n) (C⁻ (succ n) (ιₐ 0ℚ))
                       (C (succ n) (ιₐ 0ℚ)) (q (succ n)) (pr₂ vanish)
                        (pr₁ vanish)
                     ∙ Ψ-at-zero n
  where
   vanish : (C (succ n) (ιₐ 0ℚ) ＝ ιₐ 0ℚ) × (C⁻ (succ n) (ιₐ 0ℚ) ＝ ιₐ 0ℚ)
   vanish =
    C-left (succ n) (ιₐ 0ℚ) (ιₐ-upper 0ℚ (ρ (succ n)) (ρ-is-positive (succ n)))

 ψ-at-zero : ψ (ιₐ 0ℚ) ＝ a
 ψ-at-zero =
  geometric-limit.lim-of-eventually-constant (Ψ (ιₐ 0ℚ)) (Ψ-step (ιₐ 0ℚ)) a 0
              (λ d → ap (Ψ (ιₐ 0ℚ)) (zero-left-neutral d) ∙ Ψ-at-zero d)

\end{code}
