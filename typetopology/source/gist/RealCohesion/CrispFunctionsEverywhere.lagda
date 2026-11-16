Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026; prose corrected 13 November 2026, after
the final audits. See the AI disclosure in gist.RealCohesion.index.

Shulman's Theorems 11.5 and 11.2 without Axiom T: continuity at crisp
points with respect to all nearby points, and Theorem 11.2 for
arbitrary witnesses.

gist.RealCohesion.CrispContinuity proves that a crisp function
f : ℝ → ℝ is continuous at crisp points with respect to crisp points:
for rationals u < f t < v there is a rational interval around t on
whose crisp points u < f < v. gist.RealCohesion.CrispExactIVT proves
Shulman's Theorem 11.2 for crisp witnesses. Fable's note [1] extends
both to arbitrary points through Shulman's Corollary 8.16, which needs
♭ to commute with propositional truncation. We use GPT-6 Astra's
rational detection (gist.RealCohesion.RationalDetection) instead,
which follows from Axiom R♭ alone.

 * Continuity at a crisp point t with respect to all points near it,
   crisp or not. Narrow the window to u < u₁ < f t < v₁ < v and take
   the interval for (u₁ , v₁) at crisp points. If an arbitrary point s
   of the interval had f s < u₁, rational detection would give a
   rational point of the interval with f < u₁. Rationals are crisp,
   which contradicts the choice of the interval. So u < f s, and
   likewise f s < v. This is [1, Theorem A.2] for n = 1, and Shulman's
   Theorem 11.5 [2] without Axiom T. As there, the centre t is crisp
   and only the nearby point s is arbitrary; this is not continuity at
   an arbitrary centre. gist.RealCohesion.CrispFunctionsAreContinuous
   later proves the same statement, again with a crisp centre, from
   Axiom R♭ alone, without crisp excluded middle.

 * Theorem 11.2 for arbitrary witnesses: if f a < c < f b, rational
   detection gives rationals a' and b' with f a' < c < f b'. Rationals
   are crisp, so gist.RealCohesion.CrispExactIVT applies.

Both assume crisp excluded middle and that every map ℝ → Q is
constant, which follows from Axiom R♭.

[1] Fable. Shulman's stated questions: three updates, Part A.
    Working note, 10 November 2026, audited by GPT-6 Astra.
    references/F18-shulman-three-updates.md

[2] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

\begin{code}

{-# OPTIONS --safe --without-K --cohesion --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.CrispFunctionsEverywhere
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import Rationals.Type
open import Rationals.Order
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealOrder fe pe pt using (not-below-and-above)
open import gist.RealCohesion.RealLattice fe pe pt
 using (ℚ<ℝ-is-prop ; ℝ<ℚ-is-prop)
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
open import gist.RealCohesion.CrispRationals
 using (ℚ-has-crisp-representatives ; crisp-elim)
open import gist.RealCohesion.CrispContinuity fe pe pt
 using (crisp-real-continuity)
open import gist.RealCohesion.CrispExactIVT fe pe pt using (crisp-exact-IVT)
open import gist.RealCohesion.CrispExactIVT fe pe pt
 using (rational-below ; rational-above) public
open import gist.RealCohesion.RationalDetection fe pe pt
 using (rational-detection-window₂)

open PropositionalTruncation pt

\end{code}

Holding at all points, crisp or not, of a rational interval around t.

\begin{code}

Holds-Near-Everywhere : (ℝ → 𝓤₀ ̇ ) → ℝ → 𝓤₁ ̇
Holds-Near-Everywhere W t =
 ∃ (r , r') ꞉ ℚ × ℚ , (r < t) × (t < r') × ((s : ℝ) → r < s → s < r' → W s)

\end{code}

We assume crisp excluded middle and that maps ℝ → Q are constant.

\begin{code}

module _ (@♭ cem : Crisp-EM 𝓤₁)
         (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v)
       where

 crisp-functions-are-continuous-everywhere
  : (@♭ f : ℝ → ℝ) (@♭ t : ℝ) (u v : ℚ)
  → u < f t → f t < v
  → Holds-Near-Everywhere (λ s → (u < f s) × (f s < v)) t
 crisp-functions-are-continuous-everywhere f t u v l m =
  ∥∥-rec ∃-is-prop γ (rounded-left-d (f t) u l)
  where
   Goal : 𝓤₁ ̇
   Goal = Holds-Near-Everywhere (λ s → (u < f s) × (f s < v)) t

   γ : (Σ u₁ ꞉ ℚ , (u < u₁) × (u₁ < f t)) → Goal
   γ (u₁ , a , b) =
    ∥∥-rec ∃-is-prop δ
     (rounded-right-b (upper-cut-of (f t)) (rounded-from-real-R (f t)) v m)
    where
     δ : (Σ v₁ ꞉ ℚ , (v₁ < v) × (f t < v₁)) → Goal
     δ (v₁ , c , d) = ∥∥-functor ε (crisp-real-continuity cem ν f t u₁ v₁ b d)
      where
       ε : (Σ (r , r') ꞉ ℚ × ℚ , (r < t) × (t < r')
                               × ((@♭ s : ℝ) → r < s → s < r'
                                  → (u₁ < f s) × (f s < v₁)))
         → Σ (r , r') ꞉ ℚ × ℚ , (r < t) × (t < r')
                              ×
                              ((s : ℝ) → r < s → s < r' → (u < f s) × (f s < v))
       ε ((r , r') , p , p' , k) = (r , r') , p , p' , everywhere
        where
         at-rationals : (q : ℚ) → r < ιₐ q → ιₐ q < r'
                      → (u₁ < f (ιₐ q)) × (f (ιₐ q) < v₁)
         at-rationals = crisp-elim ℚ-has-crisp-representatives
                         (λ q → r < ιₐ q → ιₐ q < r'
                                → (u₁ < f (ιₐ q)) × (f (ιₐ q) < v₁))
                         (λ q₀ → k (ιₐ q₀))

         Hit : ℚ → ℚ → 𝓤₀ ̇
         Hit L U = Σ q ꞉ ℚ , ((L < f (ιₐ q)) × (f (ιₐ q) < U))
                           × ((r < id (ιₐ q)) × (id (ιₐ q) < r'))

         lower : (s : ℝ) → r < s → s < r' → u < f s
         lower s o o' =
          ∥∥-rec (ℚ<ℝ-is-prop u (f s)) ζ (ℝ-locatedness (f s) u u₁ a)
          where
           ζ : (u < f s) ∔ (f s < u₁) → u < f s
           ζ (inl w) = w
           ζ (inr w) = 𝟘-elim (∥∥-rec 𝟘-is-prop η (inhabited-from-real-L (f s)))
            where
             κ : (L : ℚ) → Hit L u₁ → 𝟘
             κ L (q , (_ , below) , (i₁ , i₂)) =
              not-below-and-above (f (ιₐ q)) u₁ (pr₁ (at-rationals q i₁ i₂))
               below

             η : (Σ L ꞉ ℚ , L < f s) → 𝟘
             η (L , L<fs) = ∥∥-rec 𝟘-is-prop (κ L)
                             (rational-detection-window₂ ν f id s L u₁ r r' L<fs
                               w o o')

         upper : (s : ℝ) → r < s → s < r' → f s < v
         upper s o o' =
          ∥∥-rec (ℝ<ℚ-is-prop (f s) v) ζ (ℝ-locatedness (f s) v₁ v c)
          where
           ζ : (v₁ < f s) ∔ (f s < v) → f s < v
           ζ (inr w) = w
           ζ (inl w) = 𝟘-elim (∥∥-rec 𝟘-is-prop η (inhabited-from-real-R (f s)))
            where
             κ : (U : ℚ) → Hit v₁ U → 𝟘
             κ U (q , (above , _) , (i₁ , i₂)) =
              not-below-and-above (f (ιₐ q)) v₁ above
               (pr₂ (at-rationals q i₁ i₂))

             η : (Σ U ꞉ ℚ , f s < U) → 𝟘
             η (U , fs<U) = ∥∥-rec 𝟘-is-prop (κ U)
                             (rational-detection-window₂ ν f id s v₁ U r r' w
                               fs<U o o')

         everywhere : (s : ℝ) → r < s → s < r' → (u < f s) × (f s < v)
         everywhere s o o' = lower s o o' , upper s o o'

\end{code}

Theorem 11.2 for arbitrary witnesses, from the crisp rational
witnesses rational-below and rational-above of
gist.RealCohesion.CrispExactIVT, which are re-exported here.

\begin{code}

 exact-IVT : (@♭ f : ℝ → ℝ) (@♭ c : ℝ) (a b : ℝ)
           → f a < c → c < f b
           → ∃ x ꞉ ℝ , f x ＝ c
 exact-IVT f c a b l m =
  ∥∥-rec ∃-is-prop γ (binary-choice (rational-below cem ν f c a l)
                                     (rational-above cem ν f c b m))
  where
   γ : (Σ α ꞉ ♭ ℚ , f (ι (♭-counit α)) < c)
     × (Σ β ꞉ ♭ ℚ , c < f (ι (♭-counit β)))
     → ∃ x ꞉ ℝ , f x ＝ c
   γ (((α ^♭) , l') , ((β ^♭) , m')) =
    crisp-exact-IVT cem ν f c (ι α) (ι β) l' m'

\end{code}
