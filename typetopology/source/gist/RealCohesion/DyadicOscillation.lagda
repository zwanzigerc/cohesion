Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 26 October 2026. See the AI disclosure in
gist.RealCohesion.index. The function is the dyadic witness proposed
in GPT-6 Astra's gameplan (25 October 2026) [2] for the counterexample of
the research notes [1, Section 5], by Claude Opus.

The concrete witness g for the zero-plateau invariant.

Let g : ℝ → ℝ be the extension to the reals of the 1-Lipschitz dyadic
profile f of gist.RealCohesion.DyadicProfile. We prove that g has the
two properties used by gist.RealCohesion.ZeroPlateauInvariant.

 * g oscillates at 0. Arbitrarily close to 0, on both sides, there are
   rising halves of bumps of both signs, on which g has a strict sign.

 * Every crisp nonzero zero of g lies in a plateau. The plateaux are
   ±[threshold k , hi k], for every level k, and ±[5/16 , 1]. Next to
   each plateau, on both sides, g has a strict sign, on a half of a bump
   or on the ramp. Given a crisp zero z > 0, we find a level n with
   threshold n < z, and then locate z by finitely many comparisons of
   z with rationals. These are decided by crisp excluded middle,
   applied to crisp representatives of the rationals
   (gist.RealCohesion.CrispRationals). If z is not in a plateau, it is
   inside a bump or on the ramp, where g is not 0. The case z < 0 is
   symmetric.

We also get g 0 ＝ g 1 ＝ 0, and hence, from the continuity of crisp
real functions, the invariance of the zero indicator along crisp real
paths in the kernel of g.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, draft of 25 October 2026.
    references/C01-write-up-2026-10-25.tex

[2] GPT-6 Astra. Gameplan for Opus: a subset of the Dedekind reals
    whose shape is not a set, 25 October 2026.
    references/A32-subset-shape-gameplan.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.DyadicOscillation
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Integers.Type hiding (abs)
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import UF.Powerset
open import Rationals.Addition
open import Rationals.Limits fe pe pt
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Type
open import DedekindReals.Type fe pe pt
open import gist.CohesiveApartness.Flat
open import gist.RealCohesion.CrispRationals
open import gist.RealCohesion.CrispRealAnalysis fe pe pt
open import gist.RealCohesion.DyadicLevels fe pe pt
open import gist.RealCohesion.DyadicProfile fe pe pt
open import gist.RealCohesion.LipschitzExtension fe pe pt
open import gist.RealCohesion.RationalArithmetic hiding (opposite)
open import gist.RealCohesion.RationalLimits fe pe pt
open import gist.RealCohesion.RationalLipschitz using (Lipschitz)
open import gist.RealCohesion.RationalPoints fe pe pt using (0ℝₐ ; 0ℝₐ-is-0ℝ)
open import gist.RealCohesion.RealKernelCocycle fe pe pt using (N ; h)
open import gist.RealCohesion.RealPathDescent fe pe pt
 using (Real-Path-Invariant)
open import gist.RealCohesion.ZeroPlateauInvariant fe pe pt

open PropositionalTruncation pt

\end{code}

The function g, and the properties of the extension that we use. We
make g abstract, so that its values are never unfolded. We define g
from a local abstract copy φ of f: in our experiments, applying
extension-agrees of gist.RealCohesion.LipschitzExtension directly to f,
which comes from an applied module, made type checking extremely slow,
while the same application to φ is fast.

\begin{code}

abstract
 φ : ℚ → ℚ
 φ = f

 φ-is-Lipschitz : Lipschitz φ
 φ-is-Lipschitz = f-is-Lipschitz

 φ-at-zero : φ 0ℚ ＝ 0ℚ
 φ-at-zero = f-at-zero

 φ-at-one : φ 1ℚ ＝ 0ℚ
 φ-at-one = f-at-one

 g : ℝ → ℝ
 g = extension φ φ-is-Lipschitz

 g-on-rationals : (q : ℚ) → g (ι q) ＝ ι (φ q)
 g-on-rationals = extension-agrees φ φ-is-Lipschitz

 g-flat : (lo hi : ℚ) → lo ≤ hi
        → ((y : ℚ) → lo ≤ y → y ≤ hi → f y ＝ 0ℚ)
        → (x : ℝ) → ¬ (x < lo) → ¬ (hi < x) → g x ＝ 0ℝ
 g-flat = flat-transfer φ φ-is-Lipschitz

 g-increasing : (σ : 𝟚) (u v : ℚ)
              → ((y : ℚ) → u ≤ y → y ≤ v → f y ＝ signed σ (y - u))
              → (x : ℝ) → u < x → x < v → Has-Sign σ (g x)
 g-increasing = increasing-signed φ φ-is-Lipschitz

 g-decreasing : (σ : 𝟚) (u v : ℚ)
              → ((y : ℚ) → u ≤ y → y ≤ v → f y ＝ signed σ (v - y))
              → (x : ℝ) → u < x → x < v → Has-Sign σ (g x)
 g-decreasing = decreasing-signed φ φ-is-Lipschitz

 g-tent : (σ : 𝟚) (u w v : ℚ)
        → ((y : ℚ) → u ≤ y → y ≤ w → f y ＝ signed σ (y - u))
        → ((y : ℚ) → w ≤ y → y ≤ v → f y ＝ signed σ (v - y))
        → (x : ℝ) → u < x → x < v → Has-Sign σ (g x)
 g-tent = tent-signed φ φ-is-Lipschitz

g-at-zero : g 0ℝ ＝ 0ℝ
g-at-zero = g-on-rationals 0ℚ ∙ ap-at ι (φ 0ℚ) 0ℚ φ-at-zero

g-at-one : g 1ℝ ＝ 0ℝ
g-at-one = g-on-rationals 1ℚ ∙ ap-at ι (φ 1ℚ) 0ℚ φ-at-one

g-at-1-is-g-at-0 : g 1ℝ ＝ g 0ℝ
g-at-1-is-g-at-0 = g-at-one ∙ g-at-zero ⁻¹

no-sign-at-zero : (σ : 𝟚) (x : ℝ) → g x ＝ 0ℝ → ¬ Has-Sign σ (g x)
no-sign-at-zero σ x e s = zero-has-no-sign σ (transport (Has-Sign σ) e s)

\end{code}

The fields of the records of gist.RealCohesion.ZeroPlateauInvariant
use the abstract copy 0ℝₐ of 0ℝ.

\begin{code}

g-at-zeroₐ : g 0ℝₐ ＝ 0ℝₐ
g-at-zeroₐ = ap g 0ℝₐ-is-0ℝ ∙ g-at-zero ∙ 0ℝₐ-is-0ℝ ⁻¹

flat-field : (lo hi : ℚ)
           → ((x : ℝ) → ¬ (x < lo) → ¬ (hi < x) → g x ＝ 0ℝ)
           → (x : ℝ) → ¬ (x < lo) → ¬ (hi < x) → g x ＝ 0ℝₐ
flat-field lo hi φ x m m' = φ x m m' ∙ 0ℝₐ-is-0ℝ ⁻¹

\end{code}

Rational facts used below.

\begin{code}

negative-of-positive : (p : ℚ) → 0ℚ < p → - p < 0ℚ
negative-of-positive = neg-is-negative

outer-falling : (y : ℚ) → 1/4 ≤ y → y ≤ 5/16 → f y ＝ signed ₁ (5/16 - y)
outer-falling y l l' =
   bump-falls 0 y (transport-at (λ (w : ℚ) → w ≤ y) 1/4 (cen 0) (cen-zero ⁻¹) l)
                  (transport-at (λ (w : ℚ) → y ≤ w) 5/16
                    (threshold 0 + threshold 0)
                    (double-threshold-0 ⁻¹) l')
 ∙ ap-at (λ (w : ℚ) → w - y) (threshold 0 + threshold 0) 5/16 double-threshold-0

outer-rising⁻ : (y : ℚ) → - 5/16 ≤ y → y ≤ - 1/4 → f y ＝ signed ₁ (y - (- 5/16))
outer-rising⁻ y l l' =
   bump-falls⁻ 0 y
    (transport-at (λ (w : ℚ) → - w ≤ y) 5/16 (threshold 0 + threshold 0)
      (double-threshold-0 ⁻¹) l)
                   (transport-at (λ (w : ℚ) → y ≤ - w) 1/4 (cen 0) (cen-zero ⁻¹)
                     l')
 ∙ ap-at (λ (w : ℚ) → y - (- w)) (threshold 0 + threshold 0) 5/16
    double-threshold-0

\end{code}

The plateaux.

\begin{code}

level-plateau : (k : ℕ) → Plateau g (threshold k) (hi k)
level-plateau k = record
 { lo'            = cen (succ k)
  ; hi'            = cen k
  ; lo'<lo         = cen-succ<threshold k
  ; lo<hi          = threshold<hi k
  ; hi<hi'         = hi<cen k
  ; away-from-zero = inl (threshold-is-positive k)
  ; sign-below     = sgn (succ k)
  ; sign-above     = sgn k
  ; flat           = flat-field (threshold k) (hi k)
                     (g-flat (threshold k) (hi k) (threshold≤hi k) (flat k))
  ; signed-below   =
   g-decreasing (sgn (succ k)) (cen (succ k)) (threshold k) (falling k)
  ; signed-above   = g-increasing (sgn k) (hi k) (cen k) (rising k)
  }

outer-plateau : Plateau g 5/16 1ℚ
outer-plateau = record
 { lo'            = 1/4
  ; hi'            = two
  ; lo'<lo         = 3 , refl
  ; lo<hi          = 10 , refl
  ; hi<hi'         = 0 , refl
  ; away-from-zero = inl (4 , refl)
  ; sign-below     = ₁
  ; sign-above     = ₁
  ; flat           = flat-field 5/16 1ℚ (g-flat 5/16 1ℚ 5/16≤1 outer-flat)
  ; signed-below   = g-decreasing ₁ 1/4 5/16 outer-falling
  ; signed-above   = g-increasing ₁ 1ℚ two (λ y l _ → outer-ramp y l)
  }

level-plateau⁻ : (k : ℕ) → Plateau g (- hi k) (- threshold k)
level-plateau⁻ k = record
 { lo'            = - cen k
  ; hi'            = - cen (succ k)
  ; lo'<lo         = ℚ<-swap (hi k) (cen k) (hi<cen k)
  ; lo<hi          = ℚ<-swap (threshold k) (hi k) (threshold<hi k)
  ; hi<hi'         = ℚ<-swap (cen (succ k)) (threshold k) (cen-succ<threshold k)
  ; away-from-zero =
   inr (negative-of-positive (threshold k) (threshold-is-positive k))
  ; sign-below     = sgn k
  ; sign-above     = sgn (succ k)
  ; flat           = flat-field (- hi k) (- threshold k)
                     (g-flat (- hi k) (- threshold k)
                       (ℚ≤-swap (threshold k) (hi k) (threshold≤hi k))
                        (flat⁻ k))
  ; signed-below   = g-decreasing (sgn k) (- cen k) (- hi k) (rising⁻ k)
  ; signed-above   =
   g-increasing (sgn (succ k)) (- threshold k) (- cen (succ k)) (falling⁻ k)
  }

outer-plateau⁻ : Plateau g (- 1ℚ) (- 5/16)
outer-plateau⁻ = record
 { lo'            = - two
  ; hi'            = - 1/4
  ; lo'<lo         = ℚ<-swap 1ℚ two (0 , refl)
  ; lo<hi          = ℚ<-swap 5/16 1ℚ (10 , refl)
  ; hi<hi'         = ℚ<-swap 1/4 5/16 (3 , refl)
  ; away-from-zero = inr (negative-of-positive 5/16 (4 , refl))
  ; sign-below     = ₁
  ; sign-above     = ₁
  ; flat           = flat-field (- 1ℚ) (- 5/16)
                     (g-flat (- 1ℚ) (- 5/16) (ℚ≤-swap 5/16 1ℚ 5/16≤1)
                       outer-flat⁻)
  ; signed-below   = g-decreasing ₁ (- two) (- 1ℚ) (λ y _ l → outer-ramp⁻ y l)
  ; signed-above   = g-increasing ₁ (- 5/16) (- 1/4) outer-rising⁻
  }

\end{code}

Oscillation at 0. The centres of the bumps tend to 0, and consecutive
bumps have opposite signs.

\begin{code}

private
 module cen-bounds =
  halving-sequence-bounds cen cen-succ 1/4 (ℚ<-coarser-than-≤ 0ℚ 1/4 0<1/4)
   (transport-at (λ (w : ℚ) → w ≤ 1/4) 1/4 (cen 0) (cen-zero ⁻¹) (ℚ≤-refl 1/4))

open cen-bounds using ()
 renaming (bound to cen-bound ; becomes-small to cen-below) public

same-or-next : (σ : 𝟚) (n : ℕ) → (sgn n ＝ σ) ∔ (sgn (succ n) ＝ σ)
same-or-next σ n = γ (sgn n) σ refl
 where
  γ : (s τ : 𝟚) → sgn n ＝ s → (sgn n ＝ τ) ∔ (opposite (sgn n) ＝ τ)
  γ ₀ ₀ e = inl e
  γ ₀ ₁ e = inr (ap opposite e)
  γ ₁ ₀ e = inr (ap opposite e)
  γ ₁ ₁ e = inl e

level-with-sign : (σ : 𝟚) (e : ℚ) → 0ℚ < e → Σ k ꞉ ℕ , (sgn k ＝ σ) × (cen k < e)
level-with-sign σ e 0<e = γ (cen-below e 0<e)
 where
  γ : (Σ n ꞉ ℕ , cen n < e) → Σ k ꞉ ℕ , (sgn k ＝ σ) × (cen k < e)
  γ (n , l) = δ (same-or-next σ n)
   where
    δ : (sgn n ＝ σ) ∔ (sgn (succ n) ＝ σ) → Σ k ꞉ ℕ , (sgn k ＝ σ) × (cen k < e)
    δ (inl s) = n , s , l
    δ (inr s) =
     succ n , s , ℚ≤-<-trans (cen (succ n)) (cen n) e (cen-decreases n) l

oscillates-right : (σ : 𝟚) (e : ℚ) → 0ℚ < e
                 → ∃ (a , b) ꞉ ℚ × ℚ , (0ℚ < a) × (a < b) × (b < e)
                                     × ((x : ℝ) → a < x → x < b
                                        → Has-Sign σ (g x))
oscillates-right σ e 0<e = ∣ γ (level-with-sign σ e 0<e) ∣
 where
  γ : (Σ k ꞉ ℕ , (sgn k ＝ σ) × (cen k < e))
    → Σ (a , b) ꞉ ℚ × ℚ , (0ℚ < a) × (a < b) × (b < e)
                        × ((x : ℝ) → a < x → x < b → Has-Sign σ (g x))
  γ (k , s , l) = (hi k , cen k) , hi-is-positive k , hi<cen k , l , δ
   where
    δ : (x : ℝ) → hi k < x → x < cen k → Has-Sign σ (g x)
    δ x a b = transport (λ τ → Has-Sign τ (g x)) s
               (g-increasing (sgn k) (hi k) (cen k) (rising k) x a b)

oscillates-left : (σ : 𝟚) (e : ℚ) → e < 0ℚ
                → ∃ (a , b) ꞉ ℚ × ℚ , (e < a) × (a < b) × (b < 0ℚ)
                                    ×
                                    ((x : ℝ) → a < x → x < b → Has-Sign σ (g x))
oscillates-left σ e e<0 = ∣ γ (level-with-sign σ (- e) (ℚ<-swap'' e e<0)) ∣
 where
  γ : (Σ k ꞉ ℕ , (sgn k ＝ σ) × (cen k < - e))
    → Σ (a , b) ꞉ ℚ × ℚ , (e < a) × (a < b) × (b < 0ℚ)
                        × ((x : ℝ) → a < x → x < b → Has-Sign σ (g x))
  γ (k , s , l) = (- cen k , - hi k) , I , II , III , δ
   where
    I : e < - cen k
    I = transport-at (λ (w : ℚ) → w < - cen k) (- (- e)) e (ℚ-minus-minus e ⁻¹)
         (ℚ<-swap (cen k) (- e) l)

    II : - cen k < - hi k
    II = ℚ<-swap (hi k) (cen k) (hi<cen k)

    III : - hi k < 0ℚ
    III = negative-of-positive (hi k) (hi-is-positive k)

    δ : (x : ℝ) → - cen k < x → x < - hi k → Has-Sign σ (g x)
    δ x a b = transport (λ τ → Has-Sign τ (g x)) s
               (g-decreasing (sgn k) (- cen k) (- hi k) (rising⁻ k) x a b)

oscillation : Oscillates-At-Zero g
oscillation = record
 { value-at-zero = g-at-zeroₐ
  ; signed-right  = oscillates-right
  ; signed-left   = oscillates-left
  }

\end{code}

The zeros of g. A real number z lies in the plateau [a , b] when
¬ (z < a) and ¬ (b < z).

\begin{code}

Plateau-Around : ℝ → 𝓤₁ ̇
Plateau-Around z = Σ (a , b) ꞉ ℚ × ℚ , Plateau g a b × ¬ (z < a) × ¬ (b < z)

module _ (@♭ cem : Crisp-EM 𝓤₁) where

 private
  cem' : Crisp-EM 𝓤₀
  cem' = cem₀ cem

  below-dec : (@♭ z : ℝ) (q : ℚ) → (z < q) ∔ ¬ (z < q)
  below-dec z =
   decide-at-rationals cem' (λ q → z < q) (λ q → ∈-is-prop (upper-cut-of z) q)

  above-dec : (@♭ z : ℝ) (q : ℚ) → (q < z) ∔ ¬ (q < z)
  above-dec z =
   decide-at-rationals cem' (λ q → q < z) (λ q → ∈-is-prop (lower-cut-of z) q)

\end{code}

Positive zeros, at least threshold n.

\begin{code}

 positive-zero : (n : ℕ) (@♭ z : ℝ) → ¬ (z < threshold n) → g z ＝ 0ℝ
               → Plateau-Around z
 positive-zero 0 z ν gz = γ (above-dec z (hi 0))
  where
   γ : (hi 0 < z) ∔ ¬ (hi 0 < z) → Plateau-Around z
   γ (inr ν') = (threshold 0 , hi 0) , level-plateau 0 , ν , ν'
   γ (inl l)  = δ (below-dec z 5/16)
    where
     δ : (z < 5/16) ∔ ¬ (z < 5/16) → Plateau-Around z
     δ (inl l') = 𝟘-elim (no-sign-at-zero (sgn 0) z gz
                   (g-tent (sgn 0) (hi 0) (cen 0) (threshold 0 + threshold 0)
                     (rising 0) (bump-falls 0) z l
                     (transport-at (λ (w : ℚ) → z < w) 5/16
                       (threshold 0 + threshold 0)
                       (double-threshold-0 ⁻¹) l')))
     δ (inr ν'') = ε (above-dec z 1ℚ)
      where
       ε : (1ℚ < z) ∔ ¬ (1ℚ < z) → Plateau-Around z
       ε (inr ν''') = (5/16 , 1ℚ) , outer-plateau , ν'' , ν'''
       ε (inl k)    = 𝟘-elim (∥∥-rec 𝟘-is-prop ζ (inhabited-from-real-R z))
        where
         ζ : (Σ v ꞉ ℚ , z < v) → 𝟘
         ζ (v , z<v) = no-sign-at-zero ₁ z gz
                        (g-increasing ₁ 1ℚ v (λ y l _ → outer-ramp y l) z k z<v)
 positive-zero (succ m) z ν gz = γ (below-dec z (threshold m))
  where
   γ : (z < threshold m) ∔ ¬ (z < threshold m) → Plateau-Around z
   γ (inr ν') = positive-zero m z ν' gz
   γ (inl l)  = δ (above-dec z (hi (succ m)))
    where
     δ : (hi (succ m) < z) ∔ ¬ (hi (succ m) < z) → Plateau-Around z
     δ (inr ν'') =
      (threshold (succ m) , hi (succ m)) , level-plateau (succ m) , ν , ν''
     δ (inl k)   = 𝟘-elim (no-sign-at-zero (sgn (succ m)) z gz
                    (g-tent (sgn (succ m)) (hi (succ m)) (cen (succ m))
                      (threshold m)
                      (rising (succ m)) (falling m) z k l))

\end{code}

Negative zeros, at most - threshold n.

\begin{code}

 negative-zero : (n : ℕ) (@♭ z : ℝ) → ¬ (- threshold n < z) → g z ＝ 0ℝ
               → Plateau-Around z
 negative-zero 0 z ν gz = γ (below-dec z (- hi 0))
  where
   γ : (z < - hi 0) ∔ ¬ (z < - hi 0) → Plateau-Around z
   γ (inr ν') = (- hi 0 , - threshold 0) , level-plateau⁻ 0 , ν' , ν
   γ (inl l)  = δ (above-dec z (- 5/16))
    where
     δ : (- 5/16 < z) ∔ ¬ (- 5/16 < z) → Plateau-Around z
     δ (inl k)   = 𝟘-elim (no-sign-at-zero (sgn 0) z gz
                    (g-tent (sgn 0) (- (threshold 0 + threshold 0)) (- cen 0)
                      (- hi 0)
                      (bump-falls⁻ 0) (rising⁻ 0) z
                      (transport-at (λ (w : ℚ) → - w < z) 5/16
                        (threshold 0 + threshold 0)
                        (double-threshold-0 ⁻¹) k)
                      l))
     δ (inr ν'') = ε (below-dec z (- 1ℚ))
      where
       ε : (z < - 1ℚ) ∔ ¬ (z < - 1ℚ) → Plateau-Around z
       ε (inr ν''') = (- 1ℚ , - 5/16) , outer-plateau⁻ , ν''' , ν''
       ε (inl k')   = 𝟘-elim (∥∥-rec 𝟘-is-prop ζ (inhabited-from-real-L z))
        where
         ζ : (Σ u ꞉ ℚ , u < z) → 𝟘
         ζ (u , u<z) = no-sign-at-zero ₁ z gz
                        (g-decreasing ₁ u (- 1ℚ) (λ y _ l' → outer-ramp⁻ y l') z
                          u<z k')
 negative-zero (succ m) z ν gz = γ (above-dec z (- threshold m))
  where
   γ : (- threshold m < z) ∔ ¬ (- threshold m < z) → Plateau-Around z
   γ (inr ν') = negative-zero m z ν' gz
   γ (inl k)  = δ (below-dec z (- hi (succ m)))
    where
     δ : (z < - hi (succ m)) ∔ ¬ (z < - hi (succ m)) → Plateau-Around z
     δ (inr ν'') =
      (- hi (succ m) , - threshold (succ m)) , level-plateau⁻ (succ m) , ν'' , ν
     δ (inl l)   = 𝟘-elim (no-sign-at-zero (sgn (succ m)) z gz
                    (g-tent (sgn (succ m)) (- threshold m) (- cen (succ m))
                      (- hi (succ m))
                      (falling⁻ m) (rising⁻ (succ m)) z k l))

\end{code}

All crisp nonzero zeros.

\begin{code}

 zeros-lie-in-plateaux : Zeros-Lie-In-Plateaux g
 zeros-lie-in-plateaux z gz ν = γ (crisp-nonzero-has-sign cem z ν)
  where
   γ : (Σ σ ꞉ 𝟚 , Has-Sign σ z) → ∥ Plateau-Around z ∥
   γ (₁ , l) = ∥∥-functor δ (rounded-left-d z 0ℚ l)
    where
     δ : (Σ e ꞉ ℚ , 0ℚ < e < z) → Plateau-Around z
     δ (e , 0<e , e<z) = positive-zero n z ν' gz
      where
       n : ℕ
       n = pr₁ (threshold-becomes-small e 0<e)

       t<e : threshold n < e
       t<e = pr₂ (threshold-becomes-small e 0<e)

       ν' : ¬ (z < threshold n)
       ν' = not-below-and-above z (threshold n)
             (below-a-real z (threshold n) e t<e e<z)
   γ (₀ , l) =
    ∥∥-functor δ (rounded-right-b (upper-cut-of z) (rounded-from-real-R z) 0ℚ l)
    where
     δ : (Σ e ꞉ ℚ , (e < 0ℚ) × (z < e)) → Plateau-Around z
     δ (e , e<0 , z<e) = negative-zero n z ν' gz
      where
       0<-e : 0ℚ < - e
       0<-e = ℚ<-swap'' e e<0

       n : ℕ
       n = pr₁ (threshold-becomes-small (- e) 0<-e)

       t<-e : threshold n < - e
       t<-e = pr₂ (threshold-becomes-small (- e) 0<-e)

       e<-t : e < - threshold n
       e<-t = transport-at (λ (w : ℚ) → w < - threshold n) (- (- e)) e
               (ℚ-minus-minus e ⁻¹)
               (ℚ<-swap (threshold n) (- e) t<-e)

       ν' : ¬ (- threshold n < z)
       ν' k = not-below-and-above z (- threshold n) k
               (above-a-real z e (- threshold n) e<-t z<e)

\end{code}

The invariance of the zero indicator for g, from the continuity of
crisp real functions.

\begin{code}

 module _ (@♭ continuity : Crisp-Real-Continuity) where

  dyadic-zero-indicator-is-invariant : Real-Path-Invariant (N cem g) (h cem g)
  dyadic-zero-indicator-is-invariant =
   zero-indicator-is-invariant cem continuity g oscillation
    zeros-lie-in-plateaux

\end{code}
