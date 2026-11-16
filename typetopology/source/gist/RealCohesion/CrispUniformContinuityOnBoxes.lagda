Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026; one sentence updated 13 November 2026,
after the final audits. See the AI disclosure in
gist.RealCohesion.index.

Uniform continuity on boxes of an ε-δ continuous map on the crisp
points of ℝⁿ: the first step of the third part of Theorem 3.3 of the
write-up [1] in n variables, gate G21 of Claude Fable 5.2's second
addendum [2].

The exact statement served. Theorem 3.3 of [1] says, under crisp
excluded middle and Axiom R♭, that for crisp n every ε-δ continuous map
♭ ℝⁿ → ♭ ℝ is a value of the canonical map ♭ (ℝⁿ → ℝ) → (♭ ℝⁿ → ♭ ℝ).
The proof makes such a map uniformly continuous on bounded sets and
extends it from the rational points. This module is the first step, for
a crisp map h that is continuous in the sense of
gist.RealCohesion.ShulmanWeakeningsStatements (is-♭-continuous: the
supremum norm, rational ε and δ). Uniform continuity is stated at crisp
rational points, which is what the extension
(gist.RealCohesion.CrispExtensionOnBoxes) uses: for every rational
ε > 0 and every real point x, crisp or not, there is a rational box
around x on whose crisp rational points h varies by less than ε
(small-oscillation-around). Crisp excluded middle is used only for
propositions in 𝓤₀, as the target Target-3-3 of
gist.RealCohesion.ShulmanWeakeningsStatements has it. Axiom R♭ is not
used here.

The proof. Fix a crisp rational ε and a crisp box C of side two. Say
that a box B spreads at scale K if it is not the case that the values
of h are ε-close at every pair of crisp rational points u and v with u
in B and v within 2⁻⁽ᴷ⁺¹⁾ of u. A box that spreads at scale K spreads at
every coarser scale, and has a subcube that spreads at scale K: by
crisp excluded middle, otherwise every subcube, and so B, would satisfy
the closeness, since u lies in one of the subcubes. So if C spreads at
every scale, the bisection of gist.RealCohesion.CrispBisection gives
crisp boxes C = B₀ ⊃ B₁ ⊃ ⋯, with sides 2^(1-j), that all spread at
every scale, and a crisp point p in all of them. Continuity of h at p,
for the tolerance ε/4, gives δ. Take rationals α < h p < β with
β - α < ε/2, j with the side of B_j below δ/4, and K with 2⁻⁽ᴷ⁺¹⁾ below
δ/4. If u is in B_j and v is within 2⁻⁽ᴷ⁺¹⁾ of u, then u and v are within
δ of p, so their values lie in (α - ε/4 , β + ε/4), whose length is
less than ε. So B_j does not spread at scale K, a contradiction. By
crisp excluded middle, then, C does not spread at some scale. Crisp
representatives extend this to all rational ε and all boxes of side
two, and every real point lies in the middle of such a box.

This is not the route of the addendum [2, §3, G21], which takes steps 1
and 2 of its gate G17: a crisp sequence of pairs of grid points that
witness the failure of uniform continuity, Bolzano–Weierstrass, and
continuity at the limit. Defining such a sequence crisply needs a crisp
proof of the failure; the bisection needs no sequence, because every
decision concerns a box. Bolzano–Weierstrass
(gist.RealCohesion.CrispBolzanoWeierstrass) is the other instance of
the same bisection. This route was reviewed in the final Fable and
Astra source audits (13 November 2026).

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, revision of 12 November 2026, Theorem 3.3.
    references/C04-write-up-2026-11-12.tex

[2] Claude Fable 5.2. Second addendum to the formalization plan,
    revision 4 of 12 November 2026.
    references/F13b-second-addendum-rev4-as-amended.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.CrispUniformContinuityOnBoxes
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Fin.Type
open import Naturals.Order
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import UF.Subsingletons-FunExt
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Properties fe pe pt using (ℝ-arithmetically-located)
open import gist.RealCohesion.BrouwerStatements fe pe pt using (ℝ^)
open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt
 using
  (is-♭-continuous ; _is-strictly-within_of_ ; _is-coordinatewise-within_of_)
open import gist.RealCohesion.ContinuityForms fe pe pt
 using (within-from-close ; close-from-within ; interval-gives-strictly-close ;
        strictly-close-below ; strictly-close-above)
open import gist.RealCohesion.CrispBisection fe pe pt
open import gist.RealCohesion.RationalBoxExtension fe pe pt
 using (In-Box ; Around) public
import gist.RealCohesion.RationalBoxExtension fe pe pt as RBE
open import gist.RealCohesion.CrispRationals
 using (ℚ-has-crisp-representatives ; ℕ-has-crisp-representatives ;
        ×-has-crisp-representatives ; Fin-functions-have-crisp-representatives ;
        crisp-elim₂ ; decide-at)
open import gist.RealCohesion.FinVectors using (Fin-choice)
open import gist.RealCohesion.NestedIntervals fe pe pt
 using (below-the-limit ; above-the-limit)
open import gist.RealCohesion.RationalArithmetic
 using (two ; minus-plus ; sum-minus-first ; <-move-left ; <-move-right)
open import gist.RealCohesion.RationalArithmetic using (widened-difference)
 public
open import gist.RealCohesion.RationalPoints fe pe pt
 using (ιₐ ; ιₐ-lower ; ιₐ-upper ; ιₐ-lower⁻¹ ; ιₐ-upper⁻¹)
open import gist.RealCohesion.RealBalls fe pe pt
open import gist.RealCohesion.RealLimits fe pe pt
 using (ρ ; ρ-antitone ; ρ-becomes-small ; ρ-is-positive)

open PropositionalTruncation pt

\end{code}

Crisp rational points of ℝⁿ, and the closeness of rational points in
the supremum norm. Open rational boxes, In-Box and Around, are in
gist.RealCohesion.RationalBoxExtension and re-exported here.

\begin{code}

♭ι : {@♭ n : ℕ} → ♭ (Fin n → ℚ) → ♭ (ℝ^ n)
♭ι (q ^♭) = (λ i → ιₐ (q i)) ^♭

Near : {n : ℕ} → ℚ → (Fin n → ℚ) → (Fin n → ℚ) → 𝓤₀ ̇
Near {n} δ u v = (i : Fin n) → (u i < v i ℚ+ δ) × (v i < u i ℚ+ δ)

\end{code}

Rational facts used below. The first is abstract: it is a closed fact
about particular rationals (see gist.RealCohesion.CrispBolzanoWeierstrass
on why such facts are kept abstract).

\begin{code}

abstract
 two-is-positive : 0ℚ < two
 two-is-positive = ℚ<-≤-trans 0ℚ 1ℚ two 0<1
                    (ℚ≤-addition-preserves-order'' 1ℚ 1ℚ
                      (ℚ<-coarser-than-≤ 0ℚ 1ℚ 0<1))

near-weakens : {n : ℕ} (δ δ' : ℚ) (u v : Fin n → ℚ) → δ ≤ δ' → Near δ u v
             → Near δ' u v
near-weakens δ δ' u v l k i =
 ℚ<-≤-trans (u i) (v i ℚ+ δ) (v i ℚ+ δ') (pr₁ (k i))
  (ℚ≤-addition-preserves-order-left δ δ' (v i) l) ,
 ℚ<-≤-trans (v i) (u i ℚ+ δ) (u i ℚ+ δ') (pr₂ (k i))
  (ℚ≤-addition-preserves-order-left δ δ' (u i) l)

plus-of-≤-< : (a b r d : ℚ) → a ≤ b → r < d → a ℚ+ r < b ℚ+ d
plus-of-≤-< a b r d l m = ℚ≤-<-trans (a ℚ+ r) (b ℚ+ r) (b ℚ+ d)
                           (ℚ≤-addition-preserves-order a b r l)
                           (ℚ<-addition-preserves-order''' r d b m)

minus-of-≤-< : (a b r d : ℚ) → a ≤ b → r < d → a ℚ- d < b ℚ- r
minus-of-≤-< a b r d l m = plus-of-≤-< a b (ℚ- d) (ℚ- r) l (ℚ<-swap r d m)

sum-with-a-half : (x e : ℚ) → x < halfₐ e → x ℚ+ halfₐ e < e
sum-with-a-half x e l = transport (x ℚ+ halfₐ e <_) (halvesₐ-add-up e)
                         (ℚ<-addition-preserves-order x (halfₐ e) (halfₐ e) l)

widened-interval-is-short
 : (x y e : ℚ) → y ℚ- x < halfₐ e
 → (y ℚ+ halfₐ (halfₐ e)) ℚ- (x ℚ- halfₐ (halfₐ e)) < e
widened-interval-is-short x y e l =
 transport (_< e) (widened-difference x y (halfₐ (halfₐ e)) ⁻¹)
  (transport (λ - → (y ℚ- x) ℚ+ - < e) (halvesₐ-add-up (halfₐ e) ⁻¹)
    (sum-with-a-half (y ℚ- x) e l))

stage-interval-is-short
 : (c s δ : ℚ) → 0ℚ < δ → s < halfₐ (halfₐ δ)
 → ((c ℚ+ s) ℚ+ halfₐ (halfₐ δ)) ℚ- (c ℚ- halfₐ (halfₐ δ)) < δ
stage-interval-is-short c s δ m l =
 widened-interval-is-short c (c ℚ+ s) δ
  (transport (_< halfₐ δ) (sum-minus-first c s ⁻¹)
    (ℚ<-trans s (halfₐ (halfₐ δ)) (halfₐ δ) l
      (halfₐ-is-less (halfₐ δ) (halfₐ-is-positive δ m))))

near-in-a-short-interval
 : (a b r u v : ℚ) → a < u → u < b → a < v → v < b → b ℚ- a < r
 → (u < v ℚ+ r) × (v < u ℚ+ r)
near-in-a-short-interval a b r u v k k' m m' w =
 γ u v k' m , γ v u m' k
 where
  b-below : b < a ℚ+ r
  b-below = transport (b <_) (ℚ+-comm r a) (<-move-right b r a w)

  γ : (y z : ℚ) → y < b → a < z → y < z ℚ+ r
  γ y z o o' = ℚ<-trans y b (z ℚ+ r) o
                (ℚ<-trans b (a ℚ+ r) (z ℚ+ r) b-below
                  (ℚ<-addition-preserves-order a z r o'))

bounds-from-strictly-within
 : (η α β : ℚ) (x t : ℝ) → x is-strictly-within η of t → α < t → t < β
 → ((α ℚ- η) < x) × (x < (β ℚ+ η))
bounds-from-strictly-within η α β x t s k k' =
 strictly-close-below η x t (pr₂ (close-from-within η x t s)) α k ,
 strictly-close-above η x t (pr₁ (close-from-within η x t s)) β k'

\end{code}

We fix crisp excluded middle and a crisp map h that is continuous at
crisp points, and write g u for the value of h at a crisp rational
point u. Close-Values ε B K says that the values at u and v are ε-close
whenever u is in B and v is within 2⁻⁽ᴷ⁺¹⁾ of u.

\begin{code}

module uniform-continuity-on-boxes
        (@♭ cem : Crisp-EM 𝓤₀)
        {@♭ n : ℕ}
        (@♭ h : ♭ (ℝ^ n) → ♭ ℝ)
        (@♭ h-is-continuous : is-♭-continuous h)
       where

 g : ♭ (Fin n → ℚ) → ℝ
 g u = ♭-counit (h (♭ι u))

 Close-Values : ℚ → Box n → ℕ → 𝓤₀ ̇
 Close-Values ε B K =
    (u v : ♭ (Fin n → ℚ))
  → ♭-counit u is-in B
  → Near (ρ K) (♭-counit u) (♭-counit v)
  → Close ε (g u) (g v)

 close-values-is-prop : (ε : ℚ) (B : Box n) (K : ℕ)
                      → is-prop (Close-Values ε B K)
 close-values-is-prop ε B K =
  Π-is-prop fe (λ u → Π-is-prop fe (λ v → Π-is-prop fe (λ _ → Π-is-prop fe
   (λ _ → Close-is-prop ε (g u) (g v)))))

 close-values-at-finer-scales
  : (ε : ℚ) (B : Box n) (K K' : ℕ) → K ≤ K' → Close-Values ε B K
  → Close-Values ε B K'
 close-values-at-finer-scales ε B K K' l c u v m k =
  c u v m
   (near-weakens (ρ K') (ρ K) (♭-counit u) (♭-counit v) (ρ-antitone K K' l) k)

\end{code}

For crisp ε and a crisp corner a, the bisection for the family of
boxes that spread.

\begin{code}

 module at-scale (@♭ ε : ℚ) (@♭ a : Fin n → ℚ) where

  Spread : Box n → ℕ → 𝓤₀ ̇
  Spread B K = ¬ Close-Values ε B K

  open bisection cem Spread (λ B K → negations-are-props fe) a public

  decide-close-values : (B : Box n) (K : ℕ) → is-decidable (Close-Values ε B K)
  decide-close-values B K =
   decide-at (×-has-crisp-representatives boxes-have-crisp-representatives
                                          ℕ-has-crisp-representatives)
    cem (λ (B , K) → Close-Values ε B K)
     (λ (B , K) → close-values-is-prop ε B K) (B , K)

  spread-is-antitone : (B : Box n) (K K' : ℕ) → K ≤ K' → Spread B K'
                     → Spread B K
  spread-is-antitone B K K' l s c =
   s (close-values-at-finer-scales ε B K K' l c)

  spread-is-in-subcubes
   : (B : Box n) (K : ℕ) → Spread B K
   → ∃ c ꞉ (Fin n → 𝟚) , Spread (subcube c B) K
  spread-is-in-subcubes B K s =
   Cases (choices-are-Compact n (λ c → Spread (subcube c B) K)
           (λ c → decide-V (subcube c B) K))
    (λ (c , t) → ∣ c , t ∣)
    (λ μ → 𝟘-elim
      (s (λ u v m k → close-in-subcubes μ (subcube-containing B (♭-counit u))
                        u v (subcube-contains B (♭-counit u) m) k)))
   where
    close-in-subcubes : ¬ (Σ c ꞉ (Fin n → 𝟚) , Spread (subcube c B) K)
                      → (c : Fin n → 𝟚) → Close-Values ε (subcube c B) K
    close-in-subcubes μ c = Cases (decide-close-values (subcube c B) K) id
                             (λ ν → 𝟘-elim (μ (c , ν)))

  open splitting spread-is-antitone spread-is-in-subcubes public

\end{code}

Pairs near the limit point. The corner and the side of a stage are
rationals; the limit point lies in every stage
(gist.RealCohesion.NestedIntervals).

\begin{code}

  point-in-stage
   : (δ : ℚ) → 0ℚ < δ → (j : ℕ) (u : Fin n → ℚ) → u is-in stage j
   → (i : Fin n) → (corner j i ℚ- halfₐ (halfₐ δ) < u i)
                 × (u i < (corner j i ℚ+ side j) ℚ+ halfₐ (halfₐ δ))
  point-in-stage δ m j u mu i =
   ℚ<-≤-trans (corner j i ℚ- halfₐ (halfₐ δ)) (corner j i) (u i)
    (ℚ<-subtraction-preserves-order (corner j i) (halfₐ (halfₐ δ))
      (quarter-is-positive δ m))
    (pr₁ (mu i)) ,
   ℚ≤-<-trans (u i) (corner j i ℚ+ side j)
    ((corner j i ℚ+ side j) ℚ+ halfₐ (halfₐ δ))
    (pr₂ (mu i))
    (ℚ<-addition-preserves-order'' (corner j i ℚ+ side j) (halfₐ (halfₐ δ))
      (quarter-is-positive δ m))

  partner-in-stage
   : (δ : ℚ) → 0ℚ < δ → (j K : ℕ) → ρ K < halfₐ (halfₐ δ)
   → (u v : Fin n → ℚ) → u is-in stage j → Near (ρ K) u v
   → (i : Fin n) → (corner j i ℚ- halfₐ (halfₐ δ) < v i)
                 × (v i < (corner j i ℚ+ side j) ℚ+ halfₐ (halfₐ δ))
  partner-in-stage δ m j K rK u v mu nr i =
   ℚ<-trans (corner j i ℚ- halfₐ (halfₐ δ)) (u i ℚ- ρ K) (v i)
    (minus-of-≤-< (corner j i) (u i) (ρ K) (halfₐ (halfₐ δ)) (pr₁ (mu i)) rK)
    (<-move-left (u i) (v i) (ρ K) (pr₁ (nr i))) ,
   ℚ<-trans (v i) (u i ℚ+ ρ K) ((corner j i ℚ+ side j) ℚ+ halfₐ (halfₐ δ))
    (pr₂ (nr i))
    (plus-of-≤-< (u i) (corner j i ℚ+ side j) (ρ K) (halfₐ (halfₐ δ))
      (pr₂ (mu i)) rK)

  point-near-the-limit
   : (δ : ℚ) → 0ℚ < δ → (j : ℕ) → side j < halfₐ (halfₐ δ)
   → (r : Fin n → ℚ)
   → ((i : Fin n) → (corner j i ℚ- halfₐ (halfₐ δ) < r i)
                  × (r i < (corner j i ℚ+ side j) ℚ+ halfₐ (halfₐ δ)))
   → (λ i → ιₐ (r i)) is-coordinatewise-within δ of limit-point
  point-near-the-limit δ m j sj r b i =
   within-from-close δ (ιₐ (r i)) (limit-point i)
    (interval-gives-strictly-close δ
      (corner j i ℚ- halfₐ (halfₐ δ))
       ((corner j i ℚ+ side j) ℚ+ halfₐ (halfₐ δ))
      (ιₐ (r i)) (limit-point i)
      (ιₐ-lower (corner j i ℚ- halfₐ (halfₐ δ)) (r i) (pr₁ (b i)))
      (ιₐ-upper (r i) ((corner j i ℚ+ side j) ℚ+ halfₐ (halfₐ δ)) (pr₂ (b i)))
      (below-the-limit (coordinate-intervals i) j
        (corner j i ℚ- halfₐ (halfₐ δ))
        (ℚ<-subtraction-preserves-order (corner j i) (halfₐ (halfₐ δ))
          (quarter-is-positive δ m)))
      (above-the-limit (coordinate-intervals i) j
        ((corner j i ℚ+ side j) ℚ+ halfₐ (halfₐ δ))
        (ℚ<-addition-preserves-order'' (corner j i ℚ+ side j) (halfₐ (halfₐ δ))
          (quarter-is-positive δ m)))
      (stage-interval-is-short (corner j i) (side j) δ m sj))

  close-values-near-the-limit
   : (δ : ℚ) (m : 0ℚ < δ) (j K : ℕ)
   → side j < halfₐ (halfₐ δ)
   → ρ K < halfₐ (halfₐ δ)
   → ((y : ♭ (ℝ^ n)) → ♭-counit y is-coordinatewise-within δ of limit-point
                     → ♭-counit (h y) is-strictly-within halfₐ (halfₐ ε)
                                      of ♭-counit (h (limit-point ^♭)))
   → (α β : ℚ)
   → α < ♭-counit (h (limit-point ^♭)) → ♭-counit (h (limit-point ^♭)) < β
   → β ℚ- α < halfₐ ε
   → Close-Values ε (stage j) K
  close-values-near-the-limit δ m j K sj rK f α β k k' w (u ^♭) (v ^♭) mu nr =
   Close-from-interval ε (α ℚ- halfₐ (halfₐ ε)) (β ℚ+ halfₐ (halfₐ ε))
    (g (u ^♭)) (g (v ^♭)) (pr₁ bu) (pr₂ bu) (pr₁ bv) (pr₂ bv)
    (widened-interval-is-short α β ε w)
   where
    bu : (α ℚ- halfₐ (halfₐ ε) < g (u ^♭)) × (g (u ^♭) < β ℚ+ halfₐ (halfₐ ε))
    bu = bounds-from-strictly-within (halfₐ (halfₐ ε)) α β (g (u ^♭))
          (♭-counit (h (limit-point ^♭)))
          (f ((λ i → ιₐ (u i)) ^♭)
             (point-near-the-limit δ m j sj u (point-in-stage δ m j u mu)))
          k k'

    bv : (α ℚ- halfₐ (halfₐ ε) < g (v ^♭)) × (g (v ^♭) < β ℚ+ halfₐ (halfₐ ε))
    bv = bounds-from-strictly-within (halfₐ (halfₐ ε)) α β (g (v ^♭))
          (♭-counit (h (limit-point ^♭)))
          (f ((λ i → ιₐ (v i)) ^♭)
             (point-near-the-limit δ m j sj v
               (partner-in-stage δ m j K rK u v mu nr)))
          k k'

  spread-contradiction
   : (δ : ℚ) (m : 0ℚ < δ)
   → (Σ j ꞉ ℕ , side j < halfₐ (halfₐ δ))
   → (Σ K ꞉ ℕ , ρ K < halfₐ (halfₐ δ))
   → ((y : ♭ (ℝ^ n)) → ♭-counit y is-coordinatewise-within δ of limit-point
                     → ♭-counit (h y) is-strictly-within halfₐ (halfₐ ε)
                                      of ♭-counit (h (limit-point ^♭)))
   → (α β : ℚ)
   → α < ♭-counit (h (limit-point ^♭)) → ♭-counit (h (limit-point ^♭)) < β
   → β ℚ- α < halfₐ ε
   → Often start → 𝟘 {𝓤₀}
  spread-contradiction δ m (j , sj) (K , rK) f α β k k' w o =
   stages-are-often o j K
    (close-values-near-the-limit δ m j K sj rK f α β k k' w)

\end{code}

So the first box does not spread at every scale, and by crisp excluded
middle it does not spread at some scale.

\begin{code}

  no-spread-at-every-scale : 0ℚ < ε → ¬ Often start
  no-spread-at-every-scale l o =
   ∥∥-rec 𝟘-is-prop γ
    (h-is-continuous (limit-point ^♭) (halfₐ (halfₐ ε))
      (quarter-is-positive ε l))
   where
    γ : (Σ δ ꞉ ℚ , (0ℚ < δ)
                 × ((y : ♭ (ℝ^ n))
                    → ♭-counit y is-coordinatewise-within δ of limit-point
                                   → ♭-counit (h y) is-strictly-within halfₐ
                                      (halfₐ ε)
                                                    of ♭-counit
                                                     (h (limit-point ^♭))))
      → 𝟘
    γ (δ , m , f) =
     ∥∥-rec 𝟘-is-prop ζ
      (ℝ-arithmetically-located (♭-counit (h (limit-point ^♭)))
        (halfₐ ε , halfₐ-is-positive ε l))
     where
      ζ : (Σ (α , β) ꞉ ℚ × ℚ ,
            (α < ♭-counit (h (limit-point ^♭)) < β) × (β ℚ- α < halfₐ ε))
        → 𝟘
      ζ ((α , β) , (k , k') , w) =
       spread-contradiction δ m
        (sides-become-small (halfₐ (halfₐ δ)) (quarter-is-positive δ m))
        (ρ-becomes-small (halfₐ (halfₐ δ)) (quarter-is-positive δ m))
        f α β k k' w o

  close-values-somewhere : 0ℚ < ε → ∃ K ꞉ ℕ , Close-Values ε start K
  close-values-somewhere l =
   Cases (cem (∃ K ꞉ ℕ , Close-Values ε start K) ∃-is-prop) id
    (λ μ → 𝟘-elim (no-spread-at-every-scale l (λ K c → μ ∣ K , c ∣)))

\end{code}

All rational ε and all boxes of side two, by crisp representatives.

\begin{code}

 close-values-on-boxes
  : (ε : ℚ) (a : Fin n → ℚ) → 0ℚ < ε → ∃ K ꞉ ℕ , Close-Values ε (a , two) K
 close-values-on-boxes =
  crisp-elim₂ ℚ-has-crisp-representatives
   (Fin-functions-have-crisp-representatives fe n 0ℚ
     ℚ-has-crisp-representatives)
   (λ ε a → 0ℚ < ε → ∃ K ꞉ ℕ , Close-Values ε (a , two) K)
   (λ ε a → at-scale.close-values-somewhere ε a)

\end{code}

Small oscillation around every real point, crisp or not: a rational box
around x on whose crisp rational points the values are ε-close. The
point lies in a rational interval (r i , s i) of length less than two
in each coordinate, so in the middle of the box of side two with corner
s - two; uniform continuity there gives a scale K, and a box around x
inside (r , s) whose sides are less than 2⁻⁽ᴷ⁺¹⁾ has the property
(Box-Inside and box-inside, which are those of
gist.RealCohesion.RationalBoxExtension).

\begin{code}

 Small-Oscillation : ℚ → (Fin n → ℚ) → (Fin n → ℚ) → 𝓤₀ ̇
 Small-Oscillation ε a b =
    (u v : ♭ (Fin n → ℚ))
  → In-Box a b (♭-counit u) → In-Box a b (♭-counit v)
  → Close ε (g u) (g v)

 Coordinate-Interval : ℝ → 𝓤₀ ̇
 Coordinate-Interval t = Σ (r , s) ꞉ ℚ × ℚ , (r < t < s) × (s ℚ- r < two)

 Box-Inside : (r s : ℚ) (t : ℝ) (K : ℕ) → 𝓤₀ ̇
 Box-Inside = RBE.Box-Inside

 box-inside : (r s : ℚ) (t : ℝ) (K : ℕ) → r < t → t < s → ∥ Box-Inside r s t K ∥
 box-inside = RBE.box-inside

 small-oscillation-from-boxes
  : (ε : ℚ) (x : ℝ^ n) (K : ℕ) (c : (i : Fin n) → Coordinate-Interval (x i))
  → Close-Values ε ((λ i → pr₂ (pr₁ (c i)) ℚ- two) , two) K
  → (d : (i : Fin n) → Box-Inside (pr₁ (pr₁ (c i))) (pr₂ (pr₁ (c i))) (x i) K)
  → Around (λ i → pr₁ (pr₁ (d i))) (λ i → pr₂ (pr₁ (d i))) x
  × Small-Oscillation ε (λ i → pr₁ (pr₁ (d i))) (λ i → pr₂ (pr₁ (d i)))
 small-oscillation-from-boxes ε x K c F d =
  (λ i → pr₁ (pr₂ (d i)) , pr₁ (pr₂ (pr₂ (d i)))) ,
  (λ u v mu mv → F u v (in-start u mu) (near u v mu mv))
  where
   inside : (u : ♭ (Fin n → ℚ))
          → In-Box (λ i → pr₁ (pr₁ (d i))) (λ i → pr₂ (pr₁ (d i))) (♭-counit u)
          → (i : Fin n)
          → (pr₁ (pr₁ (c i)) < ♭-counit u i) × (♭-counit u i < pr₂ (pr₁ (c i)))
   inside u mu i =
    pr₂ (pr₂ (pr₂ (pr₂ (d i)))) (♭-counit u i) (pr₁ (mu i)) (pr₂ (mu i))

   in-start : (u : ♭ (Fin n → ℚ))
            → In-Box (λ i → pr₁ (pr₁ (d i))) (λ i → pr₂ (pr₁ (d i)))
               (♭-counit u)
            → ♭-counit u is-in ((λ i → pr₂ (pr₁ (c i)) ℚ- two) , two)
   in-start u mu i =
    ℚ<-coarser-than-≤ (pr₂ (pr₁ (c i)) ℚ- two) (♭-counit u i)
     (ℚ<-trans (pr₂ (pr₁ (c i)) ℚ- two) (pr₁ (pr₁ (c i))) (♭-counit u i)
       (corner-below (pr₁ (pr₁ (c i))) (pr₂ (pr₁ (c i))) (pr₂ (pr₂ (c i))))
       (pr₁ (inside u mu i))) ,
    ℚ<-coarser-than-≤ (♭-counit u i) ((pr₂ (pr₁ (c i)) ℚ- two) ℚ+ two)
     (transport (♭-counit u i <_) (minus-plus (pr₂ (pr₁ (c i))) two ⁻¹)
       (pr₂ (inside u mu i)))
    where
     corner-below : (r s : ℚ) → s ℚ- r < two → s ℚ- two < r
     corner-below r s w = <-move-left s r two
                           (transport (s <_) (ℚ+-comm two r)
                             (<-move-right s two r w))

   near : (u v : ♭ (Fin n → ℚ))
        → In-Box (λ i → pr₁ (pr₁ (d i))) (λ i → pr₂ (pr₁ (d i))) (♭-counit u)
        → In-Box (λ i → pr₁ (pr₁ (d i))) (λ i → pr₂ (pr₁ (d i))) (♭-counit v)
        → Near (ρ K) (♭-counit u) (♭-counit v)
   near u v mu mv i =
    near-in-a-short-interval (pr₁ (pr₁ (d i))) (pr₂ (pr₁ (d i))) (ρ K)
     (♭-counit u i) (♭-counit v i) (pr₁ (mu i)) (pr₂ (mu i)) (pr₁ (mv i))
      (pr₂ (mv i))
     (pr₁ (pr₂ (pr₂ (pr₂ (d i)))))

 small-oscillation-around
  : (x : ℝ^ n) (ε : ℚ) → 0ℚ < ε
  →
  ∃ (a , b) ꞉ (Fin n → ℚ) × (Fin n → ℚ) , Around a b x × Small-Oscillation ε a b
 small-oscillation-around x ε l =
  ∥∥-rec ∃-is-prop γ
   (Fin-choice pt n
     (λ i → ℝ-arithmetically-located (x i) (two , two-is-positive)))
  where
   γ : ((i : Fin n) → Coordinate-Interval (x i))
     → ∃ (a , b) ꞉ (Fin n → ℚ) × (Fin n → ℚ) ,
         Around a b x × Small-Oscillation ε a b
   γ c = ∥∥-rec ∃-is-prop δ
          (close-values-on-boxes ε (λ i → pr₂ (pr₁ (c i)) ℚ- two) l)
    where
     δ : (Σ K ꞉ ℕ , Close-Values ε ((λ i → pr₂ (pr₁ (c i)) ℚ- two) , two) K)
       → ∃ (a , b) ꞉ (Fin n → ℚ) × (Fin n → ℚ) ,
           Around a b x × Small-Oscillation ε a b
     δ (K , F) =
      ∥∥-functor
       (λ d → ((λ i → pr₁ (pr₁ (d i))) , (λ i → pr₂ (pr₁ (d i)))) ,
              small-oscillation-from-boxes ε x K c F d)
       (Fin-choice pt n
         (λ i → box-inside (pr₁ (pr₁ (c i))) (pr₂ (pr₁ (c i))) (x i) K
                  (pr₁ (pr₁ (pr₂ (c i)))) (pr₂ (pr₁ (pr₂ (c i))))))

\end{code}
