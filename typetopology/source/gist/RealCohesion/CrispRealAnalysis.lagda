Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 26 October 2026. See the AI disclosure in
gist.RealCohesion.index.

Crisp real analysis: signs, continuity of crisp functions, and paths
that cannot leave zero.

This module collects the classical analysis of crisp real functions at
crisp points that is used for the zero-plateau invariant
(gist.RealCohesion.ZeroPlateauInvariant). Classical reasoning is only
applied to crisp propositions, through crisp excluded middle.

 * Signs of real numbers, and the fact that a crisp nonzero real number
   is positive or negative.

 * The continuity interface Crisp-Real-Continuity: a crisp function
   f : ℝ → ℝ is continuous at crisp points t, in the sense that for
   rationals u < f t < v there is a rational interval around t on whose
   crisp points u < f < v. This is a weak form of Shulman's Theorem
   11.5 [1], which derives the ε-δ continuity of crisp functions at
   crisp points, for all points of a neighbourhood. That theorem is
   stated with Axioms R♭ and T; its proof also uses crisp excluded
   middle, through his Theorem 8.32. We do not derive it here: it is
   an explicit assumption of the results that use it. It holds in Shulman's
   intended model, sheaves on Cartesian spaces with continuous maps, where a
   crisp map ℝ → ℝ is a continuous function. It has since been derived: from
   crisp excluded middle and Axiom R♭ in gist.RealCohesion.CrispContinuity, and
   from Axiom R♭ alone in gist.RealCohesion.CrispFunctionsAreContinuous
   (R♭-gives-crisp-real-continuity in gist.RealCohesion.Theorems).

 * Separation: if a crisp f takes values below a rational c and above c
   at two crisp rational points of an interval on whose crisp points f
   avoids a rational interval (a , b) around c, we get a contradiction.
   This is an intermediate value argument, proved from the
   connectedness of rational intervals
   (gist.RealCohesion.CrispConnectedness).

 * Staying at zero: if f t ＝ 0 at a crisp t, and on the crisp points of
   a rational interval around t the function f avoids rational
   intervals arbitrarily close to 0 on both sides, then f is 0 at all
   crisp points of that interval.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.CrispRealAnalysis
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Notation.CanonicalMap
open import Notation.Order
open import Rationals.MinMax
open import Rationals.Order
open import Rationals.Type
open import UF.Base
open import UF.Powerset
open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import gist.CohesiveApartness.Flat
open import gist.RealCohesion.CrispConnectedness fe pe pt
 using (Open-At-Crisp-Points ; crisp-interval-is-connected)
open import gist.RealCohesion.CrispDecisions
open import gist.RealCohesion.CrispRationals
open import gist.RealCohesion.RealOrder fe pe pt public

open PropositionalTruncation pt

\end{code}

Neighbourhoods. A family W holds near t if it holds at the crisp points
of a rational interval around t.

\begin{code}

Holds-Near : {𝓦 : Universe} → (ℝ → 𝓦 ̇ ) → ℝ → 𝓤₁ ⊔ 𝓦 ̇
Holds-Near W t = ∃ (r , r') ꞉ ℚ × ℚ , (r < t) × (t < r')
                                    × ((@♭ s : ℝ) → r < s → s < r' → W s)

holds-near-map : {𝓦 𝓦' : Universe} (W : ℝ → 𝓦 ̇ ) (W' : ℝ → 𝓦' ̇ ) (t : ℝ)
               → ((@♭ s : ℝ) → W s → W' s) → Holds-Near W t → Holds-Near W' t
holds-near-map W W' t f = ∥∥-functor γ
 where
  γ : (Σ (r , r') ꞉ ℚ × ℚ ,
        (r < t) × (t < r') × ((@♭ s : ℝ) → r < s → s < r' → W s))
    → Σ (r , r') ꞉ ℚ × ℚ ,
        (r < t) × (t < r') × ((@♭ s : ℝ) → r < s → s < r' → W' s)
  γ ((r , r') , a , b , k) = (r , r') , a , b , (λ s c d → f s (k s c d))

common-neighbourhood : (t : ℝ) (r r' r₁ r₁' : ℚ)
                     → r < t → t < r' → r₁ < t → t < r₁'
                     → Σ (ρ , ρ') ꞉ ℚ × ℚ , (ρ < t) × (t < ρ')
                                         × (r ≤ ρ) × (r₁ ≤ ρ) × (ρ' ≤ r')
                                         × (ρ' ≤ r₁')
common-neighbourhood t r r' r₁ r₁' a b a₁ b₁ =
 (max r r₁ , min r' r₁') ,
 γ (decide-max r r₁) ,
 δ (decide-min r' r₁') ,
 max≤ r r₁ , max≤' r r₁ , min≤ r' r₁' , min≤' r' r₁'
 where
  γ : (max r r₁ ＝ r₁) ∔ (max r r₁ ＝ r) → max r r₁ < t
  γ (inl e) = transport (_< t) (e ⁻¹) a₁
  γ (inr e) = transport (_< t) (e ⁻¹) a

  δ : (min r' r₁' ＝ r') ∔ (min r' r₁' ＝ r₁') → t < min r' r₁'
  δ (inl e) = transport (t <_) (e ⁻¹) b
  δ (inr e) = transport (t <_) (e ⁻¹) b₁

holds-near-both : {𝓦 𝓦' : Universe} (W : ℝ → 𝓦 ̇ ) (W' : ℝ → 𝓦' ̇ ) (t : ℝ)
                → Holds-Near W t → Holds-Near W' t
                → Holds-Near (λ s → W s × W' s) t
holds-near-both W W' t h h' = ∥∥-rec ∃-is-prop γ h
 where
  γ : (Σ (r , r') ꞉ ℚ × ℚ ,
        (r < t) × (t < r') × ((@♭ s : ℝ) → r < s → s < r' → W s))
    → Holds-Near (λ s → W s × W' s) t
  γ ((r , r') , a , b , k) = ∥∥-functor δ h'
   where
    δ : (Σ (r₁ , r₁') ꞉ ℚ × ℚ ,
          (r₁ < t) × (t < r₁') × ((@♭ s : ℝ) → r₁ < s → s < r₁' → W' s))
      → Σ (ρ , ρ') ꞉ ℚ × ℚ ,
          (ρ < t) × (t < ρ') × ((@♭ s : ℝ) → ρ < s → s < ρ' → W s × W' s)
    δ ((r₁ , r₁') , a₁ , b₁ , k₁) = (ρ , ρ') , c , d , ε
     where
      ν = common-neighbourhood t r r' r₁ r₁' a b a₁ b₁
      ρ  = pr₁ (pr₁ ν)
      ρ' = pr₂ (pr₁ ν)
      c  = pr₁ (pr₂ ν)
      d  = pr₁ (pr₂ (pr₂ ν))
      r≤ρ   = pr₁ (pr₂ (pr₂ (pr₂ ν)))
      r₁≤ρ  = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ ν))))
      ρ'≤r' = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ ν)))))
      ρ'≤r₁' = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ ν)))))

      ε : (@♭ s : ℝ) → ρ < s → s < ρ' → W s × W' s
      ε s l m = k s (use-rounded-real-L' s r ρ r≤ρ l)
                 (use-rounded-real-R' s ρ' r' ρ'≤r' m) ,
                k₁ s (use-rounded-real-L' s r₁ ρ r₁≤ρ l)
                 (use-rounded-real-R' s ρ' r₁' ρ'≤r₁' m)

\end{code}

A crisp rational point in two rational intervals around a real number.

\begin{code}

crisp-rational-near : (x : ℝ) (r r' r₁ r₁' : ℚ)
                    → r < x → x < r' → r₁ < x → x < r₁'
                    → Σ u ꞉ ♭ ℚ , (r < ♭-counit u) × (♭-counit u < r')
                                × (r₁ < ♭-counit u) × (♭-counit u < r₁')
crisp-rational-near x r r' r₁ r₁' a b a₁ b₁ = γ (ℚ-has-crisp-representatives α₀)
 where
  ν = common-neighbourhood x r r' r₁ r₁' a b a₁ b₁
  ρ  = pr₁ (pr₁ ν)
  ρ' = pr₂ (pr₁ ν)
  c  = pr₁ (pr₂ ν)
  d  = pr₁ (pr₂ (pr₂ ν))
  r≤ρ   = pr₁ (pr₂ (pr₂ (pr₂ ν)))
  r₁≤ρ  = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ ν))))
  ρ'≤r' = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ ν)))))
  ρ'≤r₁' = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ ν)))))

  δ : Σ α ꞉ ℚ , (ρ < α) × (α < ρ')
  δ = ℚ-dense ρ ρ' (cuts-are-ordered x ρ ρ' c d)

  α₀ : ℚ
  α₀ = pr₁ δ

  γ : (Σ u ꞉ ♭ ℚ , ♭-counit u ＝ α₀)
    → Σ u ꞉ ♭ ℚ , (r < ♭-counit u) × (♭-counit u < r')
                × (r₁ < ♭-counit u) × (♭-counit u < r₁')
  γ (u , e) = u ,
              transport (r <_) (e ⁻¹) (ℚ≤-<-trans r ρ α₀ r≤ρ (pr₁ (pr₂ δ))) ,
              transport (_< r') (e ⁻¹) (ℚ<-≤-trans α₀ ρ' r' (pr₂ (pr₂ δ)) ρ'≤r')
               ,
              transport (r₁ <_) (e ⁻¹) (ℚ≤-<-trans r₁ ρ α₀ r₁≤ρ (pr₁ (pr₂ δ))) ,
              transport (_< r₁') (e ⁻¹)
               (ℚ<-≤-trans α₀ ρ' r₁' (pr₂ (pr₂ δ)) ρ'≤r₁')

crisp-rational-between : (p q : ℚ) → p < q
                       → Σ u ꞉ ♭ ℚ , (p < ♭-counit u) × (♭-counit u < q)
crisp-rational-between p q l = γ (ℚ-has-crisp-representatives (pr₁ δ))
 where
  δ : Σ c ꞉ ℚ , (p < c) × (c < q)
  δ = ℚ-dense p q l

  γ : (Σ u ꞉ ♭ ℚ , ♭-counit u ＝ pr₁ δ)
    → Σ u ꞉ ♭ ℚ , (p < ♭-counit u) × (♭-counit u < q)
  γ (u , e) = u , transport (p <_) (e ⁻¹) (pr₁ (pr₂ δ)) ,
               transport (_< q) (e ⁻¹) (pr₂ (pr₂ δ))

\end{code}

The continuity interface, and its one-sided consequences.

\begin{code}

Crisp-Real-Continuity : 𝓤₁ ̇
Crisp-Real-Continuity =
   (@♭ f : ℝ → ℝ) (@♭ t : ℝ) (u v : ℚ)
 → u < f t → f t < v
 → Holds-Near (λ s → (u < f s) × (f s < v)) t

module _ (@♭ continuity : Crisp-Real-Continuity) where

 lower-semicontinuity : (@♭ f : ℝ → ℝ) (@♭ t : ℝ) (u : ℚ)
                      → u < f t → Holds-Near (λ s → u < f s) t
 lower-semicontinuity f t u l = ∥∥-rec ∃-is-prop γ (inhabited-from-real-R (f t))
  where
   γ : (Σ v ꞉ ℚ , f t < v) → Holds-Near (λ s → u < f s) t
   γ (v , m) = ∥∥-functor δ (continuity f t u v l m)
    where
     δ : (Σ (r , r') ꞉ ℚ × ℚ , (r < t) × (t < r')
                             × ((@♭ s : ℝ) → r < s → s < r'
                                → (u < f s) × (f s < v)))
       → Σ (r , r') ꞉ ℚ × ℚ ,
           (r < t) × (t < r') × ((@♭ s : ℝ) → r < s → s < r' → u < f s)
     δ ((r , r') , a , b , k) = (r , r') , a , b , (λ s c d → pr₁ (k s c d))

 upper-semicontinuity : (@♭ f : ℝ → ℝ) (@♭ t : ℝ) (v : ℚ)
                      → f t < v → Holds-Near (λ s → f s < v) t
 upper-semicontinuity f t v m = ∥∥-rec ∃-is-prop γ (inhabited-from-real-L (f t))
  where
   γ : (Σ u ꞉ ℚ , u < f t) → Holds-Near (λ s → f s < v) t
   γ (u , l) = ∥∥-functor δ (continuity f t u v l m)
    where
     δ : (Σ (r , r') ꞉ ℚ × ℚ , (r < t) × (t < r')
                             × ((@♭ s : ℝ) → r < s → s < r'
                                → (u < f s) × (f s < v)))
       → Σ (r , r') ꞉ ℚ × ℚ ,
           (r < t) × (t < r') × ((@♭ s : ℝ) → r < s → s < r' → f s < v)
     δ ((r , r') , a , b , k) = (r , r') , a , b , (λ s c d → pr₂ (k s c d))

\end{code}

From now on we assume crisp excluded middle. A crisp nonzero real
number has a sign.

\begin{code}

module _ (@♭ cem : Crisp-EM 𝓤₁) where

 cem₀ : Crisp-EM 𝓤₀
 cem₀ = Crisp-EM-lower {𝓤₀} {𝓤₁} cem

 crisp-nonzero-has-sign : (@♭ x : ℝ) → ¬ (x ＝ 0ℝ) → Σ σ ꞉ 𝟚 , Has-Sign σ x
 crisp-nonzero-has-sign x ν =
  γ (cem₀ (0ℚ < x) (Has-Sign-is-prop ₁ x))
   (cem₀ (x < 0ℚ) (Has-Sign-is-prop ₀ x))
  where
   γ : (0ℚ < x) ∔ ¬ (0ℚ < x) → (x < 0ℚ) ∔ ¬ (x < 0ℚ) → Σ σ ꞉ 𝟚 , Has-Sign σ x
   γ (inl l) _       = ₁ , l
   γ (inr _) (inl l) = ₀ , l
   γ (inr a) (inr b) = 𝟘-elim (ν (no-sign-gives-zero x a b))

\end{code}

Separation. The family of points where a crisp f is below a crisp
rational c is crisp; we define it at top level so that it does not
depend on the other, ordinary, data.

\begin{code}

below : (ℝ → ℝ) → ℚ → ℝ → 𝓤₀ ̇
below f c s = f s < c

below-is-prop : (f : ℝ → ℝ) (c : ℚ) (s : ℝ) → is-prop (below f c s)
below-is-prop f c s = ∈-is-prop (upper-cut-of (f s)) c

Avoids : (ℝ → ℝ) → ℚ → ℚ → ℚ → ℚ → 𝓤₁ ̇
Avoids f r r' a b = (@♭ s : ℝ) → r < s → s < r' → ¬ ((a < f s) × (f s < b))

Avoids-Intervals-Near-Zero : (ℝ → ℝ) → ℚ → ℚ → 𝓤₁ ̇
Avoids-Intervals-Near-Zero f r r' =
   ((e : ℚ) → 0ℚ < e
            → ∃ (a , b) ꞉ ℚ × ℚ ,
                (0ℚ < a) × (a < b) × (b < e) × Avoids f r r' a b)
 × ((e : ℚ) → e < 0ℚ
            → ∃ (a , b) ꞉ ℚ × ℚ ,
                (e < a) × (a < b) × (b < 0ℚ) × Avoids f r r' a b)

module _ (@♭ cem : Crisp-EM 𝓤₁)
         (@♭ continuity : Crisp-Real-Continuity)
       where

 private
  cem' : Crisp-EM 𝓤₀
  cem' = cem₀ cem

 module _ (@♭ f : ℝ → ℝ)
          (r r' a b : ℚ)
          (@♭ c : ℚ)
          (a<c : a < c)
          (c<b : c < b)
          (avoids : Avoids f r r' a b)
        where

  private
   below-open : (@♭ α β : ℚ)
              → Open-At-Crisp-Points cem' (below f c) (below-is-prop f c) α β
                 (below f c)
   below-open α β t _ _ m = upper-semicontinuity continuity f t c m

   not-below-open : (@♭ α β : ℚ)
                  → r < α → β < r'
                  → Open-At-Crisp-Points cem' (below f c) (below-is-prop f c) α
                     β
                     (λ s → ¬ below f c s)
   not-below-open α β r<α β<r' t α≤t t≤β ν =
    ∥∥-functor γ (lower-semicontinuity continuity f t c c<ft)
    where
     a<ft : a < f t
     a<ft = located-above (f t) a c a<c ν

     ft≮b : ¬ (f t < b)
     ft≮b m = avoids t (above-lower-bound t r α r<α α≤t)
                       (below-upper-bound t β r' β<r' t≤β)
                       (a<ft , m)

     c<ft : c < f t
     c<ft = located-above (f t) c b c<b ft≮b

     γ : (Σ (ρ , ρ') ꞉ ℚ × ℚ ,
           (ρ < t) × (t < ρ') × ((@♭ s : ℝ) → ρ < s → s < ρ' → c < f s))
       → Σ (ρ , ρ') ꞉ ℚ × ℚ ,
           (ρ < t) × (t < ρ') × ((@♭ s : ℝ) → ρ < s → s < ρ' → ¬ below f c s)
     γ ((ρ , ρ') , l , m , k) =
      (ρ , ρ') , l , m , (λ s n o p → not-below-and-above (f s) c (k s n o) p)

   connected : (@♭ α β : ℚ) → α < β → r < α → β < r'
             → below f c (ι α) → below f c (ι β)
   connected α β α<β r<α β<r' =
    lr-implication
     (crisp-interval-is-connected cem' (below f c) (below-is-prop f c) α β α<β
       (below-open α β) (not-below-open α β r<α β<r'))

   connected' : (@♭ α β : ℚ) → α < β → r < α → β < r'
              → below f c (ι β) → below f c (ι α)
   connected' α β α<β r<α β<r' =
    rl-implication
     (crisp-interval-is-connected cem' (below f c) (below-is-prop f c) α β α<β
       (below-open α β) (not-below-open α β r<α β<r'))

  separation : (@♭ α β : ℚ)
             → r < α → α < r' → r < β → β < r'
             → f (ι α) < c → c < f (ι β) → 𝟘 {𝓤₀}
  separation α β r<α α<r' r<β β<r' fα<c c<fβ = γ (ℚ-trichotomous α β)
   where
    γ : (α < β) ∔ (α ＝ β) ∔ (β < α) → 𝟘 {𝓤₀}
    γ (inl l)       =
     not-below-and-above (f (ι β)) c c<fβ (connected α β l r<α β<r' fα<c)
    γ (inr (inl e)) = not-below-and-above (f (ι α)) c
                       (transport (λ - → c < f (ι -)) (e ⁻¹) c<fβ) fα<c
    γ (inr (inr l)) =
     not-below-and-above (f (ι β)) c c<fβ (connected' β α l r<β α<r' fα<c)

\end{code}

Staying at zero.

\begin{code}

 module _ (@♭ f : ℝ → ℝ)
          (@♭ t : ℝ)
          (r r' : ℚ)
          (r<t : r < t)
          (t<r' : t < r')
          (ft-is-0 : f t ＝ 0ℝ)
          (avoids : Avoids-Intervals-Near-Zero f r r')
        where

  private
   positive-value-impossible : (@♭ s : ℝ) → r < s → s < r' → 0ℚ < f s → 𝟘 {𝓤₀}
   positive-value-impossible s r<s s<r' l =
    ∥∥-rec 𝟘-is-prop γ (rounded-left-d (f s) 0ℚ l)
    where
     γ : (Σ e ꞉ ℚ , (0ℚ < e) × (e < f s)) → 𝟘 {𝓤₀}
     γ (e , 0<e , e<fs) = ∥∥-rec 𝟘-is-prop δ (pr₁ avoids e 0<e)
      where
       δ : (Σ (a , b) ꞉ ℚ × ℚ ,
             (0ℚ < a) × (a < b) × (b < e) × Avoids f r r' a b) → 𝟘 {𝓤₀}
       δ ((a , b) , 0<a , a<b , b<e , av) = ε (crisp-rational-between a b a<b)
        where
         ε : (Σ u ꞉ ♭ ℚ , (a < ♭-counit u) × (♭-counit u < b)) → 𝟘 {𝓤₀}
         ε ((c ^♭) , a<c , c<b) =
          ∥∥-rec 𝟘-is-prop ζ (upper-semicontinuity continuity f t c ft<c)
          where
           ft<c : f t < c
           ft<c = transport (_< c) (ft-is-0 ⁻¹) (ℚ<-trans 0ℚ a c 0<a a<c)

           c<fs : c < f s
           c<fs = below-a-real (f s) c e (ℚ<-trans c b e c<b b<e) e<fs

           ζ : (Σ (r₁ , r₁') ꞉ ℚ × ℚ , (r₁ < t) × (t < r₁')
                                     ×
                                     ((@♭ x : ℝ) → r₁ < x → x < r₁' → f x < c))
             → 𝟘 {𝓤₀}
           ζ ((r₁ , r₁') , a₁ , b₁ , k₁) =
            ∥∥-rec 𝟘-is-prop η (lower-semicontinuity continuity f s c c<fs)
            where
             η : (Σ (r₂ , r₂') ꞉ ℚ × ℚ , (r₂ < s) × (s < r₂')
                                       × ((@♭ x : ℝ) → r₂ < x → x < r₂'
                                          → c < f x))
               → 𝟘 {𝓤₀}
             η ((r₂ , r₂') , a₂ , b₂ , k₂) =
              θ (crisp-rational-near t r r' r₁ r₁' r<t t<r' a₁ b₁)
                (crisp-rational-near s r r' r₂ r₂' r<s s<r' a₂ b₂)
              where
               θ : (Σ u ꞉ ♭ ℚ , (r < ♭-counit u) × (♭-counit u < r')
                              × (r₁ < ♭-counit u) × (♭-counit u < r₁'))
                 → (Σ u ꞉ ♭ ℚ , (r < ♭-counit u) × (♭-counit u < r')
                              × (r₂ < ♭-counit u) × (♭-counit u < r₂'))
                 → 𝟘 {𝓤₀}
               θ ((α ^♭) , r<α , α<r' , r₁<α , α<r₁')
                ((β ^♭) , r<β , β<r' , r₂<β , β<r₂') =
                separation f r r' a b c a<c c<b av α β r<α α<r' r<β β<r'
                 (k₁ (ι α) r₁<α α<r₁')
                 (k₂ (ι β) r₂<β β<r₂')

   negative-value-impossible : (@♭ s : ℝ) → r < s → s < r' → f s < 0ℚ → 𝟘 {𝓤₀}
   negative-value-impossible s r<s s<r' l =
    ∥∥-rec 𝟘-is-prop γ
     (rounded-right-b (upper-cut-of (f s)) (rounded-from-real-R (f s)) 0ℚ l)
    where
     γ : (Σ e ꞉ ℚ , (e < 0ℚ) × (f s < e)) → 𝟘 {𝓤₀}
     γ (e , e<0 , fs<e) = ∥∥-rec 𝟘-is-prop δ (pr₂ avoids e e<0)
      where
       δ : (Σ (a , b) ꞉ ℚ × ℚ ,
             (e < a) × (a < b) × (b < 0ℚ) × Avoids f r r' a b) → 𝟘 {𝓤₀}
       δ ((a , b) , e<a , a<b , b<0 , av) = ε (crisp-rational-between a b a<b)
        where
         ε : (Σ u ꞉ ♭ ℚ , (a < ♭-counit u) × (♭-counit u < b)) → 𝟘 {𝓤₀}
         ε ((c ^♭) , a<c , c<b) =
          ∥∥-rec 𝟘-is-prop ζ (lower-semicontinuity continuity f t c c<ft)
          where
           c<ft : c < f t
           c<ft = transport (c <_) (ft-is-0 ⁻¹) (ℚ<-trans c b 0ℚ c<b b<0)

           fs<c : f s < c
           fs<c = above-a-real (f s) e c (ℚ<-trans e a c e<a a<c) fs<e

           ζ : (Σ (r₁ , r₁') ꞉ ℚ × ℚ , (r₁ < t) × (t < r₁')
                                     ×
                                     ((@♭ x : ℝ) → r₁ < x → x < r₁' → c < f x))
             → 𝟘 {𝓤₀}
           ζ ((r₁ , r₁') , a₁ , b₁ , k₁) =
            ∥∥-rec 𝟘-is-prop η (upper-semicontinuity continuity f s c fs<c)
            where
             η : (Σ (r₂ , r₂') ꞉ ℚ × ℚ , (r₂ < s) × (s < r₂')
                                       × ((@♭ x : ℝ) → r₂ < x → x < r₂'
                                          → f x < c))
               → 𝟘 {𝓤₀}
             η ((r₂ , r₂') , a₂ , b₂ , k₂) =
              θ (crisp-rational-near t r r' r₁ r₁' r<t t<r' a₁ b₁)
                (crisp-rational-near s r r' r₂ r₂' r<s s<r' a₂ b₂)
              where
               θ : (Σ u ꞉ ♭ ℚ , (r < ♭-counit u) × (♭-counit u < r')
                              × (r₁ < ♭-counit u) × (♭-counit u < r₁'))
                 → (Σ u ꞉ ♭ ℚ , (r < ♭-counit u) × (♭-counit u < r')
                              × (r₂ < ♭-counit u) × (♭-counit u < r₂'))
                 → 𝟘 {𝓤₀}
               θ ((α ^♭) , r<α , α<r' , r₁<α , α<r₁')
                ((β ^♭) , r<β , β<r' , r₂<β , β<r₂') =
                separation f r r' a b c a<c c<b av β α r<β β<r' r<α α<r'
                 (k₂ (ι β) r₂<β β<r₂')
                 (k₁ (ι α) r₁<α α<r₁')

  stays-at-zero : (@♭ s : ℝ) → r < s → s < r' → f s ＝ 0ℝ
  stays-at-zero s r<s s<r' = γ (cem (f s ＝ 0ℝ) ℝ-is-set)
   where
    γ : (f s ＝ 0ℝ) ∔ ¬ (f s ＝ 0ℝ) → f s ＝ 0ℝ
    γ (inl e) = e
    γ (inr ν) = 𝟘-elim (δ (crisp-nonzero-has-sign cem (f s) ν))
     where
      δ : (Σ σ ꞉ 𝟚 , Has-Sign σ (f s)) → 𝟘 {𝓤₀}
      δ (₀ , l) = negative-value-impossible s r<s s<r' l
      δ (₁ , l) = positive-value-impossible s r<s s<r' l

\end{code}
