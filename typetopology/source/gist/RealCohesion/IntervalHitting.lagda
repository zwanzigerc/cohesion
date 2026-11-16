Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 10 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Interval hitting: a positive form of sequential continuity for
arbitrary functions, from the constancy of maps ℝ → Q.

Let f : ℝ → ℝ be any function, a any real number and z a sequence with
z j within ρ j = 2⁻⁽ʲ⁺¹⁾ of a, none of them crisp. Suppose every map
ℝ → Q is constant, where Q is the quotient of levels by finite chains
(gist.RealCohesion.FiniteChainQuotient), and that u < f a < v for
rationals u and v. Then u < f (z j) < v for some j. We prove this for
two functions at once, which also lets us say where z j lies.

It follows from sequential hitting (gist.RealCohesion.SequentialHitting)
applied to the window function 2ᵐ min (f - u , v - f). This function
is greater than 1 at a when m is large, and it is positive exactly
where u < f < v. In Fable's note on Axiom T [1], Lemma S plays this
role. Under crisp excluded middle, interval hitting gives the
continuity of crisp functions at crisp points
(gist.RealCohesion.CrispContinuity).

As in gist.RealCohesion.RealLattice, we use --lossy-unification and the
abstract embedding ιₐ.

[1] Fable. Shulman's stated questions: three updates, Part A.
    Working note, 10 November 2026, audited by GPT-6 Astra.
    references/F18-shulman-three-updates.md

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.IntervalHitting
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Order hiding (max)
open import Notation.CanonicalMap
open import Notation.Order
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.RationalArithmetic
 using (minus-zero ; <-add-right ; <-sub-right)
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealLattice fe pe pt
open import gist.RealCohesion.RealLimits fe pe pt hiding (ρ-antitone)
open import gist.RealCohesion.RealLimits fe pe pt using (ρ-antitone) public
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
open import gist.RealCohesion.SequentialHitting fe pe pt
 using (module sequential-hitting)
open import gist.RealCohesion.ApproximateIVTReduction fe pe pt
 using (dbl^-of-zero ; dbl^-of-ρ ; dbl-ℝ ; below-dbl-ℝ ; below-dbl-ℝ⁻¹)

open PropositionalTruncation pt

\end{code}

Margins. If u < x < v, then for some N the real number x is more than
ρ N away from u and from v, and then also for every larger N.

\begin{code}

Margin : ℝ → ℚ → ℚ → ℕ → 𝓤₀ ̇
Margin x u v N = ((ρ N ℚ+ u) < x) × (x < (v ℚ- ρ N))

margin-exists : (x : ℝ) (u v : ℚ) → u < x → x < v → ∃ N ꞉ ℕ , Margin x u v N
margin-exists x u v l m = ∥∥-rec ∃-is-prop γ (rounded-left-d x u l)
 where
  γ : (Σ u₀ ꞉ ℚ , (u < u₀) × (u₀ < x)) → ∃ N ꞉ ℕ , Margin x u v N
  γ (u₀ , a , b) =
   ∥∥-functor δ (rounded-right-b (upper-cut-of x) (rounded-from-real-R x) v m)
   where
    δ : (Σ v₀ ꞉ ℚ , (v₀ < v) × (x < v₀)) → Σ N ꞉ ℕ , Margin x u v N
    δ (v₀ , c , d) = N , I , II
     where
      s₁ : Σ n ꞉ ℕ , ρ n < u₀ ℚ- u
      s₁ = ρ-becomes-small (u₀ ℚ- u) (ℚ<-difference-positive u u₀ a)

      s₂ : Σ n ꞉ ℕ , ρ n < v ℚ- v₀
      s₂ = ρ-becomes-small (v ℚ- v₀) (ℚ<-difference-positive v₀ v c)

      N₁ N₂ N : ℕ
      N₁ = pr₁ s₁
      N₂ = pr₁ s₂
      N  = N₁ +ℕ N₂

      e₁ : ρ N < u₀ ℚ- u
      e₁ =
       ℚ≤-<-trans (ρ N) (ρ N₁) (u₀ ℚ- u) (ρ-antitone N₁ N (≤-+ N₁ N₂)) (pr₂ s₁)

      e₂ : ρ N < v ℚ- v₀
      e₂ =
       ℚ≤-<-trans (ρ N) (ρ N₂) (v ℚ- v₀) (ρ-antitone N₂ N (≤-+' N₁ N₂)) (pr₂ s₂)

      I : (ρ N ℚ+ u) < x
      I = use-rounded-real-L x (ρ N ℚ+ u) u₀ (<-add-right (ρ N) u₀ u e₁) b

      II : x < (v ℚ- ρ N)
      II = use-rounded-real-R x v₀ (v ℚ- ρ N)
            (<-sub-right v₀ v (ρ N)
              (transport (_< v) (ℚ+-comm (ρ N) v₀) (<-add-right (ρ N) v v₀ e₂)))
            d

margin-mono : (x : ℝ) (u v : ℚ) (N N' : ℕ) → N ≤ N' → Margin x u v N
            → Margin x u v N'
margin-mono x u v N N' l (a , b) = I , II
 where
  k : ρ N' ≤ ρ N
  k = ρ-antitone N N' l

  I : (ρ N' ℚ+ u) < x
  I = use-rounded-real-L' x (ρ N' ℚ+ u) (ρ N ℚ+ u)
       (ℚ≤-addition-preserves-order (ρ N') (ρ N) u k) a

  II : x < (v ℚ- ρ N')
  II = use-rounded-real-R' x (v ℚ- ρ N) (v ℚ- ρ N')
        (minus-is-antitone v (ρ N') (ρ N) k) b

\end{code}

The window function of f for u < v, scaled by 2ᴺ⁺¹. It is greater
than 1 where f has margin N, and positive only where u < f < v.

\begin{code}

window : ℕ → (ℝ → ℝ) → ℚ → ℚ → ℝ → ℝ
window N f u v w = dbl-ℝ (succ N) (min (f w + ιₐ (ℚ- u)) (ιₐ v + (- f w)))

window-is-large : (N : ℕ) (f : ℝ → ℝ) (u v : ℚ) (w : ℝ)
                → Margin (f w) u v N → 1ℚ < window N f u v w
window-is-large N f u v w (a , b) =
 transport (_< window N f u v w) (dbl^-of-ρ N)
  (below-dbl-ℝ (succ N) (min (f w + ιₐ (ℚ- u)) (ιₐ v + (- f w))) (ρ N)
    (below-min (f w + ιₐ (ℚ- u)) (ιₐ v + (- f w)) (ρ N)
      (translate-strict (f w) (ρ N) u a)
      (reflect-strict (f w) (ρ N) v b)))

window-is-positive⁻¹ : (N : ℕ) (f : ℝ → ℝ) (u v : ℚ) (w : ℝ)
                     → 0ℚ < window N f u v w → (u < f w) × (f w < v)
window-is-positive⁻¹ N f u v w p = I , II
 where
  m : ℝ
  m = min (f w + ιₐ (ℚ- u)) (ιₐ v + (- f w))

  positive : 0ℚ < m
  positive = below-dbl-ℝ⁻¹ (succ N) m 0ℚ
              (transport (_< dbl-ℝ (succ N) m) (dbl^-of-zero (succ N) ⁻¹) p)

  I : u < f w
  I = transport (_< f w) (ℚ-zero-left-neutral u)
       (below-translate⁻¹ (f w) 0ℚ u
         (below-min-left (f w + ιₐ (ℚ- u)) (ιₐ v + (- f w)) 0ℚ positive))

  II : f w < v
  II = transport (f w <_) (minus-zero v)
        (below-reflect⁻¹ (f w) 0ℚ v
          (below-min-right (f w + ιₐ (ℚ- u)) (ιₐ v + (- f w)) 0ℚ positive))

\end{code}

Interval hitting, for two functions and for one.

\begin{code}

module _ (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v) where

 interval-hitting₂
  : (f g : ℝ → ℝ) (a : ℝ) (z : ℕ → ℝ)
  → ((j : ℕ) → within (ρ j) (z j) a)
  → (u v u' v' : ℚ)
  → u < f a → f a < v
  → u' < g a → g a < v'
  → ∃ j ꞉ ℕ , ((u < f (z j)) × (f (z j) < v))
            × ((u' < g (z j)) × (g (z j) < v'))
 interval-hitting₂ f g a z c u v u' v' l m l' m' =
  ∥∥-rec ∃-is-prop γ (margin-exists (f a) u v l m)
  where
   Goal : 𝓤₀ ̇
   Goal = Σ j ꞉ ℕ , ((u < f (z j)) × (f (z j) < v))
                  × ((u' < g (z j)) × (g (z j) < v'))

   γ : (Σ N₁ ꞉ ℕ , Margin (f a) u v N₁) → ∥ Goal ∥
   γ (N₁ , μ₁) = ∥∥-rec ∃-is-prop δ (margin-exists (g a) u' v' l' m')
    where
     δ : (Σ N₂ ꞉ ℕ , Margin (g a) u' v' N₂) → ∥ Goal ∥
     δ (N₂ , μ₂) =
      ∥∥-functor ε (sequential-hitting.sequential-hitting ν h a z c h-at-a)
      where
       N : ℕ
       N = N₁ +ℕ N₂

       h : ℝ → ℝ
       h w = min (window N f u v w) (window N g u' v' w)

       h-at-a : ιₐ 1ℚ ≤ h a
       h-at-a = >-gives-ιₐ-≤ (h a) 1ℚ
                 (below-min (window N f u v a) (window N g u' v' a) 1ℚ
                   (window-is-large N f u v a
                     (margin-mono (f a) u v N₁ N (≤-+ N₁ N₂) μ₁))
                   (window-is-large N g u' v' a
                     (margin-mono (g a) u' v' N₂ N (≤-+' N₁ N₂) μ₂)))

       ε : (Σ k ꞉ ℕ , 0ℚ < h (z k)) → Goal
       ε (k , p) = k ,
                   window-is-positive⁻¹ N f u v (z k)
                    (below-min-left (window N f u v (z k))
                      (window N g u' v' (z k)) 0ℚ p) ,
                   window-is-positive⁻¹ N g u' v' (z k)
                    (below-min-right (window N f u v (z k))
                      (window N g u' v' (z k)) 0ℚ p)

 interval-hitting
  : (f : ℝ → ℝ) (a : ℝ) (z : ℕ → ℝ)
  → ((j : ℕ) → within (ρ j) (z j) a)
  → (u v : ℚ) → u < f a → f a < v
  → ∃ j ꞉ ℕ , (u < f (z j)) × (f (z j) < v)
 interval-hitting f a z c u v l m =
  ∥∥-functor (λ (j , o , _) → j , o)
   (interval-hitting₂ f f a z c u v u v l m l m)

\end{code}
