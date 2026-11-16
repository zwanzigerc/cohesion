Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

A double cover of the punctured plane (gate G25), §2.4 of Fable's note
on Shulman's Theorem 12.6 [1].

For w = (w₁ , w₂) in ℝ² there are four half-planes, one for each side:
east (w₁ > 0), north (w₂ > 0), west (w₁ < 0) and south (w₂ < 0). For
two sides i and j, transition i j : 𝟚 → 𝟚 is the swap if {i , j} is
{south , east}, and the identity otherwise. Cover w is the set of
families φ that give a bit φᵢ for each side i whose half-plane contains
w, such that φⱼ = transition i j φᵢ whenever both half-planes do.

 * (cocycle) If the half-planes of i, j and k all contain w, then
   transition j k ∘ transition i j = transition i k. Opposite sides
   cannot both contain w, so i, j and k lie in two adjacent sides, and
   there the condition holds because transition i i is the identity and
   transition i j = transition j i is an involution. The 64 cases are
   checked one by one; none decides an inequality between reals.

 * (E1) If the half-plane of i contains w, evaluation at i is an
   equivalence Cover w ≃ 𝟚 (Cover-≃-𝟚), with inverse b ↦ τ i b, the
   family with value transition i j b at j.

 * (E2) If the half-planes of i and j contain w, then
   τ i b = τ j (transition i j b) (τ-change).

So Cover is trivial over each half-plane and twisted once around the
origin. It is defined for every w; at w = 0 it has exactly one element,
the empty family, which the proof does not use.

[1] Claude Fable 5.2. Note: Shulman's approximate Brouwer theorem (12.6)
    without the shape modality. Revision 2, 12 November 2026, audited
    by GPT-6 Astra.
    references/F11-shulman-12-6-rev2.md

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.DoubleCover
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import MLTT.Two-Properties
 using (complement ; complement-involutive ; zero-is-not-one)
open import Notation.Order
open import UF.Base
open import UF.Equiv
open import UF.Sets
open import UF.Sets-Properties using (Σ-is-set ; Π-is-set)
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties using (props-are-sets)
open import UF.DiscreteAndSeparated using (𝟚-is-set)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt

\end{code}

The sides, their half-planes, and the transitions.

\begin{code}

data Side : 𝓤₀ ̇ where
 east north west south : Side

Half-Plane : ℝ → ℝ → Side → 𝓤₀ ̇
Half-Plane w₁ w₂ east  = 0ℝ < w₁
Half-Plane w₁ w₂ north = 0ℝ < w₂
Half-Plane w₁ w₂ west  = w₁ < 0ℝ
Half-Plane w₁ w₂ south = w₂ < 0ℝ

half-planes-are-props : (w₁ w₂ : ℝ) (i : Side) → is-prop (Half-Plane w₁ w₂ i)
half-planes-are-props w₁ w₂ east  = <-is-prop 0ℝ w₁
half-planes-are-props w₁ w₂ north = <-is-prop 0ℝ w₂
half-planes-are-props w₁ w₂ west  = <-is-prop w₁ 0ℝ
half-planes-are-props w₁ w₂ south = <-is-prop w₂ 0ℝ

east-west : (w : ℝ) → 0ℝ < w → w < 0ℝ → 𝟘 {𝓤₀}
east-west w l m = <ℝ-irreflexive 0ℝ (ℝ<-trans 0ℝ w 0ℝ l m)

twist : Side → Side → 𝟚
twist south east  = ₁
twist east  south = ₁
twist east  east  = ₀
twist east  north = ₀
twist east  west  = ₀
twist north _     = ₀
twist west  _     = ₀
twist south north = ₀
twist south west  = ₀
twist south south = ₀

flip-if : 𝟚 → 𝟚 → 𝟚
flip-if ₀ b = b
flip-if ₁ b = complement b

transition : Side → Side → 𝟚 → 𝟚
transition i j = flip-if (twist i j)

transition-refl : (i : Side) (b : 𝟚) → transition i i b ＝ b
transition-refl east  b = refl
transition-refl north b = refl
transition-refl west  b = refl
transition-refl south b = refl

cocycle : (w₁ w₂ : ℝ) (i j k : Side)
        → Half-Plane w₁ w₂ i → Half-Plane w₁ w₂ j → Half-Plane w₁ w₂ k
        → (b : 𝟚) → transition j k (transition i j b) ＝ transition i k b
cocycle w₁ w₂ east  east  east  _ _ _ _ = refl
cocycle w₁ w₂ east  east  north _ _ _ _ = refl
cocycle w₁ w₂ east  east  west  _ hj hk _ = 𝟘-elim (east-west w₁ hj hk)
cocycle w₁ w₂ east  east  south _ _ _ _ = refl
cocycle w₁ w₂ east  north east  _ _ _ _ = refl
cocycle w₁ w₂ east  north north _ _ _ _ = refl
cocycle w₁ w₂ east  north west  hi _ hk _ = 𝟘-elim (east-west w₁ hi hk)
cocycle w₁ w₂ east  north south _ hj hk _ = 𝟘-elim (east-west w₂ hj hk)
cocycle w₁ w₂ east  west  east  hi hj _ _ = 𝟘-elim (east-west w₁ hi hj)
cocycle w₁ w₂ east  west  north hi hj _ _ = 𝟘-elim (east-west w₁ hi hj)
cocycle w₁ w₂ east  west  west  hi hj _ _ = 𝟘-elim (east-west w₁ hi hj)
cocycle w₁ w₂ east  west  south hi hj _ _ = 𝟘-elim (east-west w₁ hi hj)
cocycle w₁ w₂ east  south east  _ _ _ b = complement-involutive b
cocycle w₁ w₂ east  south north _ hj hk _ = 𝟘-elim (east-west w₂ hk hj)
cocycle w₁ w₂ east  south west  hi _ hk _ = 𝟘-elim (east-west w₁ hi hk)
cocycle w₁ w₂ east  south south _ _ _ _ = refl
cocycle w₁ w₂ north east  east  _ _ _ _ = refl
cocycle w₁ w₂ north east  north _ _ _ _ = refl
cocycle w₁ w₂ north east  west  _ hj hk _ = 𝟘-elim (east-west w₁ hj hk)
cocycle w₁ w₂ north east  south hi _ hk _ = 𝟘-elim (east-west w₂ hi hk)
cocycle w₁ w₂ north north east  _ _ _ _ = refl
cocycle w₁ w₂ north north north _ _ _ _ = refl
cocycle w₁ w₂ north north west  _ _ _ _ = refl
cocycle w₁ w₂ north north south _ hj hk _ = 𝟘-elim (east-west w₂ hj hk)
cocycle w₁ w₂ north west  east  _ hj hk _ = 𝟘-elim (east-west w₁ hk hj)
cocycle w₁ w₂ north west  north _ _ _ _ = refl
cocycle w₁ w₂ north west  west  _ _ _ _ = refl
cocycle w₁ w₂ north west  south hi _ hk _ = 𝟘-elim (east-west w₂ hi hk)
cocycle w₁ w₂ north south east  hi hj _ _ = 𝟘-elim (east-west w₂ hi hj)
cocycle w₁ w₂ north south north hi hj _ _ = 𝟘-elim (east-west w₂ hi hj)
cocycle w₁ w₂ north south west  hi hj _ _ = 𝟘-elim (east-west w₂ hi hj)
cocycle w₁ w₂ north south south hi hj _ _ = 𝟘-elim (east-west w₂ hi hj)
cocycle w₁ w₂ west  east  east  hi hj _ _ = 𝟘-elim (east-west w₁ hj hi)
cocycle w₁ w₂ west  east  north hi hj _ _ = 𝟘-elim (east-west w₁ hj hi)
cocycle w₁ w₂ west  east  west  hi hj _ _ = 𝟘-elim (east-west w₁ hj hi)
cocycle w₁ w₂ west  east  south hi hj _ _ = 𝟘-elim (east-west w₁ hj hi)
cocycle w₁ w₂ west  north east  hi _ hk _ = 𝟘-elim (east-west w₁ hk hi)
cocycle w₁ w₂ west  north north _ _ _ _ = refl
cocycle w₁ w₂ west  north west  _ _ _ _ = refl
cocycle w₁ w₂ west  north south _ hj hk _ = 𝟘-elim (east-west w₂ hj hk)
cocycle w₁ w₂ west  west  east  _ hj hk _ = 𝟘-elim (east-west w₁ hk hj)
cocycle w₁ w₂ west  west  north _ _ _ _ = refl
cocycle w₁ w₂ west  west  west  _ _ _ _ = refl
cocycle w₁ w₂ west  west  south _ _ _ _ = refl
cocycle w₁ w₂ west  south east  hi _ hk _ = 𝟘-elim (east-west w₁ hk hi)
cocycle w₁ w₂ west  south north _ hj hk _ = 𝟘-elim (east-west w₂ hk hj)
cocycle w₁ w₂ west  south west  _ _ _ _ = refl
cocycle w₁ w₂ west  south south _ _ _ _ = refl
cocycle w₁ w₂ south east  east  _ _ _ _ = refl
cocycle w₁ w₂ south east  north hi _ hk _ = 𝟘-elim (east-west w₂ hk hi)
cocycle w₁ w₂ south east  west  _ hj hk _ = 𝟘-elim (east-west w₁ hj hk)
cocycle w₁ w₂ south east  south _ _ _ b = complement-involutive b
cocycle w₁ w₂ south north east  hi hj _ _ = 𝟘-elim (east-west w₂ hj hi)
cocycle w₁ w₂ south north north hi hj _ _ = 𝟘-elim (east-west w₂ hj hi)
cocycle w₁ w₂ south north west  hi hj _ _ = 𝟘-elim (east-west w₂ hj hi)
cocycle w₁ w₂ south north south hi hj _ _ = 𝟘-elim (east-west w₂ hj hi)
cocycle w₁ w₂ south west  east  _ hj hk _ = 𝟘-elim (east-west w₁ hk hj)
cocycle w₁ w₂ south west  north hi _ hk _ = 𝟘-elim (east-west w₂ hk hi)
cocycle w₁ w₂ south west  west  _ _ _ _ = refl
cocycle w₁ w₂ south west  south _ _ _ _ = refl
cocycle w₁ w₂ south south east  _ _ _ _ = refl
cocycle w₁ w₂ south south north _ hj hk _ = 𝟘-elim (east-west w₂ hk hj)
cocycle w₁ w₂ south south west  _ _ _ _ = refl
cocycle w₁ w₂ south south south _ _ _ _ = refl

\end{code}

The cover, and its triviality over each half-plane.

\begin{code}

module _ (w₁ w₂ : ℝ) where

 Compatible : ((i : Side) → Half-Plane w₁ w₂ i → 𝟚) → 𝓤₀ ̇
 Compatible φ = (i j : Side) (hi : Half-Plane w₁ w₂ i) (hj : Half-Plane w₁ w₂ j)
              → φ j hj ＝ transition i j (φ i hi)

 Compatible-is-prop : (φ : (i : Side) → Half-Plane w₁ w₂ i → 𝟚)
                    → is-prop (Compatible φ)
 Compatible-is-prop φ = Π-is-prop fe (λ i → Π-is-prop fe (λ j → Π-is-prop fe
                         (λ hi → Π-is-prop fe (λ hj → 𝟚-is-set))))

 Cover : 𝓤₀ ̇
 Cover = Σ φ ꞉ ((i : Side) → Half-Plane w₁ w₂ i → 𝟚) , Compatible φ

 Cover-is-set : is-set Cover
 Cover-is-set = Σ-is-set (Π-is-set fe (λ i → Π-is-set fe (λ _ → 𝟚-is-set)))
                 (λ φ → props-are-sets (Compatible-is-prop φ))

 τ : (i : Side) → Half-Plane w₁ w₂ i → 𝟚 → Cover
 τ i hi b = (λ j hj → transition i j b) ,
            (λ j k hj hk → cocycle w₁ w₂ i j k hi hj hk b ⁻¹)

 evaluation : (i : Side) → Half-Plane w₁ w₂ i → Cover → 𝟚
 evaluation i hi (φ , _) = φ i hi

 Cover-≃-𝟚 : (i : Side) → Half-Plane w₁ w₂ i → Cover ≃ 𝟚
 Cover-≃-𝟚 i hi = qinveq (evaluation i hi) (τ i hi , I , II)
  where
   I : τ i hi ∘ evaluation i hi ∼ id
   I (φ , c) = to-subtype-＝ Compatible-is-prop
                (dfunext fe (λ j → dfunext fe (λ hj → c i j hi hj ⁻¹)))

   II : evaluation i hi ∘ τ i hi ∼ id
   II b = transition-refl i b

 τ-change
  : (i j : Side) (hi : Half-Plane w₁ w₂ i) (hj : Half-Plane w₁ w₂ j) (b : 𝟚)
          → τ i hi b ＝ τ j hj (transition i j b)
 τ-change i j hi hj b =
  to-subtype-＝ Compatible-is-prop
   (dfunext fe (λ k → dfunext fe (λ hk → cocycle w₁ w₂ i j k hi hj hk b ⁻¹)))

 τ-is-injective : (i : Side) (hi : Half-Plane w₁ w₂ i) → τ i hi ₀ ≠ τ i hi ₁
 τ-is-injective i hi e = zero-is-not-one
                          (transition-refl i ₀ ⁻¹ ∙ ap (evaluation i hi) e
                           ∙ transition-refl i ₁)

\end{code}
