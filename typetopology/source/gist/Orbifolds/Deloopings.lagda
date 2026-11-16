Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. Orbifold gate H6 of Fable's roadmap [1].

Deloopings of groups from torsors
---------------------------------

Myers [2, Definition 2.1.2] defines a (higher) group as the type of
self-identifications of the base point of a pointed 0-connected type
BG, and an action of a group on X as a type family over BG with fibre
X over the base point [2, Theorem 5.4.1]. A group given as a set with
a multiplication (TypeTopology's Groups.Type) has such a delooping:
the type of its torsors [1, Section 4]. This module constructs it,
with TypeTopology's Groups.Torsors and Groups.GroupActions:

  BΓ = Tors Γ, pointed by the trivial torsor 𝕋 Γ;
  BΓ-is-connected : (X : BΓ) → ∥ base ＝ X ∥;
  loops-of-BΓ : (base ＝ base) ≃ ⟨ Γ ⟩;
  for a Γ-set 𝕏, the family action-family 𝕏 T = Action-Map Γ T 𝕏 of
  equivariant maps, with action-family-at-base : … ≃ ⟨ 𝕏 ⟩.

Univalence. The last three facts about identifications in BΓ need the
univalence of the universe of Γ, as a module parameter of the nested
module below; it is used once, in torsor-identifications, through
TypeTopology's univalence for group actions (Id-equiv-Action-Iso).
Since torsors are sets, univalence for sets would suffice; that weaker
form is not in TypeTopology, and the change would be confined to
torsor-identifications. BΓ, its base point and the family of a Γ-set
do not depend on univalence, which keeps them crisp when Γ is
(GroupQuotients).

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Section 4.
    references/F01-orbifolds-roadmap-rev2.md
[2] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Univalence

module gist.Orbifolds.Deloopings
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        {𝓤 : Universe}
       where

open PropositionalTruncation pt

open import Groups.Type renaming (_≅_ to _≣_)
open import Groups.GroupActions
open import Groups.Torsors {𝓤} fe pt
open import UF.Base
open import UF.Equiv
open import UF.Subsingletons

\end{code}

The delooping and the family of a Γ-set.

\begin{code}

module _ (Γ : Group 𝓤) where

 BΓ : 𝓤 ⁺ ̇
 BΓ = Tors Γ

 base : BΓ
 base = 𝕋 Γ

 action-family : Action Γ → BΓ → 𝓤 ̇
 action-family 𝕏 T = Action-Map Γ (pr₁ T) 𝕏

 action-family-at-base : (𝕏 : Action Γ) → action-family 𝕏 base ≃ ⟨ 𝕏 ⟩
 action-family-at-base 𝕏 = qinveq ev (back , back-ev , ev-back)
  where
   ev : action-family 𝕏 base → ⟨ 𝕏 ⟩
   ev (f , i) = f (unit Γ)

   back : ⟨ 𝕏 ⟩ → action-family 𝕏 base
   back x = (λ g → action-op Γ 𝕏 g x) , (λ g a → action-assoc Γ 𝕏 g a x)

   ev-back : ev ∘ back ∼ id
   ev-back x = action-unit Γ 𝕏 x

   back-ev : back ∘ ev ∼ id
   back-ev (f , i) =
    to-subtype-＝ (is-equivariant-is-prop Γ fe (pr₁ base) 𝕏)
     (dfunext fe (λ g → (i g (unit Γ))⁻¹ ∙ ap f (unit-right Γ g)))

\end{code}

Identifications in BΓ, under univalence.

\begin{code}

 module _ (ua : is-univalent 𝓤) where

  torsor-identifications : (X Y : BΓ) → (X ＝ Y) ≃ Action-Iso Γ (pr₁ X) (pr₁ Y)
  torsor-identifications X Y =
   underlying-action-injectivity Γ X Y ● Id-equiv-Action-Iso Γ ua (pr₁ X)
    (pr₁ Y)

  BΓ-is-connected : (X : BΓ) → ∥ base ＝ X ∥
  BΓ-is-connected X =
   ∥∥-functor (λ x → ⌜ torsor-identifications base X ⌝⁻¹ (triv-iso {Γ} X x))
    (torsor-carrier-prop {Γ} X)

  loops-of-BΓ : (base ＝ base) ≃ ⟨ Γ ⟩
  loops-of-BΓ =
   torsor-identifications base base ● ≃-sym (triv-torsor-right-mult Γ)

\end{code}
