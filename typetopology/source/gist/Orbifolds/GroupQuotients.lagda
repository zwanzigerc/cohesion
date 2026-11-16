Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. Orbifold gate H6 of Fable's roadmap [1].

Theorem 5.4.1 for groups given by a multiplication
--------------------------------------------------

EtaleQuotients proves Myers's Theorem 5.4.1 [2] in the scope of the
roadmap [1, Section 3.5] for a group in Myers's sense: a crisp pointed
0-connected type B with modal loop space, acting on the fibre over the
base point of a family over B. This module applies it to a group Γ
given as a set with a multiplication (TypeTopology's Groups.Type), with
B the type of Γ-torsors (Deloopings) and the family of a Γ-set 𝕏, so
that X // Γ = Σ T ꞉ BΓ Γ , action-family Γ 𝕏 T:

  theorem-5-4-1-for-groups : for a crisp group Γ whose carrier is
  modal, and a Γ-set 𝕏 whose carrier is microlinear, X // Γ is
  microlinear.

Universes. Torsors for a group in 𝓤 form a type in 𝓤 ⁺, so the
modality is taken on 𝓤 ⁺, and the test squares too; the carriers of Γ
and 𝕏, which live in 𝓤, enter through Lift. The hypotheses are about
the lifted carrier of Γ (modal) and about the carrier of 𝕏 (microlinear,
a notion insensitive to universes).

Crispness. Lemma F needs BΓ and its base point crisp. They are built
from function extensionality and truncations, which are therefore
crisp parameters of this module, as in the library's RealNull, and
the delooping is opened before the non-crisp parameters (univalence and
the modality) are introduced.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Sections 3.5 and 4.
    references/F01-orbifolds-roadmap-rev2.md
[2] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Univalence
open import Modal.Subuniverse

module gist.Orbifolds.GroupQuotients
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
        {@♭ 𝓤 : Universe}
       where

open import Groups.Type renaming (_≅_ to _≣_)
open import Groups.GroupActions
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.UniverseEmbedding using (Lift ; Lift-≃)

open import gist.Orbifolds.Deloopings fe pt {𝓤}
open import gist.Orbifolds.TestSquares fe
open import gist.Orbifolds.AbstractOrbifolds fe pt using (is-microlinear)

module _ (ua : is-univalent 𝓤)
         {𝓥 : Universe}
         (P : subuniverse (𝓤 ⁺) 𝓥)
         (P-is-reflective : subuniverse-is-reflective P)
         (P-is-sigma-closed : subuniverse-is-sigma-closed P)
         (P-is-replete : subuniverse-is-replete P)
       where

 open import Modal.ReflectiveSubuniverse P P-is-reflective using (is-modal)
 open import gist.Orbifolds.CrispLemmaF fe pt {𝓤 ⁺} P
              P-is-reflective P-is-sigma-closed P-is-replete
  using (○-preserves-crisp-pullbacks)
 open import gist.Orbifolds.EtaleQuotients fe pt {𝓤 ⁺} P
              P-is-reflective P-is-sigma-closed P-is-replete
  using (has-connected-pointed-types ; theorem-5-4-1-microlinear)

 theorem-5-4-1-for-groups
  : ○-preserves-crisp-pullbacks
  → {𝓣 : Universe} {T : 𝓣 ̇ } (σ : T → Test-Square (𝓤 ⁺))
  → has-connected-pointed-types σ
  → (@♭ Γ : Group 𝓤)
  → is-modal (Lift (𝓤 ⁺) ⟨ Γ ⟩)
  → (𝕏 : Action Γ)
  → (Π t ꞉ T , is-local (σ t) ⟨ 𝕏 ⟩)
  → is-microlinear σ (Σ X ꞉ BΓ Γ , action-family Γ 𝕏 X)
 theorem-5-4-1-for-groups π σ c Γ Γ-is-modal 𝕏 𝕏-is-microlinear t =
  local-types-are-closed-under-equivalence (σ t)
   (Σ-cong (λ X → Lift-≃ (𝓤 ⁺) (action-family Γ 𝕏 X)))
   (theorem-5-4-1-microlinear π σ c (base Γ) (BΓ-is-connected Γ ua)
     Ω-is-modal X̃ fibre-is-microlinear t)
  where
   X̃ : BΓ Γ → 𝓤 ⁺ ̇
   X̃ X = Lift (𝓤 ⁺) (action-family Γ 𝕏 X)

   Ω-is-modal : is-modal (base Γ ＝ base Γ)
   Ω-is-modal = P-is-replete (base Γ ＝ base Γ) (Lift (𝓤 ⁺) ⟨ Γ ⟩)
                 (loops-of-BΓ Γ ua ● ≃-sym (Lift-≃ (𝓤 ⁺) ⟨ Γ ⟩))
                 Γ-is-modal

   fibre-is-microlinear : is-microlinear σ (X̃ (base Γ))
   fibre-is-microlinear s =
    local-types-are-closed-under-equivalence (σ s)
     (≃-sym (Lift-≃ (𝓤 ⁺) (action-family Γ 𝕏 (base Γ))
             ● action-family-at-base Γ 𝕏))
     (𝕏-is-microlinear s)

\end{code}
