Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. Orbifold gate H8 of Fable's roadmap [1].

Theorem 6.4.1 for finite groups given by a multiplication
---------------------------------------------------------

GlobalQuotients proves Myers's Theorem 6.4.1 [2] for a group in his
sense, a crisp pointed connected type with finite loop space. This
module applies it to a crisp finite group Γ given as a set with a
multiplication (TypeTopology's Groups.Type), acting on a microlinear
set 𝕏. The delooping is the type of Γ-torsors (Deloopings), so that
X // Γ is Σ T ꞉ BΓ Γ , action-family Γ 𝕏 T:

  theorem-6-4-1-for-groups : under univalence, X // Γ is an orbifold.

  literal-theorem-6-4-1-for-groups : the same for Myers's literal
  definitions in the adopted, presentation-based reading of
  MyersMicrolinearity (Weil algebras by presentations; each square
  crisp together with its R-pushout proof): ℑ the nullification at all
  crisp pointed types that are merely spectra of presentations, literal
  microlinearity of the Γ-set, and the literal notion of orbifold
  (added after the review of 13 November 2026). For the reading of
  "literal" and of ℑ, see gist.Orbifolds.index, the paragraph on the
  scope of the statements.

As in GroupQuotients, the torsors live one universe above Γ, so the
modality and the test squares live there too. The fibres of the family
are lifted to that universe, and the result is moved back along the
equivalence.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Sections 2.2 and 4.
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
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.FiniteGroupQuotients
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ 𝓡 : Commutative-Ring)
        {@♭ 𝓤 : Universe}
       where

open PropositionalTruncation pt

open import Groups.Type renaming (_≅_ to _≣_)
open import Groups.GroupActions
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Sets
open import UF.Sets-Properties using (equiv-to-set)
open import UF.UniverseEmbedding using (Lift ; Lift-≃)

open smooth-line fe pt 𝓡 using (Postulate-K)
open import gist.Orbifolds.ProperFiniteness fe pt using (is-finite)
open import gist.Orbifolds.Nullification fe using (is-nullification)
open import gist.Orbifolds.Deloopings fe pt {𝓤}
open import gist.Orbifolds.TestSquares fe
 using (local-types-are-closed-under-equivalence)
open import gist.Orbifolds.Microlinearity fe pt 𝓡 {𝓤 ⁺}
open import gist.Orbifolds.GlobalQuotients fe pt 𝓡 {𝓤 ⁺}
 using (ℑ-preserves-crisp-pullbacks ; theorem-6-4-1)
open import gist.Orbifolds.MyersMicrolinearity fe pt 𝓡 {𝓤 ⁺}
 using (literal-ℑ-generator ; literal-ℑ-generator-point ;
        literal-nullifications-are-nullifications ;
        is-literally-microlinear ; is-literal-orbifold ;
        microlinearity-agrees ; orbifolds-agree)
import gist.Orbifolds.AbstractOrbifolds fe pt as AO

module _ (ua : is-univalent 𝓤)
         {𝓦 : Universe}
         (P : subuniverse (𝓤 ⁺) 𝓦)
         (P-is-reflective : subuniverse-is-reflective P)
         (ν : is-nullification ℑ-generator ℑ-generator-point P)
       where

 theorem-6-4-1-for-groups
  : Postulate-K
  → ℑ-preserves-crisp-pullbacks P P-is-reflective ν
  → (@♭ Γ : Group 𝓤)
  → is-finite ⟨ Γ ⟩
  → (𝕏 : Action Γ)
  → is-microlinear ⟨ 𝕏 ⟩
  → is-orbifold (Σ T ꞉ BΓ Γ , action-family Γ 𝕏 T)
 theorem-6-4-1-for-groups K π Γ Γ-is-finite 𝕏 𝕏-is-microlinear =
  AO.orbifolds-are-closed-under-equivalence infinitesimal-R-pushouts
   (Σ-cong (λ T → Lift-≃ (𝓤 ⁺) (action-family Γ 𝕏 T)))
   (theorem-6-4-1 P P-is-reflective ν K π (base Γ) (BΓ-is-connected Γ ua)
     Ω-is-finite X̃ X̃-is-set fibre-is-microlinear)
  where
   X̃ : BΓ Γ → 𝓤 ⁺ ̇
   X̃ T = Lift (𝓤 ⁺) (action-family Γ 𝕏 T)

   Ω-is-finite : is-finite (base Γ ＝ base Γ)
   Ω-is-finite = ∥∥-functor (λ (n , φ) → n , (loops-of-BΓ Γ ua ● φ)) Γ-is-finite

   fibre-equivalence : X̃ (base Γ) ≃ ⟨ 𝕏 ⟩
   fibre-equivalence = Lift-≃ (𝓤 ⁺) (action-family Γ 𝕏 (base Γ))
                     ● action-family-at-base Γ 𝕏

   X̃-is-set : is-set (X̃ (base Γ))
   X̃-is-set = equiv-to-set fibre-equivalence (carrier-is-set Γ 𝕏)

   fibre-is-microlinear : is-microlinear (X̃ (base Γ))
   fibre-is-microlinear t =
    local-types-are-closed-under-equivalence (infinitesimal-R-pushouts t)
     (≃-sym fibre-equivalence) (𝕏-is-microlinear t)

\end{code}

The same for Myers's literal definitions, in the adopted,
presentation-based reading of MyersMicrolinearity (see the paragraph
on the scope of the statements in gist.Orbifolds.index).

\begin{code}

module _ (ua : is-univalent 𝓤)
         {𝓦 : Universe}
         (P : subuniverse (𝓤 ⁺) 𝓦)
         (P-is-reflective : subuniverse-is-reflective P)
         (ν : is-nullification literal-ℑ-generator literal-ℑ-generator-point P)
       where

 literal-theorem-6-4-1-for-groups
  : Postulate-K
  → ℑ-preserves-crisp-pullbacks P P-is-reflective
     (lr-implication (literal-nullifications-are-nullifications P) ν)
  → (@♭ Γ : Group 𝓤)
  → is-finite ⟨ Γ ⟩
  → (𝕏 : Action Γ)
  → is-literally-microlinear ⟨ 𝕏 ⟩
  → is-literal-orbifold (Σ T ꞉ BΓ Γ , action-family Γ 𝕏 T)
 literal-theorem-6-4-1-for-groups K π Γ Γ-is-finite 𝕏 m =
  lr-implication (orbifolds-agree _)
   (theorem-6-4-1-for-groups ua P P-is-reflective
     (lr-implication (literal-nullifications-are-nullifications P) ν)
     K π Γ Γ-is-finite 𝕏 (rl-implication (microlinearity-agrees ⟨ 𝕏 ⟩) m))

\end{code}

