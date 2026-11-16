Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. Orbifold gate H6 of Fable's roadmap [1].

Theorem 5.4.9: crisp étale groupoids are microlinear
----------------------------------------------------

Myers [2, Definition 5.4.6] calls a pregroupoid G étale if its type of
objects G₀ is microlinear and its source map G₁ → G₀ is ℑ-étale, where
G₁ = (x , y : G₀) × G(x , y); an étale groupoid is a groupoid
equivalent to the Rezk completion of an étale pregroupoid. Theorem
5.4.9 [2] says that crisp étale groupoids are microlinear. Here, with
the Rezk completion constructed (RezkCompletion) and the argument of
EtaleQuotients (Lemma F, then Lemma G(3)):

  theorem-5-4-9-for-pregroupoids : for a crisp pregroupoid whose source
  map is étale and whose type of objects is microlinear, its Rezk
  completion is microlinear;

  crisp-étale-groupoids-are-microlinear : so is every type equivalent
  to it.

As in the rest of the folder, microlinearity is relative to a family of
test squares with connected types and a point of V₂ (Myers's
infinitesimal R-pushouts at gate H8), and the hypothesis that the
modality preserves crisp pullbacks (core item 4) enters through
Lemma F.

Universes. Presheaves with values in 𝓤 on objects in 𝓤 ⁺ form a type
in 𝓤 ⁺, so the pregroupoid has objects in 𝓤 ⁺ and morphisms in 𝓤, and
the modality lives on 𝓤 ⁺ (item 6 of the roadmap's ledger: the
universe of rG, chosen so that core item 4 applies to G₀ ×_(rG) G₀).
Function extensionality and truncations are crisp parameters, so that
the Rezk completion of a crisp pregroupoid is crisp; univalence of 𝓤
and the modality come after.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Sections 3.5, 4 and 8.
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

module gist.Orbifolds.EtaleGroupoids
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
        {@♭ 𝓤 : Universe}
       where

open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.UniverseEmbedding using (Lift ; Lift-≃)

open import gist.Orbifolds.RezkCompletion fe pt {𝓤} {𝓤 ⁺}
open import gist.Orbifolds.TestSquares fe
open import gist.Orbifolds.AbstractOrbifolds fe pt using (is-microlinear)

module _ (ua : is-univalent 𝓤)
         {𝓥 : Universe}
         (P : subuniverse (𝓤 ⁺) 𝓥)
         (P-is-reflective : subuniverse-is-reflective P)
         (P-is-sigma-closed : subuniverse-is-sigma-closed P)
         (P-is-replete : subuniverse-is-replete P)
       where

 open import gist.Orbifolds.Modalities fe pt {𝓤 ⁺} P
              P-is-reflective P-is-sigma-closed P-is-replete
  using
   (is-étale ; equivalences-are-étale ; étale-maps-are-closed-under-composition)
 open import gist.Orbifolds.CrispLemmaF fe pt {𝓤 ⁺} P
              P-is-reflective P-is-sigma-closed P-is-replete
  using (○-preserves-crisp-pullbacks)
 import gist.Orbifolds.EtaleQuotients fe pt {𝓤 ⁺} P
         P-is-reflective P-is-sigma-closed P-is-replete as EQ

 theorem-5-4-9-for-pregroupoids
  : ○-preserves-crisp-pullbacks
  → {𝓣 : Universe} {T : 𝓣 ̇ } (σ : T → Test-Square (𝓤 ⁺))
  → EQ.has-connected-pointed-types σ
  → (@♭ G : Pregroupoid)
  → is-étale (source G)
  → is-microlinear σ (Pregroupoid.ob G)
  → is-microlinear σ (Rezk-completion G)
 theorem-5-4-9-for-pregroupoids π σ c G s-is-étale =
  EQ.theorem-5-4-9-microlinear π σ c hom' (yoneda-embedding G)
   (yoneda-embedding-is-surjection G ua)
   (λ x x' →
     Lift-≃ (𝓤 ⁺) (Pregroupoid.hom G x x') ● hom-≃-identifications G ua x x')
   s'-is-étale
  where
   hom' : Pregroupoid.ob G → Pregroupoid.ob G → 𝓤 ⁺ ̇
   hom' x x' = Lift (𝓤 ⁺) (Pregroupoid.hom G x x')

   lower-arrows : EQ.arrows hom' → arrows G
   lower-arrows =
    ⌜ Σ-cong (λ x → Σ-cong (λ x' → Lift-≃ (𝓤 ⁺) (Pregroupoid.hom G x x'))) ⌝

   lower-arrows-is-equiv : is-equiv lower-arrows
   lower-arrows-is-equiv =
    ⌜⌝-is-equiv
     (Σ-cong (λ x → Σ-cong (λ x' → Lift-≃ (𝓤 ⁺) (Pregroupoid.hom G x x'))))

   s'-is-étale : is-étale (EQ.source hom')
   s'-is-étale = étale-maps-are-closed-under-composition lower-arrows (source G)
                  (equivalences-are-étale lower-arrows lower-arrows-is-equiv)
                  s-is-étale

 crisp-étale-groupoids-are-microlinear
  : ○-preserves-crisp-pullbacks
  → {𝓣 : Universe} {T : 𝓣 ̇ } (σ : T → Test-Square (𝓤 ⁺))
  → EQ.has-connected-pointed-types σ
  → (@♭ G : Pregroupoid)
  → is-étale (source G)
  → is-microlinear σ (Pregroupoid.ob G)
  → {𝓡 : Universe} (H : 𝓡 ̇ )
  → H ≃ Rezk-completion G
  → is-microlinear σ H
 crisp-étale-groupoids-are-microlinear π σ c G s-is-étale m H e t =
  local-types-are-closed-under-equivalence (σ t) (≃-sym e)
   (theorem-5-4-9-for-pregroupoids π σ c G s-is-étale m t)

\end{code}
