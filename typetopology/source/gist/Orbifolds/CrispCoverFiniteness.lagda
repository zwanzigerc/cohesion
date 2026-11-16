Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026; prose updated 13 November 2026, after the
final audits. Orbifold gate H7 of Fable's roadmap [1].

The crisp parts of finiteness under cover-properness
----------------------------------------------------

Two pieces of gate H7 that need the flat modality.

The index type of the charts [1, Section 3.6]. GPT-6 Astra [2,
Section 1] takes the crisp family of basic opens of G₁ on which the
source map is injective, indexed by a crisp subtype of ℕ. Crisp
excluded middle makes it a decidable subtype:

  crisp-subtypes-of-ℕ-are-decidable : the library's decide-at
  (gist.RealCohesion.CrispRationals), for ℕ, whose elements have crisp
  representatives (ℕ-has-crisp-representatives).

As a subtype of ℕ, the index type has decidable equality
(subtypes-of-ℕ-are-discrete), which is what Lemma D of the bridge in
Section 3.9 uses. For the official cover-properness hypothesis of T1,
the chart index must also be ♭-discrete. This is proved in
EtaleSourceMaps from Axiom C1 and ordinary setness, using the
♭-discreteness of ℕ; T1 does not use crisp excluded middle. The
decidable-subtype lemma above is a separate helper.

T1 over the abstract interfaces, an intermediate result in the sense of
the roadmap's Section 5:

  Rezk-completions-are-orbifolds : for a crisp pregroupoid whose source
  map is étale, whose type of objects is microlinear and whose
  hom-sets are properly finite, the Rezk completion is an orbifold.

It combines Theorem 5.4.9 (EtaleGroupoids) with CoverFiniteness.
Microlinearity is relative to a family of test squares (Myers's once
these are the infinitesimal R-pushouts, gate H8); the type of objects
is assumed microlinear; and hom-sets-are-properly-finite gives the last
hypothesis from charts. The target T1 has instead ordinary manifolds,
an ordinary local homeomorphism and a cover-proper anchor (gate H9).
Universes and crispness are as in EtaleGroupoids.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Sections 2.1, 3.6, 3.9 and 5.
    references/F01-orbifolds-roadmap-rev2.md
[2] GPT-6 Astra. Main aim: finiteness from the current open-cover
    properness condition, 11 November 2026.
    references/A03-cover-finiteness.txt

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Univalence
open import Modal.Subuniverse

module gist.Orbifolds.CrispCoverFiniteness
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
        {@♭ 𝓤 : Universe}
       where

open import TypeTopology.SigmaDiscrete using (Σ-is-discrete)
open import UF.DiscreteAndSeparated
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat using (Crisp-EM)
open import gist.RealCohesion.CrispRationals
 using (decide-at ; ℕ-has-crisp-representatives)

open import gist.Orbifolds.RezkCompletion fe pt {𝓤} {𝓤 ⁺}
open import gist.Orbifolds.TestSquares fe using (Test-Square)
open import gist.Orbifolds.ProperFiniteness fe pt using (is-properly-finite)
open import gist.Orbifolds.AbstractOrbifolds fe pt
 using (is-microlinear ; is-orbifold)
open import gist.Orbifolds.CoverFiniteness fe pt
 using (identity-types-of-Rezk-completions-are-properly-finite)

\end{code}

The index type of the charts.

\begin{code}

crisp-subtypes-of-ℕ-are-decidable
 : {@♭ 𝓦 : Universe}
 → (@♭ cem : Crisp-EM 𝓦)
 → (@♭ A : ℕ → 𝓦 ̇ )
 → (@♭ A-is-prop-valued : (n : ℕ) → is-prop (A n))
 → (n : ℕ) → is-decidable (A n)
crisp-subtypes-of-ℕ-are-decidable cem A A-is-prop-valued =
 decide-at ℕ-has-crisp-representatives cem A A-is-prop-valued

subtypes-of-ℕ-are-discrete : {𝓦 : Universe} (A : ℕ → 𝓦 ̇ )
                           → ((n : ℕ) → is-prop (A n))
                           → is-discrete (Σ A)
subtypes-of-ℕ-are-discrete A A-is-prop-valued =
 Σ-is-discrete ℕ-is-discrete (λ n → props-are-discrete (A-is-prop-valued n))

\end{code}

T1 over the abstract interfaces.

\begin{code}

module _ (ua : is-univalent 𝓤)
         {𝓥 : Universe}
         (P : subuniverse (𝓤 ⁺) 𝓥)
         (P-is-reflective : subuniverse-is-reflective P)
         (P-is-sigma-closed : subuniverse-is-sigma-closed P)
         (P-is-replete : subuniverse-is-replete P)
       where

 open import gist.Orbifolds.Modalities fe pt {𝓤 ⁺} P
              P-is-reflective P-is-sigma-closed P-is-replete
  using (is-étale)
 open import gist.Orbifolds.CrispLemmaF fe pt {𝓤 ⁺} P
              P-is-reflective P-is-sigma-closed P-is-replete
  using (○-preserves-crisp-pullbacks)
 open import gist.Orbifolds.EtaleQuotients fe pt {𝓤 ⁺} P
              P-is-reflective P-is-sigma-closed P-is-replete
  using (has-connected-pointed-types)
 open import gist.Orbifolds.EtaleGroupoids fe pt {𝓤}
  using (theorem-5-4-9-for-pregroupoids)

 Rezk-completions-are-orbifolds
  : ○-preserves-crisp-pullbacks
  → {𝓣 : Universe} {T : 𝓣 ̇ } (σ : T → Test-Square (𝓤 ⁺))
  → has-connected-pointed-types σ
  → (@♭ G : Pregroupoid)
  → is-étale (source G)
  → is-microlinear σ (Pregroupoid.ob G)
  → ((x y : Pregroupoid.ob G) → is-properly-finite (Pregroupoid.hom G x y))
  → is-orbifold σ (Rezk-completion G)
 Rezk-completions-are-orbifolds π σ c G s-is-étale m φ =
  theorem-5-4-9-for-pregroupoids ua P P-is-reflective P-is-sigma-closed
   P-is-replete π σ c G s-is-étale m ,
  identity-types-of-Rezk-completions-are-properly-finite G ua φ

\end{code}
