Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026 (local time); two sentences made precise
13 November 2026, after the final audits; the forms for set-indexed
covers, and the scope of the statements made precise, later that day,
in the third part of the consolidation [5, 7]; the sentence on Weil
algebras updated at the integration of the Weil comparison, the same
night [8]. Orbifold gate H9 of Fable's roadmap [1]: the target T1 and
the helper T1′.

T1: ordinary étale groupoids with a cover-proper anchor
-------------------------------------------------------

The target T1 [1, Section 2.1]: let G be a crisp pregroupoid whose
objects G₀ and arrows G₁ form ordinary manifolds, whose source map s is
an ordinary local homeomorphism, and whose anchor a = (s , t) is
cover-proper. Then the Rezk completion rG is an orbifold.

  theorem-T1′ : the helper, with "s is ℑ-étale and locally injective"
  in place of "s is a local homeomorphism";

  theorem-T1 : the target, from T1′ by the bridge 3.9
  (EtaleSourceMaps);

  theorem-T1-literal : the same for Myers's literal definitions, the
  nullification at all crisp pointed types that are merely spectra of
  presentations and literal orbifolds, through the bridges of the
  module MyersMicrolinearity, under its two readings: Weil algebras
  are given by presentations, and each square is crisp together with
  its R-pushout proof. For the reading of "literal" and of ℑ, see
  gist.Orbifolds.index, the paragraph on the scope of the statements;

  theorem-T1-for-crisp-topologies : the original crisp scope, as a
  specialization;

  theorem-T1′-for-set-indices, theorem-T1-for-set-indices,
  theorem-T1-for-crisp-topologies-and-set-indices,
  theorem-T1-literal-for-set-indices : the same, with cover-properness
  for set-indexed covers (CoverProperness), the condition of the memo
  [6]. The proof is that of T1′: cover-properness is applied once, to
  the chart index Σ n ꞉ ℕ , (s is injective on B₁ n), which is a set
  because it has decidable equality (chart-indices-are-discrete and
  discrete-types-are-sets). theorem-T1′ and theorem-T1 are now these
  forms after the restriction of the older condition, with their old
  types; the old crisp-topology and literal forms keep their proofs.
  theorem-T1-literal-for-set-indices is the endpoint that corresponds
  to the memo's theorem, with the qualifications below.

Which data are crisp [3, 4]: the pregroupoid G, hence G₀, G₁, s and the
anchor, and the basis B₁ of G₁, which gives the chart cover to which
cover-properness is applied. The topologies, the basis of G₀, the
dimensions n₀ and n₁, and all laws (setness, regularity, T₀, charts,
basis, chart domains), the local homeomorphism and the cover-properness
are ordinary arguments. The structure of G₁ is given by its laws for the
crisp basis B₁ (Ordinary-Manifold-Laws), and the record is assembled
ordinarily; the structure of G₀ is a record. The chart index lies in the
universe 𝓤 of the carriers. These distinctions are those of the
crispness release [3, 4; 5, Section 8], and the set-indexed forms keep
them.

Scope of the literal forms. They use the adopted reading of
MyersMicrolinearity. An infinitesimal variety merely admits an
ordinary presentation. A literal test square is crisp together with its
pointing, commutation, four mere variety witnesses and R-pushout proof.
The reflector ℑ is nullification at the spectra of crisp presentations,
with the stated hypothesis that it preserves crisp pullbacks;
no equivalence of ℑ with Myers's infinitesimal-disk modality has been
proved. The comparison of presentations with the Weil algebras of
Definition 4.1.1 and their Hom-spectra is formalized in
WeilVarietiesFromLargeQuotients, for Weil algebras with carrier in 𝓤₁
and from propositional extensionality for all universes; T1 does not
use it, and its hypotheses are unchanged [8]. So no form of T1 is an
unqualified formalization of Myers's Theorem
6.3.7: besides these readings, it has ordinary charts and
cover-properness in place of formal étaleness and Dubuc–Penon
properness, as the target T1 fixes.

Proof. G₀ is microlinear (ManifoldMicrolinearity). The source map is
ℑ-étale (EtaleSourceMaps, for T1). The universe adapter [2]: the
original small G, with objects and morphisms in 𝓤, has its Rezk
completion rG in 𝓤 ⁺, and Theorem 5.4.9 (EtaleQuotients) is applied to
the lifted objects and morphisms with y = Yoneda ∘ lower, so that rG is
microlinear; no second Rezk completion is formed. The hom-sets are
properly finite (CoverFiniteness) for the crisp chart cover by the
basic opens of G₁ on which s is injective: its index is ♭-discrete by
Axiom C1, it covers because s is locally injective, its members are
Penon open by regularity, and cover-properness puts every fibre of the
anchor in finitely many of them; so the identity types of rG are
properly finite.

The hypothesis that ℑ preserves crisp pullbacks is stated by the name
○-preserves-crisp-pullbacks that this module exports (its instance of
CrispLemmaF, re-exported), and theorem-T1-literal uses the same name.
A module that applies T1 states the hypothesis by this name: typed by
another instance of CrispLemmaF, the same type has to be converted
across module copies, which Agda does not finish in minutes (added at
gate H10, for T5a).

Inventory: univalence of 𝓤 (and propositional extensionality at 𝓤 from
it), Postulates K and O, Postulate Exp, of which only the translation
law is used (x < y gives x + z < y + z, from the ordered additive group
of Exp; exp and log are not used), ℑ as the nullification of core item
4 with the preservation of crisp pullbacks, and Axiom C1 for the
generators of an arbitrary family, used once: the chart index is
♭-discrete by C1, without a decision. Crisp excluded middle is not
used. The memo's dependency table bounds its paper argument, and these
hypotheses differ from it in three rows [6]: C1 and Exp are assumed
here, and crisp excluded middle, which the paper argument uses for the
chart index, is not. The memo's revision of 13 November 2026 says so
after its table [6, lines 598–606]. This inventory is that of the Agda
theorem. A paper proof may need less; no such claim is checked here.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] GPT-6 Astra. Final H9 universe guidance; original T1/T5 release,
    13 November 2026 (UTC).
    references/A29-h9-t1-t5-release.txt
[3] Claude Fable 5.2. Orbifolds T1 and T5: crisp data, ordinary
    proofs, and the order of the smooth line, 13 November 2026 (UTC).
    references/F06-orbifolds-manifold-crispness.md
[4] GPT-6 Astra. Focused manifold crispness release, 13 November 2026
    (UTC).
    references/A28-manifold-crispness-release.txt
[5] Claude Fable 5.2. Plan: the memo's set-indexed cover-properness at
    the T1 surface, 13 November 2026, Sections 3, 7 and 8
    (references/F20-cover-index-plan.md, SHA-256
    10fb9683…). The code of the additions is that of its scratch check
    OrdinaryEtaleGroupoidsSetIndexCheck.lagda (SHA-256 fbd048ea…), with
    the module names of the library.
[6] The memo on Myers's foundations and properness
    (references/C11-myers-memo-2026-11-13.tex), lines 345–350
    (the condition), 561–596 (the dependency table) and 598–606 (the
    differences of the Agda theorem).
[7] GPT-6 Astra. Consolidation implementation, third release
    (OPUS-CONSOLIDATION-RELEASE-03), 13 November 2026, with the review
    COVER-INDEX-PLAN-REVIEW of the same day.
    references/A33-consolidation-release-03.txt
    references/A34-cover-index-plan-review.txt
[8] GPT-6 Astra. Release of WG8, the integration of the Weil
    comparison, 13 November 2026 (local time), with
    Claude Fable 5.2's plan for the comparison, Section 12, and its
    addendum 01.
    references/A49-weil-release-wg8.txt
    references/F22-weil-plan.md
    references/F23-weil-plan-addendum-01.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Univalence
open import Modal.Subuniverse
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.OrdinaryEtaleGroupoids
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ 𝓡 : Commutative-Ring)
        {@♭ 𝓤 : Universe}
       where

open import UF.Base
open import UF.DiscreteAndSeparated using (discrete-types-are-sets)
open import UF.Equiv
open import UF.ImageAndSurjection pt using (is-surjection)
open import UF.UniverseEmbedding using (Lift ; lift ; lower ; Lift-≃)
open import gist.CohesiveApartness.Flat using (Axiom-C1)
open import gist.Orbifolds.SmoothOrder
open import gist.Orbifolds.Manifolds

open PropositionalTruncation pt
open smooth-line fe pt 𝓡
open smooth-order fe pt 𝓡
open ordinary-manifolds fe pt 𝓡
open import gist.Orbifolds.Topology fe pt
open import gist.Orbifolds.RezkCompletion fe pt {𝓤} {𝓤}
open import gist.Orbifolds.CoverFiniteness fe pt
 using (anchor ; hom-sets-are-properly-finite ;
        identity-types-of-Rezk-completions-are-properly-finite)
open import gist.Orbifolds.CoverProperness fe pt
open import gist.Orbifolds.Microlinearity fe pt 𝓡 {𝓤 ⁺}
open import gist.Orbifolds.MyersMicrolinearity fe pt 𝓡 {𝓤 ⁺}
 using (literal-ℑ-generator ; literal-ℑ-generator-point ; is-literal-orbifold ;
        orbifolds-agree ; literal-nullifications-are-nullifications)
open import gist.Orbifolds.Nullification fe
 using
  (is-nullification ; nullifications-are-Σ-closed ; nullifications-are-replete)
open import gist.Orbifolds.ManifoldMicrolinearity fe pt 𝓡 {𝓤}
 using (ordinary-manifolds-are-microlinear ; microlinearity-is-invariant)
open import gist.Orbifolds.EtaleSourceMaps fe pt 𝓡 {𝓤}

\end{code}

The hypotheses.

\begin{code}

module _ (ua : is-univalent 𝓤)
         (K : Postulate-K)
         (O : Postulate-O)
         (Exp : Postulate-Exp O)
         {𝓟 : Universe}
         (P : subuniverse (𝓤 ⁺) 𝓟)
         (P-is-reflective : subuniverse-is-reflective P)
         (ν : is-nullification ℑ-generator ℑ-generator-point P)
       where

 private
  translation : Translation-Law O
  translation = translation-law-from-Exp O Exp

  pe : propext 𝓤
  pe = univalence-gives-propext ua

 open import gist.Orbifolds.Modalities fe pt P P-is-reflective
              (nullifications-are-Σ-closed ℑ-generator ℑ-generator-point P ν)
              (nullifications-are-replete ℑ-generator ℑ-generator-point P ν)
  using
   (is-étale ; equivalences-are-étale ; étale-maps-are-closed-under-composition)
 import gist.Orbifolds.EtaleQuotients fe pt {𝓤 ⁺} P P-is-reflective
         (nullifications-are-Σ-closed ℑ-generator ℑ-generator-point P ν)
         (nullifications-are-replete ℑ-generator ℑ-generator-point P ν) as EQ
 open import gist.Orbifolds.CrispLemmaF fe pt {𝓤 ⁺} P P-is-reflective
              (nullifications-are-Σ-closed ℑ-generator ℑ-generator-point P ν)
              (nullifications-are-replete ℑ-generator ℑ-generator-point P ν)
  using (○-preserves-crisp-pullbacks) public

\end{code}

The universe adapter: Theorem 5.4.9 for the original small pregroupoid.

\begin{code}

 module _ (π : ○-preserves-crisp-pullbacks) where

  small-étale-pregroupoids-have-microlinear-Rezk-completions
   : (@♭ G : Pregroupoid)
   → is-étale (λ (z : Lift (𝓤 ⁺) (arrows G)) → lift (𝓤 ⁺) (source G (lower z)))
   → is-microlinear (Pregroupoid.ob G)
   → is-microlinear (Rezk-completion G)
  small-étale-pregroupoids-have-microlinear-Rezk-completions G s-is-étale m =
   EQ.theorem-5-4-9-microlinear π infinitesimal-R-pushouts
    (infinitesimal-R-pushouts-have-connected-pointed-types P P-is-reflective ν)
    hom' (λ x → yoneda-embedding G (lower x))
    (λ F → ∥∥-functor (λ (x , p) → lift (𝓤 ⁺) x , p)
            (yoneda-embedding-is-surjection G ua F))
    (λ x x' → Lift-≃ (𝓤 ⁺) (Pregroupoid.hom G (lower x) (lower x'))
              ● hom-≃-identifications G ua (lower x) (lower x'))
    s'-is-étale
    (microlinearity-is-invariant (≃-sym (Lift-≃ (𝓤 ⁺) (Pregroupoid.ob G))) m)
   where
    hom' : Lift (𝓤 ⁺) (Pregroupoid.ob G) → Lift (𝓤 ⁺) (Pregroupoid.ob G) → 𝓤 ⁺ ̇
    hom' x x' = Lift (𝓤 ⁺) (Pregroupoid.hom G (lower x) (lower x'))

    φ : EQ.arrows hom' → Lift (𝓤 ⁺) (arrows G)
    φ (x , x' , g) = lift (𝓤 ⁺) (lower x , lower x' , lower g)

    φ-is-equiv : is-equiv φ
    φ-is-equiv =
     qinvs-are-equivs φ
      ((λ w → lift (𝓤 ⁺) (pr₁ (lower w)) , lift (𝓤 ⁺) (pr₁ (pr₂ (lower w))) ,
              lift (𝓤 ⁺) (pr₂ (pr₂ (lower w)))) ,
       (λ _ → refl) , (λ _ → refl))

    s'-is-étale : is-étale (EQ.source hom')
    s'-is-étale =
     étale-maps-are-closed-under-composition φ
      (λ (z : Lift (𝓤 ⁺) (arrows G)) → lift (𝓤 ⁺) (source G (lower z)))
      (equivalences-are-étale φ φ-is-equiv) s-is-étale

\end{code}

The helper T1′ and the target T1.

\begin{code}

  module _ {𝓙 𝓖 : Universe} {J : 𝓙 ̇ } {Gen : J → 𝓖 ̇ } where

   theorem-T1′-for-set-indices
    : Axiom-C1 Gen
    → (@♭ G : Pregroupoid)
    → {n₀ : ℕ} (𝓜₀ : Ordinary-Manifold O translation K n₀ (Pregroupoid.ob G))
    → {n₁ : ℕ} (T₁ : Topology (arrows G) 𝓤) (@♭ B₁ : ℕ → Subset (arrows G) 𝓤)
    → Ordinary-Manifold-Laws O translation K n₁ T₁ B₁
    → is-étale (λ (z : Lift (𝓤 ⁺) (arrows G)) → lift (𝓤 ⁺) (source G (lower z)))
    → is-locally-injective (source G) T₁
    → is-cover-proper-for-set-indices T₁
       (product (Ordinary-Manifold.topology 𝓜₀)
                (Ordinary-Manifold.topology 𝓜₀)) (anchor G)
    → is-orbifold (Rezk-completion G)
   theorem-T1′-for-set-indices c1 G {n₀} 𝓜₀ {n₁} T₁ B₁ L₁ s-is-étale
    s-is-locally-injective a-is-cover-proper =
    small-étale-pregroupoids-have-microlinear-Rezk-completions G s-is-étale
     (ordinary-manifolds-are-microlinear pe K P P-is-reflective ν O translation
       𝓜₀) ,
    identity-types-of-Rezk-completions-are-properly-finite G ua
     (hom-sets-are-properly-finite G (Ordinary-Manifold.carrier-is-set 𝓜₀)
       (λ j f → f ∈ chart (source G) B₁ j)
       (λ j f → ∈-is-prop f (chart (source G) B₁ j))
       (s-is-injective-on-charts (source G) B₁)
       (charts-are-Penon-open (source G) B₁ T₁
         (Ordinary-Manifold-Laws.topology-is-regular L₁)
         (Ordinary-Manifold-Laws.basis-is-basis L₁))
       (fibres-of-cover-proper-maps-lie-in-finitely-many-charts-for-set-indices
         T₁
         (product (Ordinary-Manifold.topology 𝓜₀)
           (Ordinary-Manifold.topology 𝓜₀))
         (anchor G) a-is-cover-proper
         (Chart-Index (source G) B₁) (chart (source G) B₁)
         (discrete-types-are-sets
           (chart-indices-are-discrete (source G) B₁
             (Ordinary-Manifold-Laws.carrier-is-set L₁)))
         (chart-indices-are-♭-discrete c1 (source G) B₁
           (Ordinary-Manifold-Laws.carrier-is-set L₁))
         (charts-are-open (source G) B₁ T₁
           (Ordinary-Manifold-Laws.basis-is-basis L₁))
         (charts-cover (source G) B₁ T₁ s-is-locally-injective
           (Ordinary-Manifold-Laws.basis-is-basis L₁))))

   theorem-T1′
    : Axiom-C1 Gen
    → (@♭ G : Pregroupoid)
    → {n₀ : ℕ} (𝓜₀ : Ordinary-Manifold O translation K n₀ (Pregroupoid.ob G))
    → {n₁ : ℕ} (T₁ : Topology (arrows G) 𝓤) (@♭ B₁ : ℕ → Subset (arrows G) 𝓤)
    → Ordinary-Manifold-Laws O translation K n₁ T₁ B₁
    → is-étale (λ (z : Lift (𝓤 ⁺) (arrows G)) → lift (𝓤 ⁺) (source G (lower z)))
    → is-locally-injective (source G) T₁
    → is-cover-proper T₁ (product (Ordinary-Manifold.topology 𝓜₀)
                                  (Ordinary-Manifold.topology 𝓜₀)) (anchor G)
    → is-orbifold (Rezk-completion G)
   theorem-T1′ c1 G {n₀} 𝓜₀ {n₁} T₁ B₁ L₁ s-is-étale s-is-locally-injective
    a-is-cover-proper =
    theorem-T1′-for-set-indices c1 G 𝓜₀ T₁ B₁ L₁ s-is-étale
     s-is-locally-injective
     (cover-proper-maps-are-cover-proper-for-set-indices T₁
       (product (Ordinary-Manifold.topology 𝓜₀)
         (Ordinary-Manifold.topology 𝓜₀))
       (anchor G) a-is-cover-proper)

   theorem-T1-for-set-indices
    : Axiom-C1 Gen
    → (@♭ G : Pregroupoid)
    → {n₀ : ℕ} (𝓜₀ : Ordinary-Manifold O translation K n₀ (Pregroupoid.ob G))
    → {n₁ : ℕ} (T₁ : Topology (arrows G) 𝓤) (@♭ B₁ : ℕ → Subset (arrows G) 𝓤)
    → Ordinary-Manifold-Laws O translation K n₁ T₁ B₁
    → is-local-homeomorphism T₁ (Ordinary-Manifold.topology 𝓜₀) (source G)
    → is-cover-proper-for-set-indices T₁
       (product (Ordinary-Manifold.topology 𝓜₀)
                (Ordinary-Manifold.topology 𝓜₀)) (anchor G)
    → is-orbifold (Rezk-completion G)
   theorem-T1-for-set-indices c1 G {n₀} 𝓜₀ {n₁} T₁ B₁ L₁
    s-is-local-homeomorphism a-is-cover-proper =
    theorem-T1′-for-set-indices c1 G 𝓜₀ T₁ B₁ L₁
     (source-maps-of-local-homeomorphisms-are-étale pe K P P-is-reflective ν
       T₁ (Ordinary-Manifold.topology 𝓜₀)
       (Ordinary-Manifold-Laws.carrier-is-set L₁)
        (Ordinary-Manifold.carrier-is-set 𝓜₀)
       (Ordinary-Manifold-Laws.topology-is-regular L₁)
       (Ordinary-Manifold.topology-is-regular 𝓜₀)
       (manifold-topology-has-local-openness O translation K 𝓜₀)
       B₁ (Ordinary-Manifold-Laws.basis-is-basis L₁)
       (source G) s-is-local-homeomorphism)
     (local-homeomorphisms-are-locally-injective (source G) T₁
       (Ordinary-Manifold.topology 𝓜₀) s-is-local-homeomorphism)
     a-is-cover-proper

   theorem-T1
    : Axiom-C1 Gen
    → (@♭ G : Pregroupoid)
    → {n₀ : ℕ} (𝓜₀ : Ordinary-Manifold O translation K n₀ (Pregroupoid.ob G))
    → {n₁ : ℕ} (T₁ : Topology (arrows G) 𝓤) (@♭ B₁ : ℕ → Subset (arrows G) 𝓤)
    → Ordinary-Manifold-Laws O translation K n₁ T₁ B₁
    → is-local-homeomorphism T₁ (Ordinary-Manifold.topology 𝓜₀) (source G)
    → is-cover-proper T₁ (product (Ordinary-Manifold.topology 𝓜₀)
                                  (Ordinary-Manifold.topology 𝓜₀)) (anchor G)
    → is-orbifold (Rezk-completion G)
   theorem-T1 c1 G {n₀} 𝓜₀ {n₁} T₁ B₁ L₁ s-is-local-homeomorphism
    a-is-cover-proper =
    theorem-T1-for-set-indices c1 G 𝓜₀ T₁ B₁ L₁ s-is-local-homeomorphism
     (cover-proper-maps-are-cover-proper-for-set-indices T₁
       (product (Ordinary-Manifold.topology 𝓜₀)
         (Ordinary-Manifold.topology 𝓜₀))
       (anchor G) a-is-cover-proper)

\end{code}

The original crisp scope, as a specialization: the topologies, the
basis of G₀ and the laws may all be given crisply.

\begin{code}

   theorem-T1-for-crisp-topologies
    : Axiom-C1 Gen
    → (@♭ G : Pregroupoid)
    → {n₀ : ℕ} (@♭ T₀ : Topology (Pregroupoid.ob G) 𝓤)
      (@♭ B₀ : ℕ → Subset (Pregroupoid.ob G) 𝓤)
    → Ordinary-Manifold-Laws O translation K n₀ T₀ B₀
    → {n₁ : ℕ} (@♭ T₁ : Topology (arrows G) 𝓤) (@♭ B₁ : ℕ → Subset (arrows G) 𝓤)
    → Ordinary-Manifold-Laws O translation K n₁ T₁ B₁
    → is-local-homeomorphism T₁ T₀ (source G)
    → is-cover-proper T₁ (product T₀ T₀) (anchor G)
    → is-orbifold (Rezk-completion G)
   theorem-T1-for-crisp-topologies c1 G T₀ B₀ L₀ T₁ B₁ L₁ =
    theorem-T1 c1 G (manifold-from-laws O translation K T₀ B₀ L₀) T₁ B₁ L₁

   theorem-T1-for-crisp-topologies-and-set-indices
    : Axiom-C1 Gen
    → (@♭ G : Pregroupoid)
    → {n₀ : ℕ} (@♭ T₀ : Topology (Pregroupoid.ob G) 𝓤)
      (@♭ B₀ : ℕ → Subset (Pregroupoid.ob G) 𝓤)
    → Ordinary-Manifold-Laws O translation K n₀ T₀ B₀
    → {n₁ : ℕ} (@♭ T₁ : Topology (arrows G) 𝓤) (@♭ B₁ : ℕ → Subset (arrows G) 𝓤)
    → Ordinary-Manifold-Laws O translation K n₁ T₁ B₁
    → is-local-homeomorphism T₁ T₀ (source G)
    → is-cover-proper-for-set-indices T₁ (product T₀ T₀) (anchor G)
    → is-orbifold (Rezk-completion G)
   theorem-T1-for-crisp-topologies-and-set-indices c1 G T₀ B₀ L₀ T₁ B₁ L₁ =
    theorem-T1-for-set-indices c1 G
     (manifold-from-laws O translation K T₀ B₀ L₀) T₁ B₁ L₁

\end{code}

Myers's literal definitions: the nullification at all crisp pointed
types that are merely spectra of presentations, and literal orbifolds,
under the two readings of MyersMicrolinearity (Weil algebras by
presentations; each square crisp together with its R-pushout proof).

\begin{code}

module _ (ua : is-univalent 𝓤)
         (K : Postulate-K)
         (O : Postulate-O)
         (Exp : Postulate-Exp O)
         {𝓟 : Universe}
         (P : subuniverse (𝓤 ⁺) 𝓟)
         (P-is-reflective : subuniverse-is-reflective P)
         (ν : is-nullification literal-ℑ-generator literal-ℑ-generator-point P)
       where

 private
  ν' : is-nullification ℑ-generator ℑ-generator-point P
  ν' = lr-implication (literal-nullifications-are-nullifications P) ν

  translation : Translation-Law O
  translation = translation-law-from-Exp O Exp

 module _ (π : ○-preserves-crisp-pullbacks ua K O Exp P P-is-reflective ν')
          {𝓙 𝓖 : Universe} {J : 𝓙 ̇ } {Gen : J → 𝓖 ̇ }
        where

  theorem-T1-literal
   : Axiom-C1 Gen
   → (@♭ G : Pregroupoid)
   → {n₀ : ℕ} (𝓜₀ : Ordinary-Manifold O translation K n₀ (Pregroupoid.ob G))
   → {n₁ : ℕ} (T₁ : Topology (arrows G) 𝓤) (@♭ B₁ : ℕ → Subset (arrows G) 𝓤)
   → Ordinary-Manifold-Laws O translation K n₁ T₁ B₁
   → is-local-homeomorphism T₁ (Ordinary-Manifold.topology 𝓜₀) (source G)
   → is-cover-proper T₁ (product (Ordinary-Manifold.topology 𝓜₀)
                                 (Ordinary-Manifold.topology 𝓜₀)) (anchor G)
   → is-literal-orbifold (Rezk-completion G)
  theorem-T1-literal c1 G 𝓜₀ T₁ B₁ L₁ l a =
   lr-implication (orbifolds-agree (Rezk-completion G))
    (theorem-T1 ua K O Exp P P-is-reflective ν' π c1 G 𝓜₀ T₁ B₁ L₁ l a)

  theorem-T1-literal-for-set-indices
   : Axiom-C1 Gen
   → (@♭ G : Pregroupoid)
   → {n₀ : ℕ} (𝓜₀ : Ordinary-Manifold O translation K n₀ (Pregroupoid.ob G))
   → {n₁ : ℕ} (T₁ : Topology (arrows G) 𝓤) (@♭ B₁ : ℕ → Subset (arrows G) 𝓤)
   → Ordinary-Manifold-Laws O translation K n₁ T₁ B₁
   → is-local-homeomorphism T₁ (Ordinary-Manifold.topology 𝓜₀) (source G)
   → is-cover-proper-for-set-indices T₁
      (product (Ordinary-Manifold.topology 𝓜₀)
               (Ordinary-Manifold.topology 𝓜₀)) (anchor G)
   → is-literal-orbifold (Rezk-completion G)
  theorem-T1-literal-for-set-indices c1 G 𝓜₀ T₁ B₁ L₁ l a =
   lr-implication (orbifolds-agree (Rezk-completion G))
    (theorem-T1-for-set-indices ua K O Exp P P-is-reflective ν' π c1 G 𝓜₀ T₁
      B₁ L₁ l a)

\end{code}
