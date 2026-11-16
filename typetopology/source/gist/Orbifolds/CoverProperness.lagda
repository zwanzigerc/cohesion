Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026 (local time); the condition for set-indexed
covers added 13 November 2026, in the third part of the consolidation
that followed the final audits [6, 7]. Orbifold gate H9 of Fable's
roadmap [1, Section 2.1].

Cover-properness, the official condition
----------------------------------------

GPT-6 Astra's open-cover condition [2, Section 2], as fixed for the
targets [1, Section 2.1; 3, Section 2], with the binders of Fable's
reply on crispness [4, Section 1.2] and Astra's release [5, item 2].
Let p : E → B be a map, E crisp, with supplied ordinary topologies. p
is cover-proper if for every crisp family (V_i) of opens of E, indexed
by a crisp ♭-discrete type I and covering every ordinary point of E,
every ordinary point b of B merely has an open neighbourhood W and a
finite list F of indices, which may repeat indices, with
p⁻¹(W) ⊆ ⋃_{i ∈ F} V_i.

  is-cover-proper : the condition. The index type, the family and the
  carrier E are crisp; the topologies and B are ordinary; the proofs
  that the V_i are open, that they cover, and that I is ♭-discrete are
  ordinary arguments, so the condition applies to every such family,
  whatever the crispness of those proofs.
  W and F may depend on b and need not be crisp; no disjointness is
  asked; the opens are those of the supplied topologies;

  fibres-of-cover-proper-maps-lie-in-finitely-many-charts : the
  consequence for fibres that the proof of T1 uses, in the form of the
  module CoverFiniteness: the fibre over b lies in finitely many V_i.
  It is a lemma; it does not replace the official condition;

  is-cover-proper-for-set-indices : the same condition for covers
  indexed by crisp types that are sets as well as ♭-discrete; the
  premise is-set I, an ordinary argument like the others, comes before
  is-♭-discrete I, and the two conditions differ in this one line. It
  is the condition of the memo [8], whose covers are indexed by crisp
  discrete sets: a discrete set is read as a set that is ♭-discrete,
  not as a type with decidable equality;

  cover-proper-maps-are-cover-proper-for-set-indices : the older
  condition implies it, by restriction to set-indexed covers. The
  converse is not proved, nothing here uses it, and no set truncation
  is involved;

  fibres-of-cover-proper-maps-lie-in-finitely-many-charts-for-set-indices :
  the consequence for fibres from the set-indexed condition, for a
  set-indexed cover. Both consequences are one private proof.

The binders of both conditions are those described above; in
particular the topologies, the codomain, b, and the proofs about the
cover are ordinary, and the index type lies in the universe of E and B
[7, Section 8]. The condition is defined for any map out of a crisp
type, without a continuity premise.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] GPT-6 Astra. Open-cover properness: composition and the
    regular-target frame laws, 11 November 2026.
    references/A04-cover-properness-stability.txt
[3] GPT-6 Astra. Original targets, 12 November 2026
    (references/A31-original-targets.txt).
[4] Claude Fable 5.2. Orbifolds T1 and T5: crisp data, ordinary
    proofs, and the order of the smooth line, 13 November 2026 (UTC).
    references/F06-orbifolds-manifold-crispness.md
[5] GPT-6 Astra. Focused manifold crispness release, 13 November 2026
    (UTC).
    references/A28-manifold-crispness-release.txt
[6] GPT-6 Astra. Consolidation implementation, third release
    (OPUS-CONSOLIDATION-RELEASE-03), 13 November 2026, with the review
    COVER-INDEX-PLAN-REVIEW of the same day.
    references/A33-consolidation-release-03.txt
    references/A34-cover-index-plan-review.txt
[7] Claude Fable 5.2. Plan: the memo's set-indexed cover-properness at
    the T1 surface, 13 November 2026, Sections 3 and 8
    (references/F20-cover-index-plan.md, SHA-256
    10fb9683…). The code of the additions is that of its scratch check
    CoverPropernessSetIndexCheck.lagda (SHA-256 5b19ef7f…), with the
    module name of this module.
[8] The memo on Myers's foundations and properness
    (references/C11-myers-memo-2026-11-13.tex), lines 345–350.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module gist.Orbifolds.CoverProperness
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Fin.Type
open import UF.Sets using (is-set)
open import gist.CohesiveApartness.Flat using (is-♭-discrete)
open import gist.Orbifolds.Topology fe pt
open import gist.Orbifolds.CoverFiniteness fe pt
 using (fibres-lie-in-finitely-many-charts)

open PropositionalTruncation pt

is-cover-proper : {@♭ 𝓤 : Universe} {@♭ E : 𝓤 ̇ } {B : 𝓤 ̇ }
                → Topology E 𝓤 → Topology B 𝓤 → (E → B) → 𝓤 ⁺ ̇
is-cover-proper {𝓤} {E} {B} TE TB p =
   (@♭ I : 𝓤 ̇ ) (@♭ V : I → Subset E 𝓤)
 → is-♭-discrete I
 → ((i : I) → Topology.is-open TE (V i))
 → ((e : E) → ∃ i ꞉ I , e ∈ V i)
 → (b : B) → ∃ W ꞉ Subset B 𝓤 , Topology.is-open TB W × b ∈ W
                × (Σ n ꞉ ℕ , Σ F ꞉ (Fin n → I) ,
                     ((e : E) → p e ∈ W → ∃ j ꞉ Fin n , e ∈ V (F j)))

is-cover-proper-for-set-indices
 : {@♭ 𝓤 : Universe} {@♭ E : 𝓤 ̇ } {B : 𝓤 ̇ }
 → Topology E 𝓤 → Topology B 𝓤 → (E → B) → 𝓤 ⁺ ̇
is-cover-proper-for-set-indices {𝓤} {E} {B} TE TB p =
   (@♭ I : 𝓤 ̇ ) (@♭ V : I → Subset E 𝓤)
 → is-set I
 → is-♭-discrete I
 → ((i : I) → Topology.is-open TE (V i))
 → ((e : E) → ∃ i ꞉ I , e ∈ V i)
 → (b : B) → ∃ W ꞉ Subset B 𝓤 , Topology.is-open TB W × b ∈ W
                × (Σ n ꞉ ℕ , Σ F ꞉ (Fin n → I) ,
                     ((e : E) → p e ∈ W → ∃ j ꞉ Fin n , e ∈ V (F j)))

cover-proper-maps-are-cover-proper-for-set-indices
 : {@♭ 𝓤 : Universe} {@♭ E : 𝓤 ̇ } {B : 𝓤 ̇ }
   (TE : Topology E 𝓤) (TB : Topology B 𝓤) (p : E → B)
 → is-cover-proper TE TB p
 → is-cover-proper-for-set-indices TE TB p
cover-proper-maps-are-cover-proper-for-set-indices
 TE TB p cp I V I-is-set d o c b = cp I V d o c b

private
 finite-control-of-a-preimage-controls-the-fibre
  : {𝓤 : Universe} {E B I : 𝓤 ̇ } (TB : Topology B 𝓤) (p : E → B)
    (V : I → Subset E 𝓤) (b : B)
  → (∃ W ꞉ Subset B 𝓤 , Topology.is-open TB W × b ∈ W
        × (Σ n ꞉ ℕ , Σ F ꞉ (Fin n → I) ,
             ((e : E) → p e ∈ W → ∃ j ꞉ Fin n , e ∈ V (F j))))
  → ∃ n ꞉ ℕ , Σ F ꞉ (Fin n → I) ,
     ((e : fiber p b) → ∃ j ꞉ Fin n , pr₁ e ∈ V (F j))
 finite-control-of-a-preimage-controls-the-fibre TB p V b =
  ∥∥-functor
   (λ (W , oW , bW , n , F , h) →
     n , F , (λ (e , q) → h e (transport (_∈ W) (q ⁻¹) bW)))

fibres-of-cover-proper-maps-lie-in-finitely-many-charts
 : {@♭ 𝓤 : Universe} {@♭ E : 𝓤 ̇ } {B : 𝓤 ̇ }
   (TE : Topology E 𝓤) (TB : Topology B 𝓤) (p : E → B)
 → is-cover-proper TE TB p
 → (@♭ I : 𝓤 ̇ ) (@♭ V : I → Subset E 𝓤)
 → is-♭-discrete I
 → ((i : I) → Topology.is-open TE (V i))
 → ((e : E) → ∃ i ꞉ I , e ∈ V i)
 → fibres-lie-in-finitely-many-charts p (λ i e → e ∈ V i)
fibres-of-cover-proper-maps-lie-in-finitely-many-charts TE TB p cp I V d o c b =
 finite-control-of-a-preimage-controls-the-fibre TB p V b (cp I V d o c b)

fibres-of-cover-proper-maps-lie-in-finitely-many-charts-for-set-indices
 : {@♭ 𝓤 : Universe} {@♭ E : 𝓤 ̇ } {B : 𝓤 ̇ }
   (TE : Topology E 𝓤) (TB : Topology B 𝓤) (p : E → B)
 → is-cover-proper-for-set-indices TE TB p
 → (@♭ I : 𝓤 ̇ ) (@♭ V : I → Subset E 𝓤)
 → is-set I
 → is-♭-discrete I
 → ((i : I) → Topology.is-open TE (V i))
 → ((e : E) → ∃ i ꞉ I , e ∈ V i)
 → fibres-lie-in-finitely-many-charts p (λ i e → e ∈ V i)
fibres-of-cover-proper-maps-lie-in-finitely-many-charts-for-set-indices
 TE TB p cp I V I-is-set d o c b =
 finite-control-of-a-preimage-controls-the-fibre TB p V b
  (cp I V I-is-set d o c b)

\end{code}
