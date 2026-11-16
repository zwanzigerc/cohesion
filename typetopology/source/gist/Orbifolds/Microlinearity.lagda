Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026; title and first paragraph made precise
13 November 2026, after the final audits; the scope of ℑ and of the
literal forms made precise later that day, in the third part of the
consolidation [3]; the sentence on Weil algebras updated at the
integration of the Weil comparison, the same night [4]. Orbifold gate
H8 of Fable's roadmap [1].

Microlinear types and orbifolds, for spectra of presentations
-------------------------------------------------------------

Myers's definitions [2, Definitions 4.2.10–4.2.12 and 1.1.2], over the
smooth line of SmoothLine, for spectra of Weil presentations (the
literal definitions, and the proof that they agree with these, are in
MyersMicrolinearity):

  Infinitesimal-Square : a commuting square of pointed maps between
  spectra of Weil presentations;

  test-square s : that square, with its vertices lifted to a universe
  𝓥 (the universe of the modality, where the orbifolds live);

  Infinitesimal-R-Pushout : such a square that is an R-pushout, that
  is, R-local [2, Definition 4.2.10];

  infinitesimal-R-pushouts : the family of crisp infinitesimal
  R-pushouts, indexed by ♭ Infinitesimal-R-Pushout [2, Definition
  4.2.11: the squares are crisp];

  is-microlinear X : every crisp infinitesimal R-pushout is an
  X-pushout [2, Definition 4.2.12];

  is-orbifold X : X is microlinear and its identity types are properly
  finite [2, Definition 1.1.2];

  proposition-6-4-2, corollary-6-4-4 : the targets T3 and T4 for this
  notion, as instances of AbstractOrbifolds [2, Proposition 6.4.2,
  Definition 6.4.3 and Corollary 6.4.4].

ℑ, nullification at all crisp infinitesimal varieties (core item 4),
is a hypothesis, as in Nullification: a reflective subuniverse of 𝓥
whose modal types are the types null for Lift 𝓥 (Spec W) for every
crisp Weil presentation W (ℑ-generator). It is the nullification at
finite Weil spectra; no equivalence with Myers's infinitesimal-disk
modality [2, Definition 4.3.1], whose comparison with it his Remark
4.3.2 leaves open, has been proved. Under it:

  infinitesimal-R-pushouts-have-connected-pointed-types : the vertices
  of every square of the family are ℑ-connected and V₂ is pointed, the
  hypothesis under which EtaleQuotients descends microlinearity;

  discrete-types-are-ℑ-modal : under Postulate K, every type with
  decidable equality is ℑ-modal [1, Section 3.5].

Formal reading. Myers's infinitesimal varieties are pointed types
merely equivalent to a spectrum [2, Definition 4.2.1]. Here the
vertices of a square are spectra, with their presentations, the
roadmap's reading of Weil algebras by presentation [1, Section 8,
item 2]. Every square of infinitesimal varieties is merely equivalent
to a square of spectra, and X-pushouts are invariant under equivalence
of squares; for a crisp square the presentations are opened crisply,
inside the proposition to be proved. These steps are formalized in
MyersMicrolinearity (added after the review dated 13 November 2026),
which states Myers's definitions in the adopted reading and proves that
both microlinearity and nullification agree with the ones here: a
comparison of code-defined predicates. The comparison with the Weil
algebras of Definition 4.1.1 and their Hom-spectra is formalized in
WeilVarietiesFromLargeQuotients, for Weil algebras with carrier in 𝓤₁
and from propositional extensionality for all universes, an explicit
parameter; WeilMicrolinearity compares the tests and generators here
with whole crisp squares and packages of Weil varieties, and nothing
here depends on it [4]. Commuting as a
square of pointed maps asks in addition for a coherence between the
identifications that the maps are pointed; it holds automatically,
because spectra are sets. The vertices are lifted to 𝓥 because the
torsors of a group, in GlobalQuotients, live one universe up.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Sections 2.2, 3.5, 3.8 and 8.
    references/F01-orbifolds-roadmap-rev2.md
[2] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.
[3] GPT-6 Astra. Consolidation implementation, third release
    (OPUS-CONSOLIDATION-RELEASE-03), 13 November 2026: the scope of the
    statements, made precise.
    references/A33-consolidation-release-03.txt
[4] GPT-6 Astra. Release of WG8, the integration of the Weil
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
open import Modal.Subuniverse
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.Microlinearity
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ 𝓡 : Commutative-Ring)
        {@♭ 𝓥 : Universe}
       where

open import UF.DiscreteAndSeparated using (is-discrete)
open import UF.Pullback
open import UF.UniverseEmbedding using (Lift ; lift ; lower)
open import gist.CohesiveApartness.Flat using (♭ ; _^♭ ; ♭-counit)

open smooth-line fe pt 𝓡
open import gist.Orbifolds.TestSquares fe using (Test-Square ; is-local)
import gist.Orbifolds.AbstractOrbifolds fe pt as AO
open import gist.Orbifolds.Nullification fe
 using (is-nullification ; discrete-types-are-null ;
        generators-of-nullifications-are-connected ;
        nullifications-are-Σ-closed ; nullifications-are-replete)

\end{code}

Infinitesimal squares, R-pushouts, and the family of crisp
infinitesimal R-pushouts.

\begin{code}

record Infinitesimal-Square : 𝓤₀ ̇ where
 field
  W₁ W₂ W₃ W₄ : Weil-Presentation
  w₁₂ : Spec W₁ → Spec W₂
  w₁₃ : Spec W₁ → Spec W₃
  w₂₄ : Spec W₂ → Spec W₄
  w₃₄ : Spec W₃ → Spec W₄
  w₁₂-is-pointed : w₁₂ (Spec-point W₁) ＝ Spec-point W₂
  w₁₃-is-pointed : w₁₃ (Spec-point W₁) ＝ Spec-point W₃
  w₂₄-is-pointed : w₂₄ (Spec-point W₂) ＝ Spec-point W₄
  w₃₄-is-pointed : w₃₄ (Spec-point W₃) ＝ Spec-point W₄
  commutes : w₂₄ ∘ w₁₂ ∼ w₃₄ ∘ w₁₃

test-square : Infinitesimal-Square → Test-Square 𝓥
test-square s = record
 { V₁ = Lift 𝓥 (Spec W₁)
  ; V₂ = Lift 𝓥 (Spec W₂)
  ; V₃ = Lift 𝓥 (Spec W₃)
  ; V₄ = Lift 𝓥 (Spec W₄)
  ; v₁₂ = λ v → lift 𝓥 (w₁₂ (lower v))
  ; v₁₃ = λ v → lift 𝓥 (w₁₃ (lower v))
  ; v₂₄ = λ v → lift 𝓥 (w₂₄ (lower v))
  ; v₃₄ = λ v → lift 𝓥 (w₃₄ (lower v))
  ; square = λ v → ap (lift 𝓥) (commutes (lower v))
  }
 where
  open Infinitesimal-Square s

is-R-pushout : Infinitesimal-Square → 𝓥 ̇
is-R-pushout s = is-local (test-square s) R

Infinitesimal-R-Pushout : 𝓥 ̇
Infinitesimal-R-Pushout = Σ s ꞉ Infinitesimal-Square , is-R-pushout s

infinitesimal-R-pushouts : ♭ Infinitesimal-R-Pushout → Test-Square 𝓥
infinitesimal-R-pushouts u = test-square (pr₁ (♭-counit u))

\end{code}

Microlinear types and orbifolds, and the targets T3 and T4.

\begin{code}

is-microlinear : {𝓦 : Universe} → 𝓦 ̇ → 𝓥 ⊔ 𝓦 ̇
is-microlinear X = AO.is-microlinear infinitesimal-R-pushouts X

is-orbifold : {𝓦 : Universe} → 𝓦 ̇ → 𝓥 ⊔ 𝓦 ⁺ ̇
is-orbifold X = AO.is-orbifold infinitesimal-R-pushouts X

proposition-6-4-2
 : {𝓦 𝓦' 𝓦'' : Universe} {B : 𝓦 ̇ } {C : 𝓦' ̇ } {D : 𝓦'' ̇ }
 → is-orbifold B
 → is-orbifold C
 → is-orbifold D
 → (f : B → D) (g : C → D)
 → is-orbifold (pullback.pullback f g)
proposition-6-4-2 =
 AO.pullbacks-of-orbifolds-are-orbifolds infinitesimal-R-pushouts

corollary-6-4-4 : {𝓦 : Universe} {X : 𝓦 ̇ }
                → is-orbifold X
                → is-orbifold (Σ x ꞉ X , x ＝ x)
corollary-6-4-4 = AO.inertia-of-orbifolds-are-orbifolds infinitesimal-R-pushouts

\end{code}

The generators of ℑ: the spectra of crisp Weil presentations, pointed
by 0 and lifted to 𝓥.

\begin{code}

ℑ-generator : ♭ Weil-Presentation → 𝓥 ̇
ℑ-generator u = Lift 𝓥 (Spec (♭-counit u))

ℑ-generator-point : (u : ♭ Weil-Presentation) → ℑ-generator u
ℑ-generator-point u = lift 𝓥 (Spec-point (♭-counit u))

module _ {𝓦 : Universe}
         (P : subuniverse 𝓥 𝓦)
         (P-is-reflective : subuniverse-is-reflective P)
         (ν : is-nullification ℑ-generator ℑ-generator-point P)
       where

 open import gist.Orbifolds.EtaleQuotients fe pt {𝓥} P P-is-reflective
              (nullifications-are-Σ-closed ℑ-generator ℑ-generator-point P ν)
              (nullifications-are-replete ℑ-generator ℑ-generator-point P ν)
  using (has-connected-pointed-types)
 open import gist.RealCohesion.ShapeProducts fe pt P P-is-reflective
              (nullifications-are-Σ-closed ℑ-generator ℑ-generator-point P ν)
              (nullifications-are-replete ℑ-generator ℑ-generator-point P ν)
  using (is-○-connected)

 spectra-are-ℑ-connected : (@♭ W : Weil-Presentation)
                         → is-○-connected (Lift 𝓥 (Spec W))
 spectra-are-ℑ-connected W =
  generators-of-nullifications-are-connected pt ℑ-generator ℑ-generator-point
   P P-is-reflective ν (W ^♭)

 infinitesimal-R-pushouts-have-connected-pointed-types
  : has-connected-pointed-types infinitesimal-R-pushouts
 infinitesimal-R-pushouts-have-connected-pointed-types (p ^♭) =
  spectra-are-ℑ-connected (Infinitesimal-Square.W₁ (pr₁ p)) ,
  spectra-are-ℑ-connected (Infinitesimal-Square.W₂ (pr₁ p)) ,
  spectra-are-ℑ-connected (Infinitesimal-Square.W₃ (pr₁ p)) ,
  spectra-are-ℑ-connected (Infinitesimal-Square.W₄ (pr₁ p)) ,
  lift 𝓥 (Spec-point (Infinitesimal-Square.W₂ (pr₁ p)))

 discrete-types-are-ℑ-modal : Postulate-K
                            → (X : 𝓥 ̇ ) → is-discrete X
                            → subuniverse-contains P X
 discrete-types-are-ℑ-modal K X d =
  rl-implication (ν X)
   (λ u → discrete-types-are-null (ℑ-generator u) (ℑ-generator-point u)
            (λ f v → maps-from-spectra-to-𝟚-are-constant K (♭-counit u)
                      (f ∘ lift 𝓥) (lower v))
            X d)

\end{code}
