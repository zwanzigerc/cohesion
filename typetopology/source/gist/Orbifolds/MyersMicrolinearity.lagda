Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026 (local time); the scope of the literal
definitions made precise 13 November 2026, in the third part of the
consolidation [5]; the sentence on Weil algebras updated at the
integration of the Weil comparison, the same night [6]. Orbifold gate
H8 of Fable's roadmap [1], after the review dated 13 November 2026
(UTC) [2, 3].

Myers's infinitesimal varieties, and the two statement bridges
--------------------------------------------------------------

Microlinearity defines microlinear types and ℑ through squares of
spectra of crisp presentations. Myers's definitions [4, Definitions
4.2.1 and 4.2.11] use pointed types that are merely pointed-equivalent
to a spectrum. This module states his definitions in the adopted
reading (see Scope below) and proves that they agree with the formal
ones, following Fable [2, Section 1]
and the implementation plan of GPT-6 Astra's audit [3, Section 4
(c)–(f)].

  is-infinitesimal-variety V v : there merely are a presentation W and
  a pointed equivalence (V , v) ≃ Spec (normalize W) [4, Definition
  4.2.1, with Weil algebras by presentation, normalized as in
  SmoothLine]; infinitesimal-variety-predicates-agree compares it with
  the same predicate for Spec W;

  Literal-Square : a commuting square of pointed maps between pointed
  types that are infinitesimal varieties [4, Definition 4.2.11];

  literal-R-pushouts : the family of crisp literal squares together
  with their R-pushout proofs, all under ♭, the packaging of the
  formal family [3, Section 5; 2, "one reading to record"];

  is-literally-microlinear, is-literal-orbifold : Myers's Definitions
  4.2.12 and 1.1.2, in this reading;

  microlinearity-agrees : for every type X, ordinary or crisp, X is
  microlinear exactly when it is literally microlinear (Fable's
  obligation 5);

  null-at-spectra-iff-null-at-varieties,
  literal-nullifications-are-nullifications : a type is null for the
  spectra of crisp presentations exactly when it is null for every
  crisp infinitesimal variety, so nullification at either family is
  the same (obligation 6);

  literal-proposition-6-4-2, literal-corollary-6-4-4,
  literal-theorem-6-4-1 : T3, T4 and T2 for the literal definitions.
  For the reading of "literal" and of ℑ, see gist.Orbifolds.index,
  the paragraph on the scope of the statements.

Proof of microlinearity-agrees. Let L be a crisp literal square with a
crisp R-pushout proof, and X any type. Being X-local is a proposition
(being-local-is-prop), so the four crisp mere presentations of L may be
opened by crisp-∥∥-rec into it (CrispTruncation); this makes no
simultaneous choice. The four pointed equivalences then conjugate L
into a crisp square of spectra (square-of-spectra), and the
conjugation is an equivalence of test squares (square-equivalence),
whose fourth vertex is a set. By SquareEquivalences, the R-pushout
proof moves to the square of spectra; formal microlinearity gives its
X-locality, which moves back to L. Conversely, a square of spectra is
a literal square, with the canonical presentations. The commutation of
a square of pointed maps also asks for a coherence of the pointing
identifications; it holds automatically, because the vertices are sets
[3, Precision 3].

The packaging is exactly that of the formal family: the square, its
pointing and commutation, its four mere presentations and its R-pushout
proof are crisp together. A reading with a crisp square but an
ordinary R-pushout proof would need a further bridge (with Axiom C1),
which is not made here [3, Section 5].

Scope. A pointed infinitesimal variety merely admits a presentation
whose spectrum is pointed-equivalent to it. This presentation witness
is ordinary. A test square is crisp together with its R-pushout proof. What
is formalized is the normalization of presentations (SmoothLine) and
the comparison of the code-defined test predicates
(infinitesimal-variety-predicates-agree, microlinearity-agrees,
null-at-spectra-iff-null-at-varieties). That the spectrum of a
presentation is the Hom-spectrum of its normalized Weil algebra, and
that every Weil algebra in the sense of Definition 4.1.1 merely has
such a presentation, is formalized in WeilVarietiesFromLargeQuotients,
for Weil algebras with carrier in 𝓤₁ (the reverse direction in any
universe) and from propositional extensionality for all universes, an
explicit parameter; WeilMicrolinearity compares the literal tests and
generators with whole crisp squares and packages of Weil varieties,
each square crisp together with its R-pushout proof [6]. The statements
of this module do not use that comparison and keep their own
hypotheses.
Normalization preserves the spectrum, not the quotient algebra of the
original presentation. The nullification at these tests is the
nullification at finite Weil spectra; no equivalence with Myers's
infinitesimal-disk modality has been proved [5].

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] Claude Fable 5.2. Orbifolds: the two statement bridges of H8, and
    readiness for H9 and H10, 13 November 2026, Sections 1–3.
    references/F05-orbifolds-h8-bridges.md
[3] GPT-6 Astra. Fable's H8 answer: bridges, crisp truncation, and T2,
    13 November 2026.
    references/A14-h8-answer-audit.txt
[4] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.
[5] GPT-6 Astra. Consolidation implementation, third release
    (OPUS-CONSOLIDATION-RELEASE-03), 13 November 2026: the scope of the
    statements, made precise, with its prose follow-up 01. The algebraic
    comparison is that of GPT-6 Astra's reconciliation of the first
    statement reviews, 13 November 2026, Section 2.
    references/A33-consolidation-release-03.txt
    references/A35-release-03-prose-followup-01.txt
    references/A36-reconciliation-review.txt
[6] GPT-6 Astra. Release of WG8, the integration of the Weil
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

module gist.Orbifolds.MyersMicrolinearity
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ 𝓡 : Commutative-Ring)
        {@♭ 𝓥 : Universe}
       where

open PropositionalTruncation pt

open import UF.Base
open import UF.Equiv
open import UF.Equiv-FunExt using (being-equiv-is-prop)
open import UF.Pullback
open import UF.Sets
open import UF.Sets-Properties using (equiv-to-set ; Σ-is-set ; Π-is-set)
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties using (props-are-sets)
open import UF.UniverseEmbedding using (Lift ; lift ; lower ; Lift-≃)
open import gist.CohesiveApartness.Flat using (♭ ; _^♭ ; ♭-counit ; is-null)

open smooth-line fe pt 𝓡
open import gist.Orbifolds.TestSquares fe using (Test-Square ; is-local)
open import gist.Orbifolds.SquareEquivalences fe
 using (being-local-is-prop ; Square-Equivalence ;
        locality-is-invariant-under-square-equivalences)
open import gist.Orbifolds.CrispTruncation fe pt using (crisp-∥∥-rec)
open import gist.Orbifolds.ProperFiniteness fe pt using (is-finite)
import gist.Orbifolds.AbstractOrbifolds fe pt as AO
open import gist.Orbifolds.Nullification fe
 using
  (is-nullification ; null-types-are-closed-under-equivalence-of-generators)
open import gist.Orbifolds.Microlinearity fe pt 𝓡 {𝓥}
open import gist.Orbifolds.GlobalQuotients fe pt 𝓡 {𝓥}
 using (ℑ-preserves-crisp-pullbacks ; theorem-6-4-1)

\end{code}

Spectra are sets, and Myers's infinitesimal varieties.

\begin{code}

spectra-are-sets : (W : Weil-Presentation) → is-set (Spec W)
spectra-are-sets W = Σ-is-set (Π-is-set fe (λ _ → R-is-set))
                              (λ a → props-are-sets (equations-are-props W a))

Presentation-of : {𝓦 : Universe} (V : 𝓦 ̇ ) → V → 𝓦 ̇
Presentation-of V v = Σ W ꞉ Weil-Presentation ,
                      Σ e ꞉ V ≃ Spec (normalize W) ,
                        ⌜ e ⌝ v ＝ Spec-point (normalize W)

is-infinitesimal-variety : {𝓦 : Universe} (V : 𝓦 ̇ ) → V → 𝓦 ̇
is-infinitesimal-variety V v = ∥ Presentation-of V v ∥

is-infinitesimal-variety' : {𝓦 : Universe} (V : 𝓦 ̇ ) → V → 𝓦 ̇
is-infinitesimal-variety' V v =
 ∃ W ꞉ Weil-Presentation , Σ e ꞉ V ≃ Spec W , ⌜ e ⌝ v ＝ Spec-point W

normalization-inverse-is-pointed
 : (W : Weil-Presentation)
 → ⌜ ≃-sym (normalization-equivalence W) ⌝ (Spec-point W)
 ＝ Spec-point (normalize W)
normalization-inverse-is-pointed W =
 to-subtype-＝ (equations-are-props (normalize W)) refl

infinitesimal-variety-predicates-agree
 : {𝓦 : Universe} (V : 𝓦 ̇ ) (v : V)
 → is-infinitesimal-variety V v ↔ is-infinitesimal-variety' V v
infinitesimal-variety-predicates-agree V v =
 ∥∥-functor (λ (W , e , π) → normalize W , e , π) ,
 ∥∥-functor (λ (W , e , π) → W , (e ● ≃-sym (normalization-equivalence W)) ,
                             (ap ⌜ ≃-sym (normalization-equivalence W) ⌝ π
                              ∙ normalization-inverse-is-pointed W))

spectrum-is-variety : (W : Weil-Presentation)
                    → is-infinitesimal-variety (Lift 𝓥 (Spec W))
                       (lift 𝓥 (Spec-point W))
spectrum-is-variety W =
 ∣ W , (Lift-≃ 𝓥 (Spec W) ● ≃-sym (normalization-equivalence W)) ,
   normalization-inverse-is-pointed W ∣

\end{code}

Myers's test squares, and the literal family.

\begin{code}

record Literal-Square : 𝓥 ⁺ ̇ where
 field
  V₁ V₂ V₃ V₄ : 𝓥 ̇
  p₁ : V₁
  p₂ : V₂
  p₃ : V₃
  p₄ : V₄
  v₁₂ : V₁ → V₂
  v₁₃ : V₁ → V₃
  v₂₄ : V₂ → V₄
  v₃₄ : V₃ → V₄
  v₁₂-is-pointed : v₁₂ p₁ ＝ p₂
  v₁₃-is-pointed : v₁₃ p₁ ＝ p₃
  v₂₄-is-pointed : v₂₄ p₂ ＝ p₄
  v₃₄-is-pointed : v₃₄ p₃ ＝ p₄
  commutes : v₂₄ ∘ v₁₂ ∼ v₃₄ ∘ v₁₃
  V₁-is-variety : is-infinitesimal-variety V₁ p₁
  V₂-is-variety : is-infinitesimal-variety V₂ p₂
  V₃-is-variety : is-infinitesimal-variety V₃ p₃
  V₄-is-variety : is-infinitesimal-variety V₄ p₄

literal-test-square : Literal-Square → Test-Square 𝓥
literal-test-square L = record
 { V₁ = V₁ ; V₂ = V₂ ; V₃ = V₃ ; V₄ = V₄
  ; v₁₂ = v₁₂ ; v₁₃ = v₁₃ ; v₂₄ = v₂₄ ; v₃₄ = v₃₄
  ; square = commutes
  }
 where
  open Literal-Square L

Literal-R-Pushout : 𝓥 ⁺ ̇
Literal-R-Pushout = Σ L ꞉ Literal-Square , is-local (literal-test-square L) R

literal-R-pushouts : ♭ Literal-R-Pushout → Test-Square 𝓥
literal-R-pushouts u = literal-test-square (pr₁ (♭-counit u))

is-literally-microlinear : {𝓦 : Universe} → 𝓦 ̇ → 𝓥 ⁺ ⊔ 𝓦 ̇
is-literally-microlinear X = AO.is-microlinear literal-R-pushouts X

is-literal-orbifold : {𝓦 : Universe} → 𝓦 ̇ → 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
is-literal-orbifold X = AO.is-orbifold literal-R-pushouts X

\end{code}

The conjugation of a literal square by presentations of its vertices.

\begin{code}

conjugate-is-pointed
 : {𝓦 𝓦' : Universe} {A : 𝓦 ̇ } {B : 𝓦' ̇ } {SA SB : 𝓤₀ ̇ }
   {a₀ : A} {b₀ : B} {sA : SA} {sB : SB}
   (eA : A ≃ SA) (eB : B ≃ SB)
 → ⌜ eA ⌝ a₀ ＝ sA → ⌜ eB ⌝ b₀ ＝ sB
 → (f : A → B) → f a₀ ＝ b₀
 → ⌜ eB ⌝ (f (⌜ eA ⌝⁻¹ sA)) ＝ sB
conjugate-is-pointed {𝓦} {𝓦'} {A} {B} {SA} {SB} {a₀} {b₀} {sA} {sB} eA eB πA πB
 f p =
 ap (⌜ eB ⌝ ∘ f)
  (ap ⌜ eA ⌝⁻¹ (πA ⁻¹) ∙ inverses-are-retractions ⌜ eA ⌝ ⌜ eA ⌝-is-equiv a₀)
 ∙ ap ⌜ eB ⌝ p
 ∙ πB

module _ (L : Literal-Square)
         (a₁ : Presentation-of (Literal-Square.V₁ L) (Literal-Square.p₁ L))
         (a₂ : Presentation-of (Literal-Square.V₂ L) (Literal-Square.p₂ L))
         (a₃ : Presentation-of (Literal-Square.V₃ L) (Literal-Square.p₃ L))
         (a₄ : Presentation-of (Literal-Square.V₄ L) (Literal-Square.p₄ L))
       where

 open Literal-Square L

 private
  e₁ = pr₁ (pr₂ a₁)
  e₂ = pr₁ (pr₂ a₂)
  e₃ = pr₁ (pr₂ a₃)
  e₄ = pr₁ (pr₂ a₄)

  η : {𝓦 : Universe} {A : 𝓦 ̇ } {S : 𝓤₀ ̇ } (e : A ≃ S) (x : A)
    → ⌜ e ⌝⁻¹ (⌜ e ⌝ x) ＝ x
  η e = inverses-are-retractions ⌜ e ⌝ ⌜ e ⌝-is-equiv

 square-of-spectra : Infinitesimal-Square
 square-of-spectra = record
  { W₁ = normalize (pr₁ a₁)
   ; W₂ = normalize (pr₁ a₂)
   ; W₃ = normalize (pr₁ a₃)
   ; W₄ = normalize (pr₁ a₄)
   ; w₁₂ = ⌜ e₂ ⌝ ∘ v₁₂ ∘ ⌜ e₁ ⌝⁻¹
   ; w₁₃ = ⌜ e₃ ⌝ ∘ v₁₃ ∘ ⌜ e₁ ⌝⁻¹
   ; w₂₄ = ⌜ e₄ ⌝ ∘ v₂₄ ∘ ⌜ e₂ ⌝⁻¹
   ; w₃₄ = ⌜ e₄ ⌝ ∘ v₃₄ ∘ ⌜ e₃ ⌝⁻¹
   ; w₁₂-is-pointed =
    conjugate-is-pointed e₁ e₂ (pr₂ (pr₂ a₁)) (pr₂ (pr₂ a₂)) v₁₂ v₁₂-is-pointed
   ; w₁₃-is-pointed =
    conjugate-is-pointed e₁ e₃ (pr₂ (pr₂ a₁)) (pr₂ (pr₂ a₃)) v₁₃ v₁₃-is-pointed
   ; w₂₄-is-pointed =
    conjugate-is-pointed e₂ e₄ (pr₂ (pr₂ a₂)) (pr₂ (pr₂ a₄)) v₂₄ v₂₄-is-pointed
   ; w₃₄-is-pointed =
    conjugate-is-pointed e₃ e₄ (pr₂ (pr₂ a₃)) (pr₂ (pr₂ a₄)) v₃₄ v₃₄-is-pointed
   ; commutes = λ u → ap (⌜ e₄ ⌝ ∘ v₂₄) (η e₂ (v₁₂ (⌜ e₁ ⌝⁻¹ u)))
                   ∙ ap ⌜ e₄ ⌝ (commutes (⌜ e₁ ⌝⁻¹ u))
                   ∙ (ap (⌜ e₄ ⌝ ∘ v₃₄) (η e₃ (v₁₃ (⌜ e₁ ⌝⁻¹ u))))⁻¹
   }

 private
  lifted : {A : 𝓥 ̇ } {S : 𝓤₀ ̇ } → A ≃ S → A ≃ Lift 𝓥 S
  lifted {A} {S} e = e ● ≃-sym (Lift-≃ 𝓥 S)

 square-equivalence : Square-Equivalence (literal-test-square L)
                                         (test-square square-of-spectra)
 square-equivalence = record
  { e₁ = lifted e₁
   ; e₂ = lifted e₂
   ; e₃ = lifted e₃
   ; e₄ = lifted e₄
   ; c₁₂ = λ x → ap (λ - → lift 𝓥 (⌜ e₂ ⌝ (v₁₂ -))) (η e₁ x)
   ; c₁₃ = λ x → ap (λ - → lift 𝓥 (⌜ e₃ ⌝ (v₁₃ -))) (η e₁ x)
   ; c₂₄ = λ x → ap (λ - → lift 𝓥 (⌜ e₄ ⌝ (v₂₄ -))) (η e₂ x)
   ; c₃₄ = λ x → ap (λ - → lift 𝓥 (⌜ e₄ ⌝ (v₃₄ -))) (η e₃ x)
   }

 fourth-vertex-is-set : is-set (Lift 𝓥 (Spec (normalize (pr₁ a₄))))
 fourth-vertex-is-set = equiv-to-set (Lift-≃ 𝓥 (Spec (normalize (pr₁ a₄))))
                                     (spectra-are-sets (normalize (pr₁ a₄)))

 R-pushout-of-spectra : is-local (literal-test-square L) R
                      → is-local (test-square square-of-spectra) R
 R-pushout-of-spectra =
  lr-implication (locality-is-invariant-under-square-equivalences
                   (literal-test-square L) (test-square square-of-spectra)
                   square-equivalence fourth-vertex-is-set R)

\end{code}

The bridge for test squares (Fable's obligation 5).

\begin{code}

literal-square-of : Infinitesimal-Square → Literal-Square
literal-square-of s = record
 { V₁ = Lift 𝓥 (Spec W₁)
  ; V₂ = Lift 𝓥 (Spec W₂)
  ; V₃ = Lift 𝓥 (Spec W₃)
  ; V₄ = Lift 𝓥 (Spec W₄)
  ; p₁ = lift 𝓥 (Spec-point W₁)
  ; p₂ = lift 𝓥 (Spec-point W₂)
  ; p₃ = lift 𝓥 (Spec-point W₃)
  ; p₄ = lift 𝓥 (Spec-point W₄)
  ; v₁₂ = λ v → lift 𝓥 (w₁₂ (lower v))
  ; v₁₃ = λ v → lift 𝓥 (w₁₃ (lower v))
  ; v₂₄ = λ v → lift 𝓥 (w₂₄ (lower v))
  ; v₃₄ = λ v → lift 𝓥 (w₃₄ (lower v))
  ; v₁₂-is-pointed = ap (lift 𝓥) w₁₂-is-pointed
  ; v₁₃-is-pointed = ap (lift 𝓥) w₁₃-is-pointed
  ; v₂₄-is-pointed = ap (lift 𝓥) w₂₄-is-pointed
  ; v₃₄-is-pointed = ap (lift 𝓥) w₃₄-is-pointed
  ; commutes = λ v → ap (lift 𝓥) (commutes (lower v))
  ; V₁-is-variety = spectrum-is-variety W₁
  ; V₂-is-variety = spectrum-is-variety W₂
  ; V₃-is-variety = spectrum-is-variety W₃
  ; V₄-is-variety = spectrum-is-variety W₄
  }
 where
  open Infinitesimal-Square s

module _ {𝓦 : Universe} (X : 𝓦 ̇ ) where

 literally-microlinear-types-are-microlinear
  : is-literally-microlinear X → is-microlinear X
 literally-microlinear-types-are-microlinear lm (q ^♭) =
  lm ((literal-square-of (pr₁ q) , pr₂ q) ^♭)

 module _ (m : is-microlinear X) where

  local-at-a-presented-square
   : (@♭ L : Literal-Square)
   → (@♭ r : is-local (literal-test-square L) R)
   → (@♭ a₁ : Presentation-of (Literal-Square.V₁ L) (Literal-Square.p₁ L))
   → (@♭ a₂ : Presentation-of (Literal-Square.V₂ L) (Literal-Square.p₂ L))
   → (@♭ a₃ : Presentation-of (Literal-Square.V₃ L) (Literal-Square.p₃ L))
   → (@♭ a₄ : Presentation-of (Literal-Square.V₄ L) (Literal-Square.p₄ L))
   → is-local (literal-test-square L) X
  local-at-a-presented-square L r a₁ a₂ a₃ a₄ =
   rl-implication (locality-is-invariant-under-square-equivalences
                    (literal-test-square L)
                     (test-square (square-of-spectra L a₁ a₂ a₃ a₄))
                    (square-equivalence L a₁ a₂ a₃ a₄)
                    (fourth-vertex-is-set L a₁ a₂ a₃ a₄) X)
    (m ((square-of-spectra L a₁ a₂ a₃ a₄ ,
         R-pushout-of-spectra L a₁ a₂ a₃ a₄ r) ^♭))

  microlinear-types-are-literally-microlinear : is-literally-microlinear X
  microlinear-types-are-literally-microlinear (q ^♭) =
   crisp-∥∥-rec i
    (λ a₁ → crisp-∥∥-rec i
     (λ a₂ → crisp-∥∥-rec i
      (λ a₃ → crisp-∥∥-rec i
       (λ a₄ → local-at-a-presented-square (pr₁ q) (pr₂ q) a₁ a₂ a₃ a₄)
       (Literal-Square.V₄-is-variety (pr₁ q)))
      (Literal-Square.V₃-is-variety (pr₁ q)))
     (Literal-Square.V₂-is-variety (pr₁ q)))
    (Literal-Square.V₁-is-variety (pr₁ q))
   where
    i = being-local-is-prop (literal-test-square (pr₁ q)) X

 microlinearity-agrees : is-microlinear X ↔ is-literally-microlinear X
 microlinearity-agrees = microlinear-types-are-literally-microlinear ,
                         literally-microlinear-types-are-microlinear

orbifolds-agree : {𝓦 : Universe} (X : 𝓦 ̇ )
                → is-orbifold X ↔ is-literal-orbifold X
orbifolds-agree X =
 (λ (m , i) → lr-implication (microlinearity-agrees X) m , i) ,
 (λ (m , i) → rl-implication (microlinearity-agrees X) m , i)

\end{code}

The bridge for the generators of ℑ (Fable's obligation 6).

\begin{code}

Literal-Generator : 𝓥 ⁺ ̇
Literal-Generator = Σ V ꞉ 𝓥 ̇ , Σ v ꞉ V , is-infinitesimal-variety V v

literal-ℑ-generator : ♭ Literal-Generator → 𝓥 ̇
literal-ℑ-generator u = pr₁ (♭-counit u)

literal-ℑ-generator-point : (u : ♭ Literal-Generator) → literal-ℑ-generator u
literal-ℑ-generator-point u = pr₁ (pr₂ (♭-counit u))

null-at-spectra-iff-null-at-varieties
 : {𝓦 : Universe} (X : 𝓦 ̇ )
 → ((u : ♭ Weil-Presentation) → is-null (ℑ-generator u) X)
 ↔ ((u : ♭ Literal-Generator) → is-null (literal-ℑ-generator u) X)
null-at-spectra-iff-null-at-varieties X = forward , backward
 where
  forward : ((u : ♭ Weil-Presentation) → is-null (ℑ-generator u) X)
          → ((u : ♭ Literal-Generator) → is-null (literal-ℑ-generator u) X)
  forward n (q ^♭) =
   crisp-∥∥-rec (being-equiv-is-prop (λ 𝓤 𝓥 → fe) (λ (x : X) (_ : pr₁ q) → x))
    (λ a → null-types-are-closed-under-equivalence-of-generators
            (pr₁ (pr₂ a) ● ≃-sym (Lift-≃ 𝓥 (Spec (normalize (pr₁ a))))) X
            (n ((normalize (pr₁ a)) ^♭)))
    (pr₂ (pr₂ q))

  backward : ((u : ♭ Literal-Generator) → is-null (literal-ℑ-generator u) X)
           → ((u : ♭ Weil-Presentation) → is-null (ℑ-generator u) X)
  backward n (W ^♭) =
   n ((Lift 𝓥 (Spec W) , lift 𝓥 (Spec-point W) , spectrum-is-variety W) ^♭)

literal-nullifications-are-nullifications
 : {𝓦 : Universe} (P : subuniverse 𝓥 𝓦)
 → is-nullification literal-ℑ-generator literal-ℑ-generator-point P
 ↔ is-nullification ℑ-generator ℑ-generator-point P
literal-nullifications-are-nullifications P =
 (λ ν X → (λ m → rl-implication (null-at-spectra-iff-null-at-varieties X)
                   (lr-implication (ν X) m)) ,
          (λ n → rl-implication (ν X)
                   (lr-implication (null-at-spectra-iff-null-at-varieties X)
                     n))) ,
 (λ ν X → (λ m → lr-implication (null-at-spectra-iff-null-at-varieties X)
                   (lr-implication (ν X) m)) ,
          (λ n → rl-implication (ν X)
                   (rl-implication (null-at-spectra-iff-null-at-varieties X)
                     n)))

\end{code}

T3, T4 and T2 for the literal definitions.

\begin{code}

literal-proposition-6-4-2
 : {𝓦 𝓦' 𝓦'' : Universe} {B : 𝓦 ̇ } {C : 𝓦' ̇ } {D : 𝓦'' ̇ }
 → is-literal-orbifold B
 → is-literal-orbifold C
 → is-literal-orbifold D
 → (f : B → D) (g : C → D)
 → is-literal-orbifold (pullback.pullback f g)
literal-proposition-6-4-2 {𝓦} {𝓦'} {𝓦''} {B} {C} {D} oB oC oD f g =
 lr-implication (orbifolds-agree _)
  (proposition-6-4-2 (rl-implication (orbifolds-agree B) oB)
                     (rl-implication (orbifolds-agree C) oC)
                     (rl-implication (orbifolds-agree D) oD) f g)

literal-corollary-6-4-4 : {𝓦 : Universe} {X : 𝓦 ̇ }
                        → is-literal-orbifold X
                        → is-literal-orbifold (Σ x ꞉ X , x ＝ x)
literal-corollary-6-4-4 {𝓦} {X} o =
 lr-implication (orbifolds-agree _)
  (corollary-6-4-4 (rl-implication (orbifolds-agree X) o))

module _ {𝓦 : Universe}
         (P : subuniverse 𝓥 𝓦)
         (P-is-reflective : subuniverse-is-reflective P)
         (ν : is-nullification literal-ℑ-generator literal-ℑ-generator-point P)
       where

 private
  ν' : is-nullification ℑ-generator ℑ-generator-point P
  ν' = lr-implication (literal-nullifications-are-nullifications P) ν

 literal-theorem-6-4-1
  : Postulate-K
  → ℑ-preserves-crisp-pullbacks P P-is-reflective
     (lr-implication (literal-nullifications-are-nullifications P) ν)
  → {@♭ B : 𝓥 ̇ } (@♭ b₀ : B)
  → ((u : B) → ∥ b₀ ＝ u ∥)
  → is-finite (b₀ ＝ b₀)
  → (X̃ : B → 𝓥 ̇ )
  → is-set (X̃ b₀)
  → is-literally-microlinear (X̃ b₀)
  → is-literal-orbifold (Σ X̃)
 literal-theorem-6-4-1 K π b₀ B-is-connected Ω-is-finite X̃ X-is-set m =
  lr-implication (orbifolds-agree _)
   (theorem-6-4-1 P P-is-reflective ν' K π b₀ B-is-connected Ω-is-finite X̃
     X-is-set (rl-implication (microlinearity-agrees (X̃ b₀)) m))

\end{code}
