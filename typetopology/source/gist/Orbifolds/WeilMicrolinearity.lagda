Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), for gate WG7 of Claude Fable
5.2's plan for the comparison of Weil algebras with presentations [1],
as reviewed by GPT-6 Astra [2], amended by Fable's addendum 01 [3] and
released by Astra [4]; the credit and the statement of scope made
precise at the integration of the Weil comparison, 13 November 2026
(local time), as released by Astra [6]. The exported names, and the
universes, modes and hypotheses of their statements, are those of the
plan's statement companion. Claude Opus 5.5 implemented the module.
Two proofs are the drafts of [3, Section 2], token for token: that of
spectra-of-crisp-Weil-algebras-are-null-tests and the converse
direction of null-at-spectra-iff-null-at-spectra-of-Weil-algebras.
Several definitions and proofs are those of MyersMicrolinearity, token
for token after renaming, with 𝓤₂ ⊔ inserted where the universe grows;
the provenance ledger of the package lists them. The rest is Claude
Opus 5.5's. See the AI disclosure in gist.RealCohesion.index.

The crisp bridge: Weil varieties in the tests of microlinearity and
in the generators of ℑ
------------------------------------------------------------------

The module applies the comparison of
gist.Orbifolds.WeilVarietiesFromLargeQuotients, at the constructed
instance with carriers in 𝓤₁, to the crisp families of
gist.Orbifolds.Microlinearity and gist.Orbifolds.MyersMicrolinearity.
Its parameters are crisp, as in those two modules: function
extensionality, propositional truncations, propositional
extensionality pe for all universes, the ring, and the universe 𝓥 of
the test objects. pe is new here and crisp; the single-universe
univalence hypotheses of other Orbifolds modules are ordinary and do
not supply it, and no wrapper hides it. No quotient, instance,
smallness or choice parameter, univalence, resizing, Axiom C1,
Postulate K or J, or new modal axiom is assumed. The ordinary modules
of the comparison are not changed; their closed constructions are
applied here to crisp data.

Crisp and ordinary. The pointed types V, their points v, the types X
and the universes 𝓦 of the statements are ordinary. A function built
from the crisp parameters, applied to crisp inputs, gives a crisp
output; that is how crisp data move below. Nothing turns an ordinary
element of a truncation into a crisp one. The one elimination of a
crisp truncation, in spectra-of-crisp-Weil-algebras-are-null-tests, is
of a crisp element by crisp-∥∥-rec, into a proposition.

  Weil-variety-predicates-agree : a pointed type is a Weil variety, with
  its algebra in 𝓤₁, exactly when it is an infinitesimal variety in the
  sense of MyersMicrolinearity. The comparison of
  WeilVarietiesFromLargeQuotients gives Weil ↔ presented;
  is-presented-variety and
  is-infinitesimal-variety' are the same type by unfolding; and
  infinitesimal-variety-predicates-agree gives old ↔ primed. It is an
  ordinary logical equivalence of propositions.

  Weil-Square : Literal-Square with the four variety fields replaced by
  Weil-variety fields, a commuting square of pointed maps between
  pointed types that are spectra of Weil algebras (Myers's Definition
  4.2.11, with Definition 4.2.1 read through Definition 4.1.1 [5]). Its
  vertices are in 𝓥 and the Weil predicate is in 𝓤₂ ⊔ 𝓥, so the record
  is in 𝓤₂ ⊔ 𝓥 ⁺. to-literal-square and to-Weil-square copy every
  vertex, point, map, pointing proof and commutation proof and transfer
  only the four variety proofs; literal-test-square uses only the
  vertices, the maps and the commutation, so the test squares agree by
  computation.

  Weil-test-square, Weil-R-Pushout, Weil-R-pushouts, is-Weil-microlinear
  and is-Weil-orbifold : the family of crisp Weil R-pushouts and the
  predicates of AbstractOrbifolds for it, in 𝓤₂ ⊔ 𝓥 ⁺ ⊔ 𝓦 and
  𝓤₂ ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ for X in 𝓦.

  Weil-microlinearity-agrees, Weil-orbifolds-agree : microlinearity
  agrees with Weil microlinearity, and orbifolds with Weil orbifolds,
  for every ordinary X. A crisp Weil R-pushout q gives the crisp literal
  R-pushout (to-literal-square (pr₁ q) , pr₂ q), and conversely, with
  the same test square; this is composed with microlinearity-agrees.
  For orbifolds the microlinearity component is transported and the
  component on properly finite identity types is kept.

  Weil-Generator, Weil-ℑ-generator, Weil-ℑ-generator-point,
  null-at-spectra-iff-null-at-Weil-varieties,
  Weil-nullifications-are-nullifications : the crisp Weil varieties as
  generators. For null-at-spectra-iff-null-at-Weil-varieties, a crisp
  (V , v , Weil proof) is reindexed to and from a crisp literal
  generator, keeping V and v, and this is composed with
  null-at-spectra-iff-null-at-varieties.
  Weil-nullifications-are-nullifications, on a given subuniverse P, is
  proved directly: for each X, the given nullification compares
  membership of X in P with nullity at its own generators, and
  null-at-spectra-iff-null-at-Weil-varieties compares that with nullity
  at the other generators. The plan's route through
  literal-nullifications-are-nullifications is not taken. The result
  constructs no reflector and identifies none with Myers's
  infinitesimal-disk modality.

  spectra-of-crisp-Weil-algebras-are-null-tests : if X is null at the
  old generators, then it is null at the spectrum of every crisp Weil
  algebra, with crisp algebra, augmentation and Weil proof, in every
  crisp universe. The reverse theorem of the comparison, applied to the
  crisp algebra, is a crisp element of a truncation; crisp-∥∥-rec opens
  it into the proposition of being null, and the generator Lift 𝓥 (Spec
  P) is moved to the spectrum by
  e ● ≃-sym (Lift-≃ 𝓥 (Spec P)) : Specᴿ 𝓐 ≃ Lift 𝓥 (Spec P).

  null-at-spectra-iff-null-at-spectra-of-Weil-algebras : nullity at the
  old generators is nullity at the spectra of the crisp Weil algebras
  with carrier in 𝓤₁. The converse takes the Weil algebra of a crisp
  presentation P, with its augmentation and Weil proof, and uses
  Lift-≃ 𝓥 (Spec P) ● ≃-sym (spectrum-of-Weil-algebra-of P)
   : Lift 𝓥 (Spec P) ≃ Specᴿ (Weil-algebra-of P).
  The first statement holds in every crisp universe of algebras; the
  equivalence is for algebras in 𝓤₁, since its converse uses the
  constructed algebra. No algebra is lifted to a higher universe.

The packaging is exactly that of the literal family: the square, its
pointing and commutation, its four mere Weil data and its R-pushout
proof are crisp together, under one ♭. A reading with a crisp square
but an ordinary R-pushout proof would need a further bridge (with Axiom
C1), which is not made here. The four mere Weil data are never opened
by the square conversions; they become four mere presentations, which
the existing proof of microlinearity-agrees opens crisply.

Scope. This compares classes of test objects: pointed types, squares of
them, and generators. Maps of spectra induced by maps of algebras, by
precomposition, and the pointed comparisons of spectra built from them
do exist, and the proofs use those induced by isomorphisms of algebras.
Not claimed: that the spectrum of algebras is full or faithful, that an
arbitrary map of spectra, or of infinitesimal varieties, is induced by
a map of algebras, the duality of Lemma 4.2.2, anything that uses
Postulate J, or anything about the infinitesimal-disk modality. The
literal forms of the targets T2 to T4 for is-Weil-orbifold are not
stated here.

[1] Claude Fable 5.2. Plan: formalizing the comparison of Weil algebras
    with presentations, 13 November 2026, Section 8, with its statement
    companion, Section WG7 (plan SHA-256 b1662ecc…; companion SHA-256
    47974af8…).
[2] GPT-6 Astra. Review of Fable's Weil plan, 13 November 2026
    (FABLE-WEIL-PLAN-REVIEW-01).
[3] Claude Fable 5.2. Addendum 01 to the plan, 13 November 2026,
    Sections 1 and 2 (SHA-256 abf31923…).
[4] GPT-6 Astra. Release of gate WG7, 14 November 2026 UTC
    (SHA-256 9c3d8976…).
[5] David Jaz Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.
[6] GPT-6 Astra. Release of WG8, the integration of the Weil
    comparison, 13 November 2026 (local time), items O1 and O2.
    references/A49-weil-release-wg8.txt

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons using (Prop-Ext)
open import Modal.Subuniverse
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.WeilMicrolinearity
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ pe : Prop-Ext)
        (@♭ 𝓡 : Commutative-Ring)
        {@♭ 𝓥 : Universe}
       where

open import UF.Equiv
open import UF.Equiv-FunExt using (being-equiv-is-prop)
open import UF.UniverseEmbedding using (Lift-≃)
open import gist.CohesiveApartness.Flat using (♭ ; _^♭ ; ♭-counit ; is-null)

open smooth-line fe pt 𝓡
open import gist.Orbifolds.TestSquares fe using (Test-Square ; is-local)
open import gist.Orbifolds.CrispTruncation fe pt using (crisp-∥∥-rec)
import gist.Orbifolds.AbstractOrbifolds fe pt as AO
open import gist.Orbifolds.Nullification fe
 using
  (is-nullification ; null-types-are-closed-under-equivalence-of-generators)
open import gist.Orbifolds.Microlinearity fe pt 𝓡 {𝓥}
open import gist.Orbifolds.MyersMicrolinearity fe pt 𝓡 {𝓥}
open import gist.Orbifolds.WeilVarietiesFromLargeQuotients fe pt pe 𝓡

\end{code}

The predicate, against the library's.

\begin{code}

Weil-variety-predicates-agree
 : {𝓦 : Universe} (V : 𝓦 ̇ ) (v : V)
 → is-Weil-variety V v ↔ is-infinitesimal-variety V v
Weil-variety-predicates-agree V v =
 (λ w → rl-implication (infinitesimal-variety-predicates-agree V v)
          (lr-implication (Weil-varieties-are-presented-varieties V v) w)) ,
 (λ o → rl-implication (Weil-varieties-are-presented-varieties V v)
          (lr-implication (infinitesimal-variety-predicates-agree V v) o))

\end{code}

Weil squares, and the two conversions.

\begin{code}

record Weil-Square : 𝓤₂ ⊔ 𝓥 ⁺ ̇ where
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
  V₁-is-Weil-variety : is-Weil-variety V₁ p₁
  V₂-is-Weil-variety : is-Weil-variety V₂ p₂
  V₃-is-Weil-variety : is-Weil-variety V₃ p₃
  V₄-is-Weil-variety : is-Weil-variety V₄ p₄

to-literal-square : Weil-Square → Literal-Square
to-literal-square L = record
 { V₁ = V₁ ; V₂ = V₂ ; V₃ = V₃ ; V₄ = V₄
 ; p₁ = p₁ ; p₂ = p₂ ; p₃ = p₃ ; p₄ = p₄
 ; v₁₂ = v₁₂ ; v₁₃ = v₁₃ ; v₂₄ = v₂₄ ; v₃₄ = v₃₄
 ; v₁₂-is-pointed = v₁₂-is-pointed
 ; v₁₃-is-pointed = v₁₃-is-pointed
 ; v₂₄-is-pointed = v₂₄-is-pointed
 ; v₃₄-is-pointed = v₃₄-is-pointed
 ; commutes = commutes
 ; V₁-is-variety =
    lr-implication (Weil-variety-predicates-agree V₁ p₁) V₁-is-Weil-variety
 ; V₂-is-variety =
    lr-implication (Weil-variety-predicates-agree V₂ p₂) V₂-is-Weil-variety
 ; V₃-is-variety =
    lr-implication (Weil-variety-predicates-agree V₃ p₃) V₃-is-Weil-variety
 ; V₄-is-variety =
    lr-implication (Weil-variety-predicates-agree V₄ p₄) V₄-is-Weil-variety
 }
 where
  open Weil-Square L

to-Weil-square : Literal-Square → Weil-Square
to-Weil-square L = record
 { V₁ = V₁ ; V₂ = V₂ ; V₃ = V₃ ; V₄ = V₄
 ; p₁ = p₁ ; p₂ = p₂ ; p₃ = p₃ ; p₄ = p₄
 ; v₁₂ = v₁₂ ; v₁₃ = v₁₃ ; v₂₄ = v₂₄ ; v₃₄ = v₃₄
 ; v₁₂-is-pointed = v₁₂-is-pointed
 ; v₁₃-is-pointed = v₁₃-is-pointed
 ; v₂₄-is-pointed = v₂₄-is-pointed
 ; v₃₄-is-pointed = v₃₄-is-pointed
 ; commutes = commutes
 ; V₁-is-Weil-variety =
    rl-implication (Weil-variety-predicates-agree V₁ p₁) V₁-is-variety
 ; V₂-is-Weil-variety =
    rl-implication (Weil-variety-predicates-agree V₂ p₂) V₂-is-variety
 ; V₃-is-Weil-variety =
    rl-implication (Weil-variety-predicates-agree V₃ p₃) V₃-is-variety
 ; V₄-is-Weil-variety =
    rl-implication (Weil-variety-predicates-agree V₄ p₄) V₄-is-variety
 }
 where
  open Literal-Square L

\end{code}

The family of crisp Weil R-pushouts, and microlinearity.

\begin{code}

Weil-test-square : Weil-Square → Test-Square 𝓥
Weil-test-square L = literal-test-square (to-literal-square L)

Weil-R-Pushout : 𝓤₂ ⊔ 𝓥 ⁺ ̇
Weil-R-Pushout = Σ L ꞉ Weil-Square , is-local (Weil-test-square L) R

Weil-R-pushouts : ♭ Weil-R-Pushout → Test-Square 𝓥
Weil-R-pushouts u = Weil-test-square (pr₁ (♭-counit u))

is-Weil-microlinear : {𝓦 : Universe} → 𝓦 ̇ → 𝓤₂ ⊔ 𝓥 ⁺ ⊔ 𝓦 ̇
is-Weil-microlinear X = AO.is-microlinear Weil-R-pushouts X

is-Weil-orbifold : {𝓦 : Universe} → 𝓦 ̇ → 𝓤₂ ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
is-Weil-orbifold X = AO.is-orbifold Weil-R-pushouts X

Weil-microlinearity-agrees
 : {𝓦 : Universe} (X : 𝓦 ̇ ) → is-microlinear X ↔ is-Weil-microlinear X
Weil-microlinearity-agrees X =
 (λ m → literal-to-Weil (lr-implication (microlinearity-agrees X) m)) ,
 (λ m → rl-implication (microlinearity-agrees X) (Weil-to-literal m))
 where
  literal-to-Weil : is-literally-microlinear X → is-Weil-microlinear X
  literal-to-Weil lm (q ^♭) = lm ((to-literal-square (pr₁ q) , pr₂ q) ^♭)

  Weil-to-literal : is-Weil-microlinear X → is-literally-microlinear X
  Weil-to-literal wm (q ^♭) = wm ((to-Weil-square (pr₁ q) , pr₂ q) ^♭)

Weil-orbifolds-agree
 : {𝓦 : Universe} (X : 𝓦 ̇ ) → is-orbifold X ↔ is-Weil-orbifold X
Weil-orbifolds-agree X =
 (λ (m , i) → lr-implication (Weil-microlinearity-agrees X) m , i) ,
 (λ (m , i) → rl-implication (Weil-microlinearity-agrees X) m , i)

\end{code}

The crisp Weil varieties as generators.

\begin{code}

Weil-Generator : 𝓤₂ ⊔ 𝓥 ⁺ ̇
Weil-Generator = Σ V ꞉ 𝓥 ̇ , Σ v ꞉ V , is-Weil-variety V v

Weil-ℑ-generator : ♭ Weil-Generator → 𝓥 ̇
Weil-ℑ-generator u = pr₁ (♭-counit u)

Weil-ℑ-generator-point : (u : ♭ Weil-Generator) → Weil-ℑ-generator u
Weil-ℑ-generator-point u = pr₁ (pr₂ (♭-counit u))

null-at-spectra-iff-null-at-Weil-varieties
 : {𝓦 : Universe} (X : 𝓦 ̇ )
 → ((u : ♭ Weil-Presentation) → is-null (ℑ-generator u) X)
 ↔ ((u : ♭ Weil-Generator) → is-null (Weil-ℑ-generator u) X)
null-at-spectra-iff-null-at-Weil-varieties X =
 (λ n → literal-to-Weil
          (lr-implication (null-at-spectra-iff-null-at-varieties X) n)) ,
 (λ n → rl-implication (null-at-spectra-iff-null-at-varieties X)
          (Weil-to-literal n))
 where
  literal-to-Weil
   : ((u : ♭ Literal-Generator) → is-null (literal-ℑ-generator u) X)
   → ((u : ♭ Weil-Generator) → is-null (Weil-ℑ-generator u) X)
  literal-to-Weil n (q ^♭) =
   n ((pr₁ q , pr₁ (pr₂ q) ,
       lr-implication (Weil-variety-predicates-agree (pr₁ q) (pr₁ (pr₂ q)))
        (pr₂ (pr₂ q))) ^♭)

  Weil-to-literal
   : ((u : ♭ Weil-Generator) → is-null (Weil-ℑ-generator u) X)
   → ((u : ♭ Literal-Generator) → is-null (literal-ℑ-generator u) X)
  Weil-to-literal n (q ^♭) =
   n ((pr₁ q , pr₁ (pr₂ q) ,
       rl-implication (Weil-variety-predicates-agree (pr₁ q) (pr₁ (pr₂ q)))
        (pr₂ (pr₂ q))) ^♭)

Weil-nullifications-are-nullifications
 : {𝓦 : Universe} (P : subuniverse 𝓥 𝓦)
 → is-nullification Weil-ℑ-generator Weil-ℑ-generator-point P
 ↔ is-nullification ℑ-generator ℑ-generator-point P
Weil-nullifications-are-nullifications P =
 (λ ν X → (λ m → rl-implication (null-at-spectra-iff-null-at-Weil-varieties X)
                   (lr-implication (ν X) m)) ,
          (λ n → rl-implication (ν X)
                   (lr-implication
                     (null-at-spectra-iff-null-at-Weil-varieties X) n))) ,
 (λ ν X → (λ m → lr-implication (null-at-spectra-iff-null-at-Weil-varieties X)
                   (lr-implication (ν X) m)) ,
          (λ n → rl-implication (ν X)
                   (rl-implication
                     (null-at-spectra-iff-null-at-Weil-varieties X) n)))

\end{code}

The statements indexed by crisp Weil algebras.

\begin{code}

spectra-of-crisp-Weil-algebras-are-null-tests
 : {@♭ 𝓦ₐ : Universe} {𝓦 : Universe} (X : 𝓦 ̇ )
 → ((u : ♭ Weil-Presentation) → is-null (ℑ-generator u) X)
 → (@♭ 𝓐 : Algebra 𝓦ₐ) (@♭ π : Specᴿ 𝓐) (@♭ w : is-Weil-algebra 𝓐 π)
 → is-null (Specᴿ 𝓐) X
spectra-of-crisp-Weil-algebras-are-null-tests X n 𝓐 π w =
 crisp-∥∥-rec
  (being-equiv-is-prop (λ 𝓤 𝓥 → fe) (λ (x : X) (_ : Specᴿ 𝓐) → x))
  (λ a → null-types-are-closed-under-equivalence-of-generators
          (pr₁ (pr₂ a) ● ≃-sym (Lift-≃ 𝓥 (Spec (pr₁ a)))) X
          (n ((pr₁ a) ^♭)))
  (spectra-of-Weil-algebras-are-spectra-of-presentations 𝓐 π w)

null-at-spectra-iff-null-at-spectra-of-Weil-algebras
 : {𝓦 : Universe} (X : 𝓦 ̇ )
 → ((u : ♭ Weil-Presentation) → is-null (ℑ-generator u) X)
 ↔ ((@♭ 𝓐 : Algebra 𝓤₁) (@♭ π : Specᴿ 𝓐) (@♭ w : is-Weil-algebra 𝓐 π)
      → is-null (Specᴿ 𝓐) X)
null-at-spectra-iff-null-at-spectra-of-Weil-algebras X =
 (λ n 𝓐 π w → spectra-of-crisp-Weil-algebras-are-null-tests X n 𝓐 π w) ,
 backward
 where
  backward
   : ((@♭ 𝓐 : Algebra 𝓤₁) (@♭ π : Specᴿ 𝓐) (@♭ w : is-Weil-algebra 𝓐 π)
        → is-null (Specᴿ 𝓐) X)
   → ((u : ♭ Weil-Presentation) → is-null (ℑ-generator u) X)
  backward m (P ^♭) =
   null-types-are-closed-under-equivalence-of-generators
    (Lift-≃ 𝓥 (Spec P) ● ≃-sym (spectrum-of-Weil-algebra-of P)) X
    (m (Weil-algebra-of P) (augmentation-of P) (Weil-algebra-of-is-Weil P))

\end{code}
