Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), for gate WG6 of Claude Fable
5.2's plan for the comparison of Weil algebras with presentations [1],
as reviewed by GPT-6 Astra [2], amended by Fable's addendum 01 [3] and
released by Astra [4]. The exported names, and the universes and
hypotheses of their statements, are those of the plan's statement
companion, with the explicit composition of Fable's WG1 audit [5] in
lemma-4-1-3; the proofs are Claude Opus 5.5's. See the AI disclosure in
gist.RealCohesion.index.

The comparison for the constructed presented algebras
-----------------------------------------------------

The generic modules of the comparison are applied to the constructed
instance large-presented-algebras of
gist.Orbifolds.PresentedAlgebrasFromLargeQuotients, whose carriers are
in 𝓤₁, and the results are stated with every universe written out. The
module takes exactly function extensionality, propositional
truncations, propositional extensionality pe for all universes, which
the large quotients of that instance use, and the ring; there is no
quotient, instance or universe parameter. pe is an ordinary parameter
here.

The eight closed declarations:

  presented-algebra g : the algebra presented by the finite family of
  equations g, the actual constructed carrier, in 𝓤₁.

  remark-4-1-6 (Myers's Remark 4.1.6 [6]): its spectrum is the type of
  solutions of g, for every finite family g; no equation needs to
  vanish at the origin.

  lemma-4-1-3 (Myers's Lemma 4.1.3, in the plan's displayed form): the
  centering of gist.Orbifolds.WeilAlgebraPresentations at this instance.
  An algebra in any universe 𝓦 with an augmentation, merely finitely
  presented at this instance, is merely presented by a family vanishing
  at the origin, by an isomorphism that may cross universes, under
  which the augmentation is ev₀; that law is an equality of
  homomorphisms. No Weil proof, nilpotent kernel or finite generation of
  the kernel is assumed.

  is-Weil-variety (Myers's Definition 4.2.1 at this instance): the
  Weil-variety predicate with the Weil algebra in 𝓤₁, of level 𝓤₂ ⊔ 𝓣.

  spectra-of-presentations-are-spectra-of-Weil-algebras : for every
  Weil presentation P, an actual augmentation of the Weil algebra of P
  of gist.Orbifolds.WeilAlgebras, which is the algebra of normalize P in
  𝓤₁, with its Weil proof, the equivalence of its spectrum with Spec P,
  and the path from the augmentation to Spec-point P. These are data,
  not a mere existence.

  spectra-of-Weil-algebras-are-spectra-of-presentations : the spectrum
  of a Weil algebra in any universe 𝓦, with finite presentation read at
  this instance, is merely Spec P for a Weil presentation P, as a
  pointed type.

  Weil-varieties-in-any-universe-are-presented : a Weil variety with its
  algebra in any universe 𝓦 is a presented variety.

  Weil-varieties-are-presented-varieties : a pointed type in any
  universe 𝓣 is a Weil variety with its algebra in 𝓤₁ exactly when it is
  a presented variety. The left side has level 𝓤₂ ⊔ 𝓣 and the right side
  level 𝓣. This gives no representative in 𝓤₀, does not lift an algebra
  to other universes, and does not show that small representatives give
  small quotients.

The earlier results and names that state and consume these are
re-exported at this instance, unchanged: Algebra, ⟨_⟩, R-as-algebra,
Specᴿ, _≅ₐ_ and _∘ₕ_ of gist.Orbifolds.Algebras; Sol and ev₀ of
gist.Orbifolds.PresentedAlgebrasProperties; is-finitely-presented,
kernel-is-finitely-generated, kernel-is-nilpotent, is-Weil-algebra,
Weil-algebra-of, augmentation-of, Weil-algebra-of-is-Weil,
spectrum-of-Weil-algebra-of and spectrum-of-Weil-algebra-of-is-pointed
of gist.Orbifolds.WeilAlgebras; Weil-algebras-are-presented of
gist.Orbifolds.WeilAlgebraPresentations; and is-Weil-variety-at and
is-presented-variety of gist.Orbifolds.WeilVarieties. The names of
SmoothLine, such as Weil-Presentation, Spec and Spec-point, do not
depend on the instance and are not re-exported.

Assumptions: exactly fe, pt, pe and the ring. No quotient, choice,
univalence, resizing, nontriviality, excluded middle, crisp or cohesive
datum is assumed, and the module adds no option and no postulate.

[1] Claude Fable 5.2. Plan: formalizing the comparison of Weil algebras
    with presentations, 13 November 2026, Section 7.3, with its
    statement companion, Section WG6 (plan SHA-256 b1662ecc…; companion
    SHA-256 47974af8…).
[2] GPT-6 Astra. Review of Fable's Weil plan, 13 November 2026
    (FABLE-WEIL-PLAN-REVIEW-01).
[3] Claude Fable 5.2. Addendum 01 to the plan, 13 November 2026
    (SHA-256 abf31923…).
[4] GPT-6 Astra. Release of gate WG6, 14 November 2026 UTC
    (SHA-256 bfaa0fbc…).
[5] Claude Fable 5.2. WG1 implementation audit, 13 November 2026,
    Section 3 (SHA-256 e87e594a…).
[6] David Jaz Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons using (Prop-Ext)
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.WeilVarietiesFromLargeQuotients
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (pe : Prop-Ext)
        (𝓡 : Commutative-Ring)
       where

open import Fin.Type
open import UF.Equiv

open PropositionalTruncation pt
open smooth-line fe pt 𝓡
open import gist.Orbifolds.PresentedAlgebras fe pt 𝓡
open import gist.Orbifolds.PresentedAlgebrasFromLargeQuotients fe pt pe 𝓡
 using (large-presented-algebras)
open Presented-Algebras large-presented-algebras using (R⟨_⟩)

\end{code}

The re-exports, and the names used only in the proofs below, at the
instance. A module that supplies both is applied twice, with disjoint
lists of names, as in gist.RealCohesion.Plateaus.

\begin{code}

open import gist.Orbifolds.Algebras fe pt 𝓡
 using (Algebra ; ⟨_⟩ ; R-as-algebra ; Specᴿ ; _≅ₐ_ ; _∘ₕ_)
 public
open import gist.Orbifolds.PresentedAlgebrasProperties fe pt 𝓡
 large-presented-algebras
 using (Sol ; ev₀)
 public
open import gist.Orbifolds.PresentedAlgebrasProperties fe pt 𝓡
 large-presented-algebras
 using (spectrum-of-presented-algebra)
open import gist.Orbifolds.WeilAlgebras fe pt 𝓡 large-presented-algebras
 using (is-finitely-presented ; kernel-is-finitely-generated ;
        kernel-is-nilpotent ; is-Weil-algebra ; Weil-algebra-of ;
        augmentation-of ; Weil-algebra-of-is-Weil ;
        spectrum-of-Weil-algebra-of ;
        spectrum-of-Weil-algebra-of-is-pointed)
 public
open import gist.Orbifolds.WeilAlgebraPresentations fe pt 𝓡
 large-presented-algebras
 using (Weil-algebras-are-presented)
 public
open import gist.Orbifolds.WeilAlgebraPresentations fe pt 𝓡
 large-presented-algebras
 using (augmented-finitely-presented-algebras-are-centered ;
        spectra-of-Weil-algebras-are-presented)
open import gist.Orbifolds.WeilVarieties fe pt 𝓡 large-presented-algebras
 using (is-Weil-variety-at ; is-presented-variety)
 public
open import gist.Orbifolds.WeilVarieties fe pt 𝓡 large-presented-algebras
 using (Weil-varieties-are-presented ;
        Weil-varieties-are-exactly-the-presented-varieties)

\end{code}

The presented algebras and their spectra, and Lemma 4.1.3.

\begin{code}

presented-algebra : {n m : ℕ} → (Fin m → Poly n) → Algebra 𝓤₁
presented-algebra g = R⟨ g ⟩

remark-4-1-6
 : {n m : ℕ} (g : Fin m → Poly n) → Specᴿ (presented-algebra g) ≃ Sol g
remark-4-1-6 g = spectrum-of-presented-algebra g

lemma-4-1-3
 : {𝓦 : Universe} (𝓐 : Algebra 𝓦) (π : Specᴿ 𝓐)
 → is-finitely-presented 𝓐
 → ∃ n ꞉ ℕ , Σ m ꞉ ℕ , Σ f ꞉ (Fin m → Poly n) ,
   Σ z ꞉ ((j : Fin m) → ⟦ f j ⟧ (λ _ → 0ᴿ) ＝ 0ᴿ) ,
   Σ φ ꞉ presented-algebra f ≅ₐ 𝓐 ,
     _∘ₕ_ {𝓐 = presented-algebra f} {𝓑 = 𝓐} {𝓒 = R-as-algebra}
      π (pr₁ φ) ＝ ev₀ f z
lemma-4-1-3 = augmented-finitely-presented-algebras-are-centered

\end{code}

Weil varieties with the algebra in 𝓤₁, and the two theorems for spectra.

\begin{code}

is-Weil-variety : {𝓣 : Universe} (V : 𝓣 ̇ ) → V → 𝓤₂ ⊔ 𝓣 ̇
is-Weil-variety = is-Weil-variety-at 𝓤₁

spectra-of-presentations-are-spectra-of-Weil-algebras
 : (P : Weil-Presentation)
 → Σ π ꞉ Specᴿ (Weil-algebra-of P) ,
     is-Weil-algebra (Weil-algebra-of P) π
   × (Σ e ꞉ Specᴿ (Weil-algebra-of P) ≃ Spec P , ⌜ e ⌝ π ＝ Spec-point P)
spectra-of-presentations-are-spectra-of-Weil-algebras P =
 augmentation-of P , Weil-algebra-of-is-Weil P ,
 spectrum-of-Weil-algebra-of P , spectrum-of-Weil-algebra-of-is-pointed P

spectra-of-Weil-algebras-are-spectra-of-presentations
 : {𝓦 : Universe} (𝓐 : Algebra 𝓦) (π : Specᴿ 𝓐)
 → is-Weil-algebra 𝓐 π
 → ∃ P ꞉ Weil-Presentation , Σ e ꞉ Specᴿ 𝓐 ≃ Spec P , ⌜ e ⌝ π ＝ Spec-point P
spectra-of-Weil-algebras-are-spectra-of-presentations =
 spectra-of-Weil-algebras-are-presented

\end{code}

The comparison of the predicates.

\begin{code}

Weil-varieties-in-any-universe-are-presented
 : (𝓦 : Universe) {𝓣 : Universe} (V : 𝓣 ̇ ) (v : V)
 → is-Weil-variety-at 𝓦 V v → is-presented-variety V v
Weil-varieties-in-any-universe-are-presented = Weil-varieties-are-presented

Weil-varieties-are-presented-varieties
 : {𝓣 : Universe} (V : 𝓣 ̇ ) (v : V)
 → is-Weil-variety V v ↔ is-presented-variety V v
Weil-varieties-are-presented-varieties =
 Weil-varieties-are-exactly-the-presented-varieties

\end{code}
