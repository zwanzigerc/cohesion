Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), for gate WG5 of Claude Fable
5.2's plan for the comparison of Weil algebras with presentations [1],
as reviewed by GPT-6 Astra [2], amended by Fable's addendum 01 [3] and
released by Astra [4]. The exported names, and the universes and
hypotheses of their statements, are those of the plan's statement
companion, with the explicit compositions of Fable's WG1 audit [5]; the
proofs are Claude Opus 5.5's. See the AI disclosure in
gist.RealCohesion.index.

Presentations of Weil algebras
------------------------------

The module is parametrized by an instance pa of the interface of
presented algebras, with carriers in an arbitrary universe 𝓠, as
gist.Orbifolds.WeilAlgebras is. Each algebra 𝓐 below has its carrier in
an arbitrary universe 𝓦, independent of 𝓠, and a point π of its
spectrum, its augmentation.

  presentation-with-powers f z k : for a family f of equations that
  vanish at the origin, with the proof z, and for every k, the Weil
  presentation with the variables of f, the equations adjoin-powers f k
  (those of f, then the powers x_i^(k+1)), the exponent k + 1, and the
  coefficients 0 on the equations of f and δ on the powers. Its
  certificate is the witness of gist.Orbifolds.SmoothLine.normalize,
  written again with f for the equations and k for the exponent, since
  that witness is local to normalize, which is not changed. Its spectrum
  is Sol (adjoin-powers f k), by unfolding.

  augmented-finitely-presented-algebras-are-centered (Myers's Lemma
  4.1.3 [6], in the plan's displayed form): if 𝓐 is merely finitely
  presented, then merely R⟨ f ⟩ ≅ₐ 𝓐 for a family f that vanishes at the
  origin, by an isomorphism under which π is evaluation at the origin,
  ev₀. A given presentation is centered by the centering of
  gist.Orbifolds.PresentedAlgebrasProperties (augmentation-values,
  centered-relations, centering-isomorphism and its augmentation law);
  the mere existence of the presentation is eliminated into the
  proposition, and no presentation is chosen.

  algebras-with-nilpotent-kernel-are-presented : if 𝓐 is merely finitely
  presented and the kernel of π is merely nilpotent, then merely
  R⟨ poly P ⟩ ≅ₐ 𝓐 for a Weil presentation P, by an isomorphism under
  which π is ev₀. Both mere existences are eliminated into the
  proposition. From a centered presentation e : R⟨ f ⟩ ≅ₐ 𝓐 and the
  single product bound N of the kernel: the image e(x_i) of each
  generator is in the kernel, so the product of the constant family of
  length N at e(x_i) is 0; that product is e(x_i)^N
  (product-of-a-constant-family), hence e(x_i)^(N+1) = 0; and the
  inverse of e, which preserves powers and 0, gives x_i^(N+1) = 0 in
  R⟨ f ⟩. So all generators satisfy power equations with the one
  exponent N + 1; no exponent is chosen for each generator, and no
  finite choice is used. N = 0 is allowed: the empty product 1 is then
  0, and the exponent is 1. P is presentation-with-powers f z N, and the
  isomorphism is adjoining-vanishing-powers of
  gist.Orbifolds.PresentedAlgebrasProperties, R⟨ adjoin-powers f N ⟩ ≅ₐ
  R⟨ f ⟩, followed by e. The augmentation law holds because both
  homomorphisms send every generator to 0
  (homs-from-presented-are-determined-by-generators). Finite generation
  of the kernel is not assumed.

  Weil-algebras-are-presented (Theorem B, for algebras): the above, for
  the finite presentation and the nilpotence of a Weil algebra.

  spectra-of-Weil-algebras-are-presented (Theorem B, for spectra): the
  spectrum of a Weil algebra is merely equivalent to Spec P for a Weil
  presentation P, as a pointed type. The equivalence is that of the
  spectra of isomorphic algebras, which is contravariant, followed by
  the spectrum equivalence of gist.Orbifolds.PresentedAlgebrasProperties;
  it sends π to π after the isomorphism, which is ev₀, which goes to
  Spec-point P.

  spectra-of-Weil-algebras-are-merely-small : the spectrum of a Weil
  algebra is merely 𝓤₀-small in the sense of UF.Size, by Spec P, which is
  in 𝓤₀, and the inverse of that equivalence. The truncation stays; no
  resizing is used and no small representative is chosen.

The helpers for a given centered presentation and bound, and for a given
presentation with its augmentation law, are exported as well. This is
the reverse direction of the comparison; the equivalence of the
predicates and the crisp bridges are later gates.

Assumptions: function extensionality and propositional truncations, as
in SmoothLine, and the instance pa, an ordinary parameter. No
propositional extensionality, quotient, choice, univalence, resizing,
nontriviality, excluded middle or crisp datum is assumed, and the module
adds no option and no postulate.

[1] Claude Fable 5.2. Plan: formalizing the comparison of Weil algebras
    with presentations, 13 November 2026, Section 6, with its statement
    companion, Section WG5 (plan SHA-256 b1662ecc…; companion SHA-256
    47974af8…).
[2] GPT-6 Astra. Review of Fable's Weil plan, 13 November 2026
    (FABLE-WEIL-PLAN-REVIEW-01).
[3] Claude Fable 5.2. Addendum 01 to the plan, 13 November 2026
    (SHA-256 abf31923…).
[4] GPT-6 Astra. Release of gate WG5, 14 November 2026 UTC
    (SHA-256 eb882708…).
[5] Claude Fable 5.2. WG1 implementation audit, 13 November 2026,
    Section 3 (SHA-256 e87e594a…).
[6] David Jaz Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)
import gist.Orbifolds.PresentedAlgebras

module gist.Orbifolds.WeilAlgebraPresentations
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (𝓡 : Commutative-Ring)
        {𝓠 : Universe}
        (pa : gist.Orbifolds.PresentedAlgebras.Presented-Algebras fe pt 𝓡 𝓠)
       where

open import Fin.Type
open import Naturals.Addition using () renaming (_+_ to _+ᴺ_)
open import UF.Equiv
open import UF.Size using (_is_small)

open PropositionalTruncation pt
open smooth-line fe pt 𝓡
open import gist.Orbifolds.Algebras fe pt 𝓡
open gist.Orbifolds.PresentedAlgebras fe pt 𝓡
open Presented-Algebras pa
open import gist.Orbifolds.PresentedAlgebrasProperties fe pt 𝓡 pa
open import gist.Orbifolds.NilpotentIdeals fe pt 𝓡
open import gist.Orbifolds.WeilAlgebras fe pt 𝓡 pa

\end{code}

The Weil presentation of a family with adjoined powers. The certificate
is the witness of SmoothLine.normalize, with f for the equations and k
for the exponent.

\begin{code}

presentation-with-powers
 : {n m : ℕ} (f : Fin m → Poly n)
 → ((j : Fin m) → ⟦ f j ⟧ (λ _ → 0ᴿ) ＝ 0ᴿ)
 → ℕ → Weil-Presentation
presentation-with-powers {n} {m} f z k = record
 { vars = n
 ; eqns = m +ᴺ n
 ; poly = adjoin-powers f k
 ; poly-at-zero = join-induction (λ p → ⟦ p ⟧ (λ _ → 0ᴿ) ＝ 0ᴿ) f
                   (λ i → power (var i) (succ k)) z
                   (λ i → ·-zero (⟦ power (var i) k ⟧ (λ _ → 0ᴿ)))
 ; exponent = succ k
 ; coefficient = λ i → join (λ _ → con 0ᴿ) (λ i' → con (δ i i'))
 ; nilpotency = witness
 }
 where
  powers : Fin n → Poly n
  powers i = power (var i) (succ k)

  witness : (i : Fin n) (a : Fin n → R)
          → a i ^ᴿ succ k
          ＝ ∑ (λ j → ⟦ join (λ _ → con 0ᴿ) (λ i' → con (δ i i')) j ⟧ a
                     ·ᴿ ⟦ join f powers j ⟧ a)
  witness i a =
   a i ^ᴿ succ k
    ＝⟨ (value-of-power (var i) (succ k) a)⁻¹ ⟩
   ⟦ powers i ⟧ a
    ＝⟨ (Kronecker-sum i (λ i' → ⟦ powers i' ⟧ a))⁻¹ ⟩
   ∑ (λ i' → δ i i' ·ᴿ ⟦ powers i' ⟧ a)
    ＝⟨ (+-unit-left _)⁻¹ ⟩
   0ᴿ +ᴿ ∑ (λ i' → δ i i' ·ᴿ ⟦ powers i' ⟧ a)
    ＝⟨ ap (_+ᴿ ∑ (λ i' → δ i i' ·ᴿ ⟦ powers i' ⟧ a)) (zeros ⁻¹) ⟩
   ∑ (λ j → 0ᴿ ·ᴿ ⟦ f j ⟧ a) +ᴿ ∑ (λ i' → δ i i' ·ᴿ ⟦ powers i' ⟧ a)
    ＝⟨ (∑-of-join (λ j → 0ᴿ ·ᴿ ⟦ f j ⟧ a)
                   (λ i' → δ i i' ·ᴿ ⟦ powers i' ⟧ a))⁻¹ ⟩
   ∑ (join (λ j → 0ᴿ ·ᴿ ⟦ f j ⟧ a) (λ i' → δ i i' ·ᴿ ⟦ powers i' ⟧ a))
    ＝⟨ ap ∑ (dfunext fe (join-pointwise h (λ _ → con 0ᴿ) f
                          (λ i' → con (δ i i')) powers))⁻¹ ⟩
   ∑ (λ j → ⟦ join (λ _ → con 0ᴿ) (λ i' → con (δ i i')) j ⟧ a
            ·ᴿ ⟦ join f powers j ⟧ a)                  ∎
   where
    h : Poly n → Poly n → R
    h p q = ⟦ p ⟧ a ·ᴿ ⟦ q ⟧ a

    zeros : ∑ (λ j → 0ᴿ ·ᴿ ⟦ f j ⟧ a) ＝ 0ᴿ
    zeros = ∑-of-zeros _ (λ j → ·-zero-left (⟦ f j ⟧ a))

\end{code}

Myers's Lemma 4.1.3, in the displayed form: every augmented finitely
presented algebra is merely presented by a family that vanishes at the
origin, with the augmentation at the origin.

\begin{code}

augmented-finitely-presented-algebras-are-centered
 : {𝓦 : Universe} (𝓐 : Algebra 𝓦) (π : Specᴿ 𝓐)
 → is-finitely-presented 𝓐
 → ∃ n ꞉ ℕ , Σ m ꞉ ℕ , Σ f ꞉ (Fin m → Poly n) ,
   Σ z ꞉ ((j : Fin m) → ⟦ f j ⟧ (λ _ → 0ᴿ) ＝ 0ᴿ) ,
   Σ φ ꞉ R⟨ f ⟩ ≅ₐ 𝓐 ,
     _∘ₕ_ {𝓐 = R⟨ f ⟩} {𝓑 = 𝓐} {𝓒 = R-as-algebra}
      π (pr₁ φ) ＝ ev₀ f z
augmented-finitely-presented-algebras-are-centered 𝓐 π =
 ∥∥-functor (λ (n , m , g , φ) → n , m , centered-relations 𝓐 π g φ ,
                                 centered-relations-vanish-at-zero 𝓐 π g φ ,
                                 centering-isomorphism 𝓐 π g φ ,
                                 centering-commutes-with-augmentations
                                  𝓐 π g φ)

\end{code}

For a given centered presentation e and a given product bound N of the
kernel: the generators have vanishing (N+1)-st powers, and adjoining
these powers gives the presentation, with its augmentation law.

\begin{code}

module _ {𝓦 : Universe} (𝓐 : Algebra 𝓦) (π : Specᴿ 𝓐)
         {n m : ℕ} (f : Fin m → Poly n)
         (z : (j : Fin m) → ⟦ f j ⟧ (λ _ → 0ᴿ) ＝ 0ᴿ)
         (e : R⟨ f ⟩ ≅ₐ 𝓐)
         (c : _∘ₕ_ {𝓐 = R⟨ f ⟩} {𝓑 = 𝓐} {𝓒 = R-as-algebra} π (pr₁ e)
            ＝ ev₀ f z)
       where

 images-of-the-generators-are-in-the-kernel
  : (i : Fin n) → pr₁ π (pr₁ (pr₁ e) (gen f i)) ＝ 0ᴿ
 images-of-the-generators-are-in-the-kernel i =
  ap (λ h → pr₁ h (gen f i)) c ∙ ev₀-on-generators f z i

 module _ (N : ℕ)
          (ν : (w : Fin N → ⟨ 𝓐 ⟩)
             → ((l : Fin N) → pr₁ π (w l) ＝ 0ᴿ)
             → ∏ᴬ 𝓐 w ＝ Algebra.0ᴬ 𝓐)
        where

  images-of-the-generators-have-vanishing-powers
   : (i : Fin n)
   → _^ᴬ_ 𝓐 (pr₁ (pr₁ e) (gen f i)) (succ N) ＝ Algebra.0ᴬ 𝓐
  images-of-the-generators-have-vanishing-powers i =
   ap (λ - → Algebra._·ᴬ_ 𝓐 - (pr₁ (pr₁ e) (gen f i)))
      ((product-of-a-constant-family 𝓐 (pr₁ (pr₁ e) (gen f i)) N)⁻¹
       ∙ ν (λ _ → pr₁ (pr₁ e) (gen f i))
           (λ _ → images-of-the-generators-are-in-the-kernel i))
   ∙ ·ᴬ-zero-left 𝓐 (pr₁ (pr₁ e) (gen f i))

  generators-have-vanishing-powers
   : (i : Fin n)
   → _^ᴬ_ R⟨ f ⟩ (gen f i) (succ N) ＝ Algebra.0ᴬ R⟨ f ⟩
  generators-have-vanishing-powers i =
   ap (λ - → _^ᴬ_ R⟨ f ⟩ - (succ N)) ((pr₁ (pr₂ (pr₂ e)) (gen f i))⁻¹)
   ∙ (homs-preserve-powers 𝓐 R⟨ f ⟩ (pr₁ (pr₂ e))
       (pr₁ (pr₁ e) (gen f i)) (succ N))⁻¹
   ∙ ap (pr₁ (pr₁ (pr₂ e)))
        (images-of-the-generators-have-vanishing-powers i)
   ∙ homs-preserve-0 𝓐 R⟨ f ⟩ (pr₁ (pr₂ e))

  isomorphism-with-powers : R⟨ adjoin-powers f N ⟩ ≅ₐ 𝓐
  isomorphism-with-powers =
   ≅ₐ-trans {𝓐 = R⟨ adjoin-powers f N ⟩} {𝓑 = R⟨ f ⟩} {𝓒 = 𝓐}
    (adjoining-vanishing-powers f N generators-have-vanishing-powers) e

  isomorphism-with-powers-commutes-with-augmentations
   : _∘ₕ_ {𝓐 = R⟨ adjoin-powers f N ⟩} {𝓑 = 𝓐} {𝓒 = R-as-algebra}
      π (pr₁ isomorphism-with-powers)
   ＝ ev₀ (adjoin-powers f N)
          (Weil-Presentation.poly-at-zero (presentation-with-powers f z N))
  isomorphism-with-powers-commutes-with-augmentations =
   homs-from-presented-are-determined-by-generators pa (adjoin-powers f N)
    R-as-algebra _ _
    (λ i → ap (pr₁ π ∘ pr₁ (pr₁ e))
              (adjoining-vanishing-powers-on-generators f N
                generators-have-vanishing-powers i)
         ∙ images-of-the-generators-are-in-the-kernel i
         ∙ (ev₀-on-generators (adjoin-powers f N)
             (Weil-Presentation.poly-at-zero (presentation-with-powers f z N))
             i)⁻¹)

\end{code}

Algebras with a nilpotent kernel, and Theorem B for algebras.

\begin{code}

algebras-with-nilpotent-kernel-are-presented
 : {𝓦 : Universe} (𝓐 : Algebra 𝓦) (π : Specᴿ 𝓐)
 → is-finitely-presented 𝓐
 → kernel-is-nilpotent 𝓐 π
 → ∃ P ꞉ Weil-Presentation ,
   Σ φ ꞉ R⟨ Weil-Presentation.poly P ⟩ ≅ₐ 𝓐 ,
     _∘ₕ_ {𝓐 = R⟨ Weil-Presentation.poly P ⟩} {𝓑 = 𝓐} {𝓒 = R-as-algebra}
      π (pr₁ φ)
     ＝ ev₀ (Weil-Presentation.poly P) (Weil-Presentation.poly-at-zero P)
algebras-with-nilpotent-kernel-are-presented 𝓐 π p ν =
 ∥∥-rec ∥∥-is-prop
  (λ (n , m , f , z , e , c) →
    ∥∥-functor
     (λ (N , ν') →
       presentation-with-powers f z N ,
       isomorphism-with-powers 𝓐 π f z e c N ν' ,
       isomorphism-with-powers-commutes-with-augmentations 𝓐 π f z e c N ν')
     ν)
  (augmented-finitely-presented-algebras-are-centered 𝓐 π p)

Weil-algebras-are-presented
 : {𝓦 : Universe} (𝓐 : Algebra 𝓦) (π : Specᴿ 𝓐)
 → is-Weil-algebra 𝓐 π
 → ∃ P ꞉ Weil-Presentation ,
   Σ φ ꞉ R⟨ Weil-Presentation.poly P ⟩ ≅ₐ 𝓐 ,
     _∘ₕ_ {𝓐 = R⟨ Weil-Presentation.poly P ⟩} {𝓑 = 𝓐} {𝓒 = R-as-algebra}
      π (pr₁ φ)
     ＝ ev₀ (Weil-Presentation.poly P) (Weil-Presentation.poly-at-zero P)
Weil-algebras-are-presented 𝓐 π (p , _ , ν) =
 algebras-with-nilpotent-kernel-are-presented 𝓐 π p ν

\end{code}

Spectra. For a given presentation with its augmentation law, the
spectrum of the algebra is Spec P, as a pointed type; hence Theorem B
for spectra, and mere smallness.

\begin{code}

module _ {𝓦 : Universe} (𝓐 : Algebra 𝓦) (π : Specᴿ 𝓐)
         (P : Weil-Presentation)
         (φ : R⟨ Weil-Presentation.poly P ⟩ ≅ₐ 𝓐)
         (c : _∘ₕ_ {𝓐 = R⟨ Weil-Presentation.poly P ⟩} {𝓑 = 𝓐}
               {𝓒 = R-as-algebra} π (pr₁ φ)
            ＝ ev₀ (Weil-Presentation.poly P)
                   (Weil-Presentation.poly-at-zero P))
       where

 spectrum-via-presentation : Specᴿ 𝓐 ≃ Spec P
 spectrum-via-presentation =
  spectra-of-isomorphic-algebras R⟨ Weil-Presentation.poly P ⟩ 𝓐 φ
  ● spectrum-of-presented-algebra (Weil-Presentation.poly P)

 spectrum-via-presentation-is-pointed
  : ⌜ spectrum-via-presentation ⌝ π ＝ Spec-point P
 spectrum-via-presentation-is-pointed =
  ap ⌜ spectrum-of-presented-algebra (Weil-Presentation.poly P) ⌝ c
  ∙ spectrum-of-presented-algebra-is-pointed (Weil-Presentation.poly P)
     (Weil-Presentation.poly-at-zero P)

spectra-of-Weil-algebras-are-presented
 : {𝓦 : Universe} (𝓐 : Algebra 𝓦) (π : Specᴿ 𝓐)
 → is-Weil-algebra 𝓐 π
 → ∃ P ꞉ Weil-Presentation , Σ e ꞉ Specᴿ 𝓐 ≃ Spec P , ⌜ e ⌝ π ＝ Spec-point P
spectra-of-Weil-algebras-are-presented 𝓐 π w =
 ∥∥-functor (λ (P , φ , c) → P , spectrum-via-presentation 𝓐 π P φ c ,
                             spectrum-via-presentation-is-pointed 𝓐 π P φ c)
  (Weil-algebras-are-presented 𝓐 π w)

spectra-of-Weil-algebras-are-merely-small
 : {𝓦 : Universe} (𝓐 : Algebra 𝓦) (π : Specᴿ 𝓐)
 → is-Weil-algebra 𝓐 π → ∥ (Specᴿ 𝓐) is 𝓤₀ small ∥
spectra-of-Weil-algebras-are-merely-small 𝓐 π w =
 ∥∥-functor (λ (P , e , _) → Spec P , ≃-sym e)
  (spectra-of-Weil-algebras-are-presented 𝓐 π w)

\end{code}
