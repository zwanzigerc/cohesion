Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), for gate WG6 of Claude Fable
5.2's plan for the comparison of Weil algebras with presentations [1],
as reviewed by GPT-6 Astra [2], amended by Fable's addendum 01 [3] and
released by Astra [4]. The exported names, and the universes and
hypotheses of their statements, are those of the plan's statement
companion; the proofs are Claude Opus 5.5's. See the AI disclosure in
gist.RealCohesion.index.

Weil varieties and presented varieties
--------------------------------------

The module is parametrized by an instance pa of the interface of
presented algebras, with carriers in an arbitrary universe 𝓠, as
gist.Orbifolds.WeilAlgebras is. The universe 𝓦 of the algebras and the
universe 𝓣 of the pointed types are arbitrary and independent of 𝓠.

The two predicates of a pointed type (V , v):

  is-Weil-variety-at 𝓦 V v (Myers's Definition 4.2.1 [5], with the Weil
  algebra in 𝓦): merely an algebra 𝓐 in 𝓦, a point π of its spectrum, a
  proof that (𝓐 , π) is a Weil algebra, and an equivalence V ≃ Specᴿ 𝓐
  that takes v to π. Its level is 𝓠 ⊔ 𝓦 ⁺ ⊔ 𝓣: the quantifier over
  Algebra 𝓦 gives 𝓦 ⁺, is-Weil-algebra gives 𝓠 ⊔ 𝓦, and the equivalence
  gives 𝓣 ⊔ 𝓦.

  is-presented-variety V v: merely a Weil presentation W and an
  equivalence V ≃ Spec W that takes v to Spec-point W. Its level is 𝓣,
  since presentations and their spectra are in 𝓤₀. It is the defining
  expression of MyersMicrolinearity.is-infinitesimal-variety', restated
  here in the ordinary core; that the two are the same type by
  unfolding belongs to the crisp integration, a later gate, and
  MyersMicrolinearity is not imported.

Both are mere essential-image predicates: one outer propositional
truncation holds the algebra or presentation, the augmentation, the
equivalence and the pointing proof together. Nothing is resized.

The comparison:

  Weil-varieties-are-presented 𝓦 : a Weil variety with its algebra in
  any universe 𝓦 is a presented variety. The Weil witness and the mere
  presentation of gist.Orbifolds.WeilAlgebraPresentations are eliminated
  into the proposition; V ≃ Specᴿ 𝓐 is followed by Specᴿ 𝓐 ≃ Spec P, and
  the point path is the second equivalence applied to the first point
  path, followed by the second point path.

  presented-varieties-are-Weil : a presented variety is a Weil variety
  with its algebra in 𝓠. From V ≃ Spec P: the Weil algebra of P of
  gist.Orbifolds.WeilAlgebras, in 𝓠, with its augmentation and its Weil
  proof, and V ≃ Spec P followed by the inverse of
  spectrum-of-Weil-algebra-of P. That inverse takes Spec-point P to the
  augmentation, by the pointedness of the equivalence and its inverse
  law (inverse-spectrum-of-Weil-algebra-of-is-pointed, a helper). The
  witness is introduced under the truncation. The algebra is in 𝓠, not
  in an arbitrary universe.

  Weil-varieties-are-exactly-the-presented-varieties : the two
  implications, with 𝓦 = 𝓠, as a logical equivalence of the two
  propositions.

These are equivalences of the types together with their marked points.

Assumptions: function extensionality and propositional truncations, as
in SmoothLine, and the instance pa, an ordinary parameter. No
propositional extensionality, quotient, choice, univalence, resizing,
nontriviality, excluded middle, crisp or cohesive datum is assumed, and
the module adds no option and no postulate.

[1] Claude Fable 5.2. Plan: formalizing the comparison of Weil algebras
    with presentations, 13 November 2026, Sections 7.1 and 7.2, with
    its statement companion, Section WG6 (plan SHA-256 b1662ecc…;
    companion SHA-256 47974af8…).
[2] GPT-6 Astra. Review of Fable's Weil plan, 13 November 2026
    (FABLE-WEIL-PLAN-REVIEW-01).
[3] Claude Fable 5.2. Addendum 01 to the plan, 13 November 2026
    (SHA-256 abf31923…).
[4] GPT-6 Astra. Release of gate WG6, 14 November 2026 UTC
    (SHA-256 bfaa0fbc…).
[5] David Jaz Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)
import gist.Orbifolds.PresentedAlgebras

module gist.Orbifolds.WeilVarieties
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (𝓡 : Commutative-Ring)
        {𝓠 : Universe}
        (pa : gist.Orbifolds.PresentedAlgebras.Presented-Algebras fe pt 𝓡 𝓠)
       where

open import UF.Equiv

open PropositionalTruncation pt
open smooth-line fe pt 𝓡
open import gist.Orbifolds.Algebras fe pt 𝓡
open import gist.Orbifolds.WeilAlgebras fe pt 𝓡 pa
open import gist.Orbifolds.WeilAlgebraPresentations fe pt 𝓡 pa

\end{code}

The two predicates.

\begin{code}

is-Weil-variety-at
 : (𝓦 : Universe) {𝓣 : Universe} (V : 𝓣 ̇ ) → V → 𝓠 ⊔ 𝓦 ⁺ ⊔ 𝓣 ̇
is-Weil-variety-at 𝓦 V v =
 ∃ 𝓐 ꞉ Algebra 𝓦 , Σ π ꞉ Specᴿ 𝓐 ,
   is-Weil-algebra 𝓐 π × (Σ e ꞉ V ≃ Specᴿ 𝓐 , ⌜ e ⌝ v ＝ π)

is-presented-variety : {𝓣 : Universe} (V : 𝓣 ̇ ) → V → 𝓣 ̇
is-presented-variety V v =
 ∃ W ꞉ Weil-Presentation , Σ e ꞉ V ≃ Spec W , ⌜ e ⌝ v ＝ Spec-point W

\end{code}

The comparison.

\begin{code}

Weil-varieties-are-presented
 : (𝓦 : Universe) {𝓣 : Universe} (V : 𝓣 ̇ ) (v : V)
 → is-Weil-variety-at 𝓦 V v → is-presented-variety V v
Weil-varieties-are-presented 𝓦 V v =
 ∥∥-rec ∥∥-is-prop
  (λ (𝓐 , π , w , e , p) →
    ∥∥-functor (λ (P , e' , p') → P , (e ● e') , (ap ⌜ e' ⌝ p ∙ p'))
     (spectra-of-Weil-algebras-are-presented 𝓐 π w))

inverse-spectrum-of-Weil-algebra-of-is-pointed
 : (P : Weil-Presentation)
 → ⌜ ≃-sym (spectrum-of-Weil-algebra-of P) ⌝ (Spec-point P)
 ＝ augmentation-of P
inverse-spectrum-of-Weil-algebra-of-is-pointed P =
 ap ⌜ ≃-sym (spectrum-of-Weil-algebra-of P) ⌝
    ((spectrum-of-Weil-algebra-of-is-pointed P)⁻¹)
 ∙ ≃-sym-is-linv (spectrum-of-Weil-algebra-of P) (augmentation-of P)

presented-varieties-are-Weil
 : {𝓣 : Universe} (V : 𝓣 ̇ ) (v : V)
 → is-presented-variety V v → is-Weil-variety-at 𝓠 V v
presented-varieties-are-Weil V v =
 ∥∥-functor
  (λ (P , e , p) →
    Weil-algebra-of P , augmentation-of P , Weil-algebra-of-is-Weil P ,
    (e ● ≃-sym (spectrum-of-Weil-algebra-of P)) ,
    (ap ⌜ ≃-sym (spectrum-of-Weil-algebra-of P) ⌝ p
     ∙ inverse-spectrum-of-Weil-algebra-of-is-pointed P))

Weil-varieties-are-exactly-the-presented-varieties
 : {𝓣 : Universe} (V : 𝓣 ̇ ) (v : V)
 → is-Weil-variety-at 𝓠 V v ↔ is-presented-variety V v
Weil-varieties-are-exactly-the-presented-varieties V v =
 Weil-varieties-are-presented 𝓠 V v , presented-varieties-are-Weil V v

\end{code}
