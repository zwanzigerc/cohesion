Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), for gate WG4 of Claude Fable
5.2's plan for the comparison of Weil algebras with presentations [1],
as reviewed by GPT-6 Astra [2], amended by Fable's addendum 01 [3] and
released by Astra [4]. The exported names, and the universes and
hypotheses of their statements, are those of the plan's statement
companion; the proofs are Claude Opus 5.5's. See the AI disclosure in
gist.RealCohesion.index.

Weil algebras, and the Weil algebra of a presentation
-----------------------------------------------------

The module is parametrized by an instance pa of the interface of
presented algebras, with carriers in an arbitrary universe 𝓠, as
gist.Orbifolds.PresentedAlgebrasProperties is.

Myers's Definition 4.1.1 [5], read as in the plan [1, Section 5.2]. For
an algebra 𝓐 with carrier in any universe 𝓦 and a point π of its
spectrum, the augmentation:

  kernel-is-finitely-generated : merely finitely many elements of the
  kernel of π, of which every element of the kernel is a combination;

  kernel-is-nilpotent : merely a bound N such that every product of N
  elements of the kernel is 0, the product criterion. It is equivalent
  to the vanishing of the N-th power of the ideal, which such products
  generate, and avoids defining powers of ideals. N = 0 is allowed by
  the definition; the bounds constructed here are positive.

  is-finitely-presented 𝓐 : 𝓐 is merely isomorphic to an algebra R⟨ g ⟩
  of the instance, by an isomorphism that may cross universes.

  is-Weil-algebra 𝓐 π : the three together, a proposition
  (being-Weil-algebra-is-prop), in 𝓠 ⊔ 𝓦; Weil-Algebra 𝓦 : the type of
  algebras in 𝓦 with an augmentation that makes them Weil, in 𝓠 ⊔ 𝓦 ⁺.

Presented algebras whose equations vanish at the origin.

  kernel-of-ev₀-is-generated-by-the-generators : an element of R⟨ g ⟩
  killed by ev₀ is in the ideal of the generators. By (P3) it is merely
  the value of an expression p at the generators; by
  constant-term-decomposition that value is ι of p at the origin plus a
  combination of the generators; and p at the origin is the image of
  the element under ev₀, by values-under-homs, so 0.

  power-adjoined-algebras-are-Weil, products-in-the-kernel-of-ev₀-vanish
  : for every family f, every k, and a proof z that the equations of
  adjoin-powers f k vanish at the origin, the algebra of adjoin-powers
  f k, augmented by ev₀, is a Weil algebra: it is finitely presented by
  itself, the generators generate the kernel, and every product of
  k * n + 1 elements of the kernel vanishes, because the (k + 1)-st
  powers of the generators vanish by (P1) at the right indices of the
  power equations (adjoined-powers-vanish-at-the-generators) and
  products-in-ideals-of-nilpotents-vanish applies. No Weil certificate
  for f is used.

Theorem A, the second endpoint of the comparison. For a Weil
presentation P, its algebra is that of its normalization, never that of
P itself, which can fail to be a Weil algebra (the example over the
two-element field in the header of gist.Orbifolds.SmoothLine):

  Weil-algebra-of P = R⟨ poly (normalize P) ⟩, augmented by
  augmentation-of P = ev₀; Weil-algebra-of-is-Weil, with the product
  bound succ (exponent P * vars P) (products-in-the-augmentation-ideal-
  vanish); spectrum-of-Weil-algebra-of : its spectrum is equivalent to
  Spec P, as the composite of the spectrum equivalence of
  PresentedAlgebrasProperties and SmoothLine's normalization-equivalence,
  pointed (spectrum-of-Weil-algebra-of-is-pointed) and given on a point
  by its values at the generators (spectrum-of-Weil-algebra-of-is-over-Rⁿ).
  The certificate of P enters only through normalization-equivalence.

This is not the reverse direction of the comparison, which is a later
gate.

Assumptions: function extensionality and propositional truncations, as
in SmoothLine, and the instance pa, an ordinary parameter. No
propositional extensionality, quotient, choice, univalence, resizing,
nontriviality, excluded middle or crisp datum is assumed, and the module
adds no option and no postulate.

[1] Claude Fable 5.2. Plan: formalizing the comparison of Weil algebras
    with presentations, 13 November 2026, Section 5.2, with its statement
    companion, Section WG4 (plan SHA-256 b1662ecc…; companion SHA-256
    47974af8…).
[2] GPT-6 Astra. Review of Fable's Weil plan, 13 November 2026
    (FABLE-WEIL-PLAN-REVIEW-01).
[3] Claude Fable 5.2. Addendum 01 to the plan, 13 November 2026
    (SHA-256 abf31923…).
[4] GPT-6 Astra. Release of gate WG4, 13 November 2026
    (SHA-256 0499a901…).
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

module gist.Orbifolds.WeilAlgebras
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (𝓡 : Commutative-Ring)
        {𝓠 : Universe}
        (pa : gist.Orbifolds.PresentedAlgebras.Presented-Algebras fe pt 𝓡 𝓠)
       where

open import Fin.Type
open import Naturals.Addition using () renaming (_+_ to _+ᴺ_)
open import Naturals.Multiplication using (_*_)
open import UF.Base
open import UF.Equiv
open import UF.Subsingletons

open PropositionalTruncation pt
open smooth-line fe pt 𝓡
open import gist.Orbifolds.Algebras fe pt 𝓡
open gist.Orbifolds.PresentedAlgebras fe pt 𝓡
open Presented-Algebras pa
open import gist.Orbifolds.PresentedAlgebrasProperties fe pt 𝓡 pa
open import gist.Orbifolds.NilpotentIdeals fe pt 𝓡

\end{code}

Weil algebras.

\begin{code}

module _ {𝓦 : Universe} (𝓐 : Algebra 𝓦) (π : Specᴿ 𝓐) where

 kernel-is-finitely-generated : 𝓦 ̇
 kernel-is-finitely-generated =
  ∃ k ꞉ ℕ , Σ z ꞉ (Fin k → ⟨ 𝓐 ⟩) ,
    ((i : Fin k) → pr₁ π (z i) ＝ 0ᴿ)
  × ((w : ⟨ 𝓐 ⟩) → pr₁ π w ＝ 0ᴿ → is-in-the-ideal-of 𝓐 z w)

 kernel-is-nilpotent : 𝓦 ̇
 kernel-is-nilpotent =
  ∃ N ꞉ ℕ , ((w : Fin N → ⟨ 𝓐 ⟩)
            → ((l : Fin N) → pr₁ π (w l) ＝ 0ᴿ)
            → ∏ᴬ 𝓐 w ＝ Algebra.0ᴬ 𝓐)

is-finitely-presented : {𝓦 : Universe} → Algebra 𝓦 → 𝓠 ⊔ 𝓦 ̇
is-finitely-presented 𝓐 =
 ∃ n ꞉ ℕ , Σ m ꞉ ℕ , Σ g ꞉ (Fin m → Poly n) , R⟨ g ⟩ ≅ₐ 𝓐

is-Weil-algebra : {𝓦 : Universe} (𝓐 : Algebra 𝓦) → Specᴿ 𝓐 → 𝓠 ⊔ 𝓦 ̇
is-Weil-algebra 𝓐 π = is-finitely-presented 𝓐
                    × kernel-is-finitely-generated 𝓐 π
                    × kernel-is-nilpotent 𝓐 π

being-Weil-algebra-is-prop
 : {𝓦 : Universe} (𝓐 : Algebra 𝓦) (π : Specᴿ 𝓐) → is-prop (is-Weil-algebra 𝓐 π)
being-Weil-algebra-is-prop 𝓐 π =
 ×-is-prop ∥∥-is-prop (×-is-prop ∥∥-is-prop ∥∥-is-prop)

Weil-Algebra : (𝓦 : Universe) → 𝓠 ⊔ 𝓦 ⁺ ̇
Weil-Algebra 𝓦 = Σ 𝓐 ꞉ Algebra 𝓦 , Σ π ꞉ Specᴿ 𝓐 , is-Weil-algebra 𝓐 π

\end{code}

Presented algebras whose equations vanish at the origin.

\begin{code}

kernel-of-ev₀-is-generated-by-the-generators
 : {n m : ℕ} (g : Fin m → Poly n) (z : (j : Fin m) → ⟦ g j ⟧ (λ _ → 0ᴿ) ＝ 0ᴿ)
   (w : ⟨ R⟨ g ⟩ ⟩)
 → pr₁ (ev₀ g z) w ＝ 0ᴿ → is-in-the-ideal-of R⟨ g ⟩ (gen g) w
kernel-of-ev₀-is-generated-by-the-generators {n} {m} g z w o =
 ∥∥-functor γ (generation g w)
 where
  𝓖 : Algebra 𝓠
  𝓖 = R⟨ g ⟩

  module G = Algebra 𝓖

  γ : (Σ p ꞉ Poly n , ⟦ p ⟧[ 𝓖 ] (gen g) ＝ w)
    → Σ c ꞉ (Fin n → ⟨ 𝓖 ⟩) , w ＝ ∑ᴬ 𝓖 (λ i → gen g i G.·ᴬ c i)
  γ (p , e) = c , w-is-a-combination
   where
    c : Fin n → ⟨ 𝓖 ⟩
    c = pr₁ (constant-term-decomposition 𝓖 (gen g) p)

    S : ⟨ 𝓖 ⟩
    S = ∑ᴬ 𝓖 (λ i → gen g i G.·ᴬ c i)

    p-vanishes-at-zero : ⟦ p ⟧ (λ _ → 0ᴿ) ＝ 0ᴿ
    p-vanishes-at-zero =
     (values-in-R p (λ _ → 0ᴿ))⁻¹
     ∙ values-at-equal-points R-as-algebra p (λ _ → 0ᴿ) (pr₁ (ev₀ g z) ∘ gen g)
        (λ i → (ev₀-on-generators g z i)⁻¹)
     ∙ (values-under-homs 𝓖 R-as-algebra (ev₀ g z) p (gen g))⁻¹
     ∙ ap (pr₁ (ev₀ g z)) e
     ∙ o

    w-is-a-combination : w ＝ S
    w-is-a-combination =
     e ⁻¹
     ∙ pr₂ (constant-term-decomposition 𝓖 (gen g) p)
     ∙ ap (λ r → G.ι r G.+ᴬ S) p-vanishes-at-zero
     ∙ ap (G._+ᴬ S) (ι-preserves-0 𝓖)
     ∙ +ᴬ-unit-left 𝓖 S

adjoined-powers-vanish-at-the-generators
 : {n m : ℕ} (f : Fin m → Poly n) (k : ℕ) (i : Fin n)
 → _^ᴬ_ R⟨ adjoin-powers f k ⟩ (gen (adjoin-powers f k) i) (succ k)
 ＝ Algebra.0ᴬ R⟨ adjoin-powers f k ⟩
adjoined-powers-vanish-at-the-generators f k i =
 (value-of-power-in-algebras 𝓟 (var i) (succ k) (gen (adjoin-powers f k)))⁻¹
 ∙ transport (λ p → ⟦ p ⟧[ 𝓟 ] (gen (adjoin-powers f k)) ＝ Algebra.0ᴬ 𝓟)
    (join-right f (λ i' → power (var i') (succ k)) i)
    (relations-hold (adjoin-powers f k) (right-index i))
 where
  𝓟 : Algebra 𝓠
  𝓟 = R⟨ adjoin-powers f k ⟩

products-in-the-kernel-of-ev₀-vanish
 : {n m : ℕ} (f : Fin m → Poly n) (k : ℕ)
   (z : (j : Fin (m +ᴺ n)) → ⟦ adjoin-powers f k j ⟧ (λ _ → 0ᴿ) ＝ 0ᴿ)
   (w : Fin (succ (k * n)) → ⟨ R⟨ adjoin-powers f k ⟩ ⟩)
 → ((l : Fin (succ (k * n))) → pr₁ (ev₀ (adjoin-powers f k) z) (w l) ＝ 0ᴿ)
 → ∏ᴬ R⟨ adjoin-powers f k ⟩ w ＝ Algebra.0ᴬ R⟨ adjoin-powers f k ⟩
products-in-the-kernel-of-ev₀-vanish f k z w o =
 products-in-ideals-of-nilpotents-vanish R⟨ adjoin-powers f k ⟩
  (gen (adjoin-powers f k)) k (adjoined-powers-vanish-at-the-generators f k) w
  (λ l → kernel-of-ev₀-is-generated-by-the-generators (adjoin-powers f k) z
          (w l) (o l))

power-adjoined-algebras-are-Weil
 : {n m : ℕ} (f : Fin m → Poly n) (k : ℕ)
   (z : (j : Fin (m +ᴺ n)) → ⟦ adjoin-powers f k j ⟧ (λ _ → 0ᴿ) ＝ 0ᴿ)
 → is-Weil-algebra R⟨ adjoin-powers f k ⟩ (ev₀ (adjoin-powers f k) z)
power-adjoined-algebras-are-Weil {n} {m} f k z =
 ∣ n , (m +ᴺ n) , adjoin-powers f k , ≅ₐ-refl R⟨ adjoin-powers f k ⟩ ∣ ,
 ∣ n , gen (adjoin-powers f k) ,
   ev₀-on-generators (adjoin-powers f k) z ,
   kernel-of-ev₀-is-generated-by-the-generators (adjoin-powers f k) z ∣ ,
 ∣ succ (k * n) , products-in-the-kernel-of-ev₀-vanish f k z ∣

\end{code}

Theorem A.

\begin{code}

Weil-algebra-of : Weil-Presentation → Algebra 𝓠
Weil-algebra-of P = R⟨ Weil-Presentation.poly (normalize P) ⟩

augmentation-of : (P : Weil-Presentation) → Specᴿ (Weil-algebra-of P)
augmentation-of P = ev₀ (Weil-Presentation.poly (normalize P))
                        (Weil-Presentation.poly-at-zero (normalize P))

Weil-algebra-of-is-Weil
 : (P : Weil-Presentation)
 → is-Weil-algebra (Weil-algebra-of P) (augmentation-of P)
Weil-algebra-of-is-Weil P =
 power-adjoined-algebras-are-Weil (Weil-Presentation.poly P)
  (Weil-Presentation.exponent P) (Weil-Presentation.poly-at-zero (normalize P))

products-in-the-augmentation-ideal-vanish
 : (P : Weil-Presentation)
   (w : Fin (succ (Weil-Presentation.exponent P * Weil-Presentation.vars P))
      → ⟨ Weil-algebra-of P ⟩)
 → ((l : Fin (succ (Weil-Presentation.exponent P * Weil-Presentation.vars P)))
      → pr₁ (augmentation-of P) (w l) ＝ 0ᴿ)
 → ∏ᴬ (Weil-algebra-of P) w ＝ Algebra.0ᴬ (Weil-algebra-of P)
products-in-the-augmentation-ideal-vanish P =
 products-in-the-kernel-of-ev₀-vanish (Weil-Presentation.poly P)
  (Weil-Presentation.exponent P) (Weil-Presentation.poly-at-zero (normalize P))

spectrum-of-Weil-algebra-of
 : (P : Weil-Presentation) → Specᴿ (Weil-algebra-of P) ≃ Spec P
spectrum-of-Weil-algebra-of P =
 spectrum-of-presented-algebra (Weil-Presentation.poly (normalize P))
 ● normalization-equivalence P

spectrum-of-Weil-algebra-of-is-pointed
 : (P : Weil-Presentation)
 → ⌜ spectrum-of-Weil-algebra-of P ⌝ (augmentation-of P) ＝ Spec-point P
spectrum-of-Weil-algebra-of-is-pointed P =
 ap ⌜ normalization-equivalence P ⌝
    (spectrum-of-presented-algebra-is-pointed
      (Weil-Presentation.poly (normalize P))
      (Weil-Presentation.poly-at-zero (normalize P)))
 ∙ normalization-equivalence-is-pointed P

spectrum-of-Weil-algebra-of-is-over-Rⁿ
 : (P : Weil-Presentation) (h : Specᴿ (Weil-algebra-of P))
 → pr₁ (⌜ spectrum-of-Weil-algebra-of P ⌝ h)
 ＝ pr₁ h ∘ gen (Weil-Presentation.poly (normalize P))
spectrum-of-Weil-algebra-of-is-over-Rⁿ P h =
 normalization-equivalence-is-over-Rⁿ P
  (⌜ spectrum-of-presented-algebra (Weil-Presentation.poly (normalize P)) ⌝ h)
 ∙ spectrum-of-presented-algebra-is-over-Rⁿ
    (Weil-Presentation.poly (normalize P)) h

\end{code}
