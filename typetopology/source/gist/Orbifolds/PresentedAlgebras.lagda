Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), for gate WG2 of Claude Fable
5.2's plan for the comparison of Weil algebras with presentations [1],
as reviewed by GPT-6 Astra [2], amended by Fable's addendum 01 [3] and
released by Astra [4]. The exported names, and the universes and
hypotheses of their statements, are those of the plan's statement
companion; the proofs are Claude Opus 5.5's. See the AI disclosure in
gist.RealCohesion.index.

Algebras presented by generators and relations: the interface
--------------------------------------------------------------

For a finite family g : Fin m → Poly n of polynomial expressions of
gist.Orbifolds.SmoothLine in n variables, the algebra R⟨ g ⟩ presented by
the generators x₀, …, xₙ₋₁ and the relations g j = 0 is characterized by
the following properties, which the record Presented-Algebras 𝓠 asks of
an assignment of an algebra with carrier in the universe 𝓠 to every such
family.

  gen g : Fin n → ⟨ R⟨ g ⟩ ⟩, the generators.

  relations-hold (P1): the value of every g j at the generators is 0.

  universality (P2): for every algebra 𝓑, with carrier in any universe
  𝓦, and every point b of 𝓑 at which every g j vanishes, there is exactly
  one homomorphism from R⟨ g ⟩ to 𝓑 that takes the generators to b. The
  unique existence is the contractibility of a Σ-type, so it provides an
  actual homomorphism.

  generation (P3): every element of R⟨ g ⟩ is merely the value of an
  expression at the generators.

The record lives in 𝓤ω, because (P2) quantifies over the universe of 𝓑.
This is the layering of TypeTopology's Groups.Free [5]: an interface in
𝓤ω whose universal property eliminates into every universe, a
construction from general set quotients
(gist.Orbifolds.PresentedAlgebrasFromQuotients) and an instance from the
large quotients of Quotient.Large
(gist.Orbifolds.PresentedAlgebrasFromLargeQuotients), whose carriers lie
in 𝓤₁ [1, Section 2.1]. The theorems of the later gates are proved over
the interface, so that no proof depends on how the quotient is built.

Derived here, for an instance pa:

  hom-from-presented, hom-from-presented-on-generators : the homomorphism
  of (P2), and its values at the generators.

  homs-from-presented-are-determined-by-generators : two homomorphisms
  out of R⟨ g ⟩ that agree at the generators are equal. The values of
  the second at the generators satisfy the relations, by (P1) and
  values-under-homs, and both homomorphisms then lie in the singleton of
  (P2).

  presented-algebras-are-unique : any two instances give isomorphic
  algebras, for every family, also when their universes differ. So being
  finitely presented does not depend on the instance.

Assumptions: function extensionality and propositional truncations, as
in SmoothLine, and nothing else. No quotient, ideal, crisp datum, choice,
resizing, univalence or propositional extensionality is assumed, and the
module adds no option and no postulate.

[1] Claude Fable 5.2. Plan: formalizing the comparison of Weil algebras
    with presentations, 13 November 2026, Sections 2.1 and 4.1, with its
    statement companion, Section WG2 (plan SHA-256 b1662ecc…; companion
    SHA-256 47974af8…).
[2] GPT-6 Astra. Review of Fable's Weil plan, 13 November 2026
    (FABLE-WEIL-PLAN-REVIEW-01).
[3] Claude Fable 5.2. Addendum 01 to the plan, 13 November 2026
    (SHA-256 abf31923…).
[4] GPT-6 Astra. Release of gate WG2, 13 November 2026
    (SHA-256 998a4fb0…).
[5] TypeTopology, Groups/Free.lagda, at commit 52ed2eb5: the record
    good-freely-generated-group-exists and its three corollaries. The
    pattern is followed; no code is taken from it.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.PresentedAlgebras
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (𝓡 : Commutative-Ring)
       where

open import Fin.Type
open import UF.Base
open import UF.Subsingletons

open PropositionalTruncation pt
open smooth-line fe pt 𝓡
open import gist.Orbifolds.Algebras fe pt 𝓡

record Presented-Algebras (𝓠 : Universe) : 𝓤ω where
 field
  R⟨_⟩ : {n m : ℕ} → (Fin m → Poly n) → Algebra 𝓠
  gen : {n m : ℕ} (g : Fin m → Poly n) → Fin n → ⟨ R⟨ g ⟩ ⟩
  relations-hold
   : {n m : ℕ} (g : Fin m → Poly n) (j : Fin m)
   → ⟦ g j ⟧[ R⟨ g ⟩ ] (gen g) ＝ Algebra.0ᴬ R⟨ g ⟩
  universality
   : {n m : ℕ} (g : Fin m → Poly n)
     {𝓦 : Universe} (𝓑 : Algebra 𝓦) (b : Fin n → ⟨ 𝓑 ⟩)
   → ((j : Fin m) → ⟦ g j ⟧[ 𝓑 ] b ＝ Algebra.0ᴬ 𝓑)
   → ∃! h ꞉ Hom R⟨ g ⟩ 𝓑 , pr₁ h ∘ gen g ∼ b
  generation
   : {n m : ℕ} (g : Fin m → Poly n) (w : ⟨ R⟨ g ⟩ ⟩)
   → ∃ p ꞉ Poly n , ⟦ p ⟧[ R⟨ g ⟩ ] (gen g) ＝ w

module _ {𝓠 : Universe} (pa : Presented-Algebras 𝓠) where

 open Presented-Algebras pa

 hom-from-presented
  : {n m : ℕ} (g : Fin m → Poly n)
    {𝓦 : Universe} (𝓑 : Algebra 𝓦) (b : Fin n → ⟨ 𝓑 ⟩)
  → ((j : Fin m) → ⟦ g j ⟧[ 𝓑 ] b ＝ Algebra.0ᴬ 𝓑)
  → Hom R⟨ g ⟩ 𝓑
 hom-from-presented g 𝓑 b s = ∃!-witness (universality g 𝓑 b s)

 hom-from-presented-on-generators
  : {n m : ℕ} (g : Fin m → Poly n)
    {𝓦 : Universe} (𝓑 : Algebra 𝓦) (b : Fin n → ⟨ 𝓑 ⟩)
    (s : (j : Fin m) → ⟦ g j ⟧[ 𝓑 ] b ＝ Algebra.0ᴬ 𝓑)
  → pr₁ (hom-from-presented g 𝓑 b s) ∘ gen g ∼ b
 hom-from-presented-on-generators g 𝓑 b s =
  ∃!-is-witness (universality g 𝓑 b s)

 homs-from-presented-are-determined-by-generators
  : {n m : ℕ} (g : Fin m → Poly n)
    {𝓦 : Universe} (𝓑 : Algebra 𝓦) (h k : Hom R⟨ g ⟩ 𝓑)
  → pr₁ h ∘ gen g ∼ pr₁ k ∘ gen g → h ＝ k
 homs-from-presented-are-determined-by-generators {n} {m} g 𝓑 h k H =
  ap pr₁ (singletons-are-props (universality g 𝓑 (pr₁ k ∘ gen g) s)
                               (h , H) (k , (λ i → refl)))
  where
   s : (j : Fin m) → ⟦ g j ⟧[ 𝓑 ] (pr₁ k ∘ gen g) ＝ Algebra.0ᴬ 𝓑
   s j = (values-under-homs R⟨ g ⟩ 𝓑 k (g j) (gen g))⁻¹
       ∙ ap (pr₁ k) (relations-hold g j)
       ∙ homs-preserve-0 R⟨ g ⟩ 𝓑 k

presented-algebras-are-unique
 : {𝓠 𝓠' : Universe} (pa : Presented-Algebras 𝓠) (pa' : Presented-Algebras 𝓠')
   {n m : ℕ} (g : Fin m → Poly n)
 → Presented-Algebras.R⟨_⟩ pa g ≅ₐ Presented-Algebras.R⟨_⟩ pa' g
presented-algebras-are-unique {𝓠} {𝓠'} pa pa' {n} {m} g = f , f' , f'f , ff'
 where
  module P  = Presented-Algebras pa
  module P' = Presented-Algebras pa'

  𝓐 : Algebra 𝓠
  𝓐 = P.R⟨_⟩ g

  𝓐' : Algebra 𝓠'
  𝓐' = P'.R⟨_⟩ g

  f : Hom 𝓐 𝓐'
  f = hom-from-presented pa g 𝓐' (P'.gen g) (P'.relations-hold g)

  f' : Hom 𝓐' 𝓐
  f' = hom-from-presented pa' g 𝓐 (P.gen g) (P.relations-hold g)

  f-on-generators : pr₁ f ∘ P.gen g ∼ P'.gen g
  f-on-generators =
   hom-from-presented-on-generators pa g 𝓐' (P'.gen g) (P'.relations-hold g)

  f'-on-generators : pr₁ f' ∘ P'.gen g ∼ P.gen g
  f'-on-generators =
   hom-from-presented-on-generators pa' g 𝓐 (P.gen g) (P.relations-hold g)

  f'f : pr₁ f' ∘ pr₁ f ∼ id
  f'f = happly (ap pr₁ (homs-from-presented-are-determined-by-generators
                         pa g 𝓐
                         (_∘ₕ_ {𝓐 = 𝓐} {𝓑 = 𝓐'} {𝓒 = 𝓐} f' f) (id-hom 𝓐)
                         (λ i → ap (pr₁ f') (f-on-generators i)
                              ∙ f'-on-generators i)))

  ff' : pr₁ f ∘ pr₁ f' ∼ id
  ff' = happly (ap pr₁ (homs-from-presented-are-determined-by-generators
                         pa' g 𝓐'
                         (_∘ₕ_ {𝓐 = 𝓐'} {𝓑 = 𝓐} {𝓒 = 𝓐'} f f') (id-hom 𝓐')
                         (λ i → ap (pr₁ f) (f'-on-generators i)
                              ∙ f-on-generators i)))

\end{code}
