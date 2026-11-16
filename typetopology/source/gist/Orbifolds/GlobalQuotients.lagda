Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026; one sentence made precise 13 November
2026, after the final audits. Orbifold gate H8 of Fable's roadmap [1].

Global quotient orbifolds: Theorem 6.4.1 (target T2)
----------------------------------------------------

Myers's Theorem 6.4.1 [2, p. 63]: the quotient of a microlinear set by
the action of a crisp finite group is an orbifold in the sense of his
Definition 1.1.2. This is the target T2 of the roadmap [1, Section
2.2]. Here microlinearity is that of Microlinearity, for spectra of
presentations (the literal form, and its agreement with this one, is
in MyersMicrolinearity), and the
proof is over the core: ℑ is the nullification at all crisp
infinitesimal varieties, it preserves crisp pullbacks (core item 4),
and the smooth line satisfies Postulate K.

  theorem-6-4-1 : for a group in Myers's sense [2, Definition 2.1.2],
  a crisp pointed connected type B whose loop space at b₀ is finite,
  and an action, a family X̃ over B [2, Definition 2.3.1], whose fibre
  over b₀ is a microlinear set, the quotient Σ X̃ is an orbifold.

FiniteGroupQuotients has the same for a finite group given by a
multiplication, through its torsors.

The proof follows Myers and GPT-6 Astra's note on Section 6.4 [3,
Sections 2 and 3], with the roadmap's route to microlinearity [1,
Section 3.5]. Microlinearity is Theorem 5.4.1 (EtaleQuotients). Its
hypothesis that the loop space be ℑ-modal holds because a finite set
has decidable equality (discrete-types-are-ℑ-modal, from Postulate K).
For the identity types: being properly finite is a proposition and B
is connected, so it suffices to consider two points over b₀. There
(b₀ , x) = (b₀ , y) is equivalent to the type of p : b₀ = b₀ with
transport p x = y. Because the fibre is a set, this is a subtype of
the finite loop space. Myers identifies the subtype with the type of
γ : Γ with γ x = y (his Lemma 2.3.2); that transport along a loop is
the action is not needed for finiteness, and is not formalized.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Sections 2.2, 3.5 and 3.8.
    references/F01-orbifolds-roadmap-rev2.md
[2] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.
[3] GPT-6 Astra. All of Myers Section 6.4 over the adopted five-item
    core, 11 November 2026.
    references/A01-section-6-4-over-the-core.txt

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import Modal.Subuniverse
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.GlobalQuotients
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ 𝓡 : Commutative-Ring)
        {@♭ 𝓥 : Universe}
       where

open PropositionalTruncation pt

open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples using (Σ-＝-≃)
open import UF.Sets
open import UF.Subsingletons

open smooth-line fe pt 𝓡 using (Postulate-K)
open import gist.Orbifolds.ProperFiniteness fe pt
open import gist.Orbifolds.Nullification fe
 using
  (is-nullification ; nullifications-are-Σ-closed ; nullifications-are-replete)
open import gist.Orbifolds.Microlinearity fe pt 𝓡 {𝓥}

module _ {𝓦 : Universe}
         (P : subuniverse 𝓥 𝓦)
         (P-is-reflective : subuniverse-is-reflective P)
         (ν : is-nullification ℑ-generator ℑ-generator-point P)
       where

 open import gist.Orbifolds.CrispLemmaF fe pt {𝓥} P P-is-reflective
              (nullifications-are-Σ-closed ℑ-generator ℑ-generator-point P ν)
              (nullifications-are-replete ℑ-generator ℑ-generator-point P ν)
  using (○-preserves-crisp-pullbacks)
 open import gist.Orbifolds.EtaleQuotients fe pt {𝓥} P P-is-reflective
              (nullifications-are-Σ-closed ℑ-generator ℑ-generator-point P ν)
              (nullifications-are-replete ℑ-generator ℑ-generator-point P ν)
  using (theorem-5-4-1-microlinear)

\end{code}

The hypothesis of core item 4, under a name of this module, so that
modules applying theorem-6-4-1 state it in the same terms (a second
instance of CrispLemmaF would give a type that Agda identifies only
after a long unfolding).

\begin{code}

 ℑ-preserves-crisp-pullbacks : 𝓥 ⁺ ̇
 ℑ-preserves-crisp-pullbacks = ○-preserves-crisp-pullbacks

 theorem-6-4-1
  : Postulate-K
  → ℑ-preserves-crisp-pullbacks
  → {@♭ B : 𝓥 ̇ } (@♭ b₀ : B)
  → ((u : B) → ∥ b₀ ＝ u ∥)
  → is-finite (b₀ ＝ b₀)
  → (X̃ : B → 𝓥 ̇ )
  → is-set (X̃ b₀)
  → is-microlinear (X̃ b₀)
  → is-orbifold (Σ X̃)
 theorem-6-4-1 K π {B} b₀ B-is-connected Ω-is-finite X̃ X-is-set
  X-is-microlinear =
  theorem-5-4-1-microlinear π infinitesimal-R-pushouts
   (infinitesimal-R-pushouts-have-connected-pointed-types P P-is-reflective ν)
   b₀ B-is-connected Ω-is-modal X̃ X-is-microlinear ,
  identity-types
  where
   Ω-is-properly-finite : is-properly-finite (b₀ ＝ b₀)
   Ω-is-properly-finite = finite-types-are-properly-finite Ω-is-finite

   Ω-is-modal : subuniverse-contains P (b₀ ＝ b₀)
   Ω-is-modal = discrete-types-are-ℑ-modal P P-is-reflective ν K (b₀ ＝ b₀)
                 (pr₁ Ω-is-properly-finite)

   over-b₀ : (x y : X̃ b₀)
           → is-properly-finite (_＝_ {_} {Σ X̃} (b₀ , x) (b₀ , y))
   over-b₀ x y =
    properly-finite-types-are-closed-under-equivalence (≃-sym Σ-＝-≃)
                  (properly-finite-subtypes (λ p → transport X̃ p x ＝ y)
                    (λ p → X-is-set) Ω-is-properly-finite)

   γ : (b b' : B) → b₀ ＝ b → b₀ ＝ b' → (x : X̃ b) (y : X̃ b')
     → is-properly-finite (_＝_ {_} {Σ X̃} (b , x) (b' , y))
   γ b b' refl refl = over-b₀

   identity-types : (u v : Σ X̃) → is-properly-finite (u ＝ v)
   identity-types (b , x) (b' , y) =
    ∥∥-rec being-properly-finite-is-prop
     (λ p → ∥∥-rec being-properly-finite-is-prop
             (λ p' → γ b b' p p' x y)
             (B-is-connected b'))
     (B-is-connected b)

\end{code}
