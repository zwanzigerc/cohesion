Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index.

Products of contractible families are connected.

Shulman conjectures that his Axioms R♭ and AC imply Lawvere's
continuity: the canonical map ʃ (A^S) → (ʃ A)^S is an equivalence for
every crisp set A and crisp discrete set S [1, §10.3]. Equivalently,
the S-indexed products of the fibers of the unit A → ʃ A are
ʃ-connected. We prove a special case observed by GPT-6 Astra, for an
arbitrary modality: if a type I is connected, then a product of
types each equipped with an I-contraction is connected. In Shulman's
setting the modality is the shape ʃ, which is nullification at the
real line, and I is the real line.

With supplied contractions this needs no form of choice. If the
contractions merely exist, choosing them for all factors at once is an
instance of the discrete axiom of choice [1, Theorem 6.30] when the
index set is a crisp ♭-discrete set and the family is crisp (see
Discrete-Choice in gist.RealCohesion.CrispDiscreteness).

We work with TypeTopology's Σ-closed reflective subuniverses
(Modal.SigmaClosedReflectiveSubuniverse), one of the equivalent
definitions of modality of Rijke, Shulman and Spitters.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import Modal.Subuniverse

module gist.RealCohesion.ShapeProducts
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        {𝓤 𝓥 : Universe}
        (P : subuniverse 𝓤 𝓥)
        (P-is-reflective : subuniverse-is-reflective P)
        (P-is-sigma-closed : subuniverse-is-sigma-closed P)
        (P-is-replete : subuniverse-is-replete P)
       where

open import Modal.SigmaClosedReflectiveSubuniverse
             P P-is-reflective P-is-sigma-closed
open import gist.RealCohesion.ReflectionMaps P P-is-reflective
 using (maps-from-connected-to-modal-are-constant) public
open import UF.Base
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open PropositionalTruncation pt

is-○-connected : 𝓤 ̇ → 𝓤 ̇
is-○-connected A = is-singleton (○ A)

\end{code}

Maps from a connected type into a modal type are constant, because
they factor through the contractible reflection; this is
maps-from-connected-to-modal-are-constant of
gist.RealCohesion.ReflectionMaps, re-exported here.

An I-contraction of a type B, for a type I with two points i₀ and i₁,
is a centre c together with a homotopy H : I → B → B from the constant
map with value c to the identity. If I is connected, a type with an
I-contraction is connected.

\begin{code}

module _ (I : 𝓤 ̇ ) (I-is-connected : is-○-connected I) where

 module _ (i₀ i₁ : I) where

  I-contraction : 𝓤 ̇ → 𝓤 ̇
  I-contraction B = Σ c ꞉ B , Σ H ꞉ (I → B → B) ,
                     ((b : B) → H i₀ b ＝ c) × ((b : B) → H i₁ b ＝ b)

  types-with-I-contractions-are-connected
   : (B : 𝓤 ̇ ) → I-contraction B → is-○-connected B
  types-with-I-contractions-are-connected B (c , H , H₀ , H₁) =
   η B c ,
   ○-induction fe B (λ x → η B c ＝ x)
    (λ x → id-types-of-modal-types-are-modal fe P-is-replete
            (○ B) (η B c) x (○-is-modal B))
    γ
   where
    γ : (b : B) → η B c ＝ η B b
    γ b = η B c          ＝⟨ ap (η B) (H₀ b ⁻¹) ⟩
          η B (H i₀ b)
           ＝⟨ maps-from-connected-to-modal-are-constant I I-is-connected
                (○ B) (○-is-modal B) (λ t → η B (H t b)) i₀ i₁ ⟩
          η B (H i₁ b)   ＝⟨ ap (η B) (H₁ b) ⟩
          η B b          ∎

\end{code}

Products of types with I-contractions have I-contractions, by
contracting all factors simultaneously, and are therefore connected.

\begin{code}

  products-of-I-contractions
   : (S : 𝓤 ̇ ) (B : S → 𝓤 ̇ )
   → ((s : S) → I-contraction (B s))
   → I-contraction (Π B)
  products-of-I-contractions S B κ =
   (λ s → pr₁ (κ s)) ,
   (λ t f s → pr₁ (pr₂ (κ s)) t (f s)) ,
   (λ f → dfunext fe (λ s → pr₁ (pr₂ (pr₂ (κ s))) (f s))) ,
   (λ f → dfunext fe (λ s → pr₂ (pr₂ (pr₂ (κ s))) (f s)))

  products-of-I-contractible-types-are-connected
   : (S : 𝓤 ̇ ) (B : S → 𝓤 ̇ )
   → ((s : S) → I-contraction (B s))
   → is-○-connected (Π B)
  products-of-I-contractible-types-are-connected S B κ =
   types-with-I-contractions-are-connected (Π B)
    (products-of-I-contractions S B κ)

  products-of-merely-I-contractible-types-are-connected
   : (S : 𝓤 ̇ ) (B : S → 𝓤 ̇ )
   → ∥ ((s : S) → I-contraction (B s)) ∥
   → is-○-connected (Π B)
  products-of-merely-I-contractible-types-are-connected S B =
   ∥∥-rec (being-singleton-is-prop fe)
    (products-of-I-contractible-types-are-connected S B)

\end{code}
