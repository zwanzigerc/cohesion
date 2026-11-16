Claude Fable 5.2, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026, as a scratch check for gate G25 of Fable's
second addendum. Added to the folder by Claude Opus 5.5 on 12 November
2026, for gate G25, with the code unchanged except the module name,
and this header rewritten. See the AI disclosure in
gist.RealCohesion.index.

Lemma 1 of Fable's note on Shulman's Theorem 12.6 [2], without its last
step, which is Axiom R♭: a crisp type K with a crisp point to which
every point is merely equal, and whose identity types between crisp
points are ♭-discrete, is ♭-discrete
(connected-crisp-types-are-♭-discrete). The counit ♭ K → K is then a
surjective embedding. That it is an embedding rests on Shulman's
Theorem 6.1 [1], (a^♭ ＝ b^♭) ≃ ♭ (a ＝ b) for crisp a and b
(Theorem-6-1), which needs crisp identity induction with a motive that
depends on the identification (Shulman's Theorem 5.6). That principle
is derived here from the native ♯ of Agda 2.9.0
(gist.CohesiveApartness.Sharp), by the pattern of crisp-ap-^♭ in
gist.CohesiveApartness.CrispInduction (crisp-J), so the module has no
hypothesis besides propositional truncations. GPT-6 Astra compiled
Fable's check independently and audited the modules Sharp and
CrispInduction on which it rests (12 November 2026).

The module is used for the classifying type K of the proof of
Shulman's Theorem 12.6 for the square (gate G25).

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer Science
    28(6), 2018. https://arxiv.org/abs/1509.07584v3

[2] Claude Fable 5.2. Note: Shulman's approximate Brouwer theorem (12.6)
    without the shape modality. Revision 2, 12 November 2026, audited
    by GPT-6 Astra.
    references/F11-shulman-12-6-rev2.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.PropTrunc

module gist.RealCohesion.DiscreteConnectedTypes
        (@♭ pt : propositional-truncations-exist)
       where

open import UF.Embeddings
open import UF.Equiv
open import UF.ImageAndSurjection pt
open import gist.CohesiveApartness.Flat
open import gist.CohesiveApartness.Sharp
open import gist.CohesiveApartness.CrispInduction using (crisp-ap-^♭)

open PropositionalTruncation pt

\end{code}

Crisp identity induction from the native ♯. The family z, q ↦ ♯ (C z q)
is well formed because every variable counts as crisp inside ♯.
Ordinary identity induction gives an element of ♯ (C b p), which is
crisp when everything it is built from is crisp, and then ♯ can be
eliminated. The computation rule holds by definition.

\begin{code}

crisp-J : {@♭ 𝓤 𝓥 : Universe} {@♭ A : 𝓤 ̇ } (@♭ a : A)
          (@♭ C : (@♭ b : A) → @♭ (a ＝ b) → 𝓥 ̇ )
        → @♭ C a refl
        → (@♭ b : A) (@♭ p : a ＝ b) → C b p
crisp-J {𝓤} {𝓥} {A} a C c b p = crisp-elim-sharp (γ b p)
 where
  γ : (z : A) (q : a ＝ z) → ♯ (C z q)
  γ z refl = unit-sharp c

crisp-J-computes : {@♭ 𝓤 𝓥 : Universe} {@♭ A : 𝓤 ̇ } (@♭ a : A)
                   (@♭ C : (@♭ b : A) → @♭ (a ＝ b) → 𝓥 ̇ )
                   (@♭ c : C a refl)
                 → crisp-J a C c a refl ＝ c
crisp-J-computes a C c = refl

\end{code}

The form that DiscreteConnectedTypes assumed takes an ordinary element
of C a refl. It follows by applying crisp-J to the motive
C a refl → C b p, at the identity function.

\begin{code}

Crisp-Identity-Induction : 𝓤ω
Crisp-Identity-Induction =
   {@♭ 𝓤 𝓥 : Universe} {@♭ A : 𝓤 ̇ } {@♭ a : A}
   (@♭ C : (@♭ b : A) → @♭ (a ＝ b) → 𝓥 ̇ )
 → C a refl
 → (@♭ b : A) (@♭ p : a ＝ b) → C b p

crisp-identity-induction : Crisp-Identity-Induction
crisp-identity-induction {𝓤} {𝓥} {A} {a} C c b p =
 crisp-J a (λ b p → C a refl → C b p) id b p c

\end{code}

The rest is DiscreteConnectedTypes as it was, with crisp-ap-^♭ of
gist.CohesiveApartness.CrispInduction in place of its crisp-ap.

\begin{code}

module _ {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } where

 code : ♭ A → ♭ A → 𝓤 ̇
 code (a ^♭) (b ^♭) = ♭ (a ＝ b)

 code-refl : (u : ♭ A) → code u u
 code-refl (a ^♭) = refl ^♭

 enc : (u v : ♭ A) → u ＝ v → code u v
 enc u .u refl = code-refl u

 dec : (u v : ♭ A) → code u v → u ＝ v
 dec (a ^♭) (b ^♭) (p ^♭) = crisp-ap-^♭ p

 dec-enc : (u v : ♭ A) (q : u ＝ v) → dec u v (enc u v q) ＝ q
 dec-enc (a ^♭) .(a ^♭) refl = refl

 enc-crisp-ap : (@♭ a b : A) (@♭ p : a ＝ b)
              → enc (a ^♭) (b ^♭) (crisp-ap-^♭ p) ＝ p ^♭
 enc-crisp-ap a =
  crisp-identity-induction
   (λ b p → enc (a ^♭) (b ^♭) (crisp-ap-^♭ p) ＝ p ^♭) refl

 enc-dec : (u v : ♭ A) (c : code u v) → enc u v (dec u v c) ＝ c
 enc-dec (a ^♭) (b ^♭) (p ^♭) = enc-crisp-ap a b p

 Theorem-6-1 : (@♭ a b : A) → (a ^♭ ＝ b ^♭) ≃ ♭ (a ＝ b)
 Theorem-6-1 a b = qinveq (enc (a ^♭) (b ^♭))
                    (dec (a ^♭) (b ^♭) ,
                     dec-enc (a ^♭) (b ^♭) ,
                     enc-dec (a ^♭) (b ^♭))

\end{code}

If the identity types between crisp points are ♭-discrete, the counit
is an embedding.

\begin{code}

 ♭-counit-is-embedding
  : ((@♭ a b : A) → is-♭-discrete (a ＝ b))
  → is-embedding (♭-counit {𝓤} {A})
 ♭-counit-is-embedding d = embedding-criterion' ♭-counit γ
  where
   γ : (u v : ♭ A) → (♭-counit u ＝ ♭-counit v) ≃ (u ＝ v)
   γ (a ^♭) (b ^♭) = (a ＝ b)       ≃⟨ ≃-sym (♭-counit , d a b) ⟩
                     ♭ (a ＝ b)     ≃⟨ ≃-sym (Theorem-6-1 a b) ⟩
                     (a ^♭ ＝ b ^♭) ■

\end{code}

The lemma.

\begin{code}

 connected-crisp-types-are-♭-discrete
  : (@♭ k₀ : A)
  → ((x : A) → ∥ x ＝ k₀ ∥)
  → ((@♭ a b : A) → is-♭-discrete (a ＝ b))
  → is-♭-discrete A
 connected-crisp-types-are-♭-discrete k₀ c d =
  surjective-embeddings-are-equivs ♭-counit (♭-counit-is-embedding d) s
  where
   s : is-surjection (♭-counit {𝓤} {A})
   s x = ∥∥-functor (λ (p : x ＝ k₀) → (k₀ ^♭) , (p ⁻¹)) (c x)

\end{code}
