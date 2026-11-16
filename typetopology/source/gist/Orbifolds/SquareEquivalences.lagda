Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026 (local time). Orbifold gate H8 of Fable's
roadmap [1], after the review dated 13 November 2026 (UTC) [2, 3].

Locality under equivalences of test squares
-------------------------------------------

The bridge from Myers's infinitesimal varieties to spectra of
presentations [2, Section 1, obligations 2 and 3; 3, Section 4 (d)]
needs two facts about test squares that TestSquares does not have;
there, locality is invariant under equivalences of the tested type X,
not of the square.

  being-local-is-prop : being X-local is a proposition, since it is
  is-equiv of the gap map;

  locality-is-invariant-under-square-equivalences : let σ and τ be test
  squares, with equivalences eᵢ : Vᵢ ≃ Uᵢ of their vertices that commute
  with the four maps up to given homotopies (a Square-Equivalence), and
  let the fourth vertex of τ be a set. Then σ is X-local exactly when
  τ is.

The proof follows the plan of GPT-6 Astra's audit [3, Section 4 (d)].
Precomposition with e₄ is an equivalence of the domains of the two gap
maps, and precomposition with e₂ and e₃, followed by conjugation of the
homotopies with the commutation squares, is an equivalence Φ of the
cocones. The two composites agree (gap-commutes), so two-out-of-three
applies. Agreement asks that two identifications in the fourth vertex
of τ coincide: the square of σ carried along e₄, and the square of τ
conjugated by the four commutation homotopies. Since that vertex is a
set, this holds, and this is the only place where the set hypothesis
is used [3, Precision 3]. The tested type X is arbitrary.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] Claude Fable 5.2. Orbifolds: the two statement bridges of H8, and
    readiness for H9 and H10, 13 November 2026, Section 1.
    references/F05-orbifolds-h8-bridges.md
[3] GPT-6 Astra. Fable's H8 answer: bridges, crisp truncation, and T2,
    13 November 2026.
    references/A14-h8-answer-audit.txt

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt

module gist.Orbifolds.SquareEquivalences (fe : Fun-Ext) where

open import UF.Base
open import UF.Equiv
open import UF.Equiv-FunExt using (being-equiv-is-prop)
open import UF.EquivalenceExamples
 using (Π-cong ; Π-change-of-variable ; ∙-is-equiv-left ; ∙-is-equiv-right)
open import UF.PairFun
open import UF.Sets
open import UF.Subsingletons

open import gist.Orbifolds.TestSquares fe

being-local-is-prop : {𝓥 𝓦 : Universe} (σ : Test-Square 𝓥) (X : 𝓦 ̇ )
                    → is-prop (is-local σ X)
being-local-is-prop σ X = being-equiv-is-prop (λ 𝓤 𝓥 → fe) (gap σ X)

precomposition-with-equivalence-is-equiv
 : {𝓤 𝓥 𝓦 : Universe} {A : 𝓤 ̇ } {B : 𝓥 ̇ } (X : 𝓦 ̇ ) (e : A ≃ B)
 → is-equiv (λ (h : B → X) → h ∘ ⌜ e ⌝)
precomposition-with-equivalence-is-equiv X e =
 ⌜⌝-is-equiv (Π-change-of-variable fe fe (λ _ → X) ⌜ e ⌝ ⌜ e ⌝-is-equiv)

\end{code}

Identifications of cocones, from homotopies of their legs and a
coherence.

\begin{code}

module _ {𝓥 : Universe} (σ : Test-Square 𝓥) where

 open Test-Square σ

 private
  Cocone-＝' : {𝓦 : Universe} {X : 𝓦 ̇ } {a a' : V₂ → X} {b b' : V₃ → X}
               {H : a ∘ v₁₂ ∼ b ∘ v₁₃} {H' : a' ∘ v₁₂ ∼ b' ∘ v₁₃}
               (p : a ＝ a') (q : b ＝ b')
             → ((z : V₁) → H z ∙ happly q (v₁₃ z) ＝ happly p (v₁₂ z) ∙ H' z)
             → _＝_ {_} {Cocone σ X} (a , b , H) (a' , b' , H')
  Cocone-＝' {𝓦} {X} {a} {_} {b} {_} {H} {H'} refl refl c =
   ap (λ - → (a , b , -)) (dfunext fe (λ z → c z ∙ refl-left-neutral))

 Cocone-＝ : {𝓦 : Universe} {X : 𝓦 ̇ } {a a' : V₂ → X} {b b' : V₃ → X}
             {H : a ∘ v₁₂ ∼ b ∘ v₁₃} {H' : a' ∘ v₁₂ ∼ b' ∘ v₁₃}
             (α : a ∼ a') (β : b ∼ b')
           → ((z : V₁) → H z ∙ β (v₁₃ z) ＝ α (v₁₂ z) ∙ H' z)
           → _＝_ {_} {Cocone σ X} (a , b , H) (a' , b' , H')
 Cocone-＝ {𝓦} {X} {a} {a'} {b} {b'} {H} {H'} α β c =
  Cocone-＝' (dfunext fe α) (dfunext fe β)
   (λ z → ap (λ - → H z ∙ - (v₁₃ z)) (happly-funext fe b b' β)
          ∙ c z
          ∙ (ap (λ - → - (v₁₂ z) ∙ H' z) (happly-funext fe a a' α))⁻¹)

\end{code}

Equivalences of test squares, and the invariance of locality.

\begin{code}

module _ {𝓥 𝓥' : Universe} (σ : Test-Square 𝓥) (τ : Test-Square 𝓥') where

 private
  module σ = Test-Square σ
  module τ = Test-Square τ

 record Square-Equivalence : 𝓥 ⊔ 𝓥' ̇ where
  field
   e₁ : σ.V₁ ≃ τ.V₁
   e₂ : σ.V₂ ≃ τ.V₂
   e₃ : σ.V₃ ≃ τ.V₃
   e₄ : σ.V₄ ≃ τ.V₄
   c₁₂ : τ.v₁₂ ∘ ⌜ e₁ ⌝ ∼ ⌜ e₂ ⌝ ∘ σ.v₁₂
   c₁₃ : τ.v₁₃ ∘ ⌜ e₁ ⌝ ∼ ⌜ e₃ ⌝ ∘ σ.v₁₃
   c₂₄ : τ.v₂₄ ∘ ⌜ e₂ ⌝ ∼ ⌜ e₄ ⌝ ∘ σ.v₂₄
   c₃₄ : τ.v₃₄ ∘ ⌜ e₃ ⌝ ∼ ⌜ e₄ ⌝ ∘ σ.v₃₄

 module _ (E : Square-Equivalence)
          (τ-V₄-is-set : is-set τ.V₄)
          {𝓦 : Universe} (X : 𝓦 ̇ )
        where

  open Square-Equivalence E

  K : (a : τ.V₂ → X) (b : τ.V₃ → X)
    → a ∘ τ.v₁₂ ∼ b ∘ τ.v₁₃
    → (a ∘ ⌜ e₂ ⌝) ∘ σ.v₁₂ ∼ (b ∘ ⌜ e₃ ⌝) ∘ σ.v₁₃
  K a b H z = (ap a (c₁₂ z))⁻¹ ∙ H (⌜ e₁ ⌝ z) ∙ ap b (c₁₃ z)

  K-is-equiv : (a : τ.V₂ → X) (b : τ.V₃ → X) → is-equiv (K a b)
  K-is-equiv a b =
   ∘-is-equiv
    (⌜⌝-is-equiv (Π-change-of-variable fe fe
                   (λ y → a (τ.v₁₂ y) ＝ b (τ.v₁₃ y)) ⌜ e₁ ⌝ ⌜ e₁ ⌝-is-equiv))
    (⌜⌝-is-equiv (Π-cong fe fe
                   (λ z → ((λ p → (ap a (c₁₂ z))⁻¹ ∙ p) ,
                           ∙-is-equiv-left ((ap a (c₁₂ z))⁻¹))
                        ● ((λ q → q ∙ ap b (c₁₃ z)) ,
                           ∙-is-equiv-right (ap b (c₁₃ z))))))

  Φ : Cocone τ X → Cocone σ X
  Φ = pair-fun (λ a → a ∘ ⌜ e₂ ⌝) (λ a → pair-fun (λ b → b ∘ ⌜ e₃ ⌝) (K a))

  Φ-is-equiv : is-equiv Φ
  Φ-is-equiv =
   pair-fun-is-equiv _ _
    (precomposition-with-equivalence-is-equiv X e₂)
    (λ a → pair-fun-is-equiv _ _
            (precomposition-with-equivalence-is-equiv X e₃)
            (K-is-equiv a))

  gap-commutes : (h : τ.V₄ → X) → gap σ X (h ∘ ⌜ e₄ ⌝) ＝ Φ (gap τ X h)
  gap-commutes h = Cocone-＝ σ (λ y → (ap h (c₂₄ y))⁻¹) (λ y → (ap h (c₃₄ y))⁻¹)
                    coherence
   where
    coherence
     : (z : σ.V₁)
     → ap (h ∘ ⌜ e₄ ⌝) (σ.square z) ∙ (ap h (c₃₄ (σ.v₁₃ z)))⁻¹
     ＝ (ap h (c₂₄ (σ.v₁₂ z)))⁻¹
       ∙ K (h ∘ τ.v₂₄) (h ∘ τ.v₃₄) (λ y → ap h (τ.square y)) z
    coherence z =
     ap (h ∘ ⌜ e₄ ⌝) (σ.square z) ∙ (ap h (c₃₄ w))⁻¹
      ＝⟨ ap₂ _∙_ ((ap-ap ⌜ e₄ ⌝ h (σ.square z))⁻¹)
              (ap-sym h (c₃₄ w)) ⟩
     ap h (ap ⌜ e₄ ⌝ (σ.square z)) ∙ ap h ((c₃₄ w)⁻¹)
      ＝⟨ (ap-∙ h (ap ⌜ e₄ ⌝ (σ.square z)) ((c₃₄ w)⁻¹))⁻¹ ⟩
     ap h (ap ⌜ e₄ ⌝ (σ.square z) ∙ (c₃₄ w)⁻¹)
      ＝⟨ ap (ap h) (τ-V₄-is-set (ap ⌜ e₄ ⌝ (σ.square z) ∙ (c₃₄ w)⁻¹)
                        ((c₂₄ v)⁻¹ ∙ (A ∙ B ∙ C))) ⟩
     ap h ((c₂₄ v)⁻¹ ∙ (A ∙ B ∙ C))
      ＝⟨ ap-∙ h ((c₂₄ v)⁻¹) (A ∙ B ∙ C) ⟩
     ap h ((c₂₄ v)⁻¹) ∙ ap h (A ∙ B ∙ C)
      ＝⟨ ap₂ _∙_ ((ap-sym h (c₂₄ v))⁻¹) inner ⟩
     (ap h (c₂₄ v))⁻¹
      ∙ ((ap (h ∘ τ.v₂₄) (c₁₂ z))⁻¹ ∙ ap h (τ.square (⌜ e₁ ⌝ z))
         ∙ ap (h ∘ τ.v₃₄) (c₁₃ z))                                 ∎
     where
      v = σ.v₁₂ z
      w = σ.v₁₃ z
      A = (ap τ.v₂₄ (c₁₂ z))⁻¹
      B = τ.square (⌜ e₁ ⌝ z)
      C = ap τ.v₃₄ (c₁₃ z)

      inner : ap h (A ∙ B ∙ C)
            ＝ (ap (h ∘ τ.v₂₄) (c₁₂ z))⁻¹ ∙ ap h B ∙ ap (h ∘ τ.v₃₄) (c₁₃ z)
      inner =
       ap-∙ h (A ∙ B) C
       ∙ ap₂ _∙_ (ap-∙ h A B
                  ∙ ap (_∙ ap h B) ((ap-sym h (ap τ.v₂₄ (c₁₂ z)))⁻¹
                                    ∙ ap _⁻¹ (ap-ap τ.v₂₄ h (c₁₂ z))))
                 (ap-ap τ.v₃₄ h (c₁₃ z))

  locality-is-invariant-under-square-equivalences : is-local σ X ↔ is-local τ X
  locality-is-invariant-under-square-equivalences = forward , backward
   where
    forward : is-local σ X → is-local τ X
    forward l = ≃-2-out-of-3-left Φ-is-equiv
                 (equiv-closed-under-∼ (gap σ X ∘ (λ h → h ∘ ⌜ e₄ ⌝))
                   (Φ ∘ gap τ X)
                   (∘-is-equiv (precomposition-with-equivalence-is-equiv X e₄)
                     l)
                   (λ h → (gap-commutes h)⁻¹))

    backward : is-local τ X → is-local σ X
    backward l =
     ≃-2-out-of-3-right (precomposition-with-equivalence-is-equiv X e₄)
                  (equiv-closed-under-∼ (Φ ∘ gap τ X)
                    (gap σ X ∘ (λ h → h ∘ ⌜ e₄ ⌝))
                    (∘-is-equiv l Φ-is-equiv)
                    gap-commutes)

\end{code}
