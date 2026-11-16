Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. Orbifold gate H6 of Fable's roadmap [1].

The Rezk completion of a pregroupoid
------------------------------------

Myers [2, Definition 5.4.3] calls a precategory a pregroupoid if every
morphism is an isomorphism, and defines its Rezk completion [2,
Definition 5.4.5] as the essential image of the Yoneda embedding: the
presheaves F for which there merely exist an object x and a natural
isomorphism C(−, x) ≅ F. This module constructs it, as the roadmap's
Section 4 asks, and proves what Theorem 5.4.9 uses [2, proof of 5.4.9]:

  yoneda-embedding-is-surjection : the Yoneda embedding y is surjective;
  hom-≃-identifications : G(x , x') ≃ (y x ＝ y x').

Ingredients, all proved here (TypeTopology's Categories has
precategories but no presheaves or Yoneda lemma):

  - presheaves on a pregroupoid (contravariant functors to sets) and
    natural isomorphisms between them;
  - identifications of presheaves are natural isomorphisms
    (presheaf-identifications), under univalence: the type of
    presheaves with a natural isomorphism from a given one is
    contractible;
  - the Yoneda lemma for natural isomorphisms between representable
    presheaves: they correspond to morphisms, since every morphism of a
    pregroupoid is invertible (yoneda).

Universes. Objects live in a universe 𝓦, morphisms and the values of
presheaves in 𝓤; presheaves, and so the Rezk completion, live in
𝓦 ⊔ 𝓤 ⁺. Univalence of 𝓤 is a parameter of the nested module only,
so that the Rezk completion and the Yoneda embedding do not depend on
it and stay crisp when the pregroupoid is (EtaleGroupoids). The values
of presheaves are sets, so univalence for sets would suffice.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Section 4.
    references/F01-orbifolds-roadmap-rev2.md
[2] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Univalence

module gist.Orbifolds.RezkCompletion
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        {𝓤 𝓦 : Universe}
       where

open PropositionalTruncation pt

open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt using (being-equiv-is-prop)
open import UF.EquivalenceExamples using (NatΣ-equiv-gives-fiberwise-equiv)
open import UF.ImageAndSurjection pt using (is-surjection)
open import UF.Sets
open import UF.Sets-Properties using (being-set-is-prop)
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties using (props-are-sets)
open import UF.Yoneda using (univalence-via-singletons→)

\end{code}

Pregroupoids: precategories in which every morphism is invertible.

\begin{code}

record Pregroupoid : (𝓦 ⊔ 𝓤) ⁺ ̇ where
 field
  ob : 𝓦 ̇
  hom : ob → ob → 𝓤 ̇
  hom-is-set : (x y : ob) → is-set (hom x y)
  idn : (x : ob) → hom x x
  comp : {x y z : ob} → hom y z → hom x y → hom x z
  unit-left : {x y : ob} (f : hom x y) → comp (idn y) f ＝ f
  unit-right : {x y : ob} (f : hom x y) → comp f (idn x) ＝ f
  comp-assoc : {x y z w : ob} (h : hom z w) (g : hom y z) (f : hom x y)
                → comp (comp h g) f ＝ comp h (comp g f)
  inv : {x y : ob} → hom x y → hom y x
  inverse-left : {x y : ob} (f : hom x y) → comp (inv f) f ＝ idn x
  inverse-right : {x y : ob} (f : hom x y) → comp f (inv f) ＝ idn y

\end{code}

A general fact used twice: a Σ-type over a singleton base is the fibre
over any point of the base.

\begin{code}

Σ-over-singleton : {S : 𝓣 ̇ } (B : S → 𝓣' ̇ ) (i : is-singleton S) (c : S)
                 → Σ B ≃ B c
Σ-over-singleton {𝓣} {𝓣'} {S} B i c = qinveq φ (ψ , ψφ , φψ)
 where
  σ : (s : S) → s ＝ c
  σ s = singletons-are-props i s c

  φ : Σ B → B c
  φ (s , b) = transport B (σ s) b

  ψ : B c → Σ B
  ψ b = c , b

  γ : {s : S} (p : s ＝ c) (b : B s) → (c , transport B p b) ＝[ Σ B ] (s , b)
  γ refl b = refl

  ψφ : ψ ∘ φ ∼ id
  ψφ (s , b) = γ (σ s) b

  φψ : φ ∘ ψ ∼ id
  φψ b = ap (λ - → transport B - b)
            (props-are-sets (singletons-are-props i) (σ c) refl)

\end{code}

Presheaves on a pregroupoid, natural isomorphisms, and representable
presheaves.

\begin{code}

module _ (G : Pregroupoid) where

 open Pregroupoid G

 Action-On : (ob → 𝓤 ̇ ) → 𝓦 ⊔ 𝓤 ̇
 Action-On F₀ = (a b : ob) → hom a b → F₀ b → F₀ a

 presheaf-laws : (F₀ : ob → 𝓤 ̇ ) → Action-On F₀ → 𝓦 ⊔ 𝓤 ̇
 presheaf-laws F₀ F₁ =
    ((a : ob) → is-set (F₀ a))
  × ((a : ob) (u : F₀ a) → F₁ a a (idn a) u ＝ u)
  × ((a b c : ob) (g : hom b c) (f : hom a b) (u : F₀ c)
       → F₁ a c (comp g f) u ＝ F₁ a b f (F₁ b c g u))

 presheaf-laws-are-prop : (F₀ : ob → 𝓤 ̇ ) (F₁ : Action-On F₀)
                        → is-prop (presheaf-laws F₀ F₁)
 presheaf-laws-are-prop F₀ F₁ (s , l , m) =
  ×-is-prop (Π-is-prop fe (λ a → being-set-is-prop fe))
   (×-is-prop (Π₂-is-prop fe (λ a u → s a))
              (Π₆-is-prop fe (λ a b c g f u → s a)))
   (s , l , m)

 Presheaf : 𝓦 ⊔ 𝓤 ⁺ ̇
 Presheaf = Σ F₀ ꞉ (ob → 𝓤 ̇ ) , Σ F₁ ꞉ Action-On F₀ , presheaf-laws F₀ F₁

 is-natural : (F F' : Presheaf) → ((a : ob) → pr₁ F a → pr₁ F' a) → 𝓦 ⊔ 𝓤 ̇
 is-natural F F' α =
  (a b : ob) (f : hom a b) (u : pr₁ F b)
  → α a (pr₁ (pr₂ F) a b f u) ＝ pr₁ (pr₂ F') a b f (α b u)

 being-natural-is-prop : (F F' : Presheaf) (α : (a : ob) → pr₁ F a → pr₁ F' a)
                       → is-prop (is-natural F F' α)
 being-natural-is-prop F (F₀' , F₁' , s' , _) α =
  Π₄-is-prop fe (λ a b f u → s' a)

 NatIso : Presheaf → Presheaf → 𝓦 ⊔ 𝓤 ̇
 NatIso F F' = Σ α ꞉ ((a : ob) → pr₁ F a ≃ pr₁ F' a) ,
                 is-natural F F' (λ a → ⌜ α a ⌝)

 id-NatIso : (F : Presheaf) → NatIso F F
 id-NatIso F = (λ a → ≃-refl (pr₁ F a)) , (λ a b f u → refl)

 representable : ob → Presheaf
 representable x =
  (λ a → hom a x) ,
  (λ a b f h → comp h f) ,
  (λ a → hom-is-set a x) ,
  (λ a h → unit-right h) ,
  (λ a b c g f h → (comp-assoc h g f)⁻¹)

\end{code}

The Yoneda lemma for natural isomorphisms between representables.

\begin{code}

 yoneda : (x x' : ob) → hom x x' ≃ NatIso (representable x) (representable x')
 yoneda x x' = qinveq φ (ψ , ψφ , φψ)
  where
   post : (g : hom x x') (a : ob) → hom a x ≃ hom a x'
   post g a = qinveq (λ h → comp g h)
               ((λ h' → comp (inv g) h') ,
                (λ h → (comp-assoc (inv g) g h)⁻¹
                       ∙ ap (λ - → comp - h) (inverse-left g)
                       ∙ unit-left h) ,
                (λ h' → (comp-assoc g (inv g) h')⁻¹
                        ∙ ap (λ - → comp - h') (inverse-right g)
                        ∙ unit-left h'))

   φ : hom x x' → NatIso (representable x) (representable x')
   φ g = post g , (λ a b f u → (comp-assoc g u f)⁻¹)

   ψ : NatIso (representable x) (representable x') → hom x x'
   ψ (α , n) = ⌜ α x ⌝ (idn x)

   ψφ : ψ ∘ φ ∼ id
   ψφ g = unit-right g

   φψ : φ ∘ ψ ∼ id
   φψ (α , n) =
    to-subtype-＝
     (λ β → being-natural-is-prop (representable x) (representable x')
               (λ a → ⌜ β a ⌝))
     (dfunext fe (λ a → to-subtype-＝ (being-equiv-is-prop (λ 𝓤 𝓥 → fe))
                         (dfunext fe (λ h → (n a x h (idn x))⁻¹
                                            ∙ ap ⌜ α a ⌝ (unit-left h)))))

\end{code}

The Rezk completion and the Yoneda embedding (no univalence needed).

\begin{code}

 Rezk-completion : 𝓦 ⊔ 𝓤 ⁺ ̇
 Rezk-completion = Σ F ꞉ Presheaf , (∃ x ꞉ ob , NatIso (representable x) F)

 yoneda-embedding : ob → Rezk-completion
 yoneda-embedding x = representable x , ∣ x , id-NatIso (representable x) ∣

 arrows : 𝓦 ⊔ 𝓤 ̇
 arrows = Σ x ꞉ ob , Σ x' ꞉ ob , hom x x'

 source : arrows → ob
 source (x , x' , g) = x

\end{code}

Under univalence: identifications of presheaves are natural
isomorphisms; so the Yoneda embedding is surjective and its
identifications are the morphisms.

\begin{code}

 module _ (ua : is-univalent 𝓤) where

  idtoiso : (F F' : Presheaf) → F ＝ F' → NatIso F F'
  idtoiso F .F refl = id-NatIso F

  natural-isomorphs-form-a-singleton : (F : Presheaf)
                                     → is-singleton
                                        (Σ F' ꞉ Presheaf , NatIso F F')
  natural-isomorphs-form-a-singleton (F₀ , F₁ , L) =
   equiv-to-singleton
    (reassociate ● Σ-over-singleton Rest base-is-singleton
      (F₀ , (λ a → ≃-refl (F₀ a))))
    (equiv-to-singleton
      (swap ● Σ-over-singleton (λ (F₁' , _) → presheaf-laws F₀ F₁')
        action-is-singleton
                (F₁ , (λ a b f u → refl)))
      (pointed-props-are-singletons L (presheaf-laws-are-prop F₀ F₁)))
   where
    Rest : (Σ F₀' ꞉ (ob → 𝓤 ̇ ) , ((a : ob) → F₀ a ≃ F₀' a)) → 𝓦 ⊔ 𝓤 ̇
    Rest (F₀' , α) = Σ F₁' ꞉ Action-On F₀' , Σ L' ꞉ presheaf-laws F₀' F₁' ,
                      is-natural (F₀ , F₁ , L) (F₀' , F₁' , L') (λ a → ⌜ α a ⌝)

    reassociate : (Σ F' ꞉ Presheaf , NatIso (F₀ , F₁ , L) F') ≃ Σ Rest
    reassociate =
     qinveq (λ ((F₀' , F₁' , L') , α , n) → (F₀' , α) , F₁' , L' , n)
                         ((λ ((F₀' , α) , F₁' , L' , n) →
                           (F₀' , F₁' , L') , α , n) ,
                          (λ _ → refl) , (λ _ → refl))

    base-is-singleton
     : is-singleton (Σ F₀' ꞉ (ob → 𝓤 ̇ ) , ((a : ob) → F₀ a ≃ F₀' a))
    base-is-singleton =
     equiv-to-singleton
      (qinveq (λ (F₀' , α) a → F₀' a , α a)
              ((λ h → (λ a → pr₁ (h a)) , (λ a → pr₂ (h a))) ,
               (λ _ → refl) , (λ _ → refl)))
      (Π-is-singleton fe (λ a → univalence-via-singletons→ ua (F₀ a)))

    Nat₀ : Action-On F₀ → 𝓦 ⊔ 𝓤 ̇
    Nat₀ F₁' = (a b : ob) (f : hom a b) (u : F₀ b) → F₁ a b f u ＝ F₁' a b f u

    swap : Rest (F₀ , (λ a → ≃-refl (F₀ a)))
         ≃ (Σ (F₁' , _) ꞉ (Σ F₁' ꞉ Action-On F₀ , Nat₀ F₁') ,
             presheaf-laws F₀ F₁')
    swap = qinveq (λ (F₁' , L' , n) → (F₁' , n) , L')
                  ((λ ((F₁' , n) , L') → F₁' , L' , n) , (λ _ → refl) ,
                    (λ _ → refl))

    action-is-singleton : is-singleton (Σ F₁' ꞉ Action-On F₀ , Nat₀ F₁')
    action-is-singleton =
     equiv-to-singleton
      (qinveq (λ (F₁' , n) a b f u → F₁' a b f u , n a b f u)
              ((λ h →
                (λ a b f u → pr₁ (h a b f u)) , (λ a b f u → pr₂ (h a b f u))) ,
               (λ _ → refl) , (λ _ → refl)))
      (Π-is-singleton fe (λ a → Π-is-singleton fe (λ b → Π-is-singleton fe
        (λ f → Π-is-singleton fe
                (λ u → singleton-types-are-singletons (F₁ a b f u))))))

  presheaf-identifications : (F F' : Presheaf) → (F ＝ F') ≃ NatIso F F'
  presheaf-identifications F F' =
   idtoiso F F' ,
   NatΣ-equiv-gives-fiberwise-equiv (idtoiso F)
    (maps-of-singletons-are-equivs (NatΣ (idtoiso F))
      (singleton-types-are-singletons F)
      (natural-isomorphs-form-a-singleton F))
    F'

  yoneda-embedding-is-surjection : is-surjection yoneda-embedding
  yoneda-embedding-is-surjection (F , w) =
   ∥∥-functor (λ (x , β) → x , to-subtype-＝ (λ _ → ∃-is-prop)
                                 (⌜ presheaf-identifications (representable x) F
                                    ⌝⁻¹ β))
    w

  hom-≃-identifications : (x x' : ob)
                        → hom x x' ≃ (yoneda-embedding x ＝ yoneda-embedding x')
  hom-≃-identifications x x' =
   yoneda x x'
   ● ≃-sym (presheaf-identifications (representable x) (representable x'))
   ● ≃-sym (ap pr₁ ,
             embedding-gives-embedding' pr₁ (pr₁-is-embedding (λ _ → ∃-is-prop))
                       (yoneda-embedding x) (yoneda-embedding x'))

\end{code}
