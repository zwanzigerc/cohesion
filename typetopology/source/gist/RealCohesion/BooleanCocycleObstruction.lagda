Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index. The construction follows a gameplan by GPT-6
Astra (25 October 2026) [2], building on the oscillatory-image
counterexample of the research notes [1, §5.1].

A Boolean obstruction to the reflection of a set being a set.

Let ○ be a reflection onto a subuniverse of 𝓤₁, and let q : X → T be
a surjection onto a set T. Suppose that ○ X is contractible, that
every map X → 𝟚 is constant, and that the type

  B₂ = Σ A ꞉ 𝓤₀ ̇ , ∥ A ≃ 𝟚 ∥

of two-element types is modal. A Boolean cocycle on the kernel of q is
a function c x y e : 𝟚, for x y : X and e : q x ＝ q y, with

  c x y e ⊕ c y z e' ＝ c x z (e ∙ e').

If such a cocycle takes the value ₁ somewhere, then ○ T is not a set.

The idea is that c describes a double cover of T. Over t : T, the
fibre consists of the labelings of the fibre of q over t that are
compatible with c. When ○ T is a set, it is contractible, and the
double cover, which is classified by a map T → B₂ into a modal type,
becomes trivial, so it has a section. A section gives a map X → 𝟚,
which is constant by hypothesis but changes by c along the kernel, so
c is identically ₀.

The labelings live in 𝓤₁, while B₂ classifies types in 𝓤₀. We
resolve this with TypeTopology's theorem that being small is a
proposition, under univalence: each labeling type is merely
equivalent to 𝟚, so it is small, without any form of resizing or
choice. The argument needs no set quotients or set truncations, and
no higher inductive types other than propositional truncation. It
uses only the universal property of the reflection.

This is the mod 2 reduction of the ℤ-valued cocycle of the research
notes [1, Theorem 5.3].

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, draft of 25 October 2026.
    references/C01-write-up-2026-10-25.tex

[2] GPT-6 Astra. Gameplan for Opus: a subset of the Dedekind reals
    whose shape is not a set, 25 October 2026.
    references/A32-subset-shape-gameplan.md

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Univalence
open import Modal.Subuniverse

module gist.RealCohesion.BooleanCocycleObstruction
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        {𝓥 : Universe}
        (P : subuniverse 𝓤₁ 𝓥)
        (P-is-reflective : subuniverse-is-reflective P)
       where

open import MLTT.Two-Properties
open import Modal.ReflectiveSubuniverse P P-is-reflective
open import gist.RealCohesion.ReflectionMaps P P-is-reflective
open import UF.Base
open import UF.DiscreteAndSeparated using (𝟚-is-set)
open import UF.Equiv
open import UF.ImageAndSurjection pt
open import UF.Sets
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

open PropositionalTruncation pt

private
 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

\end{code}

Some Boolean arithmetic, in addition to ⊕-assoc of MLTT.Two-Properties.

\begin{code}

⊕-₀-right : (a : 𝟚) → a ⊕ ₀ ＝ a
⊕-₀-right a = ⊕-₀-right-neutral

⊕-₁-right : (a : 𝟚) → a ⊕ ₁ ＝ complement a
⊕-₁-right a = ⊕-left-complement refl

⊕-idempotent-gives-₀ : (a : 𝟚) → a ⊕ a ＝ a → a ＝ ₀
⊕-idempotent-gives-₀ a e = e ⁻¹ ∙ Lemma[b⊕b＝₀] {a}

\end{code}

The type of two-element types. The action ○-map of the reflection on
maps is from gist.RealCohesion.ReflectionMaps.

\begin{code}

B₂ : 𝓤₁ ̇
B₂ = Σ A ꞉ 𝓤₀ ̇ , ∥ A ≃ 𝟚 ∥

\end{code}

The hypotheses of the obstruction.

\begin{code}

module _ (X T : 𝓤₁ ̇ )
         (T-is-set : is-set T)
         (q : X → T)
         (q-is-surjection : is-surjection q)
         (○X-is-singleton : is-singleton (○ X))
         (maps-to-𝟚-are-constant : (k : X → 𝟚) (x y : X) → k x ＝ k y)
         (B₂-is-modal : is-modal B₂)
         (c : (x y : X) → q x ＝ q y → 𝟚)
         (c-is-cocycle : (x y z : X) (e : q x ＝ q y) (e' : q y ＝ q z)
                       → c x y e ⊕ c y z e' ＝ c x z (e ∙ e'))
         (x₁ y₁ : X)
         (e₁ : q x₁ ＝ q y₁)
         (c-is-nontrivial : c x₁ y₁ e₁ ＝ ₁)
       where

\end{code}

Since T is a set, the value of c doesn't depend on the identification,
and the cocycle law gives the value ₀ on the diagonal.

\begin{code}

 c-is-proof-irrelevant : (x y : X) (e e' : q x ＝ q y) → c x y e ＝ c x y e'
 c-is-proof-irrelevant x y e e' = ap (c x y) (T-is-set e e')

 c-is-normalized : (x : X) (e : q x ＝ q x) → c x x e ＝ ₀
 c-is-normalized x e = ⊕-idempotent-gives-₀ (c x x e)
                        (c-is-cocycle x x x e e
                         ∙ c-is-proof-irrelevant x x (e ∙ e) e)

\end{code}

The double cover. Over t : T, the cocycle restricts to the fibre F t of
q, and E t is the type of labelings of F t compatible with it.

\begin{code}

 F : T → 𝓤₁ ̇
 F = fiber q

 c-on-fiber : (t : T) → F t → F t → 𝟚
 c-on-fiber t (a , d) (b , d') = c a b (d ∙ d' ⁻¹)

 c-on-fiber-is-cocycle : (t : T) (u v w : F t)
                       → c-on-fiber t u v ⊕ c-on-fiber t v w ＝ c-on-fiber t u w
 c-on-fiber-is-cocycle t (a , d) (b , d') (b' , d'') =
  c-is-cocycle a b b' (d ∙ d' ⁻¹) (d' ∙ d'' ⁻¹)
  ∙ c-is-proof-irrelevant a b' _ _

 c-on-fiber-is-normalized : (t : T) (u : F t) → c-on-fiber t u u ＝ ₀
 c-on-fiber-is-normalized t (a , d) = c-is-normalized a (d ∙ d ⁻¹)

 is-labeling : (t : T) → (F t → 𝟚) → 𝓤₁ ̇
 is-labeling t s = (u v : F t) → s v ＝ s u ⊕ c-on-fiber t u v

 being-labeling-is-prop : (t : T) (s : F t → 𝟚) → is-prop (is-labeling t s)
 being-labeling-is-prop t s = Π₂-is-prop fe (λ u v → 𝟚-is-set)

 E : T → 𝓤₁ ̇
 E t = Σ s ꞉ (F t → 𝟚) , is-labeling t s

\end{code}

Every point of a fibre trivializes the fibre of the double cover:
evaluation at it is an equivalence with 𝟚.

\begin{code}

 labeling-at : (t : T) → F t → 𝟚 → E t
 labeling-at t u β = (λ v → β ⊕ c-on-fiber t u v) , γ
  where
   γ : is-labeling t (λ v → β ⊕ c-on-fiber t u v)
   γ v w = β ⊕ c-on-fiber t u w                     ＝⟨ I ⟩
           β ⊕ (c-on-fiber t u v ⊕ c-on-fiber t v w) ＝⟨ II ⟩
           (β ⊕ c-on-fiber t u v) ⊕ c-on-fiber t v w ∎
    where
     I = ap (β ⊕_) (c-on-fiber-is-cocycle t u v w ⁻¹)
     II = (⊕-assoc {β} {c-on-fiber t u v} {c-on-fiber t v w}) ⁻¹

 evaluation-at : (t : T) → F t → E t → 𝟚
 evaluation-at t u (s , _) = s u

 evaluation-is-equiv : (t : T) (u : F t) → is-equiv (evaluation-at t u)
 evaluation-is-equiv t u =
  qinvs-are-equivs (evaluation-at t u) (labeling-at t u , I , II)
  where
   I : labeling-at t u ∘ evaluation-at t u ∼ id
   I (s , κ) = to-subtype-＝ (being-labeling-is-prop t)
                (dfunext fe (λ v → (κ u v) ⁻¹))

   II : evaluation-at t u ∘ labeling-at t u ∼ id
   II β = ap (β ⊕_) (c-on-fiber-is-normalized t u) ∙ ⊕-₀-right β

 E-≃-𝟚 : (t : T) → F t → E t ≃ 𝟚
 E-≃-𝟚 t u = evaluation-at t u , evaluation-is-equiv t u

\end{code}

Each E t is small, because its fibre is merely inhabited and being
small is a proposition. This gives the classifying map T → B₂. We make
the proof of smallness abstract: nothing computes with it, and
unfolding it makes type checking very slow.

\begin{code}

 abstract
  E-is-small : (t : T) → E t is 𝓤₀ small
  E-is-small t = ∥∥-rec (being-small-is-prop ua (E t) 𝓤₀)
                  (λ u → 𝟚 , ≃-sym (E-≃-𝟚 t u))
                  (q-is-surjection t)

 E′ : T → 𝓤₀ ̇
 E′ t = resized (E t) (E-is-small t)

 E′-≃-E : (t : T) → E′ t ≃ E t
 E′-≃-E t = resizing-condition (E-is-small t)

 classifier : T → B₂
 classifier t = E′ t , ∥∥-functor (λ u → E′-≃-E t ● E-≃-𝟚 t u)
                        (q-is-surjection t)

\end{code}

From now on, assume that ○ T is a set. Then it is contractible: the
unit is constant, because ○ X is contractible and q is surjective, and
by the universal property of the reflection the identity of ○ T is
then constant too.

\begin{code}

 module _ (○T-is-set : is-set (○ T)) where

  t₀ : T
  t₀ = q x₁

  η-is-constant : (t : T) → η T t₀ ＝ η T t
  η-is-constant t = ∥∥-rec ○T-is-set γ (q-is-surjection t)
   where
    γ : fiber q t → η T t₀ ＝ η T t
    γ (x , d) = η T (q x₁)       ＝⟨ ○-map-on-units q x₁ ⁻¹ ⟩
                ○-map q (η X x₁) ＝⟨ ap (○-map q) I ⟩
                ○-map q (η X x)  ＝⟨ ○-map-on-units q x ⟩
                η T (q x)        ＝⟨ ap (η T) d ⟩
                η T t            ∎
     where
      I : η X x₁ ＝ η X x
      I = singletons-are-props ○X-is-singleton (η X x₁) (η X x)

  ○T-is-singleton : is-singleton (○ T)
  ○T-is-singleton =
   constant-unit-gives-singleton fe T t₀ (λ t → η-is-constant t ⁻¹)

\end{code}

Hence every map from T to a modal type is constant, by the universal
property of the reflection. In particular the classifying map is
constant, and transporting one labeling over t₀ gives a section of the
double cover. No choice is involved.

\begin{code}

  maps-to-modal-types-are-constant : (B : 𝓤₁ ̇ ) (B-is-modal : is-modal B)
                                     (f : T → B) (t : T)
                                   → f t₀ ＝ f t
  maps-to-modal-types-are-constant B B-is-modal f =
   maps-from-connected-to-modal-are-constant T ○T-is-singleton B B-is-modal f t₀

  classifier-is-constant : (t : T) → classifier t₀ ＝ classifier t
  classifier-is-constant =
   maps-to-modal-types-are-constant B₂ B₂-is-modal classifier

  base-labeling : E t₀
  base-labeling = labeling-at t₀ (x₁ , refl) ₀

  section : (t : T) → E t
  section t = ⌜ E′-≃-E t ⌝
               (⌜ idtoeq (E′ t₀) (E′ t) (ap pr₁ (classifier-is-constant t)) ⌝
                 (⌜ E′-≃-E t₀ ⌝⁻¹ base-labeling))

\end{code}

The section gives a map X → 𝟚, which changes by c along the kernel
of q.

\begin{code}

  k : X → 𝟚
  k x = pr₁ (section (q x)) (x , refl)

  transported-label : (x : X) (t : T) (e : q x ＝ t) (v : X) (d : q v ＝ t)
                    → pr₁ (section t) (v , d)
                    ＝ pr₁ (section (q x)) (v , (d ∙ e ⁻¹))
  transported-label x .(q x) refl v d = refl

  k-changes-by-c : (x y : X) (e : q x ＝ q y) → k y ＝ k x ⊕ c x y e
  k-changes-by-c x y e =
   k y                                                   ＝⟨ refl ⟩
   pr₁ (section (q y)) (y , refl)                        ＝⟨ I ⟩
   pr₁ (section (q x)) (y , (refl ∙ e ⁻¹))               ＝⟨ II ⟩
   k x ⊕ c-on-fiber (q x) (x , refl) (y , (refl ∙ e ⁻¹)) ＝⟨ III ⟩
   k x ⊕ c x y e                                         ∎
   where
    I   = transported-label x (q y) e y refl
    II  = pr₂ (section (q x)) (x , refl) (y , (refl ∙ e ⁻¹))
    III = ap (k x ⊕_) (c-is-proof-irrelevant x y _ e)

\end{code}

But k is constant, so c vanishes, contradicting its value ₁.

\begin{code}

  absurdity : 𝟘
  absurdity = complement-no-fp (k x₁) I
   where
    I : k x₁ ＝ complement (k x₁)
    I = k x₁              ＝⟨ maps-to-𝟚-are-constant k x₁ y₁ ⟩
        k y₁              ＝⟨ k-changes-by-c x₁ y₁ e₁ ⟩
        k x₁ ⊕ c x₁ y₁ e₁ ＝⟨ ap (k x₁ ⊕_) c-is-nontrivial ⟩
        k x₁ ⊕ ₁          ＝⟨ ⊕-₁-right (k x₁) ⟩
        complement (k x₁) ∎

 reflection-is-not-a-set : ¬ is-set (○ T)
 reflection-is-not-a-set = absurdity

\end{code}
