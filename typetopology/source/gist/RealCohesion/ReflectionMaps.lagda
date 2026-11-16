Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index.

The action of a reflection on maps, and its computation rule on units.
Also two facts about types whose reflection is contractible.

The first two definitions are shared by
gist.RealCohesion.ShapeContinuity and
gist.RealCohesion.BooleanCocycleObstruction. They are in a module of
their own so that the second doesn't have to assume set truncations,
which the first needs for other purposes. The two facts are shared by
gist.RealCohesion.ShapeProducts, gist.RealCohesion.BooleanCocycleObstruction
and gist.RealCohesion.RealSubsetShape.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Modal.Subuniverse
open import UF.Base using (happly)
open import UF.FunExt
open import UF.Subsingletons

module gist.RealCohesion.ReflectionMaps
        {𝓤 𝓥 : Universe}
        (P : subuniverse 𝓤 𝓥)
        (P-is-reflective : subuniverse-is-reflective P)
       where

open import Modal.ReflectiveSubuniverse P P-is-reflective

○-map : {A B : 𝓤 ̇ } → (A → B) → ○ A → ○ B
○-map {A} {B} f = ○-rec A (○ B) (○-is-modal B) (η B ∘ f)

○-map-on-units : {A B : 𝓤 ̇ } (f : A → B) (a : A)
               → ○-map f (η A a) ＝ η B (f a)
○-map-on-units {A} {B} f = ○-rec-compute A (○ B) (○-is-modal B) (η B ∘ f)

\end{code}

Maps from a type with contractible reflection into a modal type are
constant, because they factor through the reflection. And if the unit
of a type is constant, its reflection is contractible.

\begin{code}

maps-from-connected-to-modal-are-constant
 : (A : 𝓤 ̇ ) → is-singleton (○ A)
 → (D : 𝓤 ̇ ) → is-modal D → (g : A → D) (s t : A) → g s ＝ g t
maps-from-connected-to-modal-are-constant A A-is-connected D D-modal g s t =
 g s                         ＝⟨ ○-rec-compute A D D-modal g s ⁻¹ ⟩
 ○-rec A D D-modal g (η A s) ＝⟨ ap (○-rec A D D-modal g)
                                   (singletons-are-props A-is-connected _ _) ⟩
 ○-rec A D D-modal g (η A t) ＝⟨ ○-rec-compute A D D-modal g t ⟩
 g t                         ∎

constant-unit-gives-singleton : funext 𝓤 𝓤 → (A : 𝓤 ̇ ) (a₀ : A)
                              → ((a : A) → η A a ＝ η A a₀)
                              → is-singleton (○ A)
constant-unit-gives-singleton fe A a₀ c = η A a₀ , (λ z → happly I z ⁻¹)
 where
  I : id ＝ (λ (_ : ○ A) → η A a₀)
  I = ○-rec-ext A (○ A) (○-is-modal A) id (λ _ → η A a₀) (dfunext fe c)

\end{code}
