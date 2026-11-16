Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026 (local time). Orbifold gate H9 of Fable's
roadmap [1, Section 3.9].

Lemma D: étaleness is local on the source
-----------------------------------------

Lemma D is Claude Fable 5.2's [2, Section 1], audited by GPT-6 Astra
(roadmap [1, Section 3.9]). For a modality ○ in which propositions are
modal (as for every nullification at pointed types):

  lemma-D : if p : W → X is surjective and étale, and s ∘ p is étale,
  then s : X → Y is étale.

Route. Fable proves it by base change of the gap map of s along ○p. Here
the same argument is run on fibres, with the characterization of étale
maps by fibres of the module Modalities (étale-iff-fiberwise-equiv):

  - Reflection squares. For f : X → Y, a pair of F : ○X → ○Y and a
    homotopy F ∘ η ∼ η ∘ f is unique, because precomposition with η is
    an equivalence into the modal type ○Y
    (reflection-squares-are-props). So the fibrewise condition for f can
    be checked with any such square; for s ∘ p it is checked with
    ○s ∘ ○p. This replaces a coherence between ○(s ∘ p) and ○s ∘ ○p,
    for which TypeTopology's ○-induction has no computation rule.
  - For y : Y, the fibre of s ∘ p over y is Σ over the fibre of s of
    fibres of p, and those are fibres of ○p because p is étale; on the
    other side the fibre of ○s ∘ ○p is Σ over the fibre of ○s of fibres
    of ○p. Under these identifications the fibre map of s ∘ p becomes
    the map induced by the fibre map φ of s, the identity on the fibres
    of ○p; so that map is an equivalence.
  - The fibres of ○p are merely inhabited, because ○p is surjective (p
    and the units are), and so φ itself is an equivalence
    (equivalences-descend-along-surjective-families).

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Section 3.9.
    references/F01-orbifolds-roadmap-rev2.md
[2] Claude Fable 5.2. Reply: the core, nilpotence, and what Section 5.2
    needs, 11 November 2026.
    references/F07-core-and-nilpotence.md

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import Modal.Subuniverse

module gist.Orbifolds.LemmaD
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        {𝓤 𝓥 : Universe}
        (P : subuniverse 𝓤 𝓥)
        (P-is-reflective : subuniverse-is-reflective P)
        (P-is-sigma-closed : subuniverse-is-sigma-closed P)
        (P-is-replete : subuniverse-is-replete P)
       where

open PropositionalTruncation pt

open import Modal.SigmaClosedReflectiveSubuniverse P P-is-reflective
 P-is-sigma-closed
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples using (fiber-of-composite ; Σ-cong)
open import UF.ImageAndSurjection pt using (is-surjection)
open import UF.PairFun using (pair-fun ; pair-fun-fiber-≃)
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import gist.RealCohesion.ReflectionMaps P P-is-reflective
 using (○-map ; ○-map-on-units)
open import gist.Orbifolds.Modalities fe pt P P-is-reflective P-is-sigma-closed
 P-is-replete
 using (is-étale ; étale-fiber-map ; étale-iff-fiberwise-equiv ;
        étale-maps-have-fibers-of-○-map ; units-are-surjective)

\end{code}

Reflection squares are unique.

\begin{code}

Reflection-Square : {X Y : 𝓤 ̇ } → (X → Y) → 𝓤 ̇
Reflection-Square {X} {Y} f =
 Σ F ꞉ (○ X → ○ Y) , ((x : X) → F (η X x) ＝ η Y (f x))

reflection-squares-are-props : {X Y : 𝓤 ̇ } (f : X → Y)
                             → is-prop (Reflection-Square f)
reflection-squares-are-props {X} {Y} f =
 equiv-to-prop
  (Σ-cong (λ F → ≃-sym (≃-funext fe (F ∘ η X) (η Y ∘ f))))
  (singletons-are-props
    (equivs-are-vv-equivs (precomp-η X (○ Y))
      (precomp-η-is-equiv (○-is-modal Y)) (η Y ∘ f)))

square-fiber-map : {X Y : 𝓤 ̇ } (f : X → Y) (R : Reflection-Square f) (y : Y)
                 → fiber f y → fiber (pr₁ R) (η Y y)
square-fiber-map {X} {Y} f (F , c) y (x , r) = η X x , (c x ∙ ap (η Y) r)

étale-maps-have-equivalences-on-fibers
 : {X Y : 𝓤 ̇ } (f : X → Y) → is-étale f
 → (R : Reflection-Square f) (y : Y) → is-equiv (square-fiber-map f R y)
étale-maps-have-equivalences-on-fibers f e R y =
 transport (λ R' → is-equiv (square-fiber-map f R' y))
  (reflection-squares-are-props f (○-map f , ○-map-on-units f) R)
  (lr-implication (étale-iff-fiberwise-equiv f) e y)

\end{code}

Equivalences descend along families with inhabited fibres.

\begin{code}

equivalences-descend-along-surjective-families
 : {A B : 𝓤 ̇ } (φ : A → B) (F : B → 𝓤 ̇ )
 → is-equiv (pair-fun {A = λ a → F (φ a)} {B = F} φ (λ a t → t))
 → ((b : B) → ∥ F b ∥)
 → is-equiv φ
equivalences-descend-along-surjective-families {A} {B} φ F i h =
 vv-equivs-are-equivs φ
  (λ b → ∥∥-rec (being-singleton-is-prop fe)
          (λ t →
            equiv-to-singleton (fibers b t) (equivs-are-vv-equivs _ i (b , t)))
          (h b))
 where
  T : (Σ a ꞉ A , F (φ a)) → Σ F
  T = pair-fun {A = λ a → F (φ a)} {B = F} φ (λ a t → t)

  fibers : (b : B) (t : F b) → fiber φ b ≃ fiber T (b , t)
  fibers b t =
   ≃-sym (pair-fun-fiber-≃ {A = λ a → F (φ a)} {B = F} φ (λ a t → t) b t
          ● (pr₁ , pr₁-is-equiv (fiber φ b) _
              (λ _ → singleton-types'-are-singletons _)))

\end{code}

Lemma D.

\begin{code}

lemma-D
 : ((A : 𝓤 ̇ ) → is-prop A → is-modal A)
 → {W X Y : 𝓤 ̇ } (p : W → X) (s : X → Y)
 → is-surjection p
 → is-étale p
 → is-étale (s ∘ p)
 → is-étale s
lemma-D props-are-modal {W} {X} {Y} p s p-is-surjection p-is-étale q-is-étale =
 rl-implication (étale-iff-fiberwise-equiv s) γ
 where
  R : Reflection-Square (s ∘ p)
  R = (○-map s ∘ ○-map p) ,
      (λ w → ap (○-map s) (○-map-on-units p w) ∙ ○-map-on-units s (p w))

  ○p-is-surjection : is-surjection (○-map p)
  ○p-is-surjection u =
   ∥∥-rec ∥∥-is-prop
    (λ (x , ρ) → ∥∥-functor
                  (λ (w , σ) → η W w , (○-map-on-units p w ∙ ap (η X) σ ∙ ρ))
                  (p-is-surjection x))
    (units-are-surjective props-are-modal X u)

  γ : (y : Y) → is-equiv (étale-fiber-map s y)
  γ y = equivalences-descend-along-surjective-families φ F T-is-equiv
         (λ b → ○p-is-surjection (pr₁ b))
   where
    φ : fiber s y → fiber (○-map s) (η Y y)
    φ = étale-fiber-map s y

    F : fiber (○-map s) (η Y y) → 𝓤 ̇
    F b = fiber (○-map p) (pr₁ b)

    T : (Σ a ꞉ fiber s y , F (φ a)) → Σ F
    T = pair-fun {A = λ a → F (φ a)} {B = F} φ (λ a t → t)

    e₁ = fiber-of-composite p s y
    e₂ = Σ-cong
     (λ (a : fiber s y) → étale-maps-have-fibers-of-○-map p p-is-étale (pr₁ a))
    e₃ = fiber-of-composite (○-map p) (○-map s) (η Y y)

    Θ : fiber (s ∘ p) y → fiber (○-map s ∘ ○-map p) (η Y y)
    Θ = square-fiber-map (s ∘ p) R y

    key : (v : ○ W) (u : ○ X) (ρ : ○-map p v ＝ u) (α : ○-map s u ＝ η Y y)
        → _＝_ {_} {Σ F} ((u , α) , (v , ρ))
           ((○-map p v , (ap (○-map s) ρ ∙ α)) , (v , refl))
    key v .(○-map p v) refl α =
     ap (λ - → ((○-map p v , -) , (v , refl))) (refl-left-neutral ⁻¹)

    square : (z : fiber (s ∘ p) y) → T (⌜ e₁ ● e₂ ⌝ z) ＝ ⌜ e₃ ⌝ (Θ z)
    square (w , r) =
     key (η W w) (η X (p w)) (○-map-on-units p w)
      (○-map-on-units s (p w) ∙ ap (η Y) r)
     ∙ ap (λ - → ((○-map p (η W w) , -) , (η W w , refl)))
          ((∙assoc (ap (○-map s) (○-map-on-units p w)) (○-map-on-units s (p w))
             (ap (η Y) r))⁻¹)

    T-is-equiv : is-equiv T
    T-is-equiv =
     ≃-2-out-of-3-right (⌜⌝-is-equiv (e₁ ● e₂))
      (equiv-closed-under-∼ (⌜ e₃ ⌝ ∘ Θ) (T ∘ ⌜ e₁ ● e₂ ⌝)
        (∘-is-equiv
          (étale-maps-have-equivalences-on-fibers (s ∘ p) q-is-étale R y)
                    (⌜⌝-is-equiv e₃))
        square)

\end{code}
