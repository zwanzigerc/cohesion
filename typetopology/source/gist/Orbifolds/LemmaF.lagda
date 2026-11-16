Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. Orbifold gate H5 of Fable's roadmap [1].

Lemma F and Corollary F′: étale descent
---------------------------------------

Lemma F is Claude Fable 5.2's [1, Section 3.3; 2], audited by GPT-6
Astra [3, Section 2]; Corollary F′ is Astra's [3, Section 5], read by
Fable [1, Section 11].

  Lemma F. Let ○ be a modality that preserves crisp pullbacks. Let
  f : A → B be a crisp map of crisp types, K = A ×_B A, and p₂ : K → A
  the second projection. If f is surjective and p₂ is étale, then f is
  étale.

  Corollary F′. Let e : F → O be a crisp surjection of crisp sets with
  F modal. Then O is modal.

Crispness enters only through the hypothesis that ○ preserves the
crisp pullback K [3, Section 2]. This module therefore proves both for
any map whose kernel pair ○ preserves, without --cohesion:

  lemma-F : (f : A → B) → ○-preserves-pullback f f → is-surjection f
          → is-étale (pullback.pb₂ f f) → is-étale f
  corollary-F′ : (propositions are modal) → (e : F → O)
               → ○-preserves-pullback e e → is-surjection e → is-set O
               → is-modal F → is-modal O

and CrispLemmaF derives the printed forms from the hypothesis that ○
preserves crisp pullbacks (core item 4 for ℑ). "Preserves the pullback"
means that the canonical comparison ○ (A ×_C B) → ○A ×_(○C) ○B
(pullback-comparison) is an equivalence; on units it is Astra's map
η (a , b , p) ↦ (η a , η b , ν⁻¹ · ap η p · ν). Corollary F′ needs
that propositions are modal, true for nullifications at pointed types
(Nullification), and of the two types only O needs to be a set.

The proof of Lemma F follows [2] and [3]: the gap map of f is checked
on fibres; over b = f a₀ (surjectivity, inside the proposition that the
fibre map is an equivalence) the fibre of f is the fibre of p₂ over
a₀, the étale square of p₂ identifies it with the fibre of ○p₂ over
η a₀, the preserved pullback identifies that with the fibre of the
second projection of ○A ×_(○B) ○A, and that is the fibre of ○f over
η (f a₀). The point Astra stresses is that the composite of these
identifications is the canonical fibre map of the gap map of f, not
merely some equivalence of the same types (square below). The
homotopy between the comparison map and ○p₂ is chosen through
homotopy-precomp-η-equiv, as in Modalities, so that its values at
units are known.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Sections 3.3, 5 and 11.
    references/F01-orbifolds-roadmap-rev2.md
[2] Claude Fable 5.2. Audit request: étale descent from crisp pullback
    preservation, and microlinearity along étale maps, 11 November 2026,
    Section 3.3.
    references/F08-lemmas-F-G.md
[3] GPT-6 Astra. Audit of Fable's Lemmas F and G, 12 November 2026.
    references/A05-lemmas-F-G-audit.txt

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import Modal.Subuniverse

module gist.Orbifolds.LemmaF
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        {𝓤 𝓥 : Universe}
        (P : subuniverse 𝓤 𝓥)
        (P-is-reflective : subuniverse-is-reflective P)
        (P-is-sigma-closed : subuniverse-is-sigma-closed P)
        (P-is-replete : subuniverse-is-replete P)
       where

open PropositionalTruncation pt

open import Modal.SigmaClosedReflectiveSubuniverse
             P P-is-reflective P-is-sigma-closed
open import UF.Base
open import UF.Equiv
open import UF.Equiv-FunExt using (being-equiv-is-prop)
open import UF.EquivalenceExamples
open import UF.ImageAndSurjection pt using (is-surjection)
open import UF.PairFun
open import UF.Pullback
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import gist.RealCohesion.ReflectionMaps P P-is-reflective
 using (○-map ; ○-map-on-units)
open import gist.Orbifolds.Modalities
             fe pt P P-is-reflective P-is-sigma-closed P-is-replete

\end{code}

The canonical comparison of a pullback with the pullback of the
reflections.

\begin{code}

pullback-comparison-on-units
 : {A B C : 𝓤 ̇ } (f : A → C) (g : B → C)
 → pullback.pullback f g → pullback.pullback (○-map f) (○-map g)
pullback-comparison-on-units {A} {B} {C} f g ((a , b) , p) =
 (η A a , η B b) , (○-map-on-units f a ∙ ap (η C) p ∙ (○-map-on-units g b)⁻¹)

pullback-comparison
 : {A B C : 𝓤 ̇ } (f : A → C) (g : B → C)
 → ○ (pullback.pullback f g) → pullback.pullback (○-map f) (○-map g)
pullback-comparison {A} {B} {C} f g =
 ○-rec (pullback.pullback f g) (pullback.pullback (○-map f) (○-map g))
  (pullbacks-of-modal-types-are-modal' (○-map f) (○-map g)
    (○-is-modal A) (○-is-modal B) (○-is-modal C))
  (pullback-comparison-on-units f g)

○-preserves-pullback : {A B C : 𝓤 ̇ } (f : A → C) (g : B → C) → 𝓤 ̇
○-preserves-pullback f g = is-equiv (pullback-comparison f g)

transport-fiber-family
 : {X Y : 𝓤 ̇ } (g : X → Y) {y y' : Y} (p : y ＝ y') (x : X) (s : g x ＝ y)
                → transport (fiber g) p (x , s) ＝ (x , (s ∙ p))
transport-fiber-family g refl x s = refl

\end{code}

The construction for Lemma F: over a point f a₀, the canonical fibre
map of the gap map of f is a composite of equivalences.

\begin{code}

module lemma-F-construction
        {A B : 𝓤 ̇ } (f : A → B)
        (preservation : ○-preserves-pullback f f)
        (p₂-is-étale : is-étale (pullback.pb₂ f f))
       where

 K Q : 𝓤 ̇
 K = pullback.pullback f f
 Q = pullback.pullback (○-map f) (○-map f)

 p₂ : K → A
 p₂ = pullback.pb₂ f f

 q₂ : Q → ○ A
 q₂ = pullback.pb₂ (○-map f) (○-map f)

 Q-is-modal : is-modal Q
 Q-is-modal = pullbacks-of-modal-types-are-modal' (○-map f) (○-map f)
               (○-is-modal A) (○-is-modal A) (○-is-modal B)

 κ : ○ K → Q
 κ = pullback-comparison f f

 κ-on-units : κ ∘ η K ∼ pullback-comparison-on-units f f
 κ-on-units = ○-rec-compute K Q Q-is-modal (pullback-comparison-on-units f f)

 u : (a : A) → ○-map f (η A a) ＝ η B (f a)
 u = ○-map-on-units f

 h₀ : (q₂ ∘ κ) ∘ η K ∼ ○-map p₂ ∘ η K
 h₀ k = ap q₂ (κ-on-units k) ∙ (○-map-on-units p₂ k)⁻¹

 𝕙 : (q₂ ∘ κ ∼ ○-map p₂) ≃ ((q₂ ∘ κ) ∘ η K ∼ ○-map p₂ ∘ η K)
 𝕙 = homotopy-precomp-η-equiv fe K (○ A) (○-is-modal A) (q₂ ∘ κ) (○-map p₂)

 H : q₂ ∘ κ ∼ ○-map p₂
 H = ⌜ 𝕙 ⌝⁻¹ h₀

 Hη : (k : K) → H (η K k) ＝ h₀ k
 Hη = happly (≃-sym-is-rinv 𝕙 h₀)

 module _ (a₀ : A) where

  α : fiber p₂ a₀ → fiber f (f a₀)
  α = ⌜ fiber-of-pullback f f a₀ ⌝

  β : fiber p₂ a₀ → fiber (○-map p₂) (η A a₀)
  β = étale-fiber-map p₂ a₀

  δ : fiber (○-map p₂) (η A a₀) → fiber q₂ (η A a₀)
  δ (z , s) = κ z , (H z ∙ s)

  ε : fiber q₂ (η A a₀) → fiber (○-map f) (○-map f (η A a₀))
  ε = ⌜ fiber-of-pullback (○-map f) (○-map f) (η A a₀) ⌝

  ζ : fiber (○-map f) (○-map f (η A a₀)) → fiber (○-map f) (η B (f a₀))
  ζ = transport (fiber (○-map f)) (u a₀)

  composite-is-equiv : is-equiv (ζ ∘ ε ∘ δ ∘ β)
  composite-is-equiv =
   ∘-is-equiv (lr-implication (étale-iff-fiberwise-equiv p₂) p₂-is-étale a₀)
    (∘-is-equiv
      (pair-fun-is-equiv κ (λ z s → H z ∙ s) preservation
        (λ z → ∙-is-equiv-left (H z)))
      (∘-is-equiv
        ⌜ fiber-of-pullback (○-map f) (○-map f) (η A a₀) ⌝-is-equiv
        (transports-are-equivs (u a₀))))

  step-δ : (a : A) (q : f a ＝ f a₀)
         → δ (β (((a , a₀) , q) , refl))
         ＝[ fiber q₂ (η A a₀) ]
           (κ (η K ((a , a₀) , q)) , ap q₂ (κ-on-units ((a , a₀) , q)))
  step-δ a q = ap (λ - → κ (η K k) , (- ∙ ○-map-on-units p₂ k)) (Hη k)
               ∙ ap (λ - → κ (η K k) , -)
                    (inverse-cancels (ap q₂ (κ-on-units k))
                      (○-map-on-units p₂ k))
   where
    k : K
    k = (a , a₀) , q

  step-ζ : (a : A) (q : f a ＝ f a₀)
         → ζ (η A a , (u a ∙ ap (η B) q ∙ (u a₀)⁻¹))
         ＝[ fiber (○-map f) (η B (f a₀)) ]
           (η A a , (u a ∙ ap (η B) q))
  step-ζ a q =
   transport-fiber-family (○-map f) (u a₀) (η A a) (u a ∙ ap (η B) q ∙ (u a₀)⁻¹)
               ∙ ap (λ - → η A a , -)
                  (inverse-cancels (u a ∙ ap (η B) q) (u a₀))

  square : ζ ∘ ε ∘ δ ∘ β ∼ étale-fiber-map f (f a₀) ∘ α
  square (((a , .a₀) , q) , refl) =
   ap (λ - → ζ (ε -))
      (step-δ a q ∙ fiber-path q₂ (κ-on-units ((a , a₀) , q)))
   ∙ step-ζ a q

  étale-fiber-map-at-image : is-equiv (étale-fiber-map f (f a₀))
  étale-fiber-map-at-image =
   ≃-2-out-of-3-right ⌜ fiber-of-pullback f f a₀ ⌝-is-equiv
    (equiv-closed-under-∼ (ζ ∘ ε ∘ δ ∘ β) (étale-fiber-map f (f a₀) ∘ α)
      composite-is-equiv (λ w → (square w)⁻¹))

\end{code}

Lemma F.

\begin{code}

lemma-F : {A B : 𝓤 ̇ } (f : A → B)
        → ○-preserves-pullback f f
        → is-surjection f
        → is-étale (pullback.pb₂ f f)
        → is-étale f
lemma-F {A} {B} f preservation f-is-surjection p₂-is-étale =
 rl-implication (étale-iff-fiberwise-equiv f) γ
 where
  open lemma-F-construction f preservation p₂-is-étale

  γ : (b : B) → is-equiv (étale-fiber-map f b)
  γ b = ∥∥-rec (being-equiv-is-prop (λ 𝓤 𝓥 → fe) (étale-fiber-map f b))
         (λ (a₀ , p) → transport (λ - → is-equiv (étale-fiber-map f -)) p
                        (étale-fiber-map-at-image a₀))
         (f-is-surjection b)

\end{code}

Corollary F′.

\begin{code}

corollary-F′ : ((X : 𝓤 ̇ ) → is-prop X → is-modal X)
             → {F O : 𝓤 ̇ } (e : F → O)
             → ○-preserves-pullback e e
             → is-surjection e
             → is-set O
             → is-modal F
             → is-modal O
corollary-F′ props-are-modal {F} {O} e preservation e-is-surjection O-is-set
 F-is-modal =
 η-is-equiv-gives-is-modal P-is-replete O ηO-is-equiv
 where
  R-is-modal : is-modal (pullback.pullback e e)
  R-is-modal = P-is-sigma-closed (F × F) (λ z → e (pr₁ z) ＝ e (pr₂ z))
                (P-is-sigma-closed F (λ _ → F) F-is-modal (λ _ → F-is-modal))
                (λ z → props-are-modal _ O-is-set)

  e-is-étale : is-étale e
  e-is-étale = lemma-F e preservation e-is-surjection
                (maps-between-modal-types-are-étale (pullback.pb₂ e e)
                  R-is-modal F-is-modal)

  ○e-is-surjection : is-surjection (○-map e)
  ○e-is-surjection β' =
   ∥∥-rec ∥∥-is-prop
    (λ (b , p) → ∥∥-functor
                  (λ (a , q) → η F a , (○-map-on-units e a ∙ ap (η O) q ∙ p))
                  (e-is-surjection b))
    (units-are-surjective props-are-modal O β')

  pb₂-is-equiv : is-equiv (pullback.pb₂ (η O) (○-map e))
  pb₂-is-equiv =
   ≃-2-out-of-3-right e-is-étale (is-modal-gives-η-is-equiv fe F F-is-modal)

  ηO-is-equiv : is-equiv (η O)
  ηO-is-equiv = vv-equivs-are-equivs (η O) γ
   where
    γ : (β' : ○ O) → is-singleton (fiber (η O) β')
    γ β' = ∥∥-rec (being-singleton-is-prop fe)
            (λ (z , r) → transport (λ - → is-singleton (fiber (η O) -)) r
                          (equiv-to-singleton
                            (≃-sym (fiber-of-pullback (η O) (○-map e) z))
                            (equivs-are-vv-equivs _ pb₂-is-equiv z)))
            (○e-is-surjection β')

\end{code}
