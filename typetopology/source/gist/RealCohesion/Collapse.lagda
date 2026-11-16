Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Collapsing a type along a proposition (gate G25), §2.2 of Fable's note
on Shulman's Theorem 12.6 [1].

For a type X and a proposition Q, the collapse X^Q is the set quotient
of X + Q by the relation "a = b, or Q", with the propositional
disjunction. We use the large quotients of TypeTopology's
Quotient.Large, which are effective. Write η x for the class of inl x.

 * (C1) If η x = η x', then x = x' or Q (collapse-η-reflects).

 * (C2) If Q holds, the collapse is contractible, whatever X is, even
   if X is empty: the class of inr q is a centre (collapse-is-singleton).
   This is why the summand Q is there.

 * (C3) An equivalence X ≃ Y gives an equivalence of the collapses
   along the same Q (collapse-≃).

The collapse replaces the van Kampen theorem in the proof of Shulman's
Theorem 12.6 for the square: an identification η x = η x' with x ≠ x'
can only be forced by Q.

[1] Claude Fable 5.2. Note: Shulman's approximate Brouwer theorem (12.6)
    without the shape modality. Revision 2, 12 November 2026, audited
    by GPT-6 Astra.
    references/F11-shulman-12-6-rev2.md

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.Collapse
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import MLTT.Plus-Properties using (inl-lc)
open import UF.Base
open import UF.Equiv
open import UF.Sets
open import Quotient.Type using (EqRel)
open import Quotient.Large pt fe pe using (module large-quotient)

open PropositionalTruncation pt

\end{code}

The relation and the quotient.

\begin{code}

module _ {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) {Q : 𝓥 ̇ } (Q-is-prop : is-prop Q) where

 collapse-relation : X ∔ Q → X ∔ Q → 𝓤 ⊔ 𝓥 ̇
 collapse-relation a b = (a ＝ b) ∨ Q

 collapse-eqrel : EqRel {𝓤 ⊔ 𝓥} {𝓤 ⊔ 𝓥} (X ∔ Q)
 collapse-eqrel =
  collapse-relation , (λ a b → ∨-is-prop) , (λ a → ∣ inl refl ∣) ,
                  symm , trans
  where
   symm : (a b : X ∔ Q) → collapse-relation a b → collapse-relation b a
   symm a b = ∥∥-functor (cases (λ e → inl (e ⁻¹)) inr)

   trans : (a b c : X ∔ Q) → collapse-relation a b → collapse-relation b c
         → collapse-relation a c
   trans a b c r s = ∥∥-rec ∨-is-prop γ r
    where
     γ : (a ＝ b) ∔ Q → collapse-relation a c
     γ (inl e) = transport (λ - → collapse-relation - c) (e ⁻¹) s
     γ (inr q) = ∣ inr q ∣

 private
  module CQ = large-quotient (X ∔ Q) collapse-eqrel

 Collapse : (𝓤 ⊔ 𝓥) ⁺ ̇
 Collapse = CQ.X/≈

 collapse-is-set : is-set Collapse
 collapse-is-set = CQ.X/≈-is-set

 collapse-class : X ∔ Q → Collapse
 collapse-class = CQ.η

 collapse-η : X → Collapse
 collapse-η x = CQ.η (inl x)

 collapse-induction : {𝓦 : Universe} (P : Collapse → 𝓦 ̇ )
                    → ((c : Collapse) → is-prop (P c))
                    → ((a : X ∔ Q) → P (collapse-class a))
                    → (c : Collapse) → P c
 collapse-induction = CQ.quotient-induction

 collapse-class-respects : {a b : X ∔ Q} → collapse-relation a b
                         → collapse-class a ＝ collapse-class b
 collapse-class-respects = CQ.η-identifies-related-points

 collapse-η-reflects : (x x' : X) → collapse-η x ＝ collapse-η x' → (x ＝ x') ∨ Q
 collapse-η-reflects x x' e = ∥∥-functor (cases (λ d → inl (inl-lc d)) inr)
                               (CQ.η-relates-identified-points e)

 collapse-is-singleton : Q → is-singleton Collapse
 collapse-is-singleton q = collapse-class (inr q) ,
                           collapse-induction (λ c → collapse-class (inr q) ＝ c)
                            (λ c → collapse-is-set)
                            (λ a → collapse-class-respects ∣ inr q ∣)

 collapse-universal
  : {𝓦 : Universe} (A : 𝓦 ̇ ) → is-set A → (f : X ∔ Q → A)
  → ({a b : X ∔ Q} → collapse-relation a b → f a ＝ f b)
  → Σ f' ꞉ (Collapse → A) , f' ∘ collapse-class ∼ f
 collapse-universal A A-is-set f r = pr₁ (CQ.universal-property A A-is-set f r)

\end{code}

An equivalence of the types gives an equivalence of the collapses: the
map u ↦ class (e u) on X + Q respects the relation, and so does the map
for the inverse of e; their composites fix every class, by induction,
since the collapse is a set.

\begin{code}

module _ {𝓤 𝓤' 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ } {Q : 𝓥 ̇ }
         (Q-is-prop : is-prop Q) where

 private
  sum-map : (X → Y) → X ∔ Q → Y ∔ Q
  sum-map h (inl x) = inl (h x)
  sum-map h (inr q) = inr q

  sum-map-respects : (h : X → Y) {a b : X ∔ Q}
                   → collapse-relation X Q-is-prop a b
                   → collapse-relation Y Q-is-prop (sum-map h a) (sum-map h b)
  sum-map-respects h = ∥∥-functor (cases (λ e → inl (ap (sum-map h) e)) inr)

  collapse-map-data
   : (h : X → Y)
   → Σ f' ꞉ (Collapse X Q-is-prop → Collapse Y Q-is-prop)
          , f' ∘ collapse-class X Q-is-prop ∼ collapse-class Y Q-is-prop
          ∘ sum-map h
  collapse-map-data h =
   collapse-universal X Q-is-prop (Collapse Y Q-is-prop)
    (collapse-is-set Y Q-is-prop)
    (collapse-class Y Q-is-prop ∘ sum-map h)
    (λ r → collapse-class-respects Y Q-is-prop (sum-map-respects h r))

  collapse-map : (X → Y) → Collapse X Q-is-prop → Collapse Y Q-is-prop
  collapse-map h = pr₁ (collapse-map-data h)

  collapse-map-on-classes : (h : X → Y) (a : X ∔ Q)
                          → collapse-map h (collapse-class X Q-is-prop a)
                            ＝ collapse-class Y Q-is-prop (sum-map h a)
  collapse-map-on-classes h = pr₂ (collapse-map-data h)

 collapse-≃ : X ≃ Y → Collapse X Q-is-prop ≃ Collapse Y Q-is-prop
 collapse-≃ e = qinveq (collapse-map ⌜ e ⌝) (back , I , II)
  where
   inverse-sum : Y ∔ Q → X ∔ Q
   inverse-sum (inl y) = inl (⌜ e ⌝⁻¹ y)
   inverse-sum (inr q) = inr q

   inverse-respects : {a b : Y ∔ Q} → collapse-relation Y Q-is-prop a b
                    → collapse-relation X Q-is-prop (inverse-sum a)
                       (inverse-sum b)
   inverse-respects = ∥∥-functor (cases (λ d → inl (ap inverse-sum d)) inr)

   back-data : Σ f' ꞉ (Collapse Y Q-is-prop → Collapse X Q-is-prop)
                    , f' ∘ collapse-class Y Q-is-prop
                    ∼ collapse-class X Q-is-prop ∘ inverse-sum
   back-data = collapse-universal Y Q-is-prop (Collapse X Q-is-prop)
                (collapse-is-set X Q-is-prop)
                (collapse-class X Q-is-prop ∘ inverse-sum)
                (λ r → collapse-class-respects X Q-is-prop (inverse-respects r))

   back : Collapse Y Q-is-prop → Collapse X Q-is-prop
   back = pr₁ back-data

   back-on-classes : (a : Y ∔ Q) → back (collapse-class Y Q-is-prop a)
                     ＝ collapse-class X Q-is-prop (inverse-sum a)
   back-on-classes = pr₂ back-data

   I : back ∘ collapse-map ⌜ e ⌝ ∼ id
   I = collapse-induction X Q-is-prop (λ c → back (collapse-map ⌜ e ⌝ c) ＝ c)
        (λ c → collapse-is-set X Q-is-prop) γ
    where
     γ : (a : X ∔ Q) → back (collapse-map ⌜ e ⌝ (collapse-class X Q-is-prop a))
                       ＝ collapse-class X Q-is-prop a
     γ (inl x) = ap back (collapse-map-on-classes ⌜ e ⌝ (inl x))
               ∙ back-on-classes (inl (⌜ e ⌝ x))
               ∙ ap (collapse-class X Q-is-prop ∘ inl)
                    (inverses-are-retractions ⌜ e ⌝ ⌜ e ⌝-is-equiv x)
     γ (inr q) =
      ap back (collapse-map-on-classes ⌜ e ⌝ (inr q)) ∙ back-on-classes (inr q)

   II : collapse-map ⌜ e ⌝ ∘ back ∼ id
   II = collapse-induction Y Q-is-prop (λ c → collapse-map ⌜ e ⌝ (back c) ＝ c)
         (λ c → collapse-is-set Y Q-is-prop) γ
    where
     γ : (a : Y ∔ Q) → collapse-map ⌜ e ⌝ (back (collapse-class Y Q-is-prop a))
                       ＝ collapse-class Y Q-is-prop a
     γ (inl y) = ap (collapse-map ⌜ e ⌝) (back-on-classes (inl y))
               ∙ collapse-map-on-classes ⌜ e ⌝ (inl (⌜ e ⌝⁻¹ y))
               ∙ ap (collapse-class Y Q-is-prop ∘ inl)
                    (inverses-are-sections ⌜ e ⌝ ⌜ e ⌝-is-equiv y)
     γ (inr q) = ap (collapse-map ⌜ e ⌝) (back-on-classes (inr q))
               ∙ collapse-map-on-classes ⌜ e ⌝ (inr q)

\end{code}
