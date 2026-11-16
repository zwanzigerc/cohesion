Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time). Orbifold gate H10 of Fable's
roadmap [1], for the target T5b, following GPT-6 Astra's proof [2,
Sections 1–3], Fable's order of steps [3, Section 1, item 3] and Astra's
preflight [4, Sections B and C].

Orbit sets, and modal objects and arrows
----------------------------------------

Let G be a pregroupoid whose objects form a set, with anchor a = (s , t).

  orbit-relations-are-decidable : if a is Dubuc–Penon proper, then the
  orbit relation ∥ G(x , y) ∥ is decidable: it is a surjective image of
  the fibre of a over (x , y), which is compact, and compact propositions
  are decidable;

  crisp-orbit-deciders : the type of such decision families is a crisp
  proposition when G is crisp, so by Axiom C1 an ordinary decision family
  gives a crisp one, under ♭ (C1Discreteness). Only then is the orbit
  set formed, so that it is crisp [3, item 3];

  Orbit-Set G d, orbit : for a decision family d, the image of
  x ↦ (y ↦ [d x y]) in G₀ → 𝟚, with its surjection from G₀. It is a
  small set; orbits-are-effective: orbit x ＝ orbit y exactly when x and
  y are related; orbit-sets-have-decidable-equality, by two mere
  representatives and effectiveness;

  fibres-of-the-source-map-cover-orbits : the target map from the source
  fibre over x onto the orbit of x, a crisp surjection when G, d and x
  are crisp;

  orbits-are-modal, objects-are-modal, arrows-are-modal : with ℑ the
  nullification on 𝓤 ⁺ and the source map ℑ-étale (lifted to 𝓤 ⁺), the
  orbit set is ℑ-modal by K; every source fibre is ℑ-modal; at a crisp
  object the orbit is a crisp surjective image of its source fibre, so
  ℑ-modal by Corollary F′ (CrispLemmaF); at an ordinary point of the
  orbit set, which is ♭-discrete by C1, the point is first made crisp,
  then a crisp inhabitant of the crisp proposition ∥ fibre ∥ is obtained
  by C1, and the crisp truncation is opened inside the proposition to be
  proved (CrispTruncation) [2, Section 3; 4, Section C]. So G₀, the sum
  of the orbits over the orbit set, and G₁, the sum of the source fibres
  over G₀, are ℑ-modal. No orbit representative is chosen globally.

The small types are lifted to 𝓤 ⁺ for the one modality, with explicit
equivalences; no second reflector is used.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] GPT-6 Astra. DP properness implies the replacement over the
    five-item core, 11 November 2026.
    references/A02-dp-properness-implies-replacement.txt
[3] Claude Fable 5.2. Orbifolds H9 and H10: follow-up to Astra's
    readiness audits, 13 November 2026 (UTC).
    references/F04-orbifolds-h9-h10-followup.md
[4] GPT-6 Astra. H10 T5b implementation preflight, 13 November 2026
    (UTC).
    references/A24-t5b-preflight.txt

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import Modal.Subuniverse
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.OrbitSets
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ 𝓡 : Commutative-Ring)
        {@♭ 𝓤 : Universe}
       where

open import MLTT.Two-Properties using (zero-is-not-one)
open import UF.Base
open import UF.DiscreteAndSeparated using (is-discrete ; 𝟚-is-set)
open import UF.Equiv
open import UF.EquivalenceExamples using (Σ-cong ; domain-is-total-fiber)
open import UF.ImageAndSurjection pt using (is-surjection)
open import UF.Sets
open import UF.Sets-Properties using (Σ-is-set ; Π-is-set ; equiv-to-set)
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties using (props-are-sets)
open import UF.UniverseEmbedding using (Lift ; lift ; lower ; Lift-≃)
open import gist.CohesiveApartness.Flat
 using (♭ ; _^♭ ; ♭-counit ; is-♭-discrete ; Axiom-C1)

open PropositionalTruncation pt
open smooth-line fe pt 𝓡
open import gist.Orbifolds.RezkCompletion fe pt {𝓤} {𝓤}
open import gist.Orbifolds.CoverFiniteness fe pt using (anchor)
open import gist.Orbifolds.DubucPenon fe pt
open import gist.Orbifolds.C1Discreteness fe
open import gist.Orbifolds.CrispTruncation fe pt using (crisp-∥∥-rec)
open import gist.Orbifolds.Microlinearity fe pt 𝓡 {𝓤 ⁺}
 using (ℑ-generator ; ℑ-generator-point ; discrete-types-are-ℑ-modal)
open import gist.Orbifolds.Nullification fe
 using
  (is-nullification ; nullifications-are-Σ-closed ; nullifications-are-replete)

\end{code}

The orbit relation, and its decisions under Dubuc–Penon properness.

\begin{code}

module _ (G : Pregroupoid) where

 open Pregroupoid G

 orbit-relation : ob → ob → 𝓤 ̇
 orbit-relation x y = ∥ hom x y ∥

 Orbit-Decider : 𝓤 ̇
 Orbit-Decider = (x y : ob) → is-decidable (orbit-relation x y)

 being-an-orbit-decider-is-prop : is-prop Orbit-Decider
 being-an-orbit-decider-is-prop =
  Π₂-is-prop fe (λ x y → decidability-of-prop-is-prop fe ∥∥-is-prop)

 orbit-relations-are-decidable
  : is-set ob → is-DP-proper (anchor G) → Orbit-Decider
 orbit-relations-are-decidable ob-is-set p x y =
  DP-compact-propositions-are-decidable ∥∥-is-prop
   (DP-compactness-is-preserved-by-surjections h h-is-surjection
     (DP-proper-maps-have-DP-compact-fibres (anchor G)
       (×-is-set ob-is-set ob-is-set) p (x , y)))
  where
   h : fiber (anchor G) (x , y) → orbit-relation x y
   h ((x' , y' , g) , q) = ∣ transport₂ hom (ap pr₁ q) (ap pr₂ q) g ∣

   h-is-surjection : is-surjection h
   h-is-surjection t =
    ∥∥-functor (λ g → ((x , y , g) , refl) , ∥∥-is-prop _ _) t

\end{code}

The orbit set of a decision family.

\begin{code}

 module _ (d : Orbit-Decider) where

  χ : ob → ob → 𝟚
  χ x y = cases (λ _ → ₁) (λ _ → ₀) (d x y)

  Orbit-Set : 𝓤 ̇
  Orbit-Set = Σ φ ꞉ (ob → 𝟚) , ∃ x ꞉ ob , χ x ＝ φ

  orbit : ob → Orbit-Set
  orbit x = χ x , ∣ x , refl ∣

  orbit-is-surjection : is-surjection orbit
  orbit-is-surjection (φ , e) =
   ∥∥-functor (λ (x , p) → x , to-subtype-＝ (λ _ → ∃-is-prop) p) e

  orbit-sets-are-sets : is-set Orbit-Set
  orbit-sets-are-sets =
   Σ-is-set (Π-is-set fe (λ _ → 𝟚-is-set)) (λ _ → props-are-sets ∃-is-prop)

  private
   related-from-χ : (x y : ob) → χ x y ＝ ₁ → orbit-relation x y
   related-from-χ x y = γ (d x y)
    where
     γ : (e : is-decidable (orbit-relation x y))
       → cases (λ _ → ₁) (λ _ → ₀) e ＝ ₁ → orbit-relation x y
     γ (inl r) _ = r
     γ (inr ν) q = 𝟘-elim (zero-is-not-one q)

   χ-from-related : (x y : ob) → orbit-relation x y → χ x y ＝ ₁
   χ-from-related x y r = γ (d x y)
    where
     γ : (e : is-decidable (orbit-relation x y))
       → cases (λ _ → ₁) (λ _ → ₀) e ＝ ₁
     γ (inl _) = refl
     γ (inr ν) = 𝟘-elim (ν r)

   compose : {x y z : ob} → orbit-relation x y → orbit-relation y z
           → orbit-relation x z
   compose = ∥∥-functor₂ (λ f g → comp g f)

   reverse : {x y : ob} → orbit-relation x y → orbit-relation y x
   reverse = ∥∥-functor inv

   χ-agrees : (x y : ob) → orbit-relation x y → (z : ob) → χ x z ＝ χ y z
   χ-agrees x y r z = γ (d x z) (d y z)
    where
     γ : (e : is-decidable (orbit-relation x z))
         (e' : is-decidable (orbit-relation y z))
       → cases (λ _ → ₁) (λ _ → ₀) e ＝ cases (λ _ → ₁) (λ _ → ₀) e'
     γ (inl a) (inl b) = refl
     γ (inl a) (inr b) = 𝟘-elim (b (compose (reverse r) a))
     γ (inr a) (inl b) = 𝟘-elim (a (compose r b))
     γ (inr a) (inr b) = refl

  orbits-are-effective : (x y : ob) → (orbit x ＝ orbit y) ↔ orbit-relation x y
  orbits-are-effective x y =
   (λ p →
     related-from-χ x y (happly (ap pr₁ p) y ∙ χ-from-related y y ∣ idn y ∣)) ,
   (λ r → to-subtype-＝ (λ _ → ∃-is-prop) (dfunext fe (χ-agrees x y r)))

  orbit-sets-have-decidable-equality : is-discrete Orbit-Set
  orbit-sets-have-decidable-equality z z' =
   ∥∥-rec (decidability-of-prop-is-prop fe orbit-sets-are-sets)
    (λ (x , p) →
      ∥∥-rec (decidability-of-prop-is-prop fe orbit-sets-are-sets)
       (λ (x' , p') →
         transport₂ (λ a b → is-decidable (a ＝ b)) p p'
          (cases (λ r → inl (rl-implication (orbits-are-effective x x') r))
                 (λ ν →
                   inr (λ q → ν (lr-implication (orbits-are-effective x x') q)))
                 (d x x')))
       (orbit-is-surjection z'))
    (orbit-is-surjection z)

\end{code}

The target map from a source fibre onto an orbit.

\begin{code}

  fibre-to-orbit : (x : ob) → fiber (source G) x → fiber orbit (orbit x)
  fibre-to-orbit x ((x' , y , g) , p) =
   y , rl-implication (orbits-are-effective y x)
        (reverse ∣ transport (λ - → hom - y) p g ∣)

  fibres-of-the-source-map-cover-orbits
   : (x : ob) → is-surjection (fibre-to-orbit x)
  fibres-of-the-source-map-cover-orbits x (y , q) =
   ∥∥-functor
    (λ g → ((x , y , g) , refl) , to-subtype-＝ (λ _ → orbit-sets-are-sets) refl)
    (reverse (lr-implication (orbits-are-effective y x) q))

\end{code}

Crisp decision families, by Axiom C1.

\begin{code}

crisp-orbit-deciders
 : {𝓙 𝓖 : Universe} {J : 𝓙 ̇ } {Gen : J → 𝓖 ̇ } → Axiom-C1 Gen
 → (@♭ G : Pregroupoid) → Orbit-Decider G → ♭ (Orbit-Decider G)
crisp-orbit-deciders c1 G d =
 crisp-witnesses c1 (Orbit-Decider G) (being-an-orbit-decider-is-prop G) d

\end{code}

Modality: orbits, objects and arrows.

\begin{code}

module _ {𝓟 : Universe}
         (K : Postulate-K)
         (P : subuniverse (𝓤 ⁺) 𝓟)
         (P-is-reflective : subuniverse-is-reflective P)
         (ν : is-nullification ℑ-generator ℑ-generator-point P)
       where

 private
  P-is-Σ-closed : subuniverse-is-sigma-closed P
  P-is-Σ-closed = nullifications-are-Σ-closed ℑ-generator ℑ-generator-point P ν

 open import gist.Orbifolds.Modalities fe pt P P-is-reflective
              (nullifications-are-Σ-closed ℑ-generator ℑ-generator-point P ν)
              (nullifications-are-replete ℑ-generator ℑ-generator-point P ν)
  using (is-étale ; fibers-of-étale-maps-are-modal ;
          modal-types-are-closed-under-equivalence)
  public
 open import gist.Orbifolds.CrispLemmaF fe pt {𝓤 ⁺} P P-is-reflective
              (nullifications-are-Σ-closed ℑ-generator ℑ-generator-point P ν)
              (nullifications-are-replete ℑ-generator ℑ-generator-point P ν)
  using (○-preserves-crisp-pullbacks ; corollary-F′-for-nullifications) public

 is-ℑ-modal : 𝓤 ̇ → 𝓟 ̇
 is-ℑ-modal X = subuniverse-contains P (Lift (𝓤 ⁺) X)

 lifts-of-discrete-types-are-discrete : {X : 𝓤 ̇ } → is-discrete X
                                      → is-discrete (Lift (𝓤 ⁺) X)
 lifts-of-discrete-types-are-discrete d u v =
  cases (λ p → inl (ap (lift (𝓤 ⁺)) p)) (λ n → inr (λ q → n (ap lower q)))
   (d (lower u) (lower v))

 module _ (π : ○-preserves-crisp-pullbacks)
          {𝓙 𝓖 : Universe} {J : 𝓙 ̇ } {Gen : J → 𝓖 ̇ } (c1 : Axiom-C1 Gen)
          (@♭ G : Pregroupoid)
          (ob-is-set : is-set (Pregroupoid.ob G))
          (s-is-étale : is-étale
            (λ (z : Lift (𝓤 ⁺) (arrows G)) → lift (𝓤 ⁺) (source G (lower z))))
        where


  private
   s̄ : Lift (𝓤 ⁺) (arrows G) → Lift (𝓤 ⁺) (Pregroupoid.ob G)
   s̄ z = lift (𝓤 ⁺) (source G (lower z))

  source-fibres-are-modal : (x : (Pregroupoid.ob G))
                          → is-ℑ-modal (fiber (source G) x)
  source-fibres-are-modal x =
   modal-types-are-closed-under-equivalence (≃-sym e)
    (fibers-of-étale-maps-are-modal s̄ s-is-étale (lift (𝓤 ⁺) x))
   where
    e : fiber s̄ (lift (𝓤 ⁺) x) ≃ Lift (𝓤 ⁺) (fiber (source G) x)
    e = qinveq (λ (z , p) → lift (𝓤 ⁺) (lower z , ap lower p))
         ((λ w → lift (𝓤 ⁺) (pr₁ (lower w)) , ap (lift (𝓤 ⁺)) (pr₂ (lower w))) ,
          (λ (z , p) → to-Σ-＝ (refl , ap-lift-lower p)) ,
          (λ w →
            ap (lift (𝓤 ⁺)) (to-Σ-＝ (refl , ap-lower-lift (pr₂ (lower w))))))
     where
      ap-lift-lower : {u v : Lift (𝓤 ⁺) (Pregroupoid.ob G)} (p : u ＝ v)
                    → ap (lift (𝓤 ⁺)) (ap lower p) ＝ p
      ap-lift-lower refl = refl
      ap-lower-lift : {u v : (Pregroupoid.ob G)} (p : u ＝ v)
                    → ap lower (ap (lift (𝓤 ⁺)) p) ＝ p
      ap-lower-lift refl = refl

  module _ (@♭ d : Orbit-Decider G) where

   orbit-sets-are-modal : is-ℑ-modal (Orbit-Set G d)
   orbit-sets-are-modal =
    discrete-types-are-ℑ-modal P P-is-reflective ν K
     (Lift (𝓤 ⁺) (Orbit-Set G d))
     (lifts-of-discrete-types-are-discrete
       (orbit-sets-have-decidable-equality G d))

   private
    orbits-at-crisp-objects : (@♭ x : (Pregroupoid.ob G))
                            → is-ℑ-modal (fiber (orbit G d) (orbit G d x))
    orbits-at-crisp-objects x =
     corollary-F′-for-nullifications ℑ-generator ℑ-generator-point ν π
      (λ (w : Lift (𝓤 ⁺) (fiber (source G) x)) →
        lift (𝓤 ⁺) (fibre-to-orbit G d x (lower w)))
      (λ w → ∥∥-functor (λ (v , p) → lift (𝓤 ⁺) v , ap (lift (𝓤 ⁺)) p)
              (fibres-of-the-source-map-cover-orbits G d x (lower w)))
      (equiv-to-set (Lift-≃ (𝓤 ⁺) _)
        (Σ-is-set ob-is-set (λ _ → props-are-sets (orbit-sets-are-sets G d))))
      (source-fibres-are-modal x)

    being-modal-is-prop : (X : 𝓤 ̇ ) → is-prop (is-ℑ-modal X)
    being-modal-is-prop X = pr₂ P (Lift (𝓤 ⁺) X)

    orbits-are-modal-at : (u : ♭ (Orbit-Set G d))
                        → is-ℑ-modal (fiber (orbit G d) (♭-counit u))
    orbits-are-modal-at (z ^♭) =
     γ (crisp-witnesses c1 ∥ fiber (orbit G d) z ∥ ∥∥-is-prop
         (orbit-is-surjection G d z))
     where
      γ : ♭ ∥ fiber (orbit G d) z ∥ → is-ℑ-modal (fiber (orbit G d) z)
      γ (t ^♭) =
       crisp-∥∥-rec (being-modal-is-prop _)
        (λ (@♭ w) → transport (λ - → is-ℑ-modal (fiber (orbit G d) -)) (pr₂ w)
                     (orbits-at-crisp-objects (pr₁ w)))
        t

   orbits-are-modal : (z : Orbit-Set G d) → is-ℑ-modal (fiber (orbit G d) z)
   orbits-are-modal z =
    transport (λ - → is-ℑ-modal (fiber (orbit G d) -))
     (inverses-are-sections ♭-counit e z)
     (orbits-are-modal-at (inverse ♭-counit e z))
    where
     e : is-♭-discrete (Orbit-Set G d)
     e = types-with-decidable-equality-are-♭-discrete c1 (Orbit-Set G d)
          (orbit-sets-have-decidable-equality G d)

   private
    lift-sums : {A : 𝓤 ̇ } (F : A → 𝓤 ̇ )
              → (Σ F) ≃ (Σ w ꞉ Lift (𝓤 ⁺) A , Lift (𝓤 ⁺) (F (lower w)))
    lift-sums F = qinveq (λ (a , v) → lift (𝓤 ⁺) a , lift (𝓤 ⁺) v)
                   ((λ (w , u) → lower w , lower u) , (λ _ → refl) ,
                     (λ _ → refl))

    lift-of : {A B : 𝓤 ̇ } → A ≃ B → Lift (𝓤 ⁺) A ≃ B
    lift-of e = Lift-≃ (𝓤 ⁺) _ ● e

   objects-are-modal : is-ℑ-modal (Pregroupoid.ob G)
   objects-are-modal =
    modal-types-are-closed-under-equivalence
     (Lift-≃ (𝓤 ⁺) (Pregroupoid.ob G) ● domain-is-total-fiber (orbit G d) ●
       lift-sums (fiber (orbit G d)))
     (P-is-Σ-closed (Lift (𝓤 ⁺) (Orbit-Set G d))
       (λ w → Lift (𝓤 ⁺) (fiber (orbit G d) (lower w)))
       orbit-sets-are-modal (λ w → orbits-are-modal (lower w)))

   arrows-are-modal : is-ℑ-modal (arrows G)
   arrows-are-modal =
    modal-types-are-closed-under-equivalence
     (Lift-≃ (𝓤 ⁺) (arrows G) ● domain-is-total-fiber (source G) ● lift-sums
       (fiber (source G)))
     (P-is-Σ-closed (Lift (𝓤 ⁺) (Pregroupoid.ob G))
       (λ w → Lift (𝓤 ⁺) (fiber (source G) (lower w)))
       objects-are-modal (λ w → source-fibres-are-modal (lower w)))

\end{code}
