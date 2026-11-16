Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026; one sentence updated 13 November 2026,
after the final audits. Orbifold gate H3 of Fable's roadmap [2].

The modality layer: connected maps and étale maps
-------------------------------------------------

The roadmap [2, Section 3.2] assumes a modality ○ (for the orbifolds,
the infinitesimal shape ℑ, a nullification) and uses the following
facts about it.

  M1  Modal types are closed under Σ over a modal base, Π, identity
      types and pullbacks. Propositions are modal, because the
      generators are pointed. Units are surjective.
  M2  Units are connected maps; connected maps are stable under
      pullback; a connected map into a modal type is a unit.
  M3  For modal A, ○ ((a : A) × B a) ≃ (a : A) × ○ (B a).
  M4  f : X → Y is étale if X → Y ×_(○Y) ○X is an equivalence. Maps
      between modal types are étale. Étale maps are closed under
      composition and pullback. The fibre of an étale map over y is
      the fibre of ○f over η y, hence modal.

"Connected" means that ○ C is contractible. This module proves M2,
M3, M4 and the parts of M1 that TypeTopology's Modal lacks, for an
arbitrary Σ-closed replete reflective subuniverse of a universe 𝓤 in
TypeTopology's form, one of the equivalent definitions of a modality
of Rijke, Shulman and Spitters. That propositions are modal is a
property of nullifications at pointed types, not of every modality;
it is proved in Nullification, and here "units are surjective" takes
it as a hypothesis. The closure of modal types under Π, identity types
and pullbacks is TypeTopology's (Modal.ReflectiveSubuniverse; for the
pullbacks of UF.Pullback used here, pullbacks-of-modal-types-are-modal'
below); closure under Σ over a modal base is the hypothesis
P-is-sigma-closed, which holds for nullifications (Nullification).

Reuse, following [2, Section 7.1, item 2]. The reflection's action on
maps, ○-map with its rule ○-map-on-units, is that of
gist.RealCohesion.ReflectionMaps; connectedness, is-○-connected, is
that of gist.RealCohesion.ShapeProducts. Both are imported, not
redefined. These modules remain separate; consolidating their general
lemmas is optional and is not part of the final repairs.

Route. Everything rests on two facts about reflections.

  (R1) A map r : A → R into a modal type through which every map into
       a modal type factors uniquely (a reflector) is the unit, up to
       the equivalence ○-rec r : ○ A ≃ R (reflectors-are-units).
  (R2) For any A and B : A → 𝓤, the map (a , b) ↦ (a , η b) from Σ B
       to (a : A) × ○ (B a) is a reflector (Σ-reflector).

M3 is R2 with R1 when A is modal. M2 follows from M3 at the family
z ↦ fiber η z over ○ A: the reflection of A becomes (z : ○ A) ×
○ (fiber η z) with first projection homotopic to the identity, so
each ○ (fiber η z) is contractible. For M4, an étale map is the same
as a map whose fibres are those of a modal family over ○ Y pulled back
along η (étale-iff-fiberwise-equiv, étale-from-modal-family). For a
modal family E over ○ Y and fibres E (η y), the reflection of the
domain is (w : ○ Y) × E w (by M2 and M3), and the naturality square is
then a pullback; the homotopy that relates the two maps to ○ Y is
chosen through TypeTopology's homotopy-precomp-η-equiv, so that its
value at units is known. Pulling back and composing preserve such
fibre families, which gives closure under pullback and composition.
This is the modal descent of Cherubini and Rijke [3] in the form
needed here.

[1] E. Rijke, M. Shulman, B. Spitters. Modalities in homotopy type
    theory. Logical Methods in Computer Science 16(1), 2020.
[2] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Sections 3.2 and 7.1.
    references/F01-orbifolds-roadmap-rev2.md
[3] F. Cherubini, E. Rijke. Modal descent. Mathematical Structures in
    Computer Science 31, 2021. arXiv:2003.09713.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import Modal.Subuniverse

module gist.Orbifolds.Modalities
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
open import UF.EquivalenceExamples
open import UF.ImageAndSurjection pt using (is-surjection)
open import UF.PairFun
open import UF.Pullback
open import UF.Subsingletons

open import gist.RealCohesion.ReflectionMaps P P-is-reflective
 using (○-map ; ○-map-on-units)
open import gist.RealCohesion.ShapeProducts
             fe pt P P-is-reflective P-is-sigma-closed P-is-replete
 using (is-○-connected)

\end{code}

Preliminaries.

\begin{code}

modal-types-are-closed-under-equivalence : {X Y : 𝓤 ̇ }
                                         → X ≃ Y
                                         → is-modal Y
                                         → is-modal X
modal-types-are-closed-under-equivalence {X} {Y} = P-is-replete X Y

fibers-of-maps-between-modal-types-are-modal
 : {X Y : 𝓤 ̇ } (f : X → Y)
 → is-modal X
 → is-modal Y
 → (y : Y) → is-modal (fiber f y)
fibers-of-maps-between-modal-types-are-modal {X} {Y} f i j y =
 P-is-sigma-closed X (λ x → f x ＝ y) i
  (λ x → id-types-of-modal-types-are-modal fe P-is-replete Y (f x) y j)

pullbacks-of-modal-types-are-modal'
 : {X Y Z : 𝓤 ̇ } (f : X → Z) (g : Y → Z)
 → is-modal X
 → is-modal Y
 → is-modal Z
 → is-modal (pullback.pullback f g)
pullbacks-of-modal-types-are-modal' {X} {Y} {Z} f g i j k =
 P-is-sigma-closed (X × Y) (λ (z : X × Y) → f (pr₁ z) ＝ g (pr₂ z))
  (P-is-sigma-closed X (λ _ → Y) i (λ _ → j))
  (λ z → id-types-of-modal-types-are-modal fe P-is-replete Z (f (pr₁ z))
          (g (pr₂ z)) k)

precomposition-is-equiv : {A : 𝓣 ̇ } {B : 𝓣' ̇ } {Z : 𝓦 ̇ } (j : A → B)
                        → is-equiv j
                        → is-equiv (λ (h : B → Z) → h ∘ j)
precomposition-is-equiv j e =
 qinvs-are-equivs _
  ((λ k → k ∘ inverse j e) ,
   (λ h → dfunext fe (λ b → ap h (inverses-are-sections j e b))) ,
   (λ k → dfunext fe (λ a → ap k (inverses-are-retractions j e a))))

total-fiber-map : {X Y : 𝓤 ̇ } (f : X → Y) → X → Σ (fiber f)
total-fiber-map f x = f x , x , refl

total-fiber-map-is-equiv : {X Y : 𝓤 ̇ } (f : X → Y)
                         → is-equiv (total-fiber-map f)
total-fiber-map-is-equiv f =
 qinvs-are-equivs (total-fiber-map f)
  ((λ (y , x , p) → x) , (λ x → refl) , (λ { (y , x , refl) → refl }))

inverse-cancels : {A : 𝓦 ̇ } {a b c : A} (p : a ＝ b) (q : c ＝ b)
                → (p ∙ q ⁻¹) ∙ q ＝ p
inverse-cancels refl refl = refl

fiber-path : {X : 𝓦 ̇ } {Y : 𝓦' ̇ } (g : X → Y) {t t₀ : X} (κ : t ＝ t₀)
           → (t , ap g κ) ＝[ fiber g (g t₀) ] (t₀ , refl)
fiber-path g refl = refl

\end{code}

(R1) Reflectors are units.

\begin{code}

is-reflector : {A R : 𝓤 ̇ } → (A → R) → 𝓤 ⁺ ⊔ 𝓥 ̇
is-reflector {A} {R} r =
 (Z : 𝓤 ̇ ) → is-modal Z → is-equiv (λ (h : R → Z) → h ∘ r)

units-are-reflectors : (A : 𝓤 ̇ ) → is-reflector (η A)
units-are-reflectors A Z m = precomp-η-is-equiv m

reflectors-are-units : {A R : 𝓤 ̇ } (r : A → R) (R-modal : is-modal R)
                     → is-reflector r
                     → is-equiv (○-rec A R R-modal r)
reflectors-are-units {A} {R} r R-modal ρ = qinvs-are-equivs φ (ψ , ψφ , φψ)
 where
  φ : ○ A → R
  φ = ○-rec A R R-modal r

  ψ : R → ○ A
  ψ = inverse (λ (h : R → ○ A) → h ∘ r) (ρ (○ A) (○-is-modal A)) (η A)

  ψr : ψ ∘ r ＝ η A
  ψr = inverses-are-sections (λ (h : R → ○ A) → h ∘ r) (ρ (○ A) (○-is-modal A))
        (η A)

  φη : φ ∘ η A ＝ r
  φη = ○-rec-compute-pointsfree A R R-modal r

  ψφ : ψ ∘ φ ∼ id
  ψφ = happly (○-rec-ext A (○ A) (○-is-modal A) (ψ ∘ φ) id
                (ap (λ - → ψ ∘ -) φη ∙ ψr))

  φψ : φ ∘ ψ ∼ id
  φψ = happly (equivs-are-lc (λ (h : R → R) → h ∘ r) (ρ R R-modal)
                (ap (λ - → φ ∘ -) ψr ∙ φη))

reflectors-are-closed-under-precomposition
 : {A A' R : 𝓤 ̇ } (j : A' → A) (r : A → R)
 → is-equiv j
 → is-reflector r
 → is-reflector (r ∘ j)
reflectors-are-closed-under-precomposition j r e ρ Z m =
 ∘-is-equiv (ρ Z m) (precomposition-is-equiv j e)

reflectors-are-closed-under-postcomposition
 : {A R R' : 𝓤 ̇ } (r : A → R) (e : R → R')
 → is-equiv e
 → is-reflector r
 → is-reflector (e ∘ r)
reflectors-are-closed-under-postcomposition r e i ρ Z m =
 ∘-is-equiv (precomposition-is-equiv e i) (ρ Z m)

\end{code}

(R2) and M3: the reflection commutes with Σ over a modal base.

\begin{code}

Σ-unit : (A : 𝓤 ̇ ) (B : A → 𝓤 ̇ ) → Σ B → Σ a ꞉ A , ○ (B a)
Σ-unit A B (a , b) = a , η (B a) b

Σ-reflector : (A : 𝓤 ̇ ) (B : A → 𝓤 ̇ ) → is-reflector (Σ-unit A B)
Σ-reflector A B Z m =
 equiv-closed-under-∼ _ _
  (∘-is-equiv (∘-is-equiv cur-is-equiv (⌜⌝-is-equiv φ)) uncur-is-equiv)
  (λ h → refl)
 where
  cur : ((Σ a ꞉ A , ○ (B a)) → Z) → ((a : A) → ○ (B a) → Z)
  cur h a u = h (a , u)

  cur-is-equiv : is-equiv cur
  cur-is-equiv = qinvs-are-equivs cur
                    ((λ k (a , u) → k a u) , (λ h → refl) , (λ k → refl))

  φ : ((a : A) → ○ (B a) → Z) ≃ ((a : A) → B a → Z)
  φ = Π-cong fe fe (λ a → precomp-η-equiv m)

  uncur : ((a : A) → B a → Z) → (Σ B → Z)
  uncur k (a , b) = k a b

  uncur-is-equiv : is-equiv uncur
  uncur-is-equiv = qinvs-are-equivs uncur
                      ((λ h a b → h (a , b)) , (λ k → refl) , (λ h → refl))

Σ-of-reflections-is-modal : (A : 𝓤 ̇ ) (B : A → 𝓤 ̇ )
                          → is-modal A
                          → is-modal (Σ a ꞉ A , ○ (B a))
Σ-of-reflections-is-modal A B m =
 P-is-sigma-closed A (λ a → ○ (B a)) m (λ a → ○-is-modal (B a))

○-Σ-over-modal-base : (A : 𝓤 ̇ ) (B : A → 𝓤 ̇ )
                    → is-modal A
                    → ○ (Σ B) ≃ (Σ a ꞉ A , ○ (B a))
○-Σ-over-modal-base A B m =
 ○-rec (Σ B) (Σ a ꞉ A , ○ (B a)) (Σ-of-reflections-is-modal A B m) (Σ-unit A B)
  ,
 reflectors-are-units (Σ-unit A B) (Σ-of-reflections-is-modal A B m)
  (Σ-reflector A B)

\end{code}

M2: units are connected maps; connected maps are stable under
pullback; a connected map into a modal type is a unit.

\begin{code}

is-○-connected-map : {X Y : 𝓤 ̇ } → (X → Y) → 𝓤 ̇
is-○-connected-map {X} {Y} f = (y : Y) → is-○-connected (fiber f y)

units-are-connected : (A : 𝓤 ̇ ) → is-○-connected-map (η A)
units-are-connected A z =
 equiv-to-singleton (≃-sym (pr₁-fiber-equiv z))
  (equivs-are-vv-equivs pr₁ pr₁-is-equiv' z)
 where
  F : ○ A → 𝓤 ̇
  F = fiber (η A)

  T : 𝓤 ̇
  T = Σ z ꞉ ○ A , ○ (F z)

  T-modal : is-modal T
  T-modal = Σ-of-reflections-is-modal (○ A) F (○-is-modal A)

  m : A → T
  m = Σ-unit (○ A) F ∘ total-fiber-map (η A)

  φ : ○ A → T
  φ = ○-rec A T T-modal m

  φ-is-equiv : is-equiv φ
  φ-is-equiv = reflectors-are-units m T-modal
                (reflectors-are-closed-under-precomposition
                  (total-fiber-map (η A)) (Σ-unit (○ A) F)
                  (total-fiber-map-is-equiv (η A))
                  (Σ-reflector (○ A) F))

  pr₁φ : pr₁ ∘ φ ∼ id
  pr₁φ = happly (○-rec-ext A (○ A) (○-is-modal A) (pr₁ ∘ φ) id
                  (ap (λ - → pr₁ ∘ -) (○-rec-compute-pointsfree A T T-modal m)))

  pr₁-is-equiv' : is-equiv (pr₁ {𝓤} {𝓤} {○ A} {λ z → ○ (F z)})
  pr₁-is-equiv' = ≃-2-out-of-3-right φ-is-equiv
                   (equiv-closed-under-∼ id (pr₁ ∘ φ) (id-is-equiv (○ A)) pr₁φ)

○-map-is-equiv : {A B : 𝓤 ̇ } (f : A → B) → is-equiv f → is-equiv (○-map f)
○-map-is-equiv {A} {B} f e =
 reflectors-are-units (η B ∘ f) (○-is-modal B)
  (reflectors-are-closed-under-precomposition f (η B) e
    (units-are-reflectors B))

connected-types-are-closed-under-equivalence : {A B : 𝓤 ̇ }
                                             → A ≃ B
                                             → is-○-connected A
                                             → is-○-connected B
connected-types-are-closed-under-equivalence (f , e) =
 equiv-to-singleton' (○-map f , ○-map-is-equiv f e)

fiber-of-pullback : {X Y Y' : 𝓤 ̇ } (f : X → Y) (g : Y' → Y) (y' : Y')
                  → fiber (pullback.pb₂ f g) y' ≃ fiber f (g y')
fiber-of-pullback f g y' = qinveq φ (ψ , ψφ , φψ)
 where
  φ : fiber (pullback.pb₂ f g) y' → fiber f (g y')
  φ (((x , y'') , q) , r) = x , (q ∙ ap g r)

  ψ : fiber f (g y') → fiber (pullback.pb₂ f g) y'
  ψ (x , s) = ((x , y') , s) , refl

  ψφ : ψ ∘ φ ∼ id
  ψφ (((x , y'') , q) , refl) = refl

  φψ : φ ∘ ψ ∼ id
  φψ (x , s) = refl

connected-maps-are-closed-under-pullback
 : {X Y Y' : 𝓤 ̇ } (f : X → Y) (g : Y' → Y)
 → is-○-connected-map f
 → is-○-connected-map (pullback.pb₂ f g)
connected-maps-are-closed-under-pullback f g κ y' =
 connected-types-are-closed-under-equivalence
  (≃-sym (fiber-of-pullback f g y')) (κ (g y'))

connected-maps-into-modal-types-are-units
 : {A B : 𝓤 ̇ } (f : A → B) (B-modal : is-modal B)
 → is-○-connected-map f
 → is-equiv (○-rec A B B-modal f)
connected-maps-into-modal-types-are-units {A} {B} f B-modal κ =
 reflectors-are-units f B-modal
  (reflectors-are-closed-under-postcomposition
    (Σ-unit B (fiber f) ∘ total-fiber-map f) pr₁
    (pr₁-is-equiv B (λ b → ○ (fiber f b)) κ)
    (reflectors-are-closed-under-precomposition
      (total-fiber-map f) (Σ-unit B (fiber f))
      (total-fiber-map-is-equiv f)
      (Σ-reflector B (fiber f))))

\end{code}

M1, the part not in TypeTopology: if propositions are modal, units
are surjective.

\begin{code}

units-are-surjective : ((X : 𝓤 ̇ ) → is-prop X → is-modal X)
                     → (A : 𝓤 ̇ ) → is-surjection (η A)
units-are-surjective props-are-modal A z =
 ○-rec (fiber (η A) z) ∥ fiber (η A) z ∥ (props-are-modal _ ∥∥-is-prop) ∣_∣
  (center (units-are-connected A z))

\end{code}

M4: étale maps. The canonical map of f : X → Y into the pullback
Y ×_(○Y) ○X is étale-gap f, and f is étale if it is an equivalence.

\begin{code}

étale-gap : {X Y : 𝓤 ̇ } (f : X → Y) → X → pullback.pullback (η Y) (○-map f)
étale-gap {X} {Y} f x = (f x , η X x) , ((○-map-on-units f x)⁻¹)

is-étale : {X Y : 𝓤 ̇ } → (X → Y) → 𝓤 ̇
is-étale f = is-equiv (étale-gap f)

étale-fiber-map : {X Y : 𝓤 ̇ } (f : X → Y) (y : Y)
                → fiber f y → fiber (○-map f) (η Y y)
étale-fiber-map {X} {Y} f y (x , p) = η X x , (○-map-on-units f x ∙ ap (η Y) p)

étale-iff-fiberwise-equiv
 : {X Y : 𝓤 ̇ } (f : X → Y)
 → is-étale f ↔ ((y : Y) → is-equiv (étale-fiber-map f y))
étale-iff-fiberwise-equiv {X} {Y} f = I , II
 where
  α : (Σ y ꞉ Y , fiber f y) → X
  α (y , x , p) = x

  α-is-equiv : is-equiv α
  α-is-equiv = qinvs-are-equivs α
                (total-fiber-map f , (λ { (y , x , refl) → refl }) ,
                  (λ x → refl))

  β : (Σ y ꞉ Y , fiber (○-map f) (η Y y)) → pullback.pullback (η Y) (○-map f)
  β (y , z , q) = (y , z) , (q ⁻¹)

  β-is-equiv : is-equiv β
  β-is-equiv = qinvs-are-equivs β
                ((λ ((y , z) , q) → y , z , (q ⁻¹)) ,
                 (λ (y , z , q) → ap (λ - → y , z , -) (⁻¹-involutive q)) ,
                 (λ ((y , z) , q) → ap (λ - → (y , z) , -) (⁻¹-involutive q)))

  square : étale-gap f ∘ α ∼ β ∘ NatΣ (étale-fiber-map f)
  square (y , x , refl) = refl

  I : is-étale f → (y : Y) → is-equiv (étale-fiber-map f y)
  I e = NatΣ-equiv-gives-fiberwise-equiv (étale-fiber-map f)
         (≃-2-out-of-3-left β-is-equiv
           (equiv-closed-under-∼ (étale-gap f ∘ α)
             (β ∘ NatΣ (étale-fiber-map f))
             (∘-is-equiv α-is-equiv e) (λ w → square w ⁻¹)))

  II : ((y : Y) → is-equiv (étale-fiber-map f y)) → is-étale f
  II i = ≃-2-out-of-3-right α-is-equiv
          (equiv-closed-under-∼ (β ∘ NatΣ (étale-fiber-map f)) (étale-gap f ∘ α)
            (∘-is-equiv (NatΣ-is-equiv _ _ (étale-fiber-map f) i) β-is-equiv)
            square)

étale-maps-have-fibers-of-○-map
 : {X Y : 𝓤 ̇ } (f : X → Y)
 → is-étale f
 → (y : Y) → fiber f y ≃ fiber (○-map f) (η Y y)
étale-maps-have-fibers-of-○-map f e y =
 étale-fiber-map f y , lr-implication (étale-iff-fiberwise-equiv f) e y

fibers-of-étale-maps-are-modal
 : {X Y : 𝓤 ̇ } (f : X → Y)
 → is-étale f
 → (y : Y) → is-modal (fiber f y)
fibers-of-étale-maps-are-modal {X} {Y} f e y =
 modal-types-are-closed-under-equivalence
  (étale-maps-have-fibers-of-○-map f e y)
  (fibers-of-maps-between-modal-types-are-modal (○-map f)
    (○-is-modal X) (○-is-modal Y) (η Y y))

\end{code}

The converse direction: a map whose fibres are those of a modal family
over ○ Y, pulled back along η, is étale.

\begin{code}

module étale-from-modal-family-construction
        {X Y : 𝓤 ̇ } (f : X → Y) (E : ○ Y → 𝓤 ̇ )
        (E-modal : (w : ○ Y) → is-modal (E w))
        (e : (y : Y) → fiber f y ≃ E (η Y y))
       where

 T : 𝓤 ̇
 T = Σ w ꞉ ○ Y , E w

 T-modal : is-modal T
 T-modal = P-is-sigma-closed (○ Y) E (○-is-modal Y) E-modal

 τ : X → T
 τ x = η Y (f x) , ⌜ e (f x) ⌝ (x , refl)

 k : X → Σ y ꞉ Y , E (η Y y)
 k = NatΣ (λ y → ⌜ e y ⌝) ∘ total-fiber-map f

 k-is-equiv : is-equiv k
 k-is-equiv = ∘-is-equiv (total-fiber-map-is-equiv f)
               (NatΣ-is-equiv _ _ (λ y → ⌜ e y ⌝) (λ y → ⌜ e y ⌝-is-equiv))

 F : T → 𝓤 ̇
 F t = fiber (η Y) (pr₁ t)

 ℓ : (Σ y ꞉ Y , E (η Y y)) → Σ F
 ℓ (y , u) = (η Y y , u) , y , refl

 ℓ-is-equiv : is-equiv ℓ
 ℓ-is-equiv = qinvs-are-equivs ℓ
               ((λ ((w , u) , y , p) → y , transport E (p ⁻¹) u) ,
                (λ (y , u) → refl) ,
                (λ { ((w , u) , y , refl) → refl }))

 pr₁-is-equiv' : is-equiv (pr₁ {𝓤} {𝓤} {T} {λ t → ○ (F t)})
 pr₁-is-equiv' = pr₁-is-equiv T (λ t → ○ (F t))
                  (λ t → units-are-connected Y (pr₁ t))

 τ-is-reflector : is-reflector τ
 τ-is-reflector =
  reflectors-are-closed-under-precomposition k (pr₁ ∘ Σ-unit T F ∘ ℓ) k-is-equiv
   (reflectors-are-closed-under-postcomposition (Σ-unit T F ∘ ℓ) pr₁
     pr₁-is-equiv'
     (reflectors-are-closed-under-precomposition ℓ (Σ-unit T F) ℓ-is-equiv
       (Σ-reflector T F)))

 θ : ○ X → T
 θ = ○-rec X T T-modal τ

 θ-is-equiv : is-equiv θ
 θ-is-equiv = reflectors-are-units τ T-modal τ-is-reflector

 K : θ ∘ η X ∼ τ
 K = ○-rec-compute X T T-modal τ

 h₀ : (pr₁ ∘ θ) ∘ η X ∼ ○-map f ∘ η X
 h₀ x = ap pr₁ (K x) ∙ (○-map-on-units f x)⁻¹

 𝕙 : (pr₁ ∘ θ ∼ ○-map f) ≃ ((pr₁ ∘ θ) ∘ η X ∼ ○-map f ∘ η X)
 𝕙 = homotopy-precomp-η-equiv fe X (○ Y) (○-is-modal Y) (pr₁ ∘ θ) (○-map f)

 H : pr₁ ∘ θ ∼ ○-map f
 H = ⌜ 𝕙 ⌝⁻¹ h₀

 Hη : (x : X) → H (η X x) ＝ h₀ x
 Hη = happly (≃-sym-is-rinv 𝕙 h₀)

 ψ : (w : ○ Y) → fiber (○-map f) w → fiber (pr₁ {𝓤} {𝓤} {○ Y} {E}) w
 ψ w (z , q) = θ z , (H z ∙ q)

 ψ-is-equiv : (w : ○ Y) → is-equiv (ψ w)
 ψ-is-equiv w = pair-fun-is-equiv θ (λ z q → H z ∙ q) θ-is-equiv
                 (λ z → ∙-is-equiv-left (H z))

 std : (y : Y) → fiber f y → fiber (pr₁ {𝓤} {𝓤} {○ Y} {E}) (η Y y)
 std y w = (η Y y , ⌜ e y ⌝ w) , refl

 std-is-equiv : (y : Y) → is-equiv (std y)
 std-is-equiv y =
  ∘-is-equiv ⌜ e y ⌝-is-equiv
   (qinvs-are-equivs (λ u → (η Y y , u) , refl)
     ((λ ((w , u) , p) → transport E p u) ,
      (λ u → refl) ,
      (λ { ((w , u) , refl) → refl })))

 step-I : (x : X)
        → (θ (η X x) , (H (η X x) ∙ ○-map-on-units f x))
        ＝[ fiber (pr₁ {𝓤} {𝓤} {○ Y} {E}) (η Y (f x)) ]
          (θ (η X x) , (h₀ x ∙ ○-map-on-units f x))
 step-I x = ap (λ - → θ (η X x) , (- ∙ ○-map-on-units f x)) (Hη x)

 step-II : (x : X)
         → (θ (η X x) , (h₀ x ∙ ○-map-on-units f x))
         ＝[ fiber (pr₁ {𝓤} {𝓤} {○ Y} {E}) (η Y (f x)) ]
           (θ (η X x) , ap pr₁ (K x))
 step-II x = ap (λ - → θ (η X x) , -)
                (inverse-cancels (ap pr₁ (K x)) (○-map-on-units f x))

 Φ∼std : (y : Y) → ψ (η Y y) ∘ étale-fiber-map f y ∼ std y
 Φ∼std .(f x) (x , refl) =
  step-I x ∙ step-II x ∙ fiber-path (pr₁ {𝓤} {𝓤} {○ Y} {E}) (K x)

 γ : (y : Y) → is-equiv (étale-fiber-map f y)
 γ y = ≃-2-out-of-3-left (ψ-is-equiv (η Y y))
        (equiv-closed-under-∼ (std y) (ψ (η Y y) ∘ étale-fiber-map f y)
          (std-is-equiv y) (Φ∼std y))


étale-from-modal-family
 : {X Y : 𝓤 ̇ } (f : X → Y) (E : ○ Y → 𝓤 ̇ )
 → ((w : ○ Y) → is-modal (E w))
 → ((y : Y) → fiber f y ≃ E (η Y y))
 → is-étale f
étale-from-modal-family f E E-modal e =
 rl-implication (étale-iff-fiberwise-equiv f)
  (étale-from-modal-family-construction.γ f E E-modal e)

\end{code}

Closure of étale maps under pullback and composition; equivalences
and maps between modal types are étale.

\begin{code}

étale-maps-are-closed-under-pullback
 : {X Y Y' : 𝓤 ̇ } (f : X → Y) (g : Y' → Y)
 → is-étale f
 → is-étale (pullback.pb₂ f g)
étale-maps-are-closed-under-pullback {X} {Y} {Y'} f g e =
 étale-from-modal-family (pullback.pb₂ f g)
  (λ w → fiber (○-map f) (○-map g w))
  (λ w → fibers-of-maps-between-modal-types-are-modal (○-map f)
          (○-is-modal X) (○-is-modal Y) (○-map g w))
  (λ y' → fiber-of-pullback f g y'
          ● étale-maps-have-fibers-of-○-map f e (g y')
          ● transport-≃ (fiber (○-map f)) ((○-map-on-units g y')⁻¹))

étale-maps-are-closed-under-composition
 : {X Y Z : 𝓤 ̇ } (f : X → Y) (g : Y → Z)
 → is-étale f
 → is-étale g
 → is-étale (g ∘ f)
étale-maps-are-closed-under-composition {X} {Y} {Z} f g ef eg =
 étale-from-modal-family (g ∘ f) E E-modal γ
 where
  E : ○ Z → 𝓤 ̇
  E w = Σ u ꞉ fiber (○-map g) w , fiber (○-map f) (pr₁ u)

  E-modal : (w : ○ Z) → is-modal (E w)
  E-modal w =
   P-is-sigma-closed _ _
    (fibers-of-maps-between-modal-types-are-modal (○-map g)
      (○-is-modal Y) (○-is-modal Z) w)
    (λ u → fibers-of-maps-between-modal-types-are-modal (○-map f)
            (○-is-modal X) (○-is-modal Y) (pr₁ u))

  γ : (z : Z) → fiber (g ∘ f) z ≃ E (η Z z)
  γ z = fiber-of-composite f g z
        ● Σ-cong (λ u → étale-maps-have-fibers-of-○-map f ef (pr₁ u))
        ● Σ-change-of-variable (λ u → fiber (○-map f) (pr₁ u))
           (étale-fiber-map g z)
           (lr-implication (étale-iff-fiberwise-equiv g) eg z)

equivalences-are-étale : {X Y : 𝓤 ̇ } (f : X → Y) → is-equiv f → is-étale f
equivalences-are-étale f e =
 étale-from-modal-family f (λ _ → 𝟙)
  (λ _ → 𝟙-is-modal fe P-is-replete)
  (λ y → singleton-≃-𝟙 (equivs-are-vv-equivs f e y))

maps-between-modal-types-are-étale
 : {X Y : 𝓤 ̇ } (f : X → Y)
 → is-modal X
 → is-modal Y
 → is-étale f
maps-between-modal-types-are-étale {X} {Y} f i j =
 étale-from-modal-family f (λ w → fiber f (η⁻¹ w))
  (λ w → fibers-of-maps-between-modal-types-are-modal f i j (η⁻¹ w))
  (λ y →
    transport-≃ (fiber f) ((inverses-are-retractions (η Y) ηY-is-equiv y)⁻¹))
 where
  ηY-is-equiv : is-equiv (η Y)
  ηY-is-equiv = is-modal-gives-η-is-equiv fe Y j

  η⁻¹ : ○ Y → Y
  η⁻¹ = inverse (η Y) ηY-is-equiv

\end{code}
