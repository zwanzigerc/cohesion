Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. Orbifold gate H4 of Fable's roadmap [1].

Lemma G: microlinearity along étale maps
----------------------------------------

Lemma G is Claude Fable 5.2's [1, Section 3.4; 2], audited by GPT-6
Astra [3, Section 3]. For a modality ○ and an étale map f : X → Y:

  (1) for every pointed ○-connected type C, X^C ≃ X ×_Y Y^C over
      evaluation at the base point, naturally in pointed maps of C;
  (2) if the types V_j of a test square σ are ○-connected and Y is
      σ-local, so is X;
  (3) if moreover f is surjective and X is σ-local, then Y is σ-local.

"Connected" means that ○ C is contractible (is-○-connected), as Astra
insists [3, Section 3]. In (1) the map is h ↦ (h c₀ , f ∘ h), and the
naturality square for a pointed map u : C' → C commutes by an explicit
homotopy (lemma-G-1-naturality).

Formal reading of the test squares. The roadmap's squares are pointed,
with the commutation and the pointing paths as data (Pointing below).
Part (2) needs no points at all, and part (3) uses only the point of
V₂; they are stated with exactly what they use, which makes them hold
for every pointed square, coherent or not.

Route. Not the slice argument of [2], but the local families of
TestSquares, which say the same in another form:

  - modal types are σ-local when all V_j are connected
    (modal-types-are-local): with Z modal and V connected, the
    constant maps Z → Z^V are an equivalence;
  - for étale f the fibre family of f is E ∘ η with E = fiber (○-map f)
    a modal family over ○Y (Modalities); E is a local family because
    ○Y and Σ E are modal, so E ∘ η is local, and X ≃ Σ (E ∘ η);
  - (2) is then Σ-is-local of TestSquares;
  - (3): the canonical map of Σ P is the canonical map of Y paired
    with equivalences of dependent cocones (TestSquares), so a fibre of
    the canonical map of Y over a cocone c is contractible as soon as
    there is a dependent cocone of P over c. One merely exists: the
    image of c in ○Y comes from a map k' : V₄ → ○Y, sections of E along
    k' are determined by their value at one point, and that value
    merely exists because f is surjective.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Sections 3.4 and 5.
    references/F01-orbifolds-roadmap-rev2.md
[2] Claude Fable 5.2. Audit request: étale descent from crisp pullback
    preservation, and microlinearity along étale maps, 11 November 2026,
    Section 3.4.
    references/F08-lemmas-F-G.md
[3] GPT-6 Astra. Audit of Fable's Lemmas F and G, 12 November 2026.
    references/A05-lemmas-F-G-audit.txt

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import Modal.Subuniverse

module gist.Orbifolds.LemmaG
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
open import UF.Subsingletons-FunExt

open import gist.RealCohesion.ReflectionMaps P P-is-reflective
 using (○-map ; ○-map-on-units ; maps-from-connected-to-modal-are-constant)
open import gist.RealCohesion.ShapeProducts
             fe pt P P-is-reflective P-is-sigma-closed P-is-replete
 using (is-○-connected)
open import gist.Orbifolds.Modalities
             fe pt P P-is-reflective P-is-sigma-closed P-is-replete
open import gist.Orbifolds.TestSquares fe

\end{code}

Pointed test squares: the commutation and the pointing paths as data.

\begin{code}

record Pointing {𝓦 : Universe} (σ : Test-Square 𝓦) : 𝓦 ̇ where
 field
  o₁ : Test-Square.V₁ σ
  o₂ : Test-Square.V₂ σ
  o₃ : Test-Square.V₃ σ
  o₄ : Test-Square.V₄ σ
  v₁₂-pointed : Test-Square.v₁₂ σ o₁ ＝ o₂
  v₁₃-pointed : Test-Square.v₁₃ σ o₁ ＝ o₃
  v₂₄-pointed : Test-Square.v₂₄ σ o₂ ＝ o₄
  v₃₄-pointed : Test-Square.v₃₄ σ o₃ ＝ o₄
  square-pointed : Test-Square.square σ o₁
                    ∙ ap (Test-Square.v₃₄ σ) v₁₃-pointed ∙ v₃₄-pointed
                 ＝ ap (Test-Square.v₂₄ σ) v₁₂-pointed ∙ v₂₄-pointed

\end{code}

Maps from a connected type into a modal type: the constant maps are an
equivalence, and sections of a modal family along a map into a modal
type are determined by their value at a point.

\begin{code}

constant-maps-are-equiv : (C : 𝓤 ̇ ) → is-○-connected C
                        → (Z : 𝓤 ̇ ) → is-modal Z
                        → is-equiv (λ (z : Z) (_ : C) → z)
constant-maps-are-equiv C κ Z m =
 ∘-is-equiv
  (qinvs-are-equivs (λ (z : Z) (_ : ○ C) → z)
    ((λ g → g (center κ)) ,
     (λ z → refl) ,
     (λ g → dfunext fe (λ u → ap g (centrality κ u)))))
  (precomp-η-is-equiv m)

evaluation-is-equiv : (C : 𝓤 ̇ ) (c₀ : C) → is-○-connected C
                    → (W : 𝓤 ̇ ) → is-modal W
                    → (R : W → 𝓤 ̇ ) → ((w : W) → is-modal (R w))
                    → (m : C → W)
                    → is-equiv (λ (s : (c : C) → R (m c)) → s c₀)
evaluation-is-equiv C c₀ κ W W-modal R R-modal m =
 γ (m c₀) m (dfunext fe (λ c → maps-from-connected-to-modal-are-constant
                                 C κ W W-modal m c c₀))
 where
  γ : (w : W) (m' : C → W) → m' ＝ (λ _ → w)
    → is-equiv (λ (s : (c : C) → R (m' c)) → s c₀)
  γ w .(λ _ → w) refl =
   ≃-2-out-of-3-right (constant-maps-are-equiv C κ (R w) (R-modal w))
    (id-is-equiv (R w))

\end{code}

Lemma G(1): exponentials of étale maps by pointed connected types.

\begin{code}

module _ {X Y : 𝓤 ̇ } (f : X → Y) (f-is-étale : is-étale f) where

 lemma-G-1-map : (C : 𝓤 ̇ ) (c₀ : C)
               → (C → X) → pullback.pullback f (λ (k : C → Y) → k c₀)
 lemma-G-1-map C c₀ h = (h c₀ , f ∘ h) , refl

 lemma-G-1 : (C : 𝓤 ̇ ) (c₀ : C) → is-○-connected C
           → is-equiv (lemma-G-1-map C c₀)
 lemma-G-1 C c₀ κ =
  ∘-is-equiv
   (∘-is-equiv
     (∘-is-equiv (postcomposition-is-equiv (total-fiber-map f)
                   (total-fiber-map-is-equiv f))
                 d-is-equiv)
     (NatΣ-is-equiv (λ k → (c : C) → fiber f (k c)) (λ k → fiber f (k c₀))
       (λ k s → s c₀) ev-is-equiv))
   r-is-equiv
  where
   d : (C → Σ (fiber f)) → Σ k ꞉ (C → Y) , ((c : C) → fiber f (k c))
   d g = pr₁ ∘ g , pr₂ ∘ g

   d-is-equiv : is-equiv d
   d-is-equiv = qinvs-are-equivs d
                 ((λ (k , s) c → k c , s c) , (λ g → refl) , (λ (k , s) → refl))

   e : (y : Y) → fiber f y ≃ fiber (○-map f) (η Y y)
   e = étale-maps-have-fibers-of-○-map f f-is-étale

   ev-is-equiv : (k : C → Y) → is-equiv (λ (s : (c : C) → fiber f (k c)) → s c₀)
   ev-is-equiv k =
    ≃-2-out-of-3-left ⌜ e (k c₀) ⌝-is-equiv
     (∘-is-equiv (⌜⌝-is-equiv (Π-cong fe fe (λ c → e (k c))))
       (evaluation-is-equiv C c₀ κ (○ Y) (○-is-modal Y)
         (fiber (○-map f))
         (fibers-of-maps-between-modal-types-are-modal (○-map f)
           (○-is-modal X) (○-is-modal Y))
         (η Y ∘ k)))

   r : (Σ k ꞉ (C → Y) , fiber f (k c₀))
     → pullback.pullback f (λ (k : C → Y) → k c₀)
   r (k , x , p) = (x , k) , p

   r-is-equiv : is-equiv r
   r-is-equiv = qinvs-are-equivs r
                 ((λ ((x , k) , p) → k , x , p) , (λ _ → refl) , (λ _ → refl))

\end{code}

Naturality of (1) in pointed maps u : (C' , c₀') → (C , c₀): the
square formed with precomposition by u on the left and its action on
the pullbacks on the right commutes.

\begin{code}

 pullback-precomposition
  : (C C' : 𝓤 ̇ ) (c₀ : C) (c₀' : C') (u : C' → C) (q : u c₀' ＝ c₀)
  → pullback.pullback f (λ (k : C → Y) → k c₀)
  → pullback.pullback f (λ (k : C' → Y) → k c₀')
 pullback-precomposition C C' c₀ c₀' u q ((x , k) , p) =
  (x , k ∘ u) , (p ∙ (ap k q)⁻¹)

 lemma-G-1-naturality
  : (C C' : 𝓤 ̇ ) (c₀ : C) (c₀' : C') (u : C' → C) (q : u c₀' ＝ c₀)
    (h : C → X)
  → lemma-G-1-map C' c₀' (h ∘ u)
  ＝ pullback-precomposition C C' c₀ c₀' u q (lemma-G-1-map C c₀ h)
 lemma-G-1-naturality C C' .(u c₀') c₀' u refl h = refl

\end{code}

Modal types are local for a test square whose types are connected.

\begin{code}

modal-types-are-local
 : (σ : Test-Square 𝓤)
 → is-○-connected (Test-Square.V₁ σ)
 → is-○-connected (Test-Square.V₂ σ)
 → is-○-connected (Test-Square.V₃ σ)
 → is-○-connected (Test-Square.V₄ σ)
 → (Z : 𝓤 ̇ ) → is-modal Z → is-local σ Z
modal-types-are-local σ κ₁ κ₂ κ₃ κ₄ Z m =
 ≃-2-out-of-3-right c₄-is-equiv
  (≃-2-out-of-3-left ev-is-equiv
    (equiv-closed-under-∼ id (ev ∘ gap σ Z ∘ c₄) (id-is-equiv Z) evgc))
 where
  open Test-Square σ

  c : (V : 𝓤 ̇ ) → Z → (V → Z)
  c V z _ = z

  c₄ : Z → (V₄ → Z)
  c₄ = c V₄

  c₄-is-equiv : is-equiv c₄
  c₄-is-equiv = constant-maps-are-equiv V₄ κ₄ Z m

  c₂-is-equiv : is-equiv (c V₂)
  c₂-is-equiv = constant-maps-are-equiv V₂ κ₂ Z m

  precomp-v₁₃-is-equiv : is-equiv (λ (b : V₃ → Z) → b ∘ v₁₃)
  precomp-v₁₃-is-equiv = ≃-2-out-of-3-right (constant-maps-are-equiv V₃ κ₃ Z m)
                          (constant-maps-are-equiv V₁ κ₁ Z m)

  fibers-are-singletons : (a : V₂ → Z)
                        → is-singleton (Σ b ꞉ (V₃ → Z) , a ∘ v₁₂ ∼ b ∘ v₁₃)
  fibers-are-singletons a =
   equiv-to-singleton
    (Σ-cong
      (λ b → (a ∘ v₁₂ ∼ b ∘ v₁₃)  ≃⟨ ≃-sym (≃-funext fe (a ∘ v₁₂) (b ∘ v₁₃)) ⟩
             (a ∘ v₁₂ ＝ b ∘ v₁₃)  ≃⟨ ＝-flip ⟩
             (b ∘ v₁₃ ＝ a ∘ v₁₂)  ■))
    (equivs-are-vv-equivs _ precomp-v₁₃-is-equiv (a ∘ v₁₂))

  ev : Cocone σ Z → Z
  ev = inverse (c V₂) c₂-is-equiv ∘ pr₁

  ev-is-equiv : is-equiv ev
  ev-is-equiv = ∘-is-equiv
                 (pr₁-is-equiv (V₂ → Z)
                   (λ a → Σ b ꞉ (V₃ → Z) , a ∘ v₁₂ ∼ b ∘ v₁₃)
                   fibers-are-singletons)
                 (inverses-are-equivs (c V₂) c₂-is-equiv)

  evgc : ev ∘ gap σ Z ∘ c₄ ∼ id
  evgc = inverses-are-retractions (c V₂) c₂-is-equiv

\end{code}

Étale maps and the fibre family E ∘ η, which is local.

\begin{code}

module _ (σ : Test-Square 𝓤)
         (κ₁ : is-○-connected (Test-Square.V₁ σ))
         (κ₂ : is-○-connected (Test-Square.V₂ σ))
         (κ₃ : is-○-connected (Test-Square.V₃ σ))
         (κ₄ : is-○-connected (Test-Square.V₄ σ))
         {X Y : 𝓤 ̇ } (f : X → Y) (f-is-étale : is-étale f)
       where

 open Test-Square σ

 private
  E : ○ Y → 𝓤 ̇
  E = fiber (○-map f)

  E-is-modal : (w : ○ Y) → is-modal (E w)
  E-is-modal = fibers-of-maps-between-modal-types-are-modal (○-map f)
                (○-is-modal X) (○-is-modal Y)

  ○Y-is-local : is-local σ (○ Y)
  ○Y-is-local = modal-types-are-local σ κ₁ κ₂ κ₃ κ₄ (○ Y) (○-is-modal Y)

  E-is-local : is-local-family σ E
  E-is-local = local-family-from-Σ σ E ○Y-is-local
                (modal-types-are-local σ κ₁ κ₂ κ₃ κ₄ (Σ E)
                  (P-is-sigma-closed (○ Y) E (○-is-modal Y) E-is-modal))

  F : Y → 𝓤 ̇
  F = E ∘ η Y

  F-is-local : is-local-family σ F
  F-is-local = local-families-are-closed-under-reindexing σ E (η Y) E-is-local

  X-is-ΣF : X ≃ Σ F
  X-is-ΣF = (total-fiber-map f , total-fiber-map-is-equiv f)
            ● Σ-cong (étale-maps-have-fibers-of-○-map f f-is-étale)

\end{code}

Lemma G(2).

\begin{code}

 lemma-G-2 : is-local σ Y → is-local σ X
 lemma-G-2 i = local-types-are-closed-under-equivalence σ (≃-sym X-is-ΣF)
                (Σ-is-local σ F i F-is-local)

\end{code}

Lemma G(3). The fibres of the canonical map of Y are those of the
total canonical map of Σ F over any dependent cocone, and dependent
cocones merely exist.

\begin{code}

 module _ (o₂ : V₂) (f-is-surjection : is-surjection f) where

  private
   g : (k : V₄ → Y) → ((w : V₄) → F (k w)) → Cocone-Over σ F (gap σ Y k)
   g k = adjust σ F k ∘ dependent-gap σ (F ∘ k)

   g-is-equiv : (k : V₄ → Y) → is-equiv (g k)
   g-is-equiv k = ∘-is-equiv (F-is-local k) (adjust-is-equiv σ F k)

   fibers-agree : (c : Cocone σ Y) (d : Cocone-Over σ F c)
                → fiber (gap σ Y) c ≃ fiber (total-gap σ F) (c , d)
   fibers-agree c d =
    ≃-sym (pr₁-≃ (fiber (gap σ Y) c) _
            (λ (k , p) → equivs-are-vv-equivs (g k) (g-is-equiv k)
                           (transport⁻¹ (Cocone-Over σ F) p d)))
    ● ≃-sym (pair-fun-fiber-≃ (gap σ Y) g c d)

   cocones-over-exist : (c : Cocone σ Y) → ∥ Cocone-Over σ F c ∥
   cocones-over-exist (a , b , H) = ∥∥-functor γ ∥E-at-point∥
    where
     c' : Cocone σ (○ Y)
     c' = Cocone-map σ (η Y) (a , b , H)

     k' : V₄ → ○ Y
     k' = inverse (gap σ (○ Y)) ○Y-is-local c'

     k'-gap : gap σ (○ Y) k' ＝ c'
     k'-gap = inverses-are-sections (gap σ (○ Y)) ○Y-is-local c'

     k'-at-point : k' (v₂₄ o₂) ＝ η Y (a o₂)
     k'-at-point = happly (ap pr₁ k'-gap) o₂

     ∥E-at-point∥ : ∥ E (k' (v₂₄ o₂)) ∥
     ∥E-at-point∥ = ∥∥-functor
                     (λ w → transport⁻¹ E k'-at-point
                             (⌜ étale-maps-have-fibers-of-○-map f f-is-étale
                                (a o₂) ⌝ w))
                     (f-is-surjection (a o₂))

     back : Cocone-Over σ E c' → Cocone-Over σ F (a , b , H)
     back (a' , b' , H') = a' , b' , (λ z → transport-ap E (η Y) (H z) ∙ H' z)

     γ : E (k' (v₂₄ o₂)) → Cocone-Over σ F (a , b , H)
     γ u = back (transport (Cocone-Over σ E) k'-gap
                  (adjust σ E k'
                    (dependent-gap σ (E ∘ k')
                      (inverse _
                        (evaluation-is-equiv V₄ (v₂₄ o₂) κ₄ (○ Y) (○-is-modal Y)
                           E E-is-modal k') u))))

  lemma-G-3 : is-local σ X → is-local σ Y
  lemma-G-3 i = vv-equivs-are-equivs (gap σ Y) γ
   where
    ΣF-is-local : is-local σ (Σ F)
    ΣF-is-local = local-types-are-closed-under-equivalence σ X-is-ΣF i

    total-gap-is-equiv : is-equiv (total-gap σ F)
    total-gap-is-equiv =
     ≃-2-out-of-3-right (unpair-is-equiv σ F)
      (equiv-closed-under-∼ (split σ F ∘ gap σ (Σ F))
        (total-gap σ F ∘ unpair σ F)
        (∘-is-equiv ΣF-is-local (split-is-equiv σ F))
        (λ h → (gap-of-Σ σ F h)⁻¹))

    γ : (c : Cocone σ Y) → is-singleton (fiber (gap σ Y) c)
    γ c = ∥∥-rec (being-singleton-is-prop fe)
           (λ d → equiv-to-singleton (fibers-agree c d)
                   (equivs-are-vv-equivs (total-gap σ F) total-gap-is-equiv
                     (c , d)))
           (cocones-over-exist c)

\end{code}

Lemma G(2) and (3) for the roadmap's pointed squares.

\begin{code}

module _ (σ : Test-Square 𝓤) (π : Pointing σ)
         (κ₁ : is-○-connected (Test-Square.V₁ σ))
         (κ₂ : is-○-connected (Test-Square.V₂ σ))
         (κ₃ : is-○-connected (Test-Square.V₃ σ))
         (κ₄ : is-○-connected (Test-Square.V₄ σ))
         {X Y : 𝓤 ̇ } (f : X → Y) (f-is-étale : is-étale f)
       where

 lemma-G-2-pointed : is-local σ Y → is-local σ X
 lemma-G-2-pointed = lemma-G-2 σ κ₁ κ₂ κ₃ κ₄ f f-is-étale

 lemma-G-3-pointed : is-surjection f → is-local σ X → is-local σ Y
 lemma-G-3-pointed = lemma-G-3 σ κ₁ κ₂ κ₃ κ₄ f f-is-étale (Pointing.o₂ π)

\end{code}
