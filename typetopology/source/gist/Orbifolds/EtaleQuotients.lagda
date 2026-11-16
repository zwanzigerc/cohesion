Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. Orbifold gate H6 of Fable's roadmap [1].

Theorems 5.4.9 and 5.4.1 in abstract form
-----------------------------------------

The roadmap [1, Section 3.5] derives Myers's Theorems 5.4.9 and 5.4.1
[2] from Lemma F and Lemma G, without tiny types:

  5.4.9. For a crisp pregroupoid G with s étale: y : G₀ → rG is crisp
  and surjective, and G₀ ×_(rG) G₀ ≃ G₁ over G₀, with second projection
  t = s ∘ inv. By Lemma F, y is étale; if G₀ is microlinear, rG is
  microlinear by Lemma G(3).

  5.4.1, in the scope proved. Let Γ be a crisp group whose underlying
  type is ℑ-modal. Then 1 → BΓ is étale by Lemma F, the quotient map
  X → X // Γ is its pullback, and X // Γ is microlinear when X is.

This module proves both over interfaces, as intermediate results in
the sense of [1, Section 5]:

  - for 5.4.9, the Rezk completion is given by its defining data
    [1, Section 4]: a type rG with a surjection y : G₀ → rG and
    equivalences G(x, x') ≃ (y x ＝ y x'); only rG and y need to be
    crisp, and G is an arbitrary family of hom types, so the pregroupoid
    structure is not used (theorem-5-4-9, theorem-5-4-9-microlinear);
  - for 5.4.1, the delooping is any crisp pointed type (B , b₀) that is
    connected, with modal loop space b₀ ＝ b₀, and the action is a type
    family X̃ over B, whose fibre over b₀ is X and whose total space is
    X // Γ (theorem-5-4-1, quotient-maps-are-étale,
    theorem-5-4-1-microlinear). For BΓ the loop space is Γ, so the
    hypothesis is that the carrier of Γ is modal, as in [1, 3.5]; this
    is not Theorem 5.4.1 for all crisply discrete higher groups, and is
    not labelled so.

Done since, at gate H6: the Rezk completion is constructed as the
image of the Yoneda embedding (RezkCompletion, EtaleGroupoids), and BΓ
as the type of Γ-torsors with the family of a Γ-set (Deloopings,
GroupQuotients), both under univalence; they discharge the two
interfaces [1, Section 4]. At gate H8, GlobalQuotients applies
theorem-5-4-1-microlinear to groups with finite loop space, which
Postulate K makes modal (Theorem 6.4.1). (Paragraph updated at gate
H8, 12 November 2026.)

The hypothesis ○-preserves-crisp-pullbacks (core item 4 for ℑ) enters
through Lemma F (CrispLemmaF); microlinearity is relative to a family
of test squares whose types are connected, with a point of V₂ (for
Lemma G(3)), as for Myers's infinitesimal R-pushouts.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Sections 3.5, 4 and 5.
    references/F01-orbifolds-roadmap-rev2.md
[2] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import Modal.Subuniverse

module gist.Orbifolds.EtaleQuotients
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        {@♭ 𝓤 : Universe}
        {𝓥 : Universe}
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
open import UF.Pullback
open import UF.Subsingletons

open import gist.RealCohesion.ShapeProducts
             fe pt P P-is-reflective P-is-sigma-closed P-is-replete
 using (is-○-connected)
open import gist.Orbifolds.Modalities
             fe pt P P-is-reflective P-is-sigma-closed P-is-replete
open import gist.Orbifolds.CrispLemmaF
             fe pt P P-is-reflective P-is-sigma-closed P-is-replete
open import gist.Orbifolds.LemmaG
             fe pt P P-is-reflective P-is-sigma-closed P-is-replete
open import gist.Orbifolds.TestSquares fe
open import gist.Orbifolds.AbstractOrbifolds fe pt using (is-microlinear)

\end{code}

Families of test squares whose types are connected and whose V₂ has a
point, as Myers's infinitesimal R-pushouts are.

\begin{code}

has-connected-pointed-types : {𝓣 : Universe} {T : 𝓣 ̇ } (σ : T → Test-Square 𝓤)
                            → 𝓣 ⊔ 𝓤 ̇
has-connected-pointed-types {𝓣} {T} σ =
 (t : T) → is-○-connected (Test-Square.V₁ (σ t))
         × is-○-connected (Test-Square.V₂ (σ t))
         × is-○-connected (Test-Square.V₃ (σ t))
         × is-○-connected (Test-Square.V₄ (σ t))
         × Test-Square.V₂ (σ t)

microlinearity-descends-along-étale-surjections
 : {𝓣 : Universe} {T : 𝓣 ̇ } (σ : T → Test-Square 𝓤)
 → has-connected-pointed-types σ
 → {X Y : 𝓤 ̇ } (f : X → Y)
 → is-étale f
 → is-surjection f
 → is-microlinear σ X
 → is-microlinear σ Y
microlinearity-descends-along-étale-surjections σ c f e s m t =
 lemma-G-3 (σ t) κ₁ κ₂ κ₃ κ₄ f e o₂ s (m t)
 where
  κ₁ = pr₁ (c t)
  κ₂ = pr₁ (pr₂ (c t))
  κ₃ = pr₁ (pr₂ (pr₂ (c t)))
  κ₄ = pr₁ (pr₂ (pr₂ (pr₂ (c t))))
  o₂ = pr₂ (pr₂ (pr₂ (pr₂ (c t))))

\end{code}

Theorem 5.4.9, abstract: the unit of a Rezk completion is étale when
the source map is.

\begin{code}

arrows : {G₀ : 𝓤 ̇ } → (G₀ → G₀ → 𝓤 ̇ ) → 𝓤 ̇
arrows {G₀} hom = Σ x ꞉ G₀ , Σ x' ꞉ G₀ , hom x x'

source target : {G₀ : 𝓤 ̇ } (hom : G₀ → G₀ → 𝓤 ̇ ) → arrows hom → G₀
source hom (x , x' , g) = x
target hom (x , x' , g) = x'

quotient-map : {B : 𝓤 ̇ } (b₀ : B) (X̃ : B → 𝓤 ̇ ) → X̃ b₀ → Σ X̃
quotient-map b₀ X̃ x = b₀ , x

quotient-maps-are-surjections
 : {B : 𝓤 ̇ } (b₀ : B)
 → ((u : B) → ∥ b₀ ＝ u ∥)
 → (X̃ : B → 𝓤 ̇ )
 → is-surjection (quotient-map b₀ X̃)
quotient-maps-are-surjections b₀ B-is-connected X̃ (u , x') =
 ∥∥-functor (γ u x') (B-is-connected u)
 where
  γ : (u : _) (x' : X̃ u) → b₀ ＝ u → fiber (quotient-map b₀ X̃) (u , x')
  γ .b₀ x' refl = x' , refl

module _ (π : ○-preserves-crisp-pullbacks) where

 theorem-5-4-9
  : {@♭ G₀ rG : 𝓤 ̇ } (hom : G₀ → G₀ → 𝓤 ̇ ) (@♭ y : G₀ → rG)
  → is-surjection y
  → ((x x' : G₀) → hom x x' ≃ (y x ＝ y x'))
  → is-étale (source hom)
  → is-étale y
 theorem-5-4-9 {G₀} {rG} hom y y-is-surjection hom-≃ s-is-étale =
  lemma-F-crisp π y y-is-surjection p₂-is-étale
  where
   ψ : pullback.pullback y y → arrows hom
   ψ ((x , x') , q) = x , x' , ⌜ hom-≃ x x' ⌝⁻¹ q

   ψ-is-equiv : is-equiv ψ
   ψ-is-equiv =
    qinvs-are-equivs ψ
     ((λ (x , x' , g) → (x , x') , ⌜ hom-≃ x x' ⌝ g) ,
      (λ ((x , x') , q) →
        ap (λ - → (x , x') , -) (≃-sym-is-rinv (hom-≃ x x') q)) ,
      (λ (x , x' , g) → ap (λ - → x , x' , -) (≃-sym-is-linv (hom-≃ x x') g)))

   swap : pullback.pullback y y → pullback.pullback y y
   swap ((x , x') , q) = (x' , x) , (q ⁻¹)

   swap-is-equiv : is-equiv swap
   swap-is-equiv =
    qinvs-are-equivs swap
     (swap ,
      (λ ((x , x') , q) → ap (λ - → (x , x') , -) (⁻¹-involutive q)) ,
      (λ ((x , x') , q) → ap (λ - → (x , x') , -) (⁻¹-involutive q)))

   p₂-is-étale : is-étale (pullback.pb₂ y y)
   p₂-is-étale = étale-maps-are-closed-under-composition (ψ ∘ swap) (source hom)
                  (equivalences-are-étale (ψ ∘ swap)
                    (∘-is-equiv swap-is-equiv ψ-is-equiv))
                  s-is-étale

 theorem-5-4-9-microlinear
  : {𝓣 : Universe} {T : 𝓣 ̇ } (σ : T → Test-Square 𝓤)
  → has-connected-pointed-types σ
  → {@♭ G₀ rG : 𝓤 ̇ } (hom : G₀ → G₀ → 𝓤 ̇ ) (@♭ y : G₀ → rG)
  → is-surjection y
  → ((x x' : G₀) → hom x x' ≃ (y x ＝ y x'))
  → is-étale (source hom)
  → is-microlinear σ G₀
  → is-microlinear σ rG
 theorem-5-4-9-microlinear σ c hom y y-is-surjection hom-≃ s-is-étale =
  microlinearity-descends-along-étale-surjections σ c y
   (theorem-5-4-9 hom y y-is-surjection hom-≃ s-is-étale)
   y-is-surjection

\end{code}

Theorem 5.4.1, abstract: for a crisp pointed connected type with modal
loop space, the point is étale, and so is the quotient map into the
total space of any family over it.

\begin{code}

 theorem-5-4-1
  : {@♭ B : 𝓤 ̇ } (@♭ b₀ : B)
  → ((u : B) → ∥ b₀ ＝ u ∥)
  → is-modal (b₀ ＝ b₀)
  → is-étale (λ (_ : 𝟙 {𝓤}) → b₀)
 theorem-5-4-1 {B} b₀ B-is-connected Ω-is-modal =
  lemma-F-crisp π (λ (_ : 𝟙 {𝓤}) → b₀)
   (λ u → ∥∥-functor (λ p → ⋆ , p) (B-is-connected u))
   (maps-between-modal-types-are-étale _ K-is-modal
     (𝟙-is-modal fe P-is-replete))
  where
   K : 𝓤 ̇
   K = pullback.pullback (λ (_ : 𝟙 {𝓤}) → b₀) (λ (_ : 𝟙 {𝓤}) → b₀)

   K-is-Ω : K ≃ (b₀ ＝ b₀)
   K-is-Ω = qinveq (λ (_ , p) → p)
                   ((λ p → (⋆ , ⋆) , p) , (λ { ((⋆ , ⋆) , p) → refl }) ,
                     (λ p → refl))

   K-is-modal : is-modal K
   K-is-modal = P-is-replete K (b₀ ＝ b₀) K-is-Ω Ω-is-modal

 quotient-maps-are-étale
  : {@♭ B : 𝓤 ̇ } (@♭ b₀ : B)
  → ((u : B) → ∥ b₀ ＝ u ∥)
  → is-modal (b₀ ＝ b₀)
  → (X̃ : B → 𝓤 ̇ )
  → is-étale (quotient-map b₀ X̃)
 quotient-maps-are-étale {B} b₀ B-is-connected Ω-is-modal X̃ =
  étale-maps-are-closed-under-composition j (pullback.pb₂ pt₀ pr₁)
   (equivalences-are-étale j j-is-equiv)
   (étale-maps-are-closed-under-pullback pt₀ pr₁
     (theorem-5-4-1 b₀ B-is-connected Ω-is-modal))
  where
   pt₀ : 𝟙 {𝓤} → B
   pt₀ _ = b₀

   j : X̃ b₀ → pullback.pullback pt₀ (pr₁ {𝓤} {𝓤} {B} {X̃})
   j x = (⋆ , (b₀ , x)) , refl

   j-is-equiv : is-equiv j
   j-is-equiv =
    qinvs-are-equivs j
     ((λ ((_ , (u , x')) , p) → transport⁻¹ X̃ p x') ,
      (λ x → refl) ,
      (λ { ((⋆ , (u , x')) , refl) → refl }))

 theorem-5-4-1-microlinear
  : {𝓣 : Universe} {T : 𝓣 ̇ } (σ : T → Test-Square 𝓤)
  → has-connected-pointed-types σ
  → {@♭ B : 𝓤 ̇ } (@♭ b₀ : B)
  → ((u : B) → ∥ b₀ ＝ u ∥)
  → is-modal (b₀ ＝ b₀)
  → (X̃ : B → 𝓤 ̇ )
  → is-microlinear σ (X̃ b₀)
  → is-microlinear σ (Σ X̃)
 theorem-5-4-1-microlinear σ c b₀ B-is-connected Ω-is-modal X̃ =
  microlinearity-descends-along-étale-surjections σ c (quotient-map b₀ X̃)
   (quotient-maps-are-étale b₀ B-is-connected Ω-is-modal X̃)
   (quotient-maps-are-surjections b₀ B-is-connected X̃)

\end{code}
