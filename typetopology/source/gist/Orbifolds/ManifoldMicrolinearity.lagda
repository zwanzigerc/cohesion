Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026 (local time). Orbifold gate H9 of Fable's
roadmap [1], by the route of Fable's corrected guidance [2, Section 2],
the sum of the charts, in the form of GPT-6 Astra's audit [3, Section 3].

Ordinary manifolds are microlinear
----------------------------------

Microlinearity is that of the module Microlinearity, for the crisp
infinitesimal R-pushouts, with test squares in the universe 𝓤 ⁺ of the
modality; the manifolds have carriers in 𝓤, the Euclidean spaces in 𝓤₀.

  smooth-line-is-microlinear : an infinitesimal R-pushout is, by
  definition, a square for which R is local [4, Definition 4.2.10];

  Euclidean-spaces-are-microlinear : Rⁿ = Fin n → R, by closure of local
  types under the unit type and binary products (TestSquares);

  Euclidean-opens-are-microlinear : a metrically open U ⊆ Rⁿ is stable
  under ¬¬-equality, because the metric topology is regular (Theorem
  5.1.5 and Lemma 5.1.3); so its inclusion is ℑ-étale (Lemma B), and U
  is microlinear by Lemma G(2);

  modal-index-sums-are-local : Myers's Lemma 5.3.4 [4], by the argument
  of [3, Section 3]: over a modal index I, a map from the connected
  vertex V₄ to I is constant (Lemma G's constant-maps-are-equiv), so the
  family is locally the constant one, which is local; then Σ-is-local;

  sums-of-étale-maps-are-étale : Myers's Lemma 5.3.3 [4]: over a modal
  index I, if every fᵢ : Xᵢ → Y is étale, so is (i , x) ↦ fᵢ x. Its
  fibre over y is Σᵢ fiber fᵢ y, which is Σᵢ fiber (○fᵢ) (η y), the
  pullback along η of a modal family over ○Y; then
  étale-from-modal-family of the module Modalities;

  ordinary-manifolds-are-microlinear : the sum over i : ℕ of the basic
  opens Bᵢ of the countable basis of charts. Each Bᵢ is merely
  homeomorphic to a Euclidean open, hence microlinear, a proposition, so
  no chart is chosen. ℕ is ℑ-modal by K, its equality being decidable.
  Each inclusion is ℑ-étale by Lemma B, as Bᵢ is open in a regular
  space; so the sum maps étale onto M, surjectively because the basis
  covers M, and M is microlinear by Lemma G(3).

Inventory: Postulates K and O, the translation law (from Exp),
propositional extensionality at 𝓤 (for Lemma B), and ℑ as the
nullification of core item 4, as hypotheses. Crisp pullback
preservation is not used.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] Claude Fable 5.2. Orbifolds H9 and H10: follow-up to Astra's
    readiness audits, 13 November 2026 (UTC).
    references/F04-orbifolds-h9-h10-followup.md
[3] GPT-6 Astra. Fable H9 readiness audit, 13 November 2026 (UTC).
    references/A16-h9-readiness-audit.txt
[4] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import Modal.Subuniverse
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.ManifoldMicrolinearity
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ 𝓡 : Commutative-Ring)
        {@♭ 𝓤 : Universe}
       where

open import Fin.Type
open import UF.Base
open import UF.Equiv
open import UF.Equiv-FunExt using (being-equiv-is-prop)
open import UF.EquivalenceExamples using (Σ-assoc ; 𝟙-lneutral ; Σ-cong)
open import UF.DiscreteAndSeparated using (is-discrete ; ℕ-is-discrete)
open import UF.ImageAndSurjection pt using (is-surjection)
open import UF.SubtypeClassifier
open import UF.Subsingletons-FunExt
open import UF.UniverseEmbedding using (Lift ; lift ; lower ; Lift-≃)
open import gist.CohesiveApartness.Flat using (♭ ; ♭-counit)
open import gist.Orbifolds.SmoothOrder
open import gist.Orbifolds.MetricTopology
open import gist.Orbifolds.Manifolds

open PropositionalTruncation pt
open smooth-line fe pt 𝓡
open smooth-order fe pt 𝓡
open metric-topology fe pt 𝓡
open ordinary-manifolds fe pt 𝓡
open import gist.Orbifolds.Topology fe pt
open import gist.Orbifolds.TestSquares fe
open import gist.Orbifolds.Microlinearity fe pt 𝓡 {𝓤 ⁺}
open import gist.Orbifolds.Nullification fe
 using
  (is-nullification ; nullifications-are-Σ-closed ; nullifications-are-replete)

\end{code}

Microlinearity is a proposition, invariant under equivalence; R and Rⁿ
are microlinear.

\begin{code}

being-microlinear-is-prop : {𝓦 : Universe} (X : 𝓦 ̇ )
                          → is-prop (is-microlinear X)
being-microlinear-is-prop X =
 Π-is-prop fe (λ t → being-equiv-is-prop (λ 𝓤 𝓥 → fe {𝓤} {𝓥}) _)

microlinearity-is-invariant : {𝓦 𝓦' : Universe} {X : 𝓦 ̇ } {Y : 𝓦' ̇ }
                            → X ≃ Y → is-microlinear X → is-microlinear Y
microlinearity-is-invariant e m t =
 local-types-are-closed-under-equivalence (infinitesimal-R-pushouts t) e (m t)

smooth-line-is-microlinear : is-microlinear R
smooth-line-is-microlinear t = pr₂ (♭-counit t)

vectors-of-length-zero : (Fin 0 → R) ≃ 𝟙 {𝓤₀}
vectors-of-length-zero =
 qinveq (λ _ → ⋆) ((λ _ → λ ()) , (λ v → dfunext fe (λ ())) , (λ _ → refl))

vectors-of-successor-length : (n : ℕ) → (Fin (succ n) → R) ≃ (Fin n → R) × R
vectors-of-successor-length n =
 qinveq (λ v → v ∘ suc , v 𝟎)
  ((λ (v , r) → λ { (suc i) → v i ; 𝟎 → r }) ,
   (λ v → dfunext fe (λ { (suc i) → refl ; 𝟎 → refl })) ,
   (λ (v , r) → refl))

Euclidean-spaces-are-microlinear : (n : ℕ) → is-microlinear (Fin n → R)
Euclidean-spaces-are-microlinear 0 t =
 local-types-are-closed-under-equivalence (infinitesimal-R-pushouts t)
  (≃-sym vectors-of-length-zero) (𝟙-is-local (infinitesimal-R-pushouts t))
Euclidean-spaces-are-microlinear (succ n) t =
 local-types-are-closed-under-equivalence (infinitesimal-R-pushouts t)
  (≃-sym (vectors-of-successor-length n))
  (×-is-local (infinitesimal-R-pushouts t)
    (Euclidean-spaces-are-microlinear n t)
    (smooth-line-is-microlinear t))


stable-subtype-equivalence
 : {𝓧 : Universe} {X : 𝓧 ̇ } (S : X → 𝓤 ̇ )
 → (Σ x ꞉ X , S x) ≃ (Σ z ꞉ Lift (𝓤 ⁺) X , Lift (𝓤 ⁺) (S (lower z)))
stable-subtype-equivalence S =
 qinveq (λ (x , s) → lift (𝓤 ⁺) x , lift (𝓤 ⁺) s)
  ((λ (z , s) → lower z , lower s) , (λ _ → refl) , (λ _ → refl))

\end{code}

Everything else is relative to the modality ℑ, the nullification at
the crisp infinitesimal varieties, on 𝓤 ⁺.

\begin{code}

module _ {𝓟 : Universe}
         (pe : propext 𝓤)
         (K : Postulate-K)
         (P : subuniverse (𝓤 ⁺) 𝓟)
         (P-is-reflective : subuniverse-is-reflective P)
         (ν : is-nullification ℑ-generator ℑ-generator-point P)
       where

 private
  P-is-Σ-closed : subuniverse-is-sigma-closed P
  P-is-Σ-closed = nullifications-are-Σ-closed ℑ-generator ℑ-generator-point P ν

  P-is-replete : subuniverse-is-replete P
  P-is-replete = nullifications-are-replete ℑ-generator ℑ-generator-point P ν

 open import Modal.ReflectiveSubuniverse P P-is-reflective
  using (○ ; η ; ○-is-modal)
 open import gist.RealCohesion.ReflectionMaps P P-is-reflective using (○-map)
 open import gist.RealCohesion.ShapeProducts fe pt P P-is-reflective
  P-is-Σ-closed P-is-replete
  using (is-○-connected)
 open import gist.Orbifolds.Modalities fe pt P P-is-reflective P-is-Σ-closed
  P-is-replete
  using (is-étale ; étale-from-modal-family ; étale-maps-have-fibers-of-○-map ;
         fibers-of-maps-between-modal-types-are-modal)
 open import gist.Orbifolds.LemmaG fe pt P P-is-reflective P-is-Σ-closed
  P-is-replete
  using
   (modal-types-are-local ; constant-maps-are-equiv ; lemma-G-2 ; lemma-G-3)
 open import gist.Orbifolds.LemmasABForIm fe pt 𝓡 {𝓤}
  using (lemma-B-for-carriers-in-𝓤 ; lemma-B-for-carriers-in-𝓤₀)

 private
  is-modal : 𝓤 ⁺ ̇ → 𝓟 ̇
  is-modal = subuniverse-contains P

\end{code}

Myers's Lemma 5.3.4: sums over a modal index.

\begin{code}

 modal-index-sums-are-local
  : (σ : Test-Square (𝓤 ⁺))
  → is-○-connected (Test-Square.V₁ σ)
  → is-○-connected (Test-Square.V₂ σ)
  → is-○-connected (Test-Square.V₃ σ)
  → is-○-connected (Test-Square.V₄ σ)
  → (I : 𝓤 ⁺ ̇ ) → is-modal I
  → (X : I → 𝓤 ⁺ ̇ ) → ((i : I) → is-local σ (X i))
  → is-local σ (Σ X)
 modal-index-sums-are-local σ κ₁ κ₂ κ₃ κ₄ I m X l =
  Σ-is-local σ X (modal-types-are-local σ κ₁ κ₂ κ₃ κ₄ I m) X-is-local-family
  where
   open Test-Square σ

   constant : I → (V₄ → I)
   constant i _ = i

   constant-is-equiv : is-equiv constant
   constant-is-equiv = constant-maps-are-equiv V₄ κ₄ I m

   constant-families-are-local : (i : I)
                               → is-equiv (dependent-gap σ (λ (_ : V₄) → X i))
   constant-families-are-local i =
    local-family-from-Σ σ (λ (_ : 𝟙 {𝓤₀}) → X i) (𝟙-is-local σ)
     (local-types-are-closed-under-equivalence σ (≃-sym 𝟙-lneutral) (l i))
     (λ _ → ⋆)

   X-is-local-family : is-local-family σ X
   X-is-local-family k =
    transport (λ Q → is-equiv (dependent-gap σ Q))
     (ap (X ∘_) (inverses-are-sections constant constant-is-equiv k))
     (constant-families-are-local (inverse constant constant-is-equiv k))

\end{code}

Myers's Lemma 5.3.3: sums of étale maps over a modal index.

\begin{code}

 sums-of-étale-maps-are-étale
  : (I : 𝓤 ⁺ ̇ ) → is-modal I
  → {Y : 𝓤 ⁺ ̇ } (X : I → 𝓤 ⁺ ̇ ) (f : (i : I) → X i → Y)
  → ((i : I) → is-étale (f i))
  → is-étale (λ (w : Σ X) → f (pr₁ w) (pr₂ w))
 sums-of-étale-maps-are-étale I m {Y} X f e =
  étale-from-modal-family F E E-is-modal fibers
  where
   F : Σ X → Y
   F w = f (pr₁ w) (pr₂ w)

   E : ○ Y → 𝓤 ⁺ ̇
   E u = Σ i ꞉ I , fiber (○-map (f i)) u

   E-is-modal : (u : ○ Y) → is-modal (E u)
   E-is-modal u =
    P-is-Σ-closed I (λ i → fiber (○-map (f i)) u) m
     (λ i → fibers-of-maps-between-modal-types-are-modal (○-map (f i))
             (○-is-modal (X i)) (○-is-modal Y) u)

   fibers : (y : Y) → fiber F y ≃ E (η Y y)
   fibers y =
    Σ-assoc ● Σ-cong (λ i → étale-maps-have-fibers-of-○-map (f i) (e i) y)

\end{code}

Euclidean opens and chart domains are microlinear.

\begin{code}

 module _ (O : Postulate-O) (translation : Translation-Law O) where

  private
   E : (n : ℕ) → Topology (Fin n → R) 𝓤
   E = Euclidean O translation K 𝓤

  Euclidean-opens-are-microlinear
   : {n : ℕ} (U : Subset (Fin n → R) 𝓤) → Topology.is-open (E n) U
   → is-microlinear (𝕊 (E n) U)
  Euclidean-opens-are-microlinear {n} U oU t =
   local-types-are-closed-under-equivalence σ
    (≃-sym (stable-subtype-equivalence (_∈ U)))
    (lemma-G-2 σ κ₁ κ₂ κ₃ κ₄ pr₁ inclusion-is-étale
      (local-types-are-closed-under-equivalence σ
        (≃-sym (Lift-≃ (𝓤 ⁺) (Fin n → R)))
        (Euclidean-spaces-are-microlinear n t)))
   where
    σ = infinitesimal-R-pushouts t
    κ =
     infinitesimal-R-pushouts-have-connected-pointed-types P P-is-reflective ν t
    κ₁ = pr₁ κ
    κ₂ = pr₁ (pr₂ κ)
    κ₃ = pr₁ (pr₂ (pr₂ κ))
    κ₄ = pr₁ (pr₂ (pr₂ (pr₂ κ)))

    S : (Fin n → R) → 𝓤 ⁺ ̇
    S x = Lift (𝓤 ⁺) (x ∈ U)

    inclusion-is-étale
     : is-étale (λ (s : Σ z ꞉ Lift (𝓤 ⁺) (Fin n → R) , S (lower z)) → pr₁ s)
    inclusion-is-étale =
     lemma-B-for-carriers-in-𝓤₀ pe K P P-is-reflective ν S
      (λ x → equiv-to-prop (Lift-≃ (𝓤 ⁺) _) (∈-is-prop x U))
      (λ x y s d → lift (𝓤 ⁺)
                    (opens-of-regular-spaces-are-infinitesimally-stable (E n)
                      (metric-topology-is-regular O translation K) U oU x y
                       (lower s)
                      (¬¬-functor _⁻¹ d)))

  chart-domains-are-microlinear
   : {n : ℕ} {M : 𝓤 ̇ } (T : Topology M 𝓤) (B : Subset M 𝓤)
   → is-Euclidean-chart-domain O translation K n T B
   → is-microlinear (𝕊 T B)
  chart-domains-are-microlinear T B =
   ∥∥-rec (being-microlinear-is-prop _)
    (λ (V , oV , h , H) → microlinearity-is-invariant (h , pr₁ H)
                           (Euclidean-opens-are-microlinear V oV))

\end{code}

Ordinary manifolds are microlinear: the sum of the basic opens.

\begin{code}

  ordinary-manifolds-are-microlinear
   : {n : ℕ} {M : 𝓤 ̇ } → Ordinary-Manifold O translation K n M
   → is-microlinear M
  ordinary-manifolds-are-microlinear {n} {M} 𝓜 t =
   local-types-are-closed-under-equivalence σ (Lift-≃ (𝓤 ⁺) M)
    (lemma-G-3 σ κ₁ κ₂ κ₃ κ₄ F F-is-étale o₂ F-is-surjection
      (modal-index-sums-are-local σ κ₁ κ₂ κ₃ κ₄ I I-is-modal X X-is-local))
   where
    open Ordinary-Manifold 𝓜

    σ = infinitesimal-R-pushouts t
    κ =
     infinitesimal-R-pushouts-have-connected-pointed-types P P-is-reflective ν t
    κ₁ = pr₁ κ
    κ₂ = pr₁ (pr₂ κ)
    κ₃ = pr₁ (pr₂ (pr₂ κ))
    κ₄ = pr₁ (pr₂ (pr₂ (pr₂ κ)))
    o₂ = pr₂ (pr₂ (pr₂ (pr₂ κ)))

    I : 𝓤 ⁺ ̇
    I = Lift (𝓤 ⁺) ℕ

    I-is-discrete : is-discrete I
    I-is-discrete i j =
     cases (λ p → inl (ap (lift (𝓤 ⁺)) p)) (λ d → inr (λ q → d (ap lower q)))
      (ℕ-is-discrete (lower i) (lower j))

    I-is-modal : is-modal I
    I-is-modal =
     discrete-types-are-ℑ-modal P P-is-reflective ν K I I-is-discrete

    S : I → M → 𝓤 ⁺ ̇
    S i x = Lift (𝓤 ⁺) (x ∈ basis (lower i))

    X : I → 𝓤 ⁺ ̇
    X i = Σ z ꞉ Lift (𝓤 ⁺) M , S i (lower z)

    X-is-local : (i : I) → is-local σ (X i)
    X-is-local i =
     local-types-are-closed-under-equivalence σ
      (stable-subtype-equivalence (_∈ basis (lower i)))
      (chart-domains-are-microlinear topology (basis (lower i))
        (basis-consists-of-chart-domains (lower i)) t)

    inclusions-are-étale : (i : I) → is-étale (λ (s : X i) → pr₁ s)
    inclusions-are-étale i =
     lemma-B-for-carriers-in-𝓤 pe K P P-is-reflective ν (S i)
      (λ x → equiv-to-prop (Lift-≃ (𝓤 ⁺) _) (∈-is-prop x (basis (lower i))))
      (λ x y s d → lift (𝓤 ⁺)
                    (opens-of-manifolds-are-infinitesimally-stable O translation
                      K 𝓜
                      (basis (lower i)) (pr₁ basis-is-basis (lower i)) x y
                       (lower s)
                      (¬¬-functor _⁻¹ d)))

    F : Σ X → Lift (𝓤 ⁺) M
    F w = pr₁ (pr₂ w)

    F-is-étale : is-étale F
    F-is-étale = sums-of-étale-maps-are-étale I I-is-modal X (λ i s → pr₁ s)
                  inclusions-are-étale

    F-is-surjection : is-surjection F
    F-is-surjection z =
     ∥∥-functor (λ (k , m , _) → (lift (𝓤 ⁺) k , z , lift (𝓤 ⁺) m) , refl)
      (pr₂ basis-is-basis full (Topology.full-is-open topology) (lower z) ⋆)

\end{code}
