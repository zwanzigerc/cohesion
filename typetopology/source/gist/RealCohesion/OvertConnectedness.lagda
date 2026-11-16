Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index.

Overt connectedness and the set 𝟚 modulo a proposition.

For a proposition P, let 𝟚-mod P be the set obtained from 𝟚 by
identifying ₀ and ₁ exactly when P holds. We construct it as the image
of the map 𝟚 → Ω that sends ₀ to ⊤ and ₁ to P, so that no quotients
are needed.

Following Taylor, we say that a type X is overtly connected if
whenever two subsets U and V cover X and are both inhabited, their
intersection is inhabited. Shulman proves this for crisp subsets of
the real line from his Axiom R♭ [1, Theorem 11.3], and derives the
approximate intermediate value theorem for crisp functions
[1, Theorem 11.4]. Whether the crispness hypothesis can be removed is
one of the questions left open in [1].

We show, for a pointed type X, that X is overtly connected (for
arbitrary, not necessarily crisp, subsets) if and only if every set of
the form 𝟚-mod P is null with respect to X. In Shulman's setting, where
the discrete types are the ℝ-null types, this says that the
non-crisp form of [1, Theorem 11.3] is equivalent to the
discreteness of all the sets 𝟚-mod P. We deduce the approximate
intermediate value theorem from the latter, for arbitrary functions
ℝ → ℝ on TypeTopology's Dedekind reals.

The crisp case is in gist.RealCohesion.CrispDiscreteness, where we
show that 𝟚-mod P is ♭-discrete for crisp P, assuming axiom C1.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.OvertConnectedness
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import UF.Base
open import UF.ImageAndSurjection pt
open import UF.Sets
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties
open import gist.CohesiveApartness.Flat
 using (is-null ; null-iff-maps-are-constant)

open PropositionalTruncation pt

\end{code}

The set 𝟚-mod P and its two points.

\begin{code}

χ : {𝓤 : Universe} → Ω 𝓤 → 𝟚 → Ω 𝓤
χ P ₀ = ⊤
χ P ₁ = P

𝟚-mod : {𝓤 : Universe} → Ω 𝓤 → 𝓤 ⁺ ̇
𝟚-mod P = image (χ P)

[_] : {𝓤 : Universe} {P : Ω 𝓤} → 𝟚 → 𝟚-mod P
[_] {𝓤} {P} = corestriction (χ P)

𝟚-mod-is-set : {𝓤 : Universe} (P : Ω 𝓤) → is-set (𝟚-mod P)
𝟚-mod-is-set P = image-is-set (χ P) (Ω-is-set fe pe)

to-𝟚-mod-＝ : {𝓤 : Universe} {P : Ω 𝓤} {y y' : 𝟚-mod P}
            → pr₁ y ＝ pr₁ y' → y ＝ y'
to-𝟚-mod-＝ {𝓤} {P} = to-subtype-＝ (λ y → being-in-the-image-is-prop y (χ P))

\end{code}

The two points of 𝟚-mod P are equal exactly when P holds, and every
element of 𝟚-mod P is merely one of them.

\begin{code}

points-of-𝟚-mod-are-equal-iff : {𝓤 : Universe} (P : Ω 𝓤)
                              → [ ₀ ] ＝ [ ₁ ] ↔ P holds
points-of-𝟚-mod-are-equal-iff P = I , II
 where
  I : [ ₀ ] ＝ [ ₁ ] → P holds
  I e = equal-⊤-gives-holds P (ap pr₁ e ⁻¹)

  II : P holds → [ ₀ ] ＝ [ ₁ ]
  II p = to-𝟚-mod-＝ (holds-gives-equal-⊤ pe fe P p ⁻¹)

𝟚-mod-induction : {𝓤 : Universe} (P : Ω 𝓤) (y : 𝟚-mod P)
                → ∥ (y ＝ [ ₀ ]) + (y ＝ [ ₁ ]) ∥
𝟚-mod-induction P y = ∥∥-functor γ (corestrictions-are-surjections (χ P) y)
 where
  γ : (Σ i ꞉ 𝟚 , [ i ] ＝ y) → (y ＝ [ ₀ ]) + (y ＝ [ ₁ ])
  γ (₀ , e) = inl (e ⁻¹)
  γ (₁ , e) = inr (e ⁻¹)

\end{code}

Overt connectedness. To avoid size issues we take the subsets in the
universe of propositions 𝓤 ⊔ 𝓦, where 𝓦 is the universe of X, so that
the proposition that two subsets meet lives there too.

\begin{code}

is-overtly-connected : (𝓤 : Universe) {𝓦 : Universe} → 𝓦 ̇ → (𝓤 ⊔ 𝓦) ⁺ ̇
is-overtly-connected 𝓤 {𝓦} X =
   (U V : X → Ω (𝓤 ⊔ 𝓦))
 → ((x : X) → U x holds ∨ V x holds)
 → (∃ x ꞉ X , U x holds)
 → (∃ x ꞉ X , V x holds)
 → ∃ x ꞉ X , U x holds × V x holds

\end{code}

The key construction. Given a cover of X by U and V, let M be the
proposition that U and V meet. Then x ↦ (V x → M) is a map from X to
𝟚-mod M, which takes the value [ ₀ ] on U and the value [ ₁ ] on V.
Hence, if 𝟚-mod M is X-null, so that this map is constant, and both U
and V are inhabited, then [ ₀ ] ＝ [ ₁ ], that is, M holds.

The map takes values in 𝟚-mod M without any case analysis on the
disjunction, which is why no truncation elimination into sets is
needed.

\begin{code}

meet : {𝓤 𝓦 : Universe} {X : 𝓦 ̇ } → (X → Ω (𝓤 ⊔ 𝓦)) → (X → Ω (𝓤 ⊔ 𝓦))
     → Ω (𝓤 ⊔ 𝓦)
meet {𝓤} {𝓦} {X} U V = (∃ x ꞉ X , U x holds × V x holds) , ∃-is-prop

module _ {𝓤 𝓦 : Universe}
         {X : 𝓦 ̇ }
         (U V : X → Ω (𝓤 ⊔ 𝓦))
         (cover : (x : X) → U x holds ∨ V x holds)
       where

 private
  M : Ω (𝓤 ⊔ 𝓦)
  M = meet {𝓤} {𝓦} U V

 classifier : X → 𝟚-mod M
 classifier x = Q , ∥∥-functor γ (cover x)
  where
   Q : Ω (𝓤 ⊔ 𝓦)
   Q = (V x holds → M holds) , Π-is-prop fe (λ _ → holds-is-prop M)

   γ : U x holds + V x holds → Σ i ꞉ 𝟚 , χ M i ＝ Q
   γ (inl u) = ₀ , (holds-gives-equal-⊤ pe fe Q (λ v → ∣ x , u , v ∣) ⁻¹)
   γ (inr v) = ₁ , Ω-extensionality pe fe (λ m _ → m) (λ f → f v)

 classifier-on-U : (x : X) → U x holds → classifier x ＝ [ ₀ ]
 classifier-on-U x u =
  to-𝟚-mod-＝ (holds-gives-equal-⊤ pe fe _ (λ v → ∣ x , u , v ∣))

 classifier-on-V : (x : X) → V x holds → classifier x ＝ [ ₁ ]
 classifier-on-V x v =
  to-𝟚-mod-＝ (Ω-extensionality pe fe (λ f → f v) (λ m _ → m))

 meet-from-nullness : is-null X (𝟚-mod M)
                    → (∃ x ꞉ X , U x holds)
                    → (∃ x ꞉ X , V x holds)
                    → M holds
 meet-from-nullness ν = ∥∥-rec₂ (holds-is-prop M) γ
  where
   γ : (Σ x ꞉ X , U x holds) → (Σ x ꞉ X , V x holds) → M holds
   γ (a , u) (b , v) =
    lr-implication (points-of-𝟚-mod-are-equal-iff M)
     ([ ₀ ]          ＝⟨ classifier-on-U a u ⁻¹ ⟩
      classifier a   ＝⟨ lr-implication
                          (null-iff-maps-are-constant fe X b (𝟚-mod M))
                          ν classifier a ⟩
      classifier b   ＝⟨ classifier-on-V b v ⟩
      [ ₁ ]          ∎)

\end{code}

The criterion: a pointed type X is overtly connected if and only if
every set 𝟚-mod P is X-null.

For the converse direction, given a map g : X → 𝟚-mod P, we cover X by
the two subsets where g takes the value [ ₀ ] and where it takes the
value [ ₁ ]. These are expressed in Ω (𝓤 ⊔ 𝓦), rather than as
identity types of 𝟚-mod P, which live in a larger universe. Where
they meet, P holds, so that g is constant.

\begin{code}

overtly-connected-iff-𝟚-mod-null
 : {𝓤 𝓦 : Universe} (X : 𝓦 ̇ )
 → X
 → is-overtly-connected 𝓤 X ↔ ((P : Ω (𝓤 ⊔ 𝓦)) → is-null X (𝟚-mod P))
overtly-connected-iff-𝟚-mod-null {𝓤} {𝓦} X x₀ = I , II
 where
  II : ((P : Ω (𝓤 ⊔ 𝓦)) → is-null X (𝟚-mod P)) → is-overtly-connected 𝓤 X
  II ν U V cover = meet-from-nullness {𝓤} {𝓦} U V cover
                    (ν (meet {𝓤} {𝓦} U V))

  I : is-overtly-connected 𝓤 X → (P : Ω (𝓤 ⊔ 𝓦)) → is-null X (𝟚-mod P)
  I oc P = rl-implication (null-iff-maps-are-constant fe X x₀ (𝟚-mod P)) γ
   where
    γ : (g : X → 𝟚-mod P) (x : X) → g x ＝ g x₀
    γ g x = ∥∥-rec₂ (𝟚-mod-is-set P) δ (𝟚-mod-induction P (g x))
                                      (𝟚-mod-induction P (g x₀))
     where
      U V : X → Ω (𝓤 ⊔ 𝓦)
      U y = pr₁ (g y)
      V y = (pr₁ (g y) holds ↔ P holds) ,
            ×-is-prop (Π-is-prop fe (λ _ → holds-is-prop P))
                      (Π-is-prop fe (λ _ → holds-is-prop (pr₁ (g y))))

      U-from-[₀] : (y : X) → g y ＝ [ ₀ ] → U y holds
      U-from-[₀] y e = transport⁻¹ _holds (ap pr₁ e) ⋆

      V-from-[₁] : (y : X) → g y ＝ [ ₁ ] → V y holds
      V-from-[₁] y e = transport⁻¹ (λ - → - holds ↔ P holds) (ap pr₁ e)
                        (id , id)

      cover : (y : X) → U y holds ∨ V y holds
      cover y = ∥∥-functor ε (𝟚-mod-induction P (g y))
       where
        ε : (g y ＝ [ ₀ ]) + (g y ＝ [ ₁ ]) → U y holds + V y holds
        ε (inl e) = inl (U-from-[₀] y e)
        ε (inr e) = inr (V-from-[₁] y e)

      P-from-meet : (∃ y ꞉ X , U y holds × V y holds) → P holds
      P-from-meet = ∥∥-rec (holds-is-prop P) (λ (y , u , (f , _)) → f u)

      [₀]-is-[₁] : (∃ y ꞉ X , U y holds × V y holds) → [ ₀ ] ＝ [ ₁ ]
      [₀]-is-[₁] m = rl-implication (points-of-𝟚-mod-are-equal-iff P)
                      (P-from-meet m)

      δ : (g x ＝ [ ₀ ]) + (g x ＝ [ ₁ ])
        → (g x₀ ＝ [ ₀ ]) + (g x₀ ＝ [ ₁ ])
        → g x ＝ g x₀
      δ (inl e) (inl e') = e ∙ e' ⁻¹
      δ (inr e) (inr e') = e ∙ e' ⁻¹
      δ (inl e) (inr e') =
       e ∙ [₀]-is-[₁] (oc U V cover ∣ x , U-from-[₀] x e ∣
                                    ∣ x₀ , V-from-[₁] x₀ e' ∣) ∙ e' ⁻¹
      δ (inr e) (inl e') =
       e ∙ [₀]-is-[₁] (oc U V cover ∣ x₀ , U-from-[₀] x₀ e' ∣
                                    ∣ x , V-from-[₁] x e ∣) ⁻¹ ∙ e' ⁻¹

\end{code}

The approximate intermediate value theorem. We state it with real
bounds p < q in place of c - ε < c + ε, which avoids arithmetic: if
f a < q and p < f b, then some x has p < f x < q. The two subsets
{x | f x < q} and {x | p < f x} cover ℝ by weak linearity of the order,
which is where the locatedness of Dedekind reals is used.

Since ℝ lives in 𝓤₁, we lift these 𝓤₀-valued subsets to 𝓤₁.

\begin{code}

open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import Notation.Order
open import UF.UniverseEmbedding

below above : (ℝ → ℝ) → ℝ → ℝ → Ω 𝓤₁
below f q x = Lift 𝓤₁ (f x < q) , ×-is-prop (<-is-prop (f x) q) 𝟙-is-prop
above f p x = Lift 𝓤₁ (p < f x) , ×-is-prop (<-is-prop p (f x)) 𝟙-is-prop

below-above-cover : (f : ℝ → ℝ) (p q : ℝ)
                  → p < q
                  → (x : ℝ) → below f q x holds ∨ above f p x holds
below-above-cover f p q p<q x = ∥∥-functor γ (weak-linearity p q (f x) p<q)
 where
  γ : (p < f x) + (f x < q) → below f q x holds + above f p x holds
  γ (inl l) = inr (lift 𝓤₁ l)
  γ (inr l) = inl (lift 𝓤₁ l)

approximate-root-from-meet
 : (f : ℝ → ℝ) (p q : ℝ)
 → meet {𝓤₀} {𝓤₁} (below f q) (above f p) holds
 → ∃ x ꞉ ℝ , (p < f x) × (f x < q)
approximate-root-from-meet f p q =
 ∥∥-functor (λ (x , l , l') → x , lower l' , lower l)

approximate-IVT-from-𝟚-mod-nullness
 : ((P : Ω 𝓤₁) → is-null ℝ (𝟚-mod P))
 → (f : ℝ → ℝ) (p q a b : ℝ)
 → p < q
 → f a < q
 → p < f b
 → ∃ x ꞉ ℝ , (p < f x) × (f x < q)
approximate-IVT-from-𝟚-mod-nullness ν f p q a b p<q fa<q p<fb =
 approximate-root-from-meet f p q
  (meet-from-nullness {𝓤₀} {𝓤₁} (below f q) (above f p)
    (below-above-cover f p q p<q)
    (ν (meet {𝓤₀} {𝓤₁} (below f q) (above f p)))
    ∣ a , lift 𝓤₁ fa<q ∣
    ∣ b , lift 𝓤₁ p<fb ∣)

\end{code}
