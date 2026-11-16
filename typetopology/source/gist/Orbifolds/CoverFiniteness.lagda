Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026; prose updated 13 November 2026, after the
final audits. Orbifold gate H7 of Fable's roadmap [1].

Finiteness under cover-properness, abstractly
---------------------------------------------

GPT-6 Astra's argument [2], summarized in Section 3.6 of the roadmap
[1]: let G be a pregroupoid whose arrows are covered by charts on which
the source map s is injective. If each fibre of the anchor
a = (s , t) : G₁ → G₀ × G₀ lies in finitely many charts (the
consequence of cover-properness for fibres, roadmap Section 2.1), and
the charts are Penon open [3, Definition 6.2.6], then every hom-set
G(x , y) is properly finite in Myers's sense [3, Definition 6.1.3, first
sentence], and so are the identity types of the Rezk completion. Here
the charts are abstract data. Topology supplies the ordinary
topologies and Myers's Lemma 6.2.7 (opens of a regular space are
Penon open); CoverProperness supplies the official definition of
cover-properness.

  is-Penon-open : Myers's Definition 6.2.6, with "either … or" read as
  the truncated disjunction ∨;

  sets-with-finite-chart-covers-are-properly-finite : a set covered by
  finitely many Penon-open subtypes, each with at most one element, is
  properly finite [2, Sections 2 and 3];

  hom-sets-are-properly-finite : the hom-sets of a pregroupoid whose
  objects form a set, with charts as above [2, Sections 1–3];

  identity-types-of-Rezk-completions-are-properly-finite : under
  univalence, if the hom-sets are properly finite then so are the
  identity types of the Rezk completion [2, Section 4].

The fibre of the anchor over (x , y) is G(x , y); the hypothesis on
fibres is stated for the anchor itself, as gate H9 derives it from
cover-properness (CoverProperness). The index type of the charts is
arbitrary here; for the chart cover of T1 it is a crisp subtype of ℕ
(EtaleSourceMaps, CrispCoverFiniteness). The membership
propositions of the charts live in the universe of the morphisms, so
that the enumerating type does too.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Sections 2.1, 3.6 and 4.
    references/F01-orbifolds-roadmap-rev2.md
[2] GPT-6 Astra. Main aim: finiteness from the current open-cover
    properness condition, 11 November 2026.
    references/A03-cover-finiteness.txt
[3] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module gist.Orbifolds.CoverFiniteness
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import Fin.Type using (Fin)
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.ImageAndSurjection pt
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Univalence

open import gist.Orbifolds.ProperFiniteness fe pt
open import gist.Orbifolds.AbstractOrbifolds fe pt
 using (has-properly-finite-identity-types)

\end{code}

Penon open subtypes [3, Definition 6.2.6], charts on which a map is
injective, and the consequence of cover-properness for fibres: each
fibre lies in finitely many charts.

\begin{code}

is-Penon-open : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-Penon-open {X = X} U = (x : X) → U x → (y : X) → (x ≠ y) ∨ U y

is-injective-on-charts : {E : 𝓤 ̇ } {B : 𝓥 ̇ } {I : 𝓦 ̇ }
                       → (E → B) → (I → E → 𝓣 ̇ ) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
is-injective-on-charts {E = E} {I = I} p V =
 (i : I) (e e' : E) → V i e → V i e' → p e ＝ p e' → e ＝ e'

fibres-lie-in-finitely-many-charts : {E : 𝓤 ̇ } {B : 𝓥 ̇ } {I : 𝓦 ̇ }
                                   → (E → B) → (I → E → 𝓣 ̇ )
                                   → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
fibres-lie-in-finitely-many-charts {B = B} {I = I} p V =
 (b : B) → ∃ n ꞉ ℕ , Σ F ꞉ (Fin n → I) ,
            ((e : fiber p b) → ∃ j ꞉ Fin n , V (F j) (pr₁ e))

\end{code}

The finiteness argument [2, Sections 2 and 3]. Let H be a set covered
by finitely many subtypes U₀, …, U₍ₙ₋₁₎, each with at most one element
and Penon open. The type of pairs of an index j and an element of U_j
embeds into Fin n and maps onto H, so H is subfinitely enumerable. For
h and k in H, choose j with h in U_j: either h ≠ k, or k is in U_j and
then h = k. Both conclusions are propositions, so the mere choices are
allowed.

\begin{code}

sets-with-finite-chart-covers-are-properly-finite
 : {H : 𝓤 ̇ }
 → is-set H
 → (n : ℕ) (U : Fin n → H → 𝓤 ̇ )
 → ((j : Fin n) (h : H) → is-prop (U j h))
 → ((j : Fin n) (h h' : H) → U j h → U j h' → h ＝ h')
 → ((j : Fin n) → is-Penon-open (U j))
 → ((h : H) → ∃ j ꞉ Fin n , U j h)
 → is-properly-finite H
sets-with-finite-chart-covers-are-properly-finite
 {𝓤} {H} H-is-set n U U-is-prop U-is-subsingleton U-is-Penon-open U-covers =
 d , ∣ n , S , (pr₁ , pr₁-is-embedding members-are-unique) ,
              (member , member-is-surjection) ∣
 where
  S : 𝓤 ̇
  S = Σ j ꞉ Fin n , Σ h ꞉ H , U j h

  members-are-unique : (j : Fin n) → is-prop (Σ h ꞉ H , U j h)
  members-are-unique j (h , u) (h' , u') =
   to-subtype-＝ (U-is-prop j) (U-is-subsingleton j h h' u u')

  member : S → H
  member (j , h , u) = h

  member-is-surjection : is-surjection member
  member-is-surjection h =
   ∥∥-functor (λ (j , u) → (j , h , u) , refl) (U-covers h)

  d : is-discrete H
  d h k = ∥∥-rec (decidability-of-prop-is-prop fe H-is-set) γ (U-covers h)
   where
    γ : (Σ j ꞉ Fin n , U j h) → is-decidable (h ＝ k)
    γ (j , u) = ∥∥-rec (decidability-of-prop-is-prop fe H-is-set)
                 (cases inr (λ u' → inl (U-is-subsingleton j h k u u')))
                 (U-is-Penon-open j h u k)

\end{code}

Two pairs with the same first component in a set are equal only if
their second components are.

\begin{code}

second-components-agree : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                        → is-set X
                        → {x : X} {y y' : Y x}
                        → _＝_ {_} {Σ Y} (x , y) (x , y')
                        → y ＝ y'
second-components-agree {𝓤} {𝓥} {X} {Y} X-is-set {x} {y} {y'} p =
 transport (λ - → transport Y - y ＝ y')
  (X-is-set (pr₁ (from-Σ-＝ p)) refl)
  (pr₂ (from-Σ-＝ p))

\end{code}

Hom-sets [2, Sections 1–3], and the identity types of the Rezk
completion [2, Section 4]: the Yoneda embedding identifies G(x , x')
with the identifications of y x and y x', and it is surjective.

\begin{code}

module _ {𝓤 𝓦 : Universe} where

 open import gist.Orbifolds.RezkCompletion fe pt {𝓤} {𝓦}

 module _ (G : Pregroupoid) where

  open Pregroupoid G

  anchor : arrows G → ob × ob
  anchor (x , x' , g) = x , x'

  hom-sets-are-properly-finite
   : is-set ob
   → {𝓘 : Universe} {I : 𝓘 ̇ } (V : I → arrows G → 𝓤 ̇ )
   → ((i : I) (f : arrows G) → is-prop (V i f))
   → is-injective-on-charts (source G) V
   → ((i : I) → is-Penon-open (V i))
   → fibres-lie-in-finitely-many-charts anchor V
   → (x y : ob) → is-properly-finite (hom x y)
  hom-sets-are-properly-finite ob-is-set {𝓘} {I} V V-is-prop V-is-injective
                               V-is-Penon-open V-is-finite x y =
   ∥∥-rec being-properly-finite-is-prop γ (V-is-finite (x , y))
   where
    ι : hom x y → arrows G
    ι h = x , y , h

    ι-is-lc : (h h' : hom x y) → ι h ＝ ι h' → h ＝ h'
    ι-is-lc h h' p = second-components-agree ob-is-set
                      (second-components-agree ob-is-set p)

    γ : (Σ n ꞉ ℕ , Σ F ꞉ (Fin n → I) ,
           ((e : fiber anchor (x , y)) → ∃ j ꞉ Fin n , V (F j) (pr₁ e)))
      → is-properly-finite (hom x y)
    γ (n , F , c) =
     sets-with-finite-chart-covers-are-properly-finite (hom-is-set x y) n
      (λ j h → V (F j) (ι h))
      (λ j h → V-is-prop (F j) (ι h))
      (λ j h h' u u' →
        ι-is-lc h h' (V-is-injective (F j) (ι h) (ι h') u u' refl))
      (λ j h u k → ∥∥-functor (cases (λ ν → inl (λ p → ν (ap ι p))) inr)
                    (V-is-Penon-open (F j) (ι h) u (ι k)))
      (λ h → c (ι h , refl))

  module _ (ua : is-univalent 𝓤) where

   identity-types-of-Rezk-completions-are-properly-finite
    : ((x y : ob) → is-properly-finite (hom x y))
    → has-properly-finite-identity-types (Rezk-completion G)
   identity-types-of-Rezk-completions-are-properly-finite φ F F' =
    ∥∥-rec being-properly-finite-is-prop
     (λ (x , p) → ∥∥-rec being-properly-finite-is-prop
                   (λ (x' , p') →
                     transport₂ (λ A B → is-properly-finite (A ＝ B))
                                   p p' (γ x x'))
                   (yoneda-embedding-is-surjection G ua F'))
     (yoneda-embedding-is-surjection G ua F)
    where
     γ : (x x' : ob)
       → is-properly-finite (yoneda-embedding G x ＝ yoneda-embedding G x')
     γ x x' = properly-finite-types-are-closed-under-equivalence'
               (hom-≃-identifications G ua x x') (φ x x')

\end{code}
