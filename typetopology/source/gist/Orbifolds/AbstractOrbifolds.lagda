Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. Orbifold gate H2 of Fable's roadmap [2].

Abstract orbifolds: pullbacks and inertia
-----------------------------------------

Myers [1, Definition 1.1.2] defines an orbifold as a microlinear type
whose identity types are properly finite. Here microlinearity is taken
relative to an arbitrary family σ : T → Test-Square 𝓥 of test squares
(TestSquares): X is microlinear for σ if it is σ t-local for every t.
Gate H8 instantiates σ with Myers's infinitesimal R-pushouts; until
then the results below are intermediate results in the sense of [2,
Section 5]: the targets over the abstract interface of layer L2.

  T3 (abstract)  pullbacks-of-orbifolds-are-orbifolds.
                 If B, C, D are orbifolds and f : B → D, g : C → D,
                 then B ×_D C is an orbifold. Nothing is crisp.
                 This is Myers's Proposition 6.4.2 [1] with the
                 abstract notion of microlinearity.

  T4 (abstract)  inertia-of-orbifolds-are-orbifolds.
                 If X is an orbifold, so is (x : X) × (x ＝ x).
                 This is Myers's Definition 6.4.3 and Corollary 6.4.4
                 [1] with the abstract notion of microlinearity.

B ×_D C is TypeTopology's pullback, (Σ (b , c) ꞉ B × C , f b ＝ g c),
of UF.Pullback. The universes of B, C and D are arbitrary.

The proofs are those of GPT-6 Astra [3, Sections 4–6], except that the
inertia type is treated directly, as the identity family of X pulled
back along the diagonal, rather than as the pullback of the diagonal
along itself; for its identity types this gives a subtype of x ＝ y
instead of a subtype of a product. Identity types: an identification
in a Σ-type whose family has sets as values is a subtype of the
identification of first components (Σ-identity-types-are-properly-finite).
For the pullback the family is (b , c) ↦ (f b ＝ g c), whose values
are sets because the identity types of D are properly finite, hence
have decidable equality; for inertia it is x ↦ (x ＝ x). Microlinearity
is TestSquares, square by square.

The unit type and binary products of orbifolds are orbifolds, and
orbifolds are closed under equivalence within a universe; [3, Section
6] uses the first two for its route to inertia.

[1] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.
[2] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Sections 2.2, 3.8 and 5.
    references/F01-orbifolds-roadmap-rev2.md
[3] GPT-6 Astra. All of Myers Section 6.4 over the adopted five-item
    core, 11 November 2026.
    references/A01-section-6-4-over-the-core.txt

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module gist.Orbifolds.AbstractOrbifolds
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open import UF.Base
open import UF.Embeddings using (ap-is-equiv)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Pullback
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-Properties using (props-are-sets)

open import gist.Orbifolds.ProperFiniteness fe pt
open import gist.Orbifolds.TestSquares fe

\end{code}

Properly finite identity types, and the identity types of Σ-types.

\begin{code}

has-properly-finite-identity-types : 𝓤 ̇ → 𝓤 ⁺ ̇
has-properly-finite-identity-types X = (x y : X) → is-properly-finite (x ＝ y)

Σ-identity-types-are-properly-finite
 : {A : 𝓤 ̇ } (E : A → 𝓥 ̇ )
 → ((a : A) → is-set (E a))
 → (u v : Σ E)
 → is-properly-finite (pr₁ u ＝ pr₁ v)
 → is-properly-finite (u ＝ v)
Σ-identity-types-are-properly-finite E E-is-set-valued u v =
 properly-finite-sums-of-props
  (λ p → transport E p (pr₂ u) ＝ pr₂ v)
  (λ p → E-is-set-valued (pr₁ v))
  Σ-＝-≃

\end{code}

Microlinearity for a family of test squares, and orbifolds.

\begin{code}

module _ {𝓣 𝓥 : Universe} {T : 𝓣 ̇ } (σ : T → Test-Square 𝓥) where

 is-microlinear : 𝓤 ̇ → 𝓣 ⊔ 𝓥 ⊔ 𝓤 ̇
 is-microlinear X = (t : T) → is-local (σ t) X

 is-orbifold : 𝓤 ̇ → 𝓣 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 is-orbifold X = is-microlinear X × has-properly-finite-identity-types X

\end{code}

T3, abstract: pullbacks of orbifolds are orbifolds.

\begin{code}

 pullbacks-of-orbifolds-are-orbifolds
  : {B : 𝓤 ̇ } {C : 𝓤' ̇ } {D : 𝓦 ̇ }
  → is-orbifold B
  → is-orbifold C
  → is-orbifold D
  → (f : B → D) (g : C → D)
  → is-orbifold (pullback.pullback f g)
 pullbacks-of-orbifolds-are-orbifolds (mB , iB) (mC , iC) (mD , iD) f g =
  (λ t → pullbacks-of-local-types-are-local (σ t) f g (mB t) (mC t) (mD t)) ,
  (λ u v → Σ-identity-types-are-properly-finite
            (λ (z : _ × _) → f (pr₁ z) ＝ g (pr₂ z))
            (λ z → properly-finite-types-are-sets (iD (f (pr₁ z)) (g (pr₂ z))))
            u v
            (properly-finite-types-are-closed-under-equivalence (≃-sym ×-＝-≃)
              (properly-finite-products (iB _ _) (iC _ _))))

\end{code}

T4, abstract: inertia types of orbifolds are orbifolds.

\begin{code}

 inertia-of-orbifolds-are-orbifolds : {X : 𝓤 ̇ }
                                    → is-orbifold X
                                    → is-orbifold (Σ x ꞉ X , x ＝ x)
 inertia-of-orbifolds-are-orbifolds (m , i) =
  (λ t → inertia-of-local-types-is-local (σ t) (m t)) ,
  (λ u v → Σ-identity-types-are-properly-finite
            (λ x → x ＝ x)
            (λ x → properly-finite-types-are-sets (i x x))
            u v
            (i (pr₁ u) (pr₁ v)))

\end{code}

The unit type, binary products, and closure under equivalence.

\begin{code}

 𝟙-is-orbifold : is-orbifold (𝟙 {𝓤})
 𝟙-is-orbifold = (λ t → 𝟙-is-local (σ t)) ,
                 (λ x y → props-are-properly-finite (props-are-sets 𝟙-is-prop))

 products-of-orbifolds-are-orbifolds : {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                                     → is-orbifold X
                                     → is-orbifold Y
                                     → is-orbifold (X × Y)
 products-of-orbifolds-are-orbifolds (m , i) (m' , i') =
  (λ t → ×-is-local (σ t) (m t) (m' t)) ,
  (λ u v → properly-finite-types-are-closed-under-equivalence (≃-sym ×-＝-≃)
            (properly-finite-products (i _ _) (i' _ _)))

 orbifolds-are-closed-under-equivalence : {X Y : 𝓤 ̇ }
                                        → X ≃ Y
                                        → is-orbifold X
                                        → is-orbifold Y
 orbifolds-are-closed-under-equivalence φ (m , i) =
  (λ t → local-types-are-closed-under-equivalence (σ t) φ (m t)) ,
  (λ y y' → properly-finite-types-are-closed-under-equivalence
             (≃-sym (ap ⌜ φ ⌝⁻¹ , ap-is-equiv ⌜ φ ⌝⁻¹ (⌜⌝⁻¹-is-equiv φ)))
             (i (⌜ φ ⌝⁻¹ y) (⌜ φ ⌝⁻¹ y')))

\end{code}
