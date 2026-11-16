Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), for gate WG2 of Claude Fable
5.2's plan for the comparison of Weil algebras with presentations [1],
as reviewed by GPT-6 Astra [2], amended by Fable's addendum 01 [3] and
released by Astra [4]. The exported names, and the universes and
hypotheses of their statements, are those of the plan's statement
companion; the proofs are Claude Opus 5.5's. See the AI disclosure in
gist.RealCohesion.index.

Presented algebras from set quotients
-------------------------------------

Let g : Fin m → Poly n be a finite family of polynomial expressions of
gist.Orbifolds.SmoothLine. The algebra presented by g is the quotient of
the existing type Poly n by the congruence that the laws of a
commutative ring, the laws of the constants and the relations generate.

  congruence._≈₀_ : the inductive family of derivations: reflexivity,
  symmetry, transitivity, compatibility with ⊕ and ⊗, the eight laws of
  a commutative ring (with additive inverses, the negative of p being
  con (-ᴿ 1ᴿ) ⊗ p, so that Poly needs no new constructor), the laws
  con r ⊕ con s ≈₀ con (r +ᴿ s) and con r ⊗ con s ≈₀ con (r ·ᴿ s), and
  the relations g j ≈₀ con 0ᴿ. The law ⊕-inverse is a constructor: the
  other laws are those of a commutative semiring and of the constants,
  and they do not give additive inverses. This congruence is formal;
  it is not equality of values at the points of R.

  congruence._≈_, congruence.≋ : its propositional truncation, an
  equivalence relation with values in 𝓤₀.

  congruence.soundness : in every algebra 𝓑, with carrier in any
  universe, and at every point b at which every g j vanishes, related
  expressions have equal values. The proof is by induction on the
  derivation; the case ⊕-inverse is minus-one-times of
  gist.Orbifolds.Algebras.

For a family ℓ of universes with sq : general-set-quotients-exist ℓ, the
interface of TypeTopology's Quotient.Type, the carrier Q is Poly n / ≋, a
type in 𝓤₀ ⊔ ℓ 𝓤₀, which is ℓ 𝓤₀. Its constants 0, 1 and ι r are the
classes of con 0ᴿ, con 1ᴿ and con r; addition and multiplication descend
from ⊕ and ⊗ by extension₂/, and the negative from p ↦ con (-ᴿ 1ᴿ) ⊗ p by
extension₁/, all three on the strength of the compatibility constructors.
On classes they compute by naturality/ and naturality₂/
(+Q-on-classes, ·Q-on-classes, -Q-on-classes). The eight ring laws hold
by /-induction, /-induction₂ and /-induction₃, because each holds of the
representatives up to a single constructor, and the three laws of the
structure map by con-⊕, con-⊗ and refl. This is quotient-algebra.

  class-of-var, values-at-the-generators : the generators are the classes
  of the variables, and the value of every expression p at them is the
  class of p, by induction on p.

  presented-algebras-from-quotients : the instance of the interface of
  gist.Orbifolds.PresentedAlgebras, at the universe ℓ 𝓤₀.
  (P1) The class of g j is the class of con 0ᴿ, by the constructor
  relation.
  (P2) For 𝓑 and b as above, the map p ↦ ⟦ p ⟧[ 𝓑 ] b identifies related
  expressions, by soundness, and so has a mediating map on Q
  (mediating-map/); it is a homomorphism, by induction on classes, and
  takes the generators to b. Any homomorphism that takes the generators
  to b agrees with it on every class, by values-at-the-generators,
  values-under-homs and values-at-equal-points, hence everywhere
  (at-most-one-mediating-map/). So the Σ-type of (P2) is a singleton.
  (P3) Every element of Q is merely a class (η/-is-surjection), and the
  class of p is the value of p at the generators.

No effectivity of the quotient is used: the construction never needs to
recover a derivation from an equation of classes.

Assumptions: function extensionality and propositional truncations, as
in SmoothLine; the set quotients are the explicit parameter sq of the
construction. No crisp datum, choice, resizing, univalence or
propositional extensionality is assumed, and the module adds no option
and no postulate.

[1] Claude Fable 5.2. Plan: formalizing the comparison of Weil algebras
    with presentations, 13 November 2026, Sections 2 and 4.2, with its
    statement companion, Section WG2 (plan SHA-256 b1662ecc…; companion
    SHA-256 47974af8…).
[2] GPT-6 Astra. Review of Fable's Weil plan, 13 November 2026
    (FABLE-WEIL-PLAN-REVIEW-01).
[3] Claude Fable 5.2. Addendum 01 to the plan, 13 November 2026
    (SHA-256 abf31923…).
[4] GPT-6 Astra. Release of gate WG2, 13 November 2026
    (SHA-256 998a4fb0…).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.PresentedAlgebrasFromQuotients
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (𝓡 : Commutative-Ring)
       where

open import Fin.Type
open import Quotient.Type
open import UF.Base hiding (_≈_)
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open PropositionalTruncation pt
open smooth-line fe pt 𝓡
open import gist.Orbifolds.Algebras fe pt 𝓡
open import gist.Orbifolds.PresentedAlgebras fe pt 𝓡

module congruence {n m : ℕ} (g : Fin m → Poly n) where

 data _≈₀_ : Poly n → Poly n → 𝓤₀ ̇ where
  ≈₀-refl    : (p : Poly n) → p ≈₀ p
  ≈₀-sym     : {p q : Poly n} → p ≈₀ q → q ≈₀ p
  ≈₀-trans   : {p q r : Poly n} → p ≈₀ q → q ≈₀ r → p ≈₀ r
  ⊕-cong     : {p p' q q' : Poly n} → p ≈₀ p' → q ≈₀ q' → (p ⊕ q) ≈₀ (p' ⊕ q')
  ⊗-cong     : {p p' q q' : Poly n} → p ≈₀ p' → q ≈₀ q' → (p ⊗ q) ≈₀ (p' ⊗ q')
  ⊕-assoc    : (p q r : Poly n) → ((p ⊕ q) ⊕ r) ≈₀ (p ⊕ (q ⊕ r))
  ⊕-comm     : (p q : Poly n) → (p ⊕ q) ≈₀ (q ⊕ p)
  ⊕-unit     : (p : Poly n) → (p ⊕ con 0ᴿ) ≈₀ p
  ⊕-inverse  : (p : Poly n) → (p ⊕ (con (-ᴿ 1ᴿ) ⊗ p)) ≈₀ con 0ᴿ
  ⊗-assoc    : (p q r : Poly n) → ((p ⊗ q) ⊗ r) ≈₀ (p ⊗ (q ⊗ r))
  ⊗-comm     : (p q : Poly n) → (p ⊗ q) ≈₀ (q ⊗ p)
  ⊗-unit     : (p : Poly n) → (p ⊗ con 1ᴿ) ≈₀ p
  ⊗-distr    : (p q r : Poly n) → (p ⊗ (q ⊕ r)) ≈₀ ((p ⊗ q) ⊕ (p ⊗ r))
  con-⊕      : (r s : R) → (con r ⊕ con s) ≈₀ con (r +ᴿ s)
  con-⊗      : (r s : R) → (con r ⊗ con s) ≈₀ con (r ·ᴿ s)
  relation   : (j : Fin m) → g j ≈₀ con 0ᴿ

 _≈_ : Poly n → Poly n → 𝓤₀ ̇
 p ≈ q = ∥ p ≈₀ q ∥

 ≋ : EqRel {𝓤₀} {𝓤₀} (Poly n)
 ≋ = _≈_ ,
     (λ p q → ∥∥-is-prop) ,
     (λ p → ∣ ≈₀-refl p ∣) ,
     (λ p q → ∥∥-functor ≈₀-sym) ,
     (λ p q r → ∥∥-functor₂ ≈₀-trans)

 negative : Poly n → Poly n
 negative p = con (-ᴿ 1ᴿ) ⊗ p

 ⊕-respects-≈ : {p q p' q' : Poly n} → p ≈ p' → q ≈ q' → (p ⊕ q) ≈ (p' ⊕ q')
 ⊕-respects-≈ = ∥∥-functor₂ ⊕-cong

 ⊗-respects-≈ : {p q p' q' : Poly n} → p ≈ p' → q ≈ q' → (p ⊗ q) ≈ (p' ⊗ q')
 ⊗-respects-≈ = ∥∥-functor₂ ⊗-cong

 negative-respects-≈ : {p q : Poly n} → p ≈ q → negative p ≈ negative q
 negative-respects-≈ = ∥∥-functor (⊗-cong (≈₀-refl (con (-ᴿ 1ᴿ))))

 soundness
  : {𝓦 : Universe} (𝓑 : Algebra 𝓦) (b : Fin n → ⟨ 𝓑 ⟩)
  → ((j : Fin m) → ⟦ g j ⟧[ 𝓑 ] b ＝ Algebra.0ᴬ 𝓑)
  → {p q : Poly n} → p ≈₀ q → ⟦ p ⟧[ 𝓑 ] b ＝ ⟦ q ⟧[ 𝓑 ] b
 soundness 𝓑 b s = γ
  where
   open Algebra 𝓑

   v : Poly n → A
   v p = ⟦ p ⟧[ 𝓑 ] b

   γ : {p q : Poly n} → p ≈₀ q → v p ＝ v q
   γ (≈₀-refl p)     = refl
   γ (≈₀-sym d)      = (γ d)⁻¹
   γ (≈₀-trans d e)  = γ d ∙ γ e
   γ (⊕-cong d e)    = ap₂ _+ᴬ_ (γ d) (γ e)
   γ (⊗-cong d e)    = ap₂ _·ᴬ_ (γ d) (γ e)
   γ (⊕-assoc p q r) = +ᴬ-assoc (v p) (v q) (v r)
   γ (⊕-comm p q)    = +ᴬ-comm (v p) (v q)
   γ (⊕-unit p)      = ap (v p +ᴬ_) (ι-preserves-0 𝓑) ∙ +ᴬ-unit (v p)
   γ (⊕-inverse p)   = minus-one-times 𝓑 (v p) ∙ (ι-preserves-0 𝓑)⁻¹
   γ (⊗-assoc p q r) = ·ᴬ-assoc (v p) (v q) (v r)
   γ (⊗-comm p q)    = ·ᴬ-comm (v p) (v q)
   γ (⊗-unit p)      = ap (v p ·ᴬ_) ι-preserves-1 ∙ ·ᴬ-unit (v p)
   γ (⊗-distr p q r) = distributivityᴬ (v p) (v q) (v r)
   γ (con-⊕ r s)     = (ι-preserves-+ r s)⁻¹
   γ (con-⊗ r s)     = (ι-preserves-· r s)⁻¹
   γ (relation j)    = s j ∙ (ι-preserves-0 𝓑)⁻¹

 soundness-for-≈
  : {𝓦 : Universe} (𝓑 : Algebra 𝓦) (b : Fin n → ⟨ 𝓑 ⟩)
  → ((j : Fin m) → ⟦ g j ⟧[ 𝓑 ] b ＝ Algebra.0ᴬ 𝓑)
  → {p q : Poly n} → p ≈ q → ⟦ p ⟧[ 𝓑 ] b ＝ ⟦ q ⟧[ 𝓑 ] b
 soundness-for-≈ 𝓑 b s = ∥∥-rec (Algebra.A-is-set 𝓑) (soundness 𝓑 b s)

module _ {ℓ : Universe → Universe} (sq : general-set-quotients-exist ℓ) where

 open general-set-quotients-exist sq

 module _ {n m : ℕ} (g : Fin m → Poly n) where

  open congruence g

  Q : ℓ 𝓤₀ ̇
  Q = Poly n / ≋

  identify : {p q : Poly n} → p ≈₀ q → η/ ≋ p ＝ η/ ≋ q
  identify d = η/-identifies-related-points ≋ ∣ d ∣

  _+Q_ _·Q_ : Q → Q → Q
  _+Q_ = extension₂/ ≋ _⊕_ ⊕-respects-≈
  _·Q_ = extension₂/ ≋ _⊗_ ⊗-respects-≈

  -Q_ : Q → Q
  -Q_ = extension₁/ ≋ negative negative-respects-≈

  +Q-on-classes : (p q : Poly n) → (η/ ≋ p) +Q (η/ ≋ q) ＝ η/ ≋ (p ⊕ q)
  +Q-on-classes = naturality₂/ ≋ _⊕_ ⊕-respects-≈

  ·Q-on-classes : (p q : Poly n) → (η/ ≋ p) ·Q (η/ ≋ q) ＝ η/ ≋ (p ⊗ q)
  ·Q-on-classes = naturality₂/ ≋ _⊗_ ⊗-respects-≈

  -Q-on-classes : (p : Poly n) → -Q (η/ ≋ p) ＝ η/ ≋ (con (-ᴿ 1ᴿ) ⊗ p)
  -Q-on-classes = naturality/ ≋ negative negative-respects-≈

  +Q-assoc : (x y z : Q) → (x +Q y) +Q z ＝ x +Q (y +Q z)
  +Q-assoc = /-induction₃ fe ≋ (λ x y z → /-is-set ≋) γ
   where
    γ : (p q r : Poly n)
      → ((η/ ≋ p) +Q (η/ ≋ q)) +Q (η/ ≋ r) ＝ (η/ ≋ p) +Q ((η/ ≋ q) +Q (η/ ≋ r))
    γ p q r = ap (_+Q (η/ ≋ r)) (+Q-on-classes p q)
            ∙ +Q-on-classes (p ⊕ q) r
            ∙ identify (⊕-assoc p q r)
            ∙ (+Q-on-classes p (q ⊕ r))⁻¹
            ∙ ap ((η/ ≋ p) +Q_) ((+Q-on-classes q r)⁻¹)

  +Q-comm : (x y : Q) → x +Q y ＝ y +Q x
  +Q-comm = /-induction₂ fe ≋ (λ x y → /-is-set ≋) γ
   where
    γ : (p q : Poly n) → (η/ ≋ p) +Q (η/ ≋ q) ＝ (η/ ≋ q) +Q (η/ ≋ p)
    γ p q = +Q-on-classes p q
          ∙ identify (⊕-comm p q)
          ∙ (+Q-on-classes q p)⁻¹

  +Q-unit : (x : Q) → x +Q (η/ ≋ (con 0ᴿ)) ＝ x
  +Q-unit = /-induction ≋ (λ x → /-is-set ≋) γ
   where
    γ : (p : Poly n) → (η/ ≋ p) +Q (η/ ≋ (con 0ᴿ)) ＝ η/ ≋ p
    γ p = +Q-on-classes p (con 0ᴿ) ∙ identify (⊕-unit p)

  +Q-inverse : (x : Q) → x +Q (-Q x) ＝ η/ ≋ (con 0ᴿ)
  +Q-inverse = /-induction ≋ (λ x → /-is-set ≋) γ
   where
    γ : (p : Poly n) → (η/ ≋ p) +Q (-Q (η/ ≋ p)) ＝ η/ ≋ (con 0ᴿ)
    γ p = ap ((η/ ≋ p) +Q_) (-Q-on-classes p)
        ∙ +Q-on-classes p (con (-ᴿ 1ᴿ) ⊗ p)
        ∙ identify (⊕-inverse p)

  ·Q-assoc : (x y z : Q) → (x ·Q y) ·Q z ＝ x ·Q (y ·Q z)
  ·Q-assoc = /-induction₃ fe ≋ (λ x y z → /-is-set ≋) γ
   where
    γ : (p q r : Poly n)
      → ((η/ ≋ p) ·Q (η/ ≋ q)) ·Q (η/ ≋ r) ＝ (η/ ≋ p) ·Q ((η/ ≋ q) ·Q (η/ ≋ r))
    γ p q r = ap (_·Q (η/ ≋ r)) (·Q-on-classes p q)
            ∙ ·Q-on-classes (p ⊗ q) r
            ∙ identify (⊗-assoc p q r)
            ∙ (·Q-on-classes p (q ⊗ r))⁻¹
            ∙ ap ((η/ ≋ p) ·Q_) ((·Q-on-classes q r)⁻¹)

  ·Q-comm : (x y : Q) → x ·Q y ＝ y ·Q x
  ·Q-comm = /-induction₂ fe ≋ (λ x y → /-is-set ≋) γ
   where
    γ : (p q : Poly n) → (η/ ≋ p) ·Q (η/ ≋ q) ＝ (η/ ≋ q) ·Q (η/ ≋ p)
    γ p q = ·Q-on-classes p q
          ∙ identify (⊗-comm p q)
          ∙ (·Q-on-classes q p)⁻¹

  ·Q-unit : (x : Q) → x ·Q (η/ ≋ (con 1ᴿ)) ＝ x
  ·Q-unit = /-induction ≋ (λ x → /-is-set ≋) γ
   where
    γ : (p : Poly n) → (η/ ≋ p) ·Q (η/ ≋ (con 1ᴿ)) ＝ η/ ≋ p
    γ p = ·Q-on-classes p (con 1ᴿ) ∙ identify (⊗-unit p)

  Q-distributivity : (x y z : Q) → x ·Q (y +Q z) ＝ (x ·Q y) +Q (x ·Q z)
  Q-distributivity = /-induction₃ fe ≋ (λ x y z → /-is-set ≋) γ
   where
    γ : (p q r : Poly n)
      → (η/ ≋ p) ·Q ((η/ ≋ q) +Q (η/ ≋ r))
      ＝ ((η/ ≋ p) ·Q (η/ ≋ q)) +Q ((η/ ≋ p) ·Q (η/ ≋ r))
    γ p q r = ap ((η/ ≋ p) ·Q_) (+Q-on-classes q r)
            ∙ ·Q-on-classes p (q ⊕ r)
            ∙ identify (⊗-distr p q r)
            ∙ (+Q-on-classes (p ⊗ q) (p ⊗ r))⁻¹
            ∙ ap₂ _+Q_ ((·Q-on-classes p q)⁻¹) ((·Q-on-classes p r)⁻¹)

  classes-of-constants-preserve-+
   : (r s : R) → η/ ≋ (con (r +ᴿ s)) ＝ (η/ ≋ (con r)) +Q (η/ ≋ (con s))
  classes-of-constants-preserve-+ r s =
   identify (≈₀-sym (con-⊕ r s)) ∙ (+Q-on-classes (con r) (con s))⁻¹

  classes-of-constants-preserve-·
   : (r s : R) → η/ ≋ (con (r ·ᴿ s)) ＝ (η/ ≋ (con r)) ·Q (η/ ≋ (con s))
  classes-of-constants-preserve-· r s =
   identify (≈₀-sym (con-⊗ r s)) ∙ (·Q-on-classes (con r) (con s))⁻¹

  quotient-algebra : Algebra (ℓ 𝓤₀)
  quotient-algebra = record
                      { A = Q
                      ; A-is-set = /-is-set ≋
                      ; 0ᴬ = η/ ≋ (con 0ᴿ)
                      ; 1ᴬ = η/ ≋ (con 1ᴿ)
                      ; _+ᴬ_ = _+Q_
                      ; _·ᴬ_ = _·Q_
                      ; -ᴬ_ = -Q_
                      ; +ᴬ-assoc = +Q-assoc
                      ; +ᴬ-comm = +Q-comm
                      ; +ᴬ-unit = +Q-unit
                      ; +ᴬ-inverse = +Q-inverse
                      ; ·ᴬ-assoc = ·Q-assoc
                      ; ·ᴬ-comm = ·Q-comm
                      ; ·ᴬ-unit = ·Q-unit
                      ; distributivityᴬ = Q-distributivity
                      ; ι = λ r → η/ ≋ (con r)
                      ; ι-preserves-1 = refl
                      ; ι-preserves-+ = classes-of-constants-preserve-+
                      ; ι-preserves-· = classes-of-constants-preserve-·
                      }

  class-of-var : Fin n → Q
  class-of-var i = η/ ≋ (var i)

  values-at-the-generators
   : (p : Poly n) → ⟦ p ⟧[ quotient-algebra ] class-of-var ＝ η/ ≋ p
  values-at-the-generators (var i) = refl
  values-at-the-generators (con r) = refl
  values-at-the-generators (p ⊕ q) =
   ap₂ _+Q_ (values-at-the-generators p) (values-at-the-generators q)
   ∙ +Q-on-classes p q
  values-at-the-generators (p ⊗ q) =
   ap₂ _·Q_ (values-at-the-generators p) (values-at-the-generators q)
   ∙ ·Q-on-classes p q

  relations-hold-in-the-quotient
   : (j : Fin m)
   → ⟦ g j ⟧[ quotient-algebra ] class-of-var ＝ Algebra.0ᴬ quotient-algebra
  relations-hold-in-the-quotient j =
   values-at-the-generators (g j) ∙ identify (relation j)

  generation-in-the-quotient
   : (w : Q) → ∃ p ꞉ Poly n , ⟦ p ⟧[ quotient-algebra ] class-of-var ＝ w
  generation-in-the-quotient w =
   ∥∥-functor (λ σ → pr₁ σ , (values-at-the-generators (pr₁ σ) ∙ pr₂ σ))
              (η/-is-surjection ≋ pt w)

  module _ {𝓦 : Universe} (𝓑 : Algebra 𝓦) (b : Fin n → ⟨ 𝓑 ⟩)
           (s : (j : Fin m) → ⟦ g j ⟧[ 𝓑 ] b ＝ Algebra.0ᴬ 𝓑)
         where

   private
    module B = Algebra 𝓑

    value-map : Poly n → ⟨ 𝓑 ⟩
    value-map p = ⟦ p ⟧[ 𝓑 ] b

    value-map-respects-≈ : identifies-related-points ≋ value-map
    value-map-respects-≈ = soundness-for-≈ 𝓑 b s

   mediating-hom-map : Q → ⟨ 𝓑 ⟩
   mediating-hom-map =
    mediating-map/ ≋ B.A-is-set value-map value-map-respects-≈

   mediating-hom-map-on-classes
    : (p : Poly n) → mediating-hom-map (η/ ≋ p) ＝ ⟦ p ⟧[ 𝓑 ] b
   mediating-hom-map-on-classes =
    universality-triangle/ ≋ B.A-is-set value-map value-map-respects-≈

   mediating-hom : Hom quotient-algebra 𝓑
   mediating-hom = mediating-hom-map , preserves-+ , preserves-· , preserves-ι
    where
     μ : Q → ⟨ 𝓑 ⟩
     μ = mediating-hom-map

     μ-η : (p : Poly n) → μ (η/ ≋ p) ＝ ⟦ p ⟧[ 𝓑 ] b
     μ-η = mediating-hom-map-on-classes

     preserves-+ : (x y : Q) → μ (x +Q y) ＝ μ x B.+ᴬ μ y
     preserves-+ = /-induction₂ fe ≋ (λ x y → B.A-is-set) γ
      where
       γ : (p q : Poly n)
         → μ ((η/ ≋ p) +Q (η/ ≋ q)) ＝ μ (η/ ≋ p) B.+ᴬ μ (η/ ≋ q)
       γ p q = ap μ (+Q-on-classes p q)
             ∙ μ-η (p ⊕ q)
             ∙ ap₂ B._+ᴬ_ ((μ-η p)⁻¹) ((μ-η q)⁻¹)

     preserves-· : (x y : Q) → μ (x ·Q y) ＝ μ x B.·ᴬ μ y
     preserves-· = /-induction₂ fe ≋ (λ x y → B.A-is-set) γ
      where
       γ : (p q : Poly n)
         → μ ((η/ ≋ p) ·Q (η/ ≋ q)) ＝ μ (η/ ≋ p) B.·ᴬ μ (η/ ≋ q)
       γ p q = ap μ (·Q-on-classes p q)
             ∙ μ-η (p ⊗ q)
             ∙ ap₂ B._·ᴬ_ ((μ-η p)⁻¹) ((μ-η q)⁻¹)

     preserves-ι : (r : R) → μ (η/ ≋ (con r)) ＝ B.ι r
     preserves-ι r = μ-η (con r)

   mediating-hom-on-generators : pr₁ mediating-hom ∘ class-of-var ∼ b
   mediating-hom-on-generators i = mediating-hom-map-on-classes (var i)

   homs-agreeing-on-generators-agree-on-classes
    : (k : Hom quotient-algebra 𝓑)
    → pr₁ k ∘ class-of-var ∼ b
    → (p : Poly n) → pr₁ k (η/ ≋ p) ＝ ⟦ p ⟧[ 𝓑 ] b
   homs-agreeing-on-generators-agree-on-classes k K p =
    ap (pr₁ k) ((values-at-the-generators p)⁻¹)
    ∙ values-under-homs quotient-algebra 𝓑 k p class-of-var
    ∙ values-at-equal-points 𝓑 p (pr₁ k ∘ class-of-var) b K

   universality-of-the-quotient
    : ∃! h ꞉ Hom quotient-algebra 𝓑 , pr₁ h ∘ class-of-var ∼ b
   universality-of-the-quotient =
    (mediating-hom , mediating-hom-on-generators) , c
    where
     c : (σ : Σ h ꞉ Hom quotient-algebra 𝓑 , pr₁ h ∘ class-of-var ∼ b)
       → (mediating-hom , mediating-hom-on-generators) ＝ σ
     c (k , K) =
      to-subtype-＝
       (λ h → Π-is-prop fe (λ i → B.A-is-set))
       (to-Hom-＝ quotient-algebra 𝓑 mediating-hom k
         (at-most-one-mediating-map/ ≋ B.A-is-set mediating-hom-map (pr₁ k)
           (λ p → mediating-hom-map-on-classes p
                ∙ (homs-agreeing-on-generators-agree-on-classes k K p)⁻¹)))

 presented-algebras-from-quotients : Presented-Algebras (ℓ 𝓤₀)
 presented-algebras-from-quotients =
  record
   { R⟨_⟩ = quotient-algebra
   ; gen = class-of-var
   ; relations-hold = relations-hold-in-the-quotient
   ; universality = universality-of-the-quotient
   ; generation = generation-in-the-quotient
   }

\end{code}
