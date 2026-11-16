Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), for gate WG1 of Claude Fable
5.2's plan for the comparison of Weil algebras with presentations [1],
as reviewed by GPT-6 Astra [2], amended by Fable's addendum 01 [3] and
released by Astra [4]. The exported names, and the universes and
hypotheses of their statements, are those of the plan's statement
companion. The term spectra-of-isomorphic-algebras-on-points supplies
the three algebra arguments of composition explicitly. The proofs are
Claude Opus 5.5's. See the AI disclosure in
gist.RealCohesion.index.

Algebras over the smooth line, their homomorphisms and spectra
--------------------------------------------------------------

Let 𝓡 be a commutative ring with carrier R in 𝓤₀, as in
gist.Orbifolds.SmoothLine. An algebra over 𝓡 with carrier in a universe
𝓦 is a commutative ring with carrier in 𝓦 together with a ring
homomorphism ι from R, its structure map. The record Algebra repeats the
fields of Commutative-Ring at 𝓦, with names that carry a superscript A
so that they do not shadow the names that smooth-line opens, and adds ι
with three laws. Commutative-Ring itself fixes its carrier in 𝓤₀, and
the later gates need algebras whose carriers lie in 𝓤₁, so this module
states its own ring lemmas once, for every universe, and leaves
Commutative-Ring and smooth-line untouched [1, Section 2.4].

  R-as-algebra : R over itself, with ι the identity.

  ·ᴬ-zero, ·ᴬ-zero-left, ·ᴬ-unit-left, +ᴬ-unit-left, ι-preserves-0,
  minus-one-times, the powers _^ᴬ_ (x ^ᴬ succ k is (x ^ᴬ k) ·ᴬ x, as in
  SmoothLine) and powers-vanish-from-an-exponent-on : lemmas about one
  algebra, with the helpers distributivityᴬ-right and
  +ᴬ-idempotents-are-zero.

  is-hom, Hom : a homomorphism of algebras preserves addition,
  multiplication and the structure maps. These three clauses suffice:
  it then preserves 0, by additivity and cancellation, and 1, through
  the structure maps (homs-preserve-0, homs-preserve-1), so the
  definition is equivalent to the one with five clauses. Homomorphisms
  form a set (being-hom-is-prop, Hom-is-set), and two of them with
  pointwise equal maps are equal (to-Hom-＝). The three clauses are
  homs-preserve-+, homs-preserve-· and homs-preserve-ι; id-hom and _∘ₕ_
  are the identity and composition.

  _≅ₐ_ : isomorphisms of algebras, between algebras whose carriers may
  lie in different universes, with ≅ₐ-refl, ≅ₐ-sym and ≅ₐ-trans.

  Specᴿ : the spectrum of an algebra, its homomorphisms to R (Myers's
  Definition 4.1.5 [5]). An augmented algebra is an algebra 𝓐 with a
  point π of Specᴿ 𝓐, by which Specᴿ 𝓐 is pointed, as in his Definition
  4.2.1; there is no separate record. Isomorphic algebras have
  equivalent spectra, by precomposition
  (spectra-of-isomorphic-algebras), with the formula for points
  (spectra-of-isomorphic-algebras-on-points).

  ⟦_⟧[_] : the value of a polynomial expression of SmoothLine, the
  existing type Poly n, at a point of an algebra: var i gives the i-th
  coordinate, con r gives ι r, and ⊕ and ⊗ give +ᴬ and ·ᴬ. Values in R
  agree with those of SmoothLine (values-in-R), commute with
  homomorphisms (values-under-homs), depend only on the point
  (values-at-equal-points), and turn substitution into composition
  (values-of-substitutions); the value of power p k is the k-th power
  of the value of p (value-of-power-in-algebras).

Each statement about expressions is proved by induction on the
expression. values-in-R is not refl, since both sides are stuck on a
variable expression, and value-of-power-in-algebras differs from
SmoothLine.value-of-power in its base case, where power p 0 is con 1ᴿ,
whose value is ι 1ᴿ.

Assumptions: function extensionality and propositional truncations, as
in SmoothLine; the truncations are not used in this module, which has
them as a parameter for the sake of smooth-line. No quotient, ideal,
crisp datum, choice, resizing, univalence or propositional
extensionality is assumed, and the module adds no option and no
postulate. It is the foundation of the comparison and no part of it is
the comparison itself: the presented algebras, the Weil algebras and
the two directions of the comparison are the later gates of [1].

[1] Claude Fable 5.2. Plan: formalizing the comparison of Weil algebras
    with presentations, 13 November 2026, Sections 3 and 9, with its
    statement companion, Section WG1 (plan SHA-256 b1662ecc…; companion
    SHA-256 47974af8…).
[2] GPT-6 Astra. Review of Fable's Weil plan, 13 November 2026
    (FABLE-WEIL-PLAN-REVIEW-01).
[3] Claude Fable 5.2. Addendum 01 to the plan for the Weil comparison,
    13 November 2026 (SHA-256 abf31923…).
[4] GPT-6 Astra. Weil implementation, gate WG1, 13 November 2026
    (OPUS-WEIL-RELEASE-WG1, SHA-256 8b119ef2…).
[5] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.Algebras
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (𝓡 : Commutative-Ring)
       where

open import Fin.Type
open import Naturals.Order using (Order-ℕ-ℕ ; ≤-split ; unique-least)
open import Notation.Order using (_≤_)
open import UF.Base
open import UF.Equiv
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties

open smooth-line fe pt 𝓡

\end{code}

The record of algebras, and R over itself.

\begin{code}

record Algebra (𝓦 : Universe) : 𝓦 ⁺ ̇ where
 field
  A : 𝓦 ̇
  A-is-set : is-set A
  0ᴬ 1ᴬ : A
  _+ᴬ_ _·ᴬ_ : A → A → A
  -ᴬ_ : A → A
  +ᴬ-assoc : (x y z : A) → (x +ᴬ y) +ᴬ z ＝ x +ᴬ (y +ᴬ z)
  +ᴬ-comm : (x y : A) → x +ᴬ y ＝ y +ᴬ x
  +ᴬ-unit : (x : A) → x +ᴬ 0ᴬ ＝ x
  +ᴬ-inverse : (x : A) → x +ᴬ (-ᴬ x) ＝ 0ᴬ
  ·ᴬ-assoc : (x y z : A) → (x ·ᴬ y) ·ᴬ z ＝ x ·ᴬ (y ·ᴬ z)
  ·ᴬ-comm : (x y : A) → x ·ᴬ y ＝ y ·ᴬ x
  ·ᴬ-unit : (x : A) → x ·ᴬ 1ᴬ ＝ x
  distributivityᴬ : (x y z : A) → x ·ᴬ (y +ᴬ z) ＝ (x ·ᴬ y) +ᴬ (x ·ᴬ z)
  ι : R → A
  ι-preserves-1 : ι 1ᴿ ＝ 1ᴬ
  ι-preserves-+ : (r s : R) → ι (r +ᴿ s) ＝ ι r +ᴬ ι s
  ι-preserves-· : (r s : R) → ι (r ·ᴿ s) ＝ ι r ·ᴬ ι s

 infixl 6 _+ᴬ_
 infixl 7 _·ᴬ_

⟨_⟩ : {𝓦 : Universe} → Algebra 𝓦 → 𝓦 ̇
⟨ 𝓐 ⟩ = Algebra.A 𝓐

R-as-algebra : Algebra 𝓤₀
R-as-algebra = record
                { A = R
                ; A-is-set = R-is-set
                ; 0ᴬ = 0ᴿ
                ; 1ᴬ = 1ᴿ
                ; _+ᴬ_ = _+ᴿ_
                ; _·ᴬ_ = _·ᴿ_
                ; -ᴬ_ = -ᴿ_
                ; +ᴬ-assoc = +-assoc
                ; +ᴬ-comm = +-comm
                ; +ᴬ-unit = +-unit
                ; +ᴬ-inverse = +-inverse
                ; ·ᴬ-assoc = ·-assoc
                ; ·ᴬ-comm = ·-comm
                ; ·ᴬ-unit = ·-unit
                ; distributivityᴬ = distributivity
                ; ι = id
                ; ι-preserves-1 = refl
                ; ι-preserves-+ = λ r s → refl
                ; ι-preserves-· = λ r s → refl
                }

\end{code}

Lemmas about one algebra. ·ᴬ-zero is the proof of SmoothLine.·-zero
with the names of the algebra; ι-preserves-0 cancels ι 0ᴿ +ᴬ ι 0ᴿ ＝ ι 0ᴿ;
minus-one-times is the one fact about negation that the construction of
the later gates needs.

\begin{code}

module _ {𝓦 : Universe} (𝓐 : Algebra 𝓦) where

 open Algebra 𝓐

 ·ᴬ-zero : (x : A) → x ·ᴬ 0ᴬ ＝ 0ᴬ
 ·ᴬ-zero x =
  x ·ᴬ 0ᴬ                                  ＝⟨ (+ᴬ-unit (x ·ᴬ 0ᴬ))⁻¹ ⟩
  x ·ᴬ 0ᴬ +ᴬ 0ᴬ
   ＝⟨ ap (x ·ᴬ 0ᴬ +ᴬ_) ((+ᴬ-inverse (x ·ᴬ 0ᴬ))⁻¹) ⟩
  x ·ᴬ 0ᴬ +ᴬ (x ·ᴬ 0ᴬ +ᴬ (-ᴬ (x ·ᴬ 0ᴬ)))
   ＝⟨ (+ᴬ-assoc (x ·ᴬ 0ᴬ) (x ·ᴬ 0ᴬ) (-ᴬ (x ·ᴬ 0ᴬ)))⁻¹ ⟩
  x ·ᴬ 0ᴬ +ᴬ x ·ᴬ 0ᴬ +ᴬ (-ᴬ (x ·ᴬ 0ᴬ))
   ＝⟨ ap (_+ᴬ (-ᴬ (x ·ᴬ 0ᴬ))) ((distributivityᴬ x 0ᴬ 0ᴬ)⁻¹) ⟩
  x ·ᴬ (0ᴬ +ᴬ 0ᴬ) +ᴬ (-ᴬ (x ·ᴬ 0ᴬ))
   ＝⟨ ap (λ - → x ·ᴬ - +ᴬ (-ᴬ (x ·ᴬ 0ᴬ))) (+ᴬ-unit 0ᴬ) ⟩
  x ·ᴬ 0ᴬ +ᴬ (-ᴬ (x ·ᴬ 0ᴬ))                ＝⟨ +ᴬ-inverse (x ·ᴬ 0ᴬ) ⟩
  0ᴬ                                       ∎

 ·ᴬ-zero-left : (x : A) → 0ᴬ ·ᴬ x ＝ 0ᴬ
 ·ᴬ-zero-left x = ·ᴬ-comm 0ᴬ x ∙ ·ᴬ-zero x

 ·ᴬ-unit-left : (x : A) → 1ᴬ ·ᴬ x ＝ x
 ·ᴬ-unit-left x = ·ᴬ-comm 1ᴬ x ∙ ·ᴬ-unit x

 +ᴬ-unit-left : (x : A) → 0ᴬ +ᴬ x ＝ x
 +ᴬ-unit-left x = +ᴬ-comm 0ᴬ x ∙ +ᴬ-unit x

 distributivityᴬ-right : (x y z : A) → (x +ᴬ y) ·ᴬ z ＝ (x ·ᴬ z) +ᴬ (y ·ᴬ z)
 distributivityᴬ-right x y z =
  (x +ᴬ y) ·ᴬ z           ＝⟨ ·ᴬ-comm (x +ᴬ y) z ⟩
  z ·ᴬ (x +ᴬ y)           ＝⟨ distributivityᴬ z x y ⟩
  (z ·ᴬ x) +ᴬ (z ·ᴬ y)    ＝⟨ ap₂ _+ᴬ_ (·ᴬ-comm z x) (·ᴬ-comm z y) ⟩
  (x ·ᴬ z) +ᴬ (y ·ᴬ z)    ∎

 +ᴬ-idempotents-are-zero : (y : A) → y +ᴬ y ＝ y → y ＝ 0ᴬ
 +ᴬ-idempotents-are-zero y e =
  y                       ＝⟨ (+ᴬ-unit y)⁻¹ ⟩
  y +ᴬ 0ᴬ                 ＝⟨ ap (y +ᴬ_) ((+ᴬ-inverse y)⁻¹) ⟩
  y +ᴬ (y +ᴬ (-ᴬ y))      ＝⟨ (+ᴬ-assoc y y (-ᴬ y))⁻¹ ⟩
  y +ᴬ y +ᴬ (-ᴬ y)        ＝⟨ ap (_+ᴬ (-ᴬ y)) e ⟩
  y +ᴬ (-ᴬ y)             ＝⟨ +ᴬ-inverse y ⟩
  0ᴬ                      ∎

 ι-preserves-0 : ι 0ᴿ ＝ 0ᴬ
 ι-preserves-0 = +ᴬ-idempotents-are-zero (ι 0ᴿ)
                  ((ι-preserves-+ 0ᴿ 0ᴿ)⁻¹ ∙ ap ι (+-unit 0ᴿ))

 minus-one-times : (x : A) → x +ᴬ (ι (-ᴿ 1ᴿ) ·ᴬ x) ＝ 0ᴬ
 minus-one-times x =
  x +ᴬ (ι (-ᴿ 1ᴿ) ·ᴬ x)
   ＝⟨ ap (λ - → - +ᴬ (ι (-ᴿ 1ᴿ) ·ᴬ x)) ((·ᴬ-unit-left x)⁻¹) ⟩
  (1ᴬ ·ᴬ x) +ᴬ (ι (-ᴿ 1ᴿ) ·ᴬ x)
   ＝⟨ ap (λ - → (- ·ᴬ x) +ᴬ (ι (-ᴿ 1ᴿ) ·ᴬ x)) (ι-preserves-1 ⁻¹) ⟩
  (ι 1ᴿ ·ᴬ x) +ᴬ (ι (-ᴿ 1ᴿ) ·ᴬ x)
   ＝⟨ (distributivityᴬ-right (ι 1ᴿ) (ι (-ᴿ 1ᴿ)) x)⁻¹ ⟩
  (ι 1ᴿ +ᴬ ι (-ᴿ 1ᴿ)) ·ᴬ x
   ＝⟨ ap (_·ᴬ x) ((ι-preserves-+ 1ᴿ (-ᴿ 1ᴿ))⁻¹) ⟩
  ι (1ᴿ +ᴿ (-ᴿ 1ᴿ)) ·ᴬ x
   ＝⟨ ap (λ - → ι - ·ᴬ x) (+-inverse 1ᴿ) ⟩
  ι 0ᴿ ·ᴬ x
   ＝⟨ ap (_·ᴬ x) ι-preserves-0 ⟩
  0ᴬ ·ᴬ x
   ＝⟨ ·ᴬ-zero-left x ⟩
  0ᴬ
   ∎

 _^ᴬ_ : A → ℕ → A
 x ^ᴬ 0      = 1ᴬ
 x ^ᴬ succ k = (x ^ᴬ k) ·ᴬ x

 powers-vanish-from-an-exponent-on
  : (x : A) (a b : ℕ) → x ^ᴬ a ＝ 0ᴬ → a ≤ b → x ^ᴬ b ＝ 0ᴬ
 powers-vanish-from-an-exponent-on x a 0        p l =
  transport (λ - → x ^ᴬ - ＝ 0ᴬ) (unique-least a l) p
 powers-vanish-from-an-exponent-on x a (succ b) p l =
  Cases (≤-split a b l)
   (λ (m : a ≤ b) → ap (_·ᴬ x) (powers-vanish-from-an-exponent-on x a b p m)
                    ∙ ·ᴬ-zero-left x)
   (λ (e : a ＝ succ b) → transport (λ - → x ^ᴬ - ＝ 0ᴬ) e p)

\end{code}

Homomorphisms. Their three clauses are named, so that later modules do
not project into the triple.

\begin{code}

module _ {𝓦 𝓣 : Universe} (𝓐 : Algebra 𝓦) (𝓑 : Algebra 𝓣) where

 private
  module A = Algebra 𝓐
  module B = Algebra 𝓑

 is-hom : (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) → 𝓦 ⊔ 𝓣 ̇
 is-hom h = ((x y : ⟨ 𝓐 ⟩) → h (x A.+ᴬ y) ＝ h x B.+ᴬ h y)
          × ((x y : ⟨ 𝓐 ⟩) → h (x A.·ᴬ y) ＝ h x B.·ᴬ h y)
          × ((r : R) → h (A.ι r) ＝ B.ι r)

 Hom : 𝓦 ⊔ 𝓣 ̇
 Hom = Σ h ꞉ (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) , is-hom h

 homs-preserve-+ : (h : Hom) (x y : ⟨ 𝓐 ⟩)
                 → pr₁ h (x A.+ᴬ y) ＝ pr₁ h x B.+ᴬ pr₁ h y
 homs-preserve-+ h = pr₁ (pr₂ h)

 homs-preserve-· : (h : Hom) (x y : ⟨ 𝓐 ⟩)
                 → pr₁ h (x A.·ᴬ y) ＝ pr₁ h x B.·ᴬ pr₁ h y
 homs-preserve-· h = pr₁ (pr₂ (pr₂ h))

 homs-preserve-ι : (h : Hom) (r : R) → pr₁ h (A.ι r) ＝ B.ι r
 homs-preserve-ι h = pr₂ (pr₂ (pr₂ h))

 being-hom-is-prop : (h : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) → is-prop (is-hom h)
 being-hom-is-prop h =
  ×-is-prop (Π-is-prop fe (λ x → Π-is-prop fe (λ y → B.A-is-set)))
   (×-is-prop (Π-is-prop fe (λ x → Π-is-prop fe (λ y → B.A-is-set)))
     (Π-is-prop fe (λ r → B.A-is-set)))

 Hom-is-set : is-set Hom
 Hom-is-set = Σ-is-set (Π-is-set fe (λ _ → B.A-is-set))
               (λ h → props-are-sets (being-hom-is-prop h))

 to-Hom-＝ : (h k : Hom) → pr₁ h ∼ pr₁ k → h ＝ k
 to-Hom-＝ h k H = to-subtype-＝ being-hom-is-prop (dfunext fe H)

 homs-preserve-0 : (h : Hom) → pr₁ h A.0ᴬ ＝ B.0ᴬ
 homs-preserve-0 h =
  +ᴬ-idempotents-are-zero 𝓑 (pr₁ h A.0ᴬ)
   ((homs-preserve-+ h A.0ᴬ A.0ᴬ)⁻¹ ∙ ap (pr₁ h) (A.+ᴬ-unit A.0ᴬ))

 homs-preserve-1 : (h : Hom) → pr₁ h A.1ᴬ ＝ B.1ᴬ
 homs-preserve-1 h = ap (pr₁ h) (A.ι-preserves-1 ⁻¹)
                   ∙ homs-preserve-ι h 1ᴿ
                   ∙ B.ι-preserves-1

 homs-preserve-powers
  : (h : Hom) (x : ⟨ 𝓐 ⟩) (k : ℕ) → pr₁ h (_^ᴬ_ 𝓐 x k) ＝ _^ᴬ_ 𝓑 (pr₁ h x) k
 homs-preserve-powers h x 0        = homs-preserve-1 h
 homs-preserve-powers h x (succ k) =
  homs-preserve-· h (_^ᴬ_ 𝓐 x k) x
  ∙ ap (λ - → - B.·ᴬ pr₁ h x) (homs-preserve-powers h x k)

id-hom : {𝓦 : Universe} (𝓐 : Algebra 𝓦) → Hom 𝓐 𝓐
id-hom 𝓐 = id , (λ x y → refl) , (λ x y → refl) , (λ r → refl)

_∘ₕ_ : {𝓦 𝓣 𝓣' : Universe} {𝓐 : Algebra 𝓦} {𝓑 : Algebra 𝓣} {𝓒 : Algebra 𝓣'}
     → Hom 𝓑 𝓒 → Hom 𝓐 𝓑 → Hom 𝓐 𝓒
_∘ₕ_ {𝓦} {𝓣} {𝓣'} {𝓐} {𝓑} {𝓒} g f =
 pr₁ g ∘ pr₁ f ,
 (λ x y → ap (pr₁ g) (homs-preserve-+ 𝓐 𝓑 f x y)
          ∙ homs-preserve-+ 𝓑 𝓒 g (pr₁ f x) (pr₁ f y)) ,
 (λ x y → ap (pr₁ g) (homs-preserve-· 𝓐 𝓑 f x y)
          ∙ homs-preserve-· 𝓑 𝓒 g (pr₁ f x) (pr₁ f y)) ,
 (λ r → ap (pr₁ g) (homs-preserve-ι 𝓐 𝓑 f r) ∙ homs-preserve-ι 𝓑 𝓒 g r)

\end{code}

Isomorphisms, between algebras whose carriers may lie in different
universes. Where an implicit algebra cannot be read off the type of an
argument, since Hom unfolds to a Σ-type over the carriers, it is given
by name.

\begin{code}

_≅ₐ_ : {𝓦 𝓣 : Universe} → Algebra 𝓦 → Algebra 𝓣 → 𝓦 ⊔ 𝓣 ̇
𝓐 ≅ₐ 𝓑 = Σ h ꞉ Hom 𝓐 𝓑 , Σ k ꞉ Hom 𝓑 𝓐 ,
           (pr₁ k ∘ pr₁ h ∼ id) × (pr₁ h ∘ pr₁ k ∼ id)

≅ₐ-refl : {𝓦 : Universe} (𝓐 : Algebra 𝓦) → 𝓐 ≅ₐ 𝓐
≅ₐ-refl 𝓐 = id-hom 𝓐 , id-hom 𝓐 , (λ x → refl) , (λ x → refl)

≅ₐ-sym : {𝓦 𝓣 : Universe} {𝓐 : Algebra 𝓦} {𝓑 : Algebra 𝓣}
       → 𝓐 ≅ₐ 𝓑 → 𝓑 ≅ₐ 𝓐
≅ₐ-sym (h , k , ε , η) = k , h , η , ε

≅ₐ-trans : {𝓦 𝓣 𝓣' : Universe} {𝓐 : Algebra 𝓦} {𝓑 : Algebra 𝓣}
           {𝓒 : Algebra 𝓣'}
         → 𝓐 ≅ₐ 𝓑 → 𝓑 ≅ₐ 𝓒 → 𝓐 ≅ₐ 𝓒
≅ₐ-trans {𝓦} {𝓣} {𝓣'} {𝓐} {𝓑} {𝓒} (h , k , ε , η) (h' , k' , ε' , η') =
 _∘ₕ_ {𝓐 = 𝓐} {𝓑 = 𝓑} {𝓒 = 𝓒} h' h ,
 _∘ₕ_ {𝓐 = 𝓒} {𝓑 = 𝓑} {𝓒 = 𝓐} k k' ,
 (λ x → ap (pr₁ k) (ε' (pr₁ h x)) ∙ ε x) ,
 (λ z → ap (pr₁ h') (η (pr₁ k' z)) ∙ η' z)

\end{code}

Spectra (Myers, Definition 4.1.5), and the equivalence of the spectra
of isomorphic algebras, by precomposition.

\begin{code}

Specᴿ : {𝓦 : Universe} → Algebra 𝓦 → 𝓦 ̇
Specᴿ 𝓐 = Hom 𝓐 R-as-algebra

Specᴿ-is-set : {𝓦 : Universe} (𝓐 : Algebra 𝓦) → is-set (Specᴿ 𝓐)
Specᴿ-is-set 𝓐 = Hom-is-set 𝓐 R-as-algebra

spectra-of-isomorphic-algebras
 : {𝓦 𝓣 : Universe} (𝓐 : Algebra 𝓦) (𝓑 : Algebra 𝓣)
 → 𝓐 ≅ₐ 𝓑 → Specᴿ 𝓑 ≃ Specᴿ 𝓐
spectra-of-isomorphic-algebras 𝓐 𝓑 (h , k , ε , η) = qinveq f (g , gf , fg)
 where
  f : Specᴿ 𝓑 → Specᴿ 𝓐
  f π = _∘ₕ_ {𝓐 = 𝓐} {𝓑 = 𝓑} {𝓒 = R-as-algebra} π h

  g : Specᴿ 𝓐 → Specᴿ 𝓑
  g π' = _∘ₕ_ {𝓐 = 𝓑} {𝓑 = 𝓐} {𝓒 = R-as-algebra} π' k

  gf : g ∘ f ∼ id
  gf π = to-Hom-＝ 𝓑 R-as-algebra (g (f π)) π (λ y → ap (pr₁ π) (η y))

  fg : f ∘ g ∼ id
  fg π' = to-Hom-＝ 𝓐 R-as-algebra (f (g π')) π' (λ x → ap (pr₁ π') (ε x))

spectra-of-isomorphic-algebras-on-points
 : {𝓦 𝓣 : Universe} (𝓐 : Algebra 𝓦) (𝓑 : Algebra 𝓣) (φ : 𝓐 ≅ₐ 𝓑)
   (π : Specᴿ 𝓑)
 → ⌜ spectra-of-isomorphic-algebras 𝓐 𝓑 φ ⌝ π
 ＝ _∘ₕ_ {𝓐 = 𝓐} {𝓑 = 𝓑} {𝓒 = R-as-algebra} π (pr₁ φ)
spectra-of-isomorphic-algebras-on-points 𝓐 𝓑 φ π = refl

\end{code}

Values of polynomial expressions in algebras, and substitution.

\begin{code}

⟦_⟧[_] : {𝓦 : Universe} {n : ℕ}
       → Poly n → (𝓐 : Algebra 𝓦) → (Fin n → ⟨ 𝓐 ⟩) → ⟨ 𝓐 ⟩
⟦ var i ⟧[ 𝓐 ] a = a i
⟦ con r ⟧[ 𝓐 ] a = Algebra.ι 𝓐 r
⟦ p ⊕ q ⟧[ 𝓐 ] a = Algebra._+ᴬ_ 𝓐 (⟦ p ⟧[ 𝓐 ] a) (⟦ q ⟧[ 𝓐 ] a)
⟦ p ⊗ q ⟧[ 𝓐 ] a = Algebra._·ᴬ_ 𝓐 (⟦ p ⟧[ 𝓐 ] a) (⟦ q ⟧[ 𝓐 ] a)

values-in-R : {n : ℕ} (p : Poly n) (a : Fin n → R)
            → ⟦ p ⟧[ R-as-algebra ] a ＝ ⟦ p ⟧ a
values-in-R (var i) a = refl
values-in-R (con r) a = refl
values-in-R (p ⊕ q) a = ap₂ _+ᴿ_ (values-in-R p a) (values-in-R q a)
values-in-R (p ⊗ q) a = ap₂ _·ᴿ_ (values-in-R p a) (values-in-R q a)

values-under-homs
 : {𝓦 𝓣 : Universe} (𝓐 : Algebra 𝓦) (𝓑 : Algebra 𝓣) (h : Hom 𝓐 𝓑)
   {n : ℕ} (p : Poly n) (a : Fin n → ⟨ 𝓐 ⟩)
 → pr₁ h (⟦ p ⟧[ 𝓐 ] a) ＝ ⟦ p ⟧[ 𝓑 ] (pr₁ h ∘ a)
values-under-homs 𝓐 𝓑 h (var i) a = refl
values-under-homs 𝓐 𝓑 h (con r) a = homs-preserve-ι 𝓐 𝓑 h r
values-under-homs 𝓐 𝓑 h (p ⊕ q) a =
 homs-preserve-+ 𝓐 𝓑 h (⟦ p ⟧[ 𝓐 ] a) (⟦ q ⟧[ 𝓐 ] a)
 ∙ ap₂ (Algebra._+ᴬ_ 𝓑) (values-under-homs 𝓐 𝓑 h p a)
                         (values-under-homs 𝓐 𝓑 h q a)
values-under-homs 𝓐 𝓑 h (p ⊗ q) a =
 homs-preserve-· 𝓐 𝓑 h (⟦ p ⟧[ 𝓐 ] a) (⟦ q ⟧[ 𝓐 ] a)
 ∙ ap₂ (Algebra._·ᴬ_ 𝓑) (values-under-homs 𝓐 𝓑 h p a)
                         (values-under-homs 𝓐 𝓑 h q a)

values-at-equal-points
 : {𝓦 : Universe} (𝓐 : Algebra 𝓦) {n : ℕ} (p : Poly n) (a a' : Fin n → ⟨ 𝓐 ⟩)
 → a ∼ a' → ⟦ p ⟧[ 𝓐 ] a ＝ ⟦ p ⟧[ 𝓐 ] a'
values-at-equal-points 𝓐 (var i) a a' H = H i
values-at-equal-points 𝓐 (con r) a a' H = refl
values-at-equal-points 𝓐 (p ⊕ q) a a' H =
 ap₂ (Algebra._+ᴬ_ 𝓐) (values-at-equal-points 𝓐 p a a' H)
                       (values-at-equal-points 𝓐 q a a' H)
values-at-equal-points 𝓐 (p ⊗ q) a a' H =
 ap₂ (Algebra._·ᴬ_ 𝓐) (values-at-equal-points 𝓐 p a a' H)
                       (values-at-equal-points 𝓐 q a a' H)

substitute : {n k : ℕ} → (Fin n → Poly k) → Poly n → Poly k
substitute σ (var i) = σ i
substitute σ (con r) = con r
substitute σ (p ⊕ q) = substitute σ p ⊕ substitute σ q
substitute σ (p ⊗ q) = substitute σ p ⊗ substitute σ q

values-of-substitutions
 : {𝓦 : Universe} (𝓐 : Algebra 𝓦) {n k : ℕ} (σ : Fin n → Poly k) (p : Poly n)
   (a : Fin k → ⟨ 𝓐 ⟩)
 → ⟦ substitute σ p ⟧[ 𝓐 ] a ＝ ⟦ p ⟧[ 𝓐 ] (λ i → ⟦ σ i ⟧[ 𝓐 ] a)
values-of-substitutions 𝓐 σ (var i) a = refl
values-of-substitutions 𝓐 σ (con r) a = refl
values-of-substitutions 𝓐 σ (p ⊕ q) a =
 ap₂ (Algebra._+ᴬ_ 𝓐) (values-of-substitutions 𝓐 σ p a)
                       (values-of-substitutions 𝓐 σ q a)
values-of-substitutions 𝓐 σ (p ⊗ q) a =
 ap₂ (Algebra._·ᴬ_ 𝓐) (values-of-substitutions 𝓐 σ p a)
                       (values-of-substitutions 𝓐 σ q a)

value-of-power-in-algebras
 : {𝓦 : Universe} (𝓐 : Algebra 𝓦) {n : ℕ} (p : Poly n) (k : ℕ)
   (a : Fin n → ⟨ 𝓐 ⟩)
 → ⟦ power p k ⟧[ 𝓐 ] a ＝ _^ᴬ_ 𝓐 (⟦ p ⟧[ 𝓐 ] a) k
value-of-power-in-algebras 𝓐 p 0        a = Algebra.ι-preserves-1 𝓐
value-of-power-in-algebras 𝓐 p (succ k) a =
 ap (λ - → Algebra._·ᴬ_ 𝓐 - (⟦ p ⟧[ 𝓐 ] a))
    (value-of-power-in-algebras 𝓐 p k a)

\end{code}
