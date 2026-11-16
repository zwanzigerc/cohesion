{-# OPTIONS --safe --without-K #-}

-- The unit of an idempotent H-space is an embedded point.
-- Claude (Fable), 12 November 2026; see HIGHER-RESEARCH-FABLE-01.txt, section 3.
--
-- Let m be a binary operation on a type M with a two-sided unit e, both unit
-- laws holding up to a path, and with  m x x ≡ x  for all x. No associativity,
-- commutativity or coherence is assumed. Then every loop at e is trivial, and
-- for every x the type  x ≡ e  is a proposition.
--
-- Use: for a finite-product-preserving endofunctor T of an ∞-topos S and the
-- subobject classifier Ω of S, the object TΩ with T(∧) and T(⊤) is such an
-- M. So T(⊤) : 1 → TΩ is a monomorphism, and the fibre
--   F = { q : Ω | η(q) = T(⊤) }
-- of any map η : Ω → TΩ is a SUBOBJECT of Ω, in particular a set. This is
-- what the principal-filter argument needs in order to use continuity with
-- set exponents only.
--
-- Plain Agda: no cohesion, no axioms, no K.
module IdempotentUnit where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality

private
  variable
    a b : Level
    X : Set a

sym : {x y : X} → x ≡ y → y ≡ x
sym refl = refl

infixr 5 _∙_
_∙_ : {x y z : X} → x ≡ y → y ≡ z → x ≡ z
refl ∙ q = q

ap : {Y : Set b} (f : X → Y) {x y : X} → x ≡ y → f x ≡ f y
ap f refl = refl

subst : (P : X → Set b) {x y : X} → x ≡ y → P x → P y
subst P refl u = u

right-unit : {x y : X} (p : x ≡ y) → p ∙ refl ≡ p
right-unit refl = refl

right-inverse : {x y : X} (p : x ≡ y) → p ∙ sym p ≡ refl
right-inverse refl = refl

assoc : {w x y z : X} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
      → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc refl q r = refl

cancel : {x y : X} (p : x ≡ y) (q : y ≡ y) → p ≡ p ∙ q → q ≡ refl
cancel refl q h = sym h

------------------------------------------------------------------------
-- Loops at e carried to loops at u along a path h : u ≡ e.

conj : {u e : X} → u ≡ e → e ≡ e → u ≡ u
conj refl p = p

unconj : {u e : X} → u ≡ e → u ≡ u → e ≡ e
unconj refl p = p

conj-unconj : {u e : X} (h : u ≡ e) (p : u ≡ u) → conj h (unconj h p) ≡ p
conj-unconj refl p = refl

conj-path : {u e : X} (h : u ≡ e) (p : e ≡ e) → h ∙ p ∙ sym h ≡ conj h p
conj-path refl p = right-unit p

-- Naturality of a homotopy from g to the identity.
natural : (g : X → X) (h : (x : X) → g x ≡ x) {x y : X} (p : x ≡ y)
        → ap g p ≡ h x ∙ p ∙ sym (h y)
natural g h {x} refl = sym (right-inverse (h x))

natural-loop : (g : X → X) (h : (x : X) → g x ≡ x) {e : X} (p : e ≡ e)
             → ap g p ≡ conj (h e) p
natural-loop g h {e} p = natural g h p ∙ conj-path (h e) p

-- A binary operation applied to two paths.
diagonal : (m : X → X → X) {x y : X} (p : x ≡ y)
         → ap (λ z → m z z) p ≡ ap (λ z → m z x) p ∙ ap (m y) p
diagonal m refl = refl

interchange : (m : X → X → X) {x x′ y y′ : X} (p : x ≡ x′) (q : y ≡ y′)
            → ap (λ z → m z y) p ∙ ap (m x′) q ≡ ap (m x) q ∙ ap (λ z → m z y′) p
interchange m refl refl = refl

------------------------------------------------------------------------
-- The path algebra, with the base point of the three structure paths free.
-- l, r, i stand for the left-unit, right-unit and idempotence paths at e.

private
  commute-rewrite : {u : X} {x x′ y y′ : u ≡ u}
                  → x ≡ x′ → y ≡ y′ → x ∙ y ≡ y ∙ x → x′ ∙ y′ ≡ y′ ∙ x′
  commute-rewrite refl refl h = h

  product-rewrite : {u : X} {d d′ x x′ y y′ : u ≡ u}
                  → d ≡ d′ → x ≡ x′ → y ≡ y′ → d ≡ x ∙ y → d′ ≡ x′ ∙ y′
  product-rewrite refl refl refl h = h

  algebra : {u e : X} (l r i : u ≡ e)
          → ((p q : e ≡ e) → conj r p ∙ conj l q ≡ conj l q ∙ conj r p)
          → ((p : e ≡ e) → conj i p ≡ conj r p ∙ conj l p)
          → (p : e ≡ e) → p ≡ refl
  algebra {e = e} refl r i commute-rl square p =
    cancel p p (sym (fixed i p) ∙ square p ∙ ap (λ z → z ∙ p) (fixed r p))
    where
    -- Eckmann–Hilton: all loops at e commute.
    commute : (x y : e ≡ e) → x ∙ y ≡ y ∙ x
    commute x y = subst (λ z → z ∙ y ≡ y ∙ z) (conj-unconj r x)
      (commute-rl (unconj r x) y)

    -- Hence conjugation by a loop is the identity.
    fixed : (h x : e ≡ e) → conj h x ≡ x
    fixed h x = sym (conj-path h x)
              ∙ ap (λ z → h ∙ z) (commute x (sym h))
              ∙ sym (assoc h (sym h) x)
              ∙ ap (λ z → z ∙ x) (right-inverse h)

------------------------------------------------------------------------
-- The theorem.

module _ {M : Set a} (e : M) (m : M → M → M)
  (left-unit : (x : M) → m e x ≡ x)
  (right-unit′ : (x : M) → m x e ≡ x)
  (idempotent : (x : M) → m x x ≡ x) where

  loop-trivial : (p : e ≡ e) → p ≡ refl
  loop-trivial = algebra (left-unit e) (right-unit′ e) (idempotent e)
    (λ p q → commute-rewrite
      (natural-loop (λ z → m z e) right-unit′ p)
      (natural-loop (m e) left-unit q)
      (interchange m p q))
    (λ p → product-rewrite
      (natural-loop (λ z → m z z) idempotent p)
      (natural-loop (λ z → m z e) right-unit′ p)
      (natural-loop (m e) left-unit p)
      (diagonal m p))

  -- The unit is an embedded point: paths into it are unique.
  unit-embedded : (x : M) (s t : x ≡ e) → s ≡ t
  unit-embedded x s refl = loop-trivial s
