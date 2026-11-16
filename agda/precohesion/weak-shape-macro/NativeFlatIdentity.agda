{-# OPTIONS --safe --without-K --cohesion #-}

-- The identity types of ♭ A: (box x ≡ box y) ≃ ♭ (x ≡ y).
-- Claude (Fable), 14 November 2026; fable-impl-19 (HANDOFF-35, item 2).
--
-- Literally --safe, and without --flat-split: nothing is postulated, and no
-- crisp argument is matched against refl. The only primitive of cohesion
-- that is used, besides ♭ itself, is the native ♯ of Agda 2.9.0, through
-- NativeSharp.
--
-- PROVENANCE. This is a port of a fragment of
--   RealCohesion/DiscreteConnectedTypes.lagda
--   sha256 2994bc47d40cf91de702c4387b3c10a1edc2cd9332a78dfea199c3c1c5906b76
-- (copy in the village folder classifier-reuse-source-01/, read there):
--   source 66-79    crisp-J, crisp-J-computes        section 1 below
--   source 89-98    crisp-identity-induction         section 1
--   source 107-137  code, code-refl, enc, dec, dec-enc, enc-crisp-ap,
--                   enc-dec, Theorem-6-1             section 2
-- The source is written against TypeTopology (MLTT.Spartan, UF.Equiv) and
-- three modules of its own gist that were not among the files supplied
-- (Flat, Sharp, CrispInduction); their names are matched here by the way
-- the fragment uses them. The port uses the village's representations:
--   _＝_, _^♭                    builtin _≡_, Foundations.box
--   unit-sharp, crisp-elim-sharp  NativeSharp.sharp-unit, sharp-extract
--   crisp-ap-^♭                   NativeSharp.box-crisp-path
--   qinveq, _≃_                   Adjointify.quasi-inverse, Foundations.IsEquiv
--                                 (contractible fibres)
-- The module of the source has a parameter, a crisp assumption that
-- propositional truncations exist. The ported fragment does not use it, and
-- this module has no parameter and no hypothesis at all. Section 3 (♭ of a
-- proposition, ♭ of a set) is not in the source.
--
-- precohesion-shape0/FlatIdentity.agda is another thing: it proves one
-- direction, box x ≡ box y from a crisp x ≡ y, at level zero, by a crisp
-- match on refl (--flat-split). DiscretePullback has a family `Code` with
-- the same clauses as FlatCode below and the map from paths to it; that
-- module carries --flat-split, which is infective, so a module without the
-- flag cannot import it.
module NativeFlatIdentity where

open import Foundations
open import NativeSharp
  using (♯; sharp-unit; sharp-extract; box-crisp-path)
open import Adjointify using (quasi-inverse)
open import SmallPropositions using (retract-is-prop)

------------------------------------------------------------------------
-- 1. Crisp identity induction with a motive that depends on the
--    identification (Shulman, Brouwer's fixed-point theorem in real-cohesive
--    homotopy type theory, Theorem 5.6), derived from the native ♯.
--
--    The family  z, q ↦ ♯ (C z q)  is well formed because inside ♯ every
--    variable that is usable at that point counts as crisp. (♯ does not
--    make a variable usable that is not: an entry of the context that is
--    already inaccessible stays inaccessible.) Ordinary identity induction
--    gives an element of ♯ (C y p); it is crisp when everything it is built
--    from is crisp, and then ♯ can be eliminated.

crisp-J : {@♭ a b : Level} {@♭ A : Set a} (@♭ x : A)
        → (@♭ C : (@♭ y : A) → (@♭ p : x ≡ y) → Set b)
        → (@♭ c : C x refl)
        → (@♭ y : A) (@♭ p : x ≡ y) → C y p
crisp-J {A = A} x C c y p = sharp-extract (γ y p)
  where
  γ : (z : A) (q : x ≡ z) → ♯ (C z q)
  γ z refl = sharp-unit c

-- The computation rule holds by definition.
crisp-J-computes : {@♭ a b : Level} {@♭ A : Set a} (@♭ x : A)
                 → (@♭ C : (@♭ y : A) → (@♭ p : x ≡ y) → Set b)
                 → (@♭ c : C x refl)
                 → crisp-J x C c x refl ≡ c
crisp-J-computes x C c = refl

-- The form with an ORDINARY element of C x refl: crisp-J at the motive
-- C x refl → C y p, at the identity function.
crisp-identity-induction :
  {@♭ a b : Level} {@♭ A : Set a} {@♭ x : A}
  → (@♭ C : (@♭ y : A) → (@♭ p : x ≡ y) → Set b)
  → C x refl
  → (@♭ y : A) (@♭ p : x ≡ y) → C y p
crisp-identity-induction {x = x} C c y p =
  crisp-J x (λ y p → C x refl → C y p) (λ c → c) y p c

------------------------------------------------------------------------
-- 2. The identity types of ♭ A (Shulman, Theorem 6.1), by encode and decode.

module _ {@♭ a : Level} {@♭ A : Set a} where

  FlatCode : ♭ A → ♭ A → Set a
  FlatCode (box x) (box y) = ♭ (x ≡ y)

  flat-code-refl : (u : ♭ A) → FlatCode u u
  flat-code-refl (box x) = box refl

  flat-encode : (u v : ♭ A) → u ≡ v → FlatCode u v
  flat-encode u .u refl = flat-code-refl u

  flat-decode : (u v : ♭ A) → FlatCode u v → u ≡ v
  flat-decode (box x) (box y) (box p) = box-crisp-path p

  flat-decode-encode : (u v : ♭ A) (q : u ≡ v)
                     → flat-decode u v (flat-encode u v q) ≡ q
  flat-decode-encode (box x) .(box x) refl = refl

  flat-encode-box-path : (@♭ x y : A) (@♭ p : x ≡ y)
                       → flat-encode (box x) (box y) (box-crisp-path p) ≡ box p
  flat-encode-box-path x =
    crisp-identity-induction
      (λ y p → flat-encode (box x) (box y) (box-crisp-path p) ≡ box p) refl

  flat-encode-decode : (u v : ♭ A) (c : FlatCode u v)
                     → flat-encode u v (flat-decode u v c) ≡ c
  flat-encode-decode (box x) (box y) (box p) = flat-encode-box-path x y p

  -- For all u and v, not only for boxed crisp points.
  flat-identity : (u v : ♭ A) → IsEquiv (flat-encode u v)
  flat-identity u v = quasi-inverse (flat-decode u v)
    (flat-encode-decode u v) (flat-decode-encode u v)

  -- The statement of the source: (box x ≡ box y) ≃ ♭ (x ≡ y) for crisp x, y.
  box-path-to-flat : (@♭ x y : A) → box x ≡ box y → ♭ (x ≡ y)
  box-path-to-flat x y = flat-encode (box x) (box y)

  box-identity-equiv : (@♭ x y : A) → IsEquiv (box-path-to-flat x y)
  box-identity-equiv x y = flat-identity (box x) (box y)

  -- Its inverse is box-crisp-path, by computation.
  box-identity-inverse : (@♭ x y : A) (@♭ p : x ≡ y)
                       → inverse (box-identity-equiv x y) (box p)
                         ≡ box-crisp-path p
  box-identity-inverse x y p = refl

------------------------------------------------------------------------
-- 3. Consequences: ♭ preserves propositions and sets. The proofs of the
--    hypotheses are crisp, since their values are boxed.

flat-prop : {@♭ a : Level} {@♭ A : Set a}
          → (@♭ A-prop : IsProp A) → IsProp (♭ A)
flat-prop A-prop (box x) (box y) = box-crisp-path (A-prop x y)

flat-code-prop : {@♭ a : Level} {@♭ A : Set a} (@♭ A-set : IsSet A)
               → (u v : ♭ A) → IsProp (FlatCode u v)
flat-code-prop A-set (box x) (box y) = flat-prop (A-set x y)

flat-set : {@♭ a : Level} {@♭ A : Set a}
         → (@♭ A-set : IsSet A) → IsSet (♭ A)
flat-set A-set u v =
  retract-is-prop (flat-encode u v) (flat-decode u v)
    (flat-decode-encode u v)
    (flat-code-prop A-set u v)
