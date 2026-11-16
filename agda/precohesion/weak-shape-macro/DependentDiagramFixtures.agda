{-# OPTIONS --cohesion --without-K --flat-split #-}

-- A reindexing diagram that depends on the two variables of a dependent
-- crisp context. Fixtures for ReindexingAcceptanceB; fable-impl-10.
-- They are in a module of their own because a capture refuses definitions
-- of its own file that do not unfold: source and context types must be
-- imported (see DependentContextFixtures).
--
-- WHY THERE ARE POSTULATES HERE. The earlier finite fixtures supply
-- decidable equality and therefore discharge the comparison by
-- DecidableReindexing. This fixture instead uses fixed abstract discrete
-- sets Row and Col WITHOUT SUPPLIED equality deciders, with an abstract
-- map between them and an abstract family of arbitrary types, so that a
-- generic client does not rely on decidable local bases. The postulates
-- are a convenient way to provide closed imported fixture constants.
-- They are input data of a test, not axioms of the foundation: no
-- statement about shape is postulated, and nothing is assumed about the
-- equality of Row or Col, or about the h-level of Cell. They are real
-- assumptions of every client that imports them and belong in its
-- inventory. (They are consistent: take Row = Col = Bool, step = id,
-- Cell = λ _ → ⊤. In that instance equality IS decidable: the fixture
-- does not exhibit a diagram whose comparison fails to be invertible.)
-- (Wording corrected in fable-impl-11, M10-CLIENT-AND-RUNNER-AUDIT-01,
-- 7 (a): native definability does not imply decidable equality.)
module DependentDiagramFixtures where

open import Foundations
open import Agda.Builtin.Bool
open import ShapeElim using (module SigmaDiscrete)
open import GlobalChoice using (×-set)
open import BoolDecidable using (bool-is-discrete; bool-is-set)
open import DependentContextFixtures using (Code; Source)

postulate
  Row Col : Set
  row-discrete : Discrete Row
  row-set : IsSet Row
  col-discrete : Discrete Col
  col-set : IsSet Col
  step : Col → Row
  -- A family of arbitrary types over Row: no sethood.
  Cell : Row → Set

-- The local bases at the point (b , v) of the context. The base on the C
-- side depends on b.
BaseB : (b : Bool) → Code b → Set
BaseB b v = Row

BaseC : (b : Bool) → Code b → Set
BaseC true v = Col
BaseC false v = Col × Bool

baseMap : (b : Bool) (v : Code b) → BaseC b v → BaseB b v
baseMap true v k = step k
baseMap false v k = step (fst k)

-- The source family: it depends on both variables of the context and on
-- the point of the base, and its fibres are not assumed to be sets.
Fam : (b : Bool) (v : Code b) → BaseB b v → Set
Fam b v r = Source b v × Cell r

-- Discreteness and sethood of the local bases. No decision procedure.
baseB-discrete : (@♭ b : Bool) (@♭ v : Code b) → Discrete (BaseB b v)
baseB-discrete b v = row-discrete

baseB-set : (b : Bool) (v : Code b) → IsSet (BaseB b v)
baseB-set b v = row-set

baseC-discrete : (@♭ b : Bool) (@♭ v : Code b) → Discrete (BaseC b v)
baseC-discrete true v = col-discrete
baseC-discrete false v = SigmaDiscrete.discrete col-discrete (λ _ → bool-is-discrete)

baseC-set : (b : Bool) (v : Code b) → IsSet (BaseC b v)
baseC-set true v = col-set
baseC-set false v = ×-set col-set bool-is-set
