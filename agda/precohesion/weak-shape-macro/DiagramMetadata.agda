{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The closed part of a diagram over a context, as an INDEX: the data of
-- the staged route to the empty context. Claude (Fable), 13 November 2026;
-- after fable-impl-14 (HANDOFF-31; S3-METADATA-STAGING-PREFLIGHT-01;
-- S3-METADATA-NATIVE-FIDELITY-01; FABLE-REVIEW-06-ADDENDUM-01 section 3).
-- Postulate-free; no reflection; no capture; no shape is mentioned except
-- through the bundle that a descriptor wraps.
--
--   CrispPi A B            (@♭ x : A) → B x, under a name
--   PresentedBy F T        a presentation of F g by T g at every point g
--   DiagramMeta ℓ          the closed data of a CapturedDiagram ℓ
--   meta-of                its constructor as a function, the level first
--   MetaField              its accessors
--   WholeB m, WholeC m     the two closed whole sources of m
--   metadata d             the metadata of a bundle
--   CapturedDiagramFor m   a bundle whose metadata is m: the DESCRIPTOR;
--                          its constructor is `describe`
--   bundle                 the bundle of a descriptor
--
-- WHAT IS IN THE METADATA, AND WHAT IS NOT. In: the packed context with
-- its discreteness witness and decision procedure; the packed diagram
-- B, C, f, A with its four evidence terms; the two families that the two
-- captures store; one presentation family per side. The map f is a field
-- on its own: it stays in the index when the family is constant and the
-- local total source on the C side, at a point, no longer shows it. Out:
-- the stored point, the two payloads, function extensionality and every
-- hypothesis of a theorem.
-- So the metadata are the fields of CapturedDiagram other than g₀, KB
-- and KC, in the same order and at the same types, EXCEPT that the four
-- presentation fields of a side are one field here: the family
--   (g : G) → Presentation (FB g) (LocalTotal B A g)
-- of which they are the four components. The direct generator audits
-- exactly that family and defines the four fields of the bundle as its
-- components; an index that repeated each of them would repeat the
-- context, both families and the presentation eight times.
--
-- A value of DiagramMeta ℓ is native data. That the TYPE is closed says
-- nothing about a particular term: a term of this type written inside a
-- module may mention the variables of the module. Whether a given term is
-- closed is decided where it is used (ReadCapturedDiagram), not here.
--
-- THE DESCRIPTOR. CapturedDiagramFor is a data family; its index is
-- crisp and relevant, and its one constructor takes a whole bundle and
-- puts the bundle's own metadata there. So
--   * the head is rigid: Agda compares two types  CapturedDiagramFor m,
--     CapturedDiagramFor m′  by comparing m and m′;
--   * a descriptor is a view of a bundle that already exists. The point,
--     the payloads and the two rebuilt wrappers are those of the bundle,
--     unchanged (bundle (describe d) is d by computation);
--   * nothing here says that an index is closed, that two bundles with
--     one index have the same payloads, or that a payload is a constant.
--
-- CrispPi. Reflected syntax has no cohesion annotation, so a reflected Π
-- cannot have a crisp binder. A reflected λ handed to the second argument
-- of CrispPi receives its binder from the native type of that argument,
-- as the leaves of the unpack combinators do. Only an OUTER telescope is
-- to be written this way; nothing is to be crispified inside a domain or
-- an index.
module DiagramMetadata where

open import Foundations
open import DecidableData using (DecEq)
open import DiagramData

CrispPi : {@♭ a b : Level} (@♭ A : Set a) (@♭ B : (@♭ x : A) → Set b)
        → Set (a ⊔ b)
CrispPi A B = (@♭ x : A) → B x

-- Under a name for the reason given at the head of DiagramBundle (FORM OF
-- THE CONSTRUCTORS): a function type with an ordinary binder that is
-- applied to earlier crisp arguments is refused in a constructor's
-- telescope when written inline. This is the type of the parameter of
-- DiagramData.Presented.
PresentedBy : {@♭ ℓ : Level} {@♭ G : Set ℓ} (@♭ F T : G → Set ℓ) → Set ℓ
PresentedBy {G = G} F T = (g : G) → Presentation (F g) (T g)

------------------------------------------------------------------------
-- The metadata.

data DiagramMeta (@♭ ℓ : Level) : Set (lsuc ℓ) where
  diagram-meta :
    (@♭ G : Set ℓ) (@♭ dG : Discrete G) (@♭ dec : DecEq G)
    (@♭ B C : G → Set ℓ)
    (@♭ dB : DiscreteOver B) (@♭ B-set : AllSets B)
    (@♭ dC : DiscreteOver C) (@♭ C-set : AllSets C)
    (@♭ f : MapsOver C B)
    (@♭ A : Σ G B → Set ℓ)
    (@♭ FB FC : G → Set ℓ)
    (@♭ presB : PresentedBy FB (LocalTotal B A))
    (@♭ presC : PresentedBy FC (LocalTotal C (Reindexed f A)))
    → DiagramMeta ℓ

-- The constructor as a function, with the level as its first argument. A
-- generated index is written with this name: it has no constructor whose
-- parameter reflected syntax would drop, and every argument is visible.
meta-of :
  (@♭ ℓ : Level)
  (@♭ G : Set ℓ) (@♭ dG : Discrete G) (@♭ dec : DecEq G)
  (@♭ B C : G → Set ℓ)
  (@♭ dB : DiscreteOver B) (@♭ B-set : AllSets B)
  (@♭ dC : DiscreteOver C) (@♭ C-set : AllSets C)
  (@♭ f : MapsOver C B)
  (@♭ A : Σ G B → Set ℓ)
  (@♭ FB FC : G → Set ℓ)
  (@♭ presB : PresentedBy FB (LocalTotal B A))
  (@♭ presC : PresentedBy FC (LocalTotal C (Reindexed f A)))
  → DiagramMeta ℓ
meta-of ℓ = diagram-meta

module MetaField {@♭ ℓ : Level} where

  G : (@♭ m : DiagramMeta ℓ) → Set ℓ
  G (diagram-meta G _ _ _ _ _ _ _ _ _ _ _ _ _ _) = G

  dG : (@♭ m : DiagramMeta ℓ) → Discrete (G m)
  dG (diagram-meta _ dG _ _ _ _ _ _ _ _ _ _ _ _ _) = dG

  dec : (@♭ m : DiagramMeta ℓ) → DecEq (G m)
  dec (diagram-meta _ _ dec _ _ _ _ _ _ _ _ _ _ _ _) = dec

  B : (@♭ m : DiagramMeta ℓ) → G m → Set ℓ
  B (diagram-meta _ _ _ B _ _ _ _ _ _ _ _ _ _ _) = B

  C : (@♭ m : DiagramMeta ℓ) → G m → Set ℓ
  C (diagram-meta _ _ _ _ C _ _ _ _ _ _ _ _ _ _) = C

  dB : (@♭ m : DiagramMeta ℓ) (@♭ g : G m) → Discrete (B m g)
  dB (diagram-meta _ _ _ _ _ dB _ _ _ _ _ _ _ _ _) = dB

  B-set : (@♭ m : DiagramMeta ℓ) (g : G m) → IsSet (B m g)
  B-set (diagram-meta _ _ _ _ _ _ B-set _ _ _ _ _ _ _ _) = B-set

  dC : (@♭ m : DiagramMeta ℓ) (@♭ g : G m) → Discrete (C m g)
  dC (diagram-meta _ _ _ _ _ _ _ dC _ _ _ _ _ _ _) = dC

  C-set : (@♭ m : DiagramMeta ℓ) (g : G m) → IsSet (C m g)
  C-set (diagram-meta _ _ _ _ _ _ _ _ C-set _ _ _ _ _ _) = C-set

  f : (@♭ m : DiagramMeta ℓ) (g : G m) → C m g → B m g
  f (diagram-meta _ _ _ _ _ _ _ _ _ f _ _ _ _ _) = f

  A : (@♭ m : DiagramMeta ℓ) → Σ (G m) (B m) → Set ℓ
  A (diagram-meta _ _ _ _ _ _ _ _ _ _ A _ _ _ _) = A

  FB : (@♭ m : DiagramMeta ℓ) → G m → Set ℓ
  FB (diagram-meta _ _ _ _ _ _ _ _ _ _ _ FB _ _ _) = FB

  FC : (@♭ m : DiagramMeta ℓ) → G m → Set ℓ
  FC (diagram-meta _ _ _ _ _ _ _ _ _ _ _ _ FC _ _) = FC

  presB : (@♭ m : DiagramMeta ℓ) (g : G m)
        → Presentation (FB m g) (LocalTotal (B m) (A m) g)
  presB (diagram-meta _ _ _ _ _ _ _ _ _ _ _ _ _ presB _) = presB

  presC : (@♭ m : DiagramMeta ℓ) (g : G m)
        → Presentation (FC m g) (LocalTotal (C m) (Reindexed (f m) (A m)) g)
  presC (diagram-meta _ _ _ _ _ _ _ _ _ _ _ _ _ _ presC) = presC

-- The two closed whole sources of a diagram: the total sources over the
-- WHOLE packed context. For the metadata of a bundle d these are, by
-- computation, the source types of  AssembleCaptured.derivedB fe d  and
-- derivedC. The map is in the second one only through the family. These
-- are closed types whose family is a packed term: it computes at a point
-- of the packed context that is a tuple of crisp variables, not at a
-- variable point. So two whole sources whose fibres over every such
-- point are one type need not be convertible as written
-- (StagedDiagramMaps: for a constant family the two whole sources of one
-- diagram get two shapes).
WholeB WholeC : {@♭ ℓ : Level} (@♭ m : DiagramMeta ℓ) → Set ℓ
WholeB m = Σ (Σ (MetaField.G m) (MetaField.B m)) (MetaField.A m)
WholeC m = Σ (Σ (MetaField.G m) (MetaField.C m))
             (Reindexed (MetaField.f m) (MetaField.A m))

------------------------------------------------------------------------
-- The metadata of a bundle, and the descriptor.

-- Written with the accessors of the bundle, not by matching on it: then
-- WholeB (metadata d) and WholeC (metadata d) compute for a VARIABLE d.
-- The four presentation fields of a side are paired into one family; for
-- a bundle whose fields are the four components of a family p, as the
-- direct generator defines them, the pair is p by the η rules of
-- functions and of Σ.
metadata : {@♭ ℓ : Level} (@♭ d : CapturedDiagram ℓ) → DiagramMeta ℓ
metadata d = diagram-meta
  (F.G d) (F.dG d) (F.dec d) (F.B d) (F.C d)
  (F.dB d) (F.B-set d) (F.dC d) (F.C-set d) (F.f d) (F.A d)
  (F.FB d) (F.FC d)
  (λ g → F.outB d g , F.inB d g , F.secB d g , F.retB d g)
  (λ g → F.outC d g , F.inC d g , F.secC d g , F.retC d g)
  where module F = CapturedField

data CapturedDiagramFor {@♭ ℓ : Level} :
    (@♭ m : DiagramMeta ℓ) → Set (lsuc ℓ) where
  describe : (@♭ d : CapturedDiagram ℓ) → CapturedDiagramFor (metadata d)

bundle : {@♭ ℓ : Level} {@♭ m : DiagramMeta ℓ}
       → (@♭ s : CapturedDiagramFor m) → CapturedDiagram ℓ
bundle (describe d) = d
