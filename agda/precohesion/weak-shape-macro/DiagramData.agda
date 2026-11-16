{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The data of a closed diagram bundle, and the view of its two payloads as
-- captured shapes. Claude (Fable), 13 November 2026; generator checkpoint
-- after fable-impl-11 (HANDOFF-24, HANDOFF-28). Postulate-free; no
-- reflection; no capture.
--
-- This module is below the capture frontend: CaptureReuse imports it, so
-- that a visible bundle can be consulted when a shape is requested. It
-- imports nothing of the assembly library. ClosedDiagram and ClosedField
-- are the declarations of fable-impl-11's DiagramBundle, moved here
-- unchanged; DiagramBundle re-exports them.
--
--   ClosedDiagram ℓ, ClosedField   as in fable-impl-11
--   closed-seed X K                the wrapper of a SUPPLIED closed payload
--   ClosedSeed.sourceB, sourceC    the two total sources of a bundle
--   ClosedSeed.seedB, seedC        its two payloads as captured shapes
--   ClosedDiagramOf … d            d is the constructor on the given data
-- and, since step S3c (last section):
--   AllSets, MapsOver, …, Presented   abbreviations and presentations for
--                                  diagrams over a context
--   CapturedDiagram ℓ, CapturedField  a diagram stated inside a context,
--                                  with its two captures; localB, localC
--                                  are its REGISTRATION VIEW
--   PackedDiagramOf, CapturedDiagramOf  the two checks of the direct
--                                  generator
--
-- closed-seed is the constructor of CapturedShape on the terminal packed
-- context, the fields a capture in the empty context writes, and the
-- supplied payload. It takes the payload as an argument: it is a view of a
-- choice that already exists, not a source of shapes. For the wrapper s of
-- a capture in the empty context,  closed-seed X (whole-context s)  is s by
-- computation (DeclareDiagramClient: rebuilt-same, rebuilt₁-same).
--
-- The seeds are the REGISTRATION VIEW of a bundle and must stay
-- transparent: the matcher of CaptureReuse compares their sources and
-- whole payloads by conversion. Opacity belongs to the derived reflection
-- interfaces of DiagramAssembly, which bind their own copies.
module DiagramData where

open import Foundations
open import CaptureContext
  using (CrispUnitAt; end-at; unit-at-discrete; unpack-unit-at;
         Raise; raise; lower; lower-raise; raise-lower)
open import CapturedShape using (CapturedShape; captured)
open import RelativeSliceShape using (RelativeShapeOver)
open import GlobalPrecohesion using (Closed)
open import DecidableData using (DecEq)

------------------------------------------------------------------------
-- Closed diagrams (fable-impl-11, DiagramBundle).

data ClosedDiagram (@♭ ℓ : Level) : Set (lsuc ℓ) where
  closed-diagram :
    (@♭ B C : Set ℓ)
    (@♭ dB : Discrete B) (@♭ B-set : IsSet B)
    (@♭ dC : Discrete C) (@♭ C-set : IsSet C)
    (@♭ f : C → B) (@♭ A : B → Set ℓ)
    (@♭ KB : Closed (Σ B A)) (@♭ KC : Closed (Σ C (A ∘ f)))
    → ClosedDiagram ℓ

module ClosedField {@♭ ℓ : Level} where

  B : (@♭ d : ClosedDiagram ℓ) → Set ℓ
  B (closed-diagram B _ _ _ _ _ _ _ _ _) = B

  C : (@♭ d : ClosedDiagram ℓ) → Set ℓ
  C (closed-diagram _ C _ _ _ _ _ _ _ _) = C

  dB : (@♭ d : ClosedDiagram ℓ) → Discrete (B d)
  dB (closed-diagram _ _ dB _ _ _ _ _ _ _) = dB

  B-set : (@♭ d : ClosedDiagram ℓ) → IsSet (B d)
  B-set (closed-diagram _ _ _ B-set _ _ _ _ _ _) = B-set

  dC : (@♭ d : ClosedDiagram ℓ) → Discrete (C d)
  dC (closed-diagram _ _ _ _ dC _ _ _ _ _) = dC

  C-set : (@♭ d : ClosedDiagram ℓ) → IsSet (C d)
  C-set (closed-diagram _ _ _ _ _ C-set _ _ _ _) = C-set

  f : (@♭ d : ClosedDiagram ℓ) → C d → B d
  f (closed-diagram _ _ _ _ _ _ f _ _ _) = f

  A : (@♭ d : ClosedDiagram ℓ) → B d → Set ℓ
  A (closed-diagram _ _ _ _ _ _ _ A _ _) = A

  KB : (@♭ d : ClosedDiagram ℓ) → Closed (Σ (B d) (A d))
  KB (closed-diagram _ _ _ _ _ _ _ _ KB _) = KB

  KC : (@♭ d : ClosedDiagram ℓ) → Closed (Σ (C d) (A d ∘ f d))
  KC (closed-diagram _ _ _ _ _ _ _ _ _ KC) = KC

------------------------------------------------------------------------
-- The registration view.

closed-seed : {@♭ ℓ : Level} (@♭ X : Set ℓ) (@♭ K : Closed X)
            → CapturedShape {ℓ = ℓ} X
closed-seed {ℓ} X K =
  captured (CrispUnitAt ℓ) unit-at-discrete (unpack-unit-at (Raise ℓ X)) K
    end-at raise lower (lower-raise {b = ℓ}) raise-lower

module ClosedSeed {@♭ ℓ : Level} where

  sourceB : (@♭ d : ClosedDiagram ℓ) → Set ℓ
  sourceB d = Σ (ClosedField.B d) (ClosedField.A d)

  sourceC : (@♭ d : ClosedDiagram ℓ) → Set ℓ
  sourceC d = Σ (ClosedField.C d) (ClosedField.A d ∘ ClosedField.f d)

  seedB : (@♭ d : ClosedDiagram ℓ) → CapturedShape {ℓ = ℓ} (sourceB d)
  seedB d = closed-seed (sourceB d) (ClosedField.KB d)

  seedC : (@♭ d : ClosedDiagram ℓ) → CapturedShape {ℓ = ℓ} (sourceC d)
  seedC d = closed-seed (sourceC d) (ClosedField.KC d)

------------------------------------------------------------------------
-- The last check of the generator (DeclareDiagram). After the public
-- name d is defined, the generator has Agda check the constructor term
--   generated KB KC
-- at the type  ClosedDiagramOf dB B-set dC C-set f A d  formed from the
-- user's own typed arguments. Checking that DIRECT constructor forces d
-- to convert to the bundle constructor on those arguments and the two
-- payloads, so the stored fields are compared with the native inputs and
-- not with their reflected images. Nothing is claimed about other ways
-- of inhabiting the type.

data ClosedDiagramOf {@♭ ℓ : Level} {@♭ B C : Set ℓ}
  (@♭ dB : Discrete B) (@♭ B-set : IsSet B)
  (@♭ dC : Discrete C) (@♭ C-set : IsSet C)
  (@♭ f : C → B) (@♭ A : B → Set ℓ) : ClosedDiagram ℓ → Set (lsuc ℓ) where
  generated : (@♭ KB : Closed (Σ B A)) (@♭ KC : Closed (Σ C (A ∘ f)))
            → ClosedDiagramOf dB B-set dC C-set f A
                (closed-diagram B C dB B-set dC C-set f A KB KC)

------------------------------------------------------------------------
-- Step S3c, 13 November 2026 (after fable-impl-13): the data of diagrams
-- over a context. Moved here unchanged from DiagramBundle, which
-- re-exports every name: the abbreviations of the bundles over a context,
-- the presentations, the captured bundle with its accessors, and the two
-- certificate types of the direct generator. Nothing of the assembly
-- library, of the decision PROOFS or of reflection is imported for them.
-- CaptureReuse consults the two rebuilt wrappers of a visible captured
-- bundle, CapturedField.localB and localC, exactly as it consults the two
-- seeds of a closed one.

module _ {@♭ ℓ : Level} where

  AllSets : {@♭ G : Set ℓ} (@♭ B : G → Set ℓ) → Set ℓ
  AllSets {G} B = (g : G) → IsSet (B g)

  MapsOver : {@♭ G : Set ℓ} (@♭ C B : G → Set ℓ) → Set ℓ
  MapsOver {G} C B = (g : G) → C g → B g

  -- The family on the C side of an open diagram.
  Reindexed : {@♭ G : Set ℓ} {@♭ B C : G → Set ℓ}
            → (@♭ f : MapsOver C B) (@♭ A : Σ G B → Set ℓ) → Σ G C → Set ℓ
  Reindexed f A = A ∘ (λ w → fst w , f (fst w) (snd w))

  -- For captured diagrams (step S3a). The local total source of a family
  -- over Σ G B, as a family over the context; and a pointwise inverse law
  -- between two maps of families over the context.
  LocalTotal : {@♭ G : Set ℓ} (@♭ B : G → Set ℓ) (@♭ A : Σ G B → Set ℓ)
             → G → Set ℓ
  LocalTotal B A g = Σ (B g) (λ y → A (g , y))

  SectionOver : {@♭ G : Set ℓ} {@♭ F T : G → Set ℓ}
              → (@♭ out : MapsOver F T) (@♭ back : MapsOver T F) → Set ℓ
  SectionOver {G} {F} {T} out back = (g : G) (z : T g) → out g (back g z) ≡ z

  -- For the direct generator (step S3b). Discreteness of every fibre, at a
  -- CRISP point of the context: the type of the fields dB and dC of the
  -- two bundles over a context, under a name. Reflected syntax cannot
  -- write the crisp binder; a generator names this type instead.
  DiscreteOver : {@♭ G : Set ℓ} (@♭ B : G → Set ℓ) → Set ℓ
  DiscreteOver {G} B = (@♭ g : G) → Discrete (B g)

  -- The family over one fibre of the base, at a point of the context.
  -- Under a name for the reason given at the head of DiagramBundle (FORM
  -- OF THE CONSTRUCTORS): an inline λ with an ordinary binder is refused
  -- where crisp data are expected in a constructor's type.
  FibreAt : {@♭ G : Set ℓ} {@♭ B : G → Set ℓ}
          → (@♭ A : Σ G B → Set ℓ) (@♭ g : G) → B g → Set ℓ
  FibreAt A g y = A (g , y)

  -- A family over the total space of B, from its curried form. The packed
  -- family of the direct generator is  OverTotal Ã₂  for a nest of
  -- eliminators Ã₂; so the generator writes no λ and no projection.
  OverTotal : {@♭ G : Set ℓ} {@♭ B : G → Set ℓ}
            → ((g : G) → B g → Set ℓ) → Σ G B → Set ℓ
  OverTotal A w = A (fst w) (snd w)

  -- A presentation of one type by another: two maps and their two inverse
  -- laws. `lowering` is the presentation that every capture has: the
  -- raised copy of its source by the source, with the capture's own
  -- source maps and laws. The direct generator packs ONE such family per
  -- side, a nest of eliminators with leaf `lowering`, and the four fields
  -- of the bundle are its four components (Presented). So no packed
  -- inverse law mentions the packed maps as terms.
  Presentation : (F T : Set ℓ) → Set ℓ
  Presentation F T =
    Σ (F → T) (λ out → Σ (T → F) (λ back →
      ((z : T) → out (back z) ≡ z) × ((u : F) → back (out u) ≡ u)))

  lowering : {X : Set ℓ} → Presentation (Raise ℓ X) X
  lowering = lower , raise , (λ z → refl) , raise-lower

  module Presented {@♭ G : Set ℓ} {@♭ F T : G → Set ℓ}
    (@♭ p : (g : G) → Presentation (F g) (T g)) where

    out : MapsOver F T
    out g = fst (p g)

    back : MapsOver T F
    back g = fst (snd (p g))

    section-law : SectionOver out back
    section-law g = fst (snd (snd (p g)))

    retraction-law : SectionOver back out
    retraction-law g = snd (snd (snd (p g)))

------------------------------------------------------------------------
-- Captured diagrams: a diagram stated INSIDE a context, with the two
-- captures made there. Step S3a of the direct in-module route
-- (DIRECT-OPEN-DIAGRAM-ROUTE-01; FABLE-REVIEW-06 sections 4.2 to 4.4).
-- Claude (Fable), 13 November 2026; after fable-impl-12. No reflection, no
-- capture, no postulate: a value of this type is made by a frontend, or
-- typed in (AssemblyClientDirect), from data that already exist.
--
-- FIELDS, all crisp.
--   G dG dec                the packed context, discrete, with decidable
--                           equality
--   B C dB B-set dC C-set f A
--                           the packed diagram, as in OpenDiagram
--   g₀                      the stored point: the context at which the
--                           bundle was made
--   FB FC                   the two families over G that the two captures
--                           STORE (not an assumed normal form of them)
--   KB KC                   the whole payloads of the two captures,
--                           relative reflections of FB and FC over G
--   outB inB secB retB      a pointwise presentation of FB by the local
--                           total source  LocalTotal B A:  two maps of
--                           families over G and their two inverse laws,
--                           pointwise, with no function extensionality
--   outC inC secC retC      the same for FC and LocalTotal C (Reindexed f A)
-- There is no payload of a WHOLE total here and none is needed: the whole
-- data are derived (AssembleCaptured). The two payloads are contextual
-- choices. Nothing says they are closed constants, and for bundles made at
-- different points of the context nothing identifies them.
--
-- localB, localC rebuild the two wrappers from the stored fields: the
-- constructor of CapturedShape on G, dG, the stored family and payload,
-- the stored point, and the presentation AT THAT POINT as source maps.
-- An arbitrary pointwise presentation does not recover an original
-- wrapper: the rebuilt wrapper is the capture exactly when the stored
-- fields are the capture's own context, discreteness witness, family,
-- payload and point, and the presentation at that point is the capture's
-- own source maps and laws. For the bundles of AssemblyClientDirect and
-- AssemblyDirectLevelCheck that holds by computation, for both wrappers
-- (local-is-captured). A generator has to emit exactly those fields.

data CapturedDiagram (@♭ ℓ : Level) : Set (lsuc ℓ) where
  captured-diagram :
    (@♭ G : Set ℓ) (@♭ dG : Discrete G) (@♭ dec : DecEq G)
    (@♭ B C : G → Set ℓ)
    (@♭ dB : (@♭ g : G) → Discrete (B g)) (@♭ B-set : AllSets B)
    (@♭ dC : (@♭ g : G) → Discrete (C g)) (@♭ C-set : AllSets C)
    (@♭ f : MapsOver C B)
    (@♭ A : Σ G B → Set ℓ)
    (@♭ g₀ : G)
    (@♭ FB FC : G → Set ℓ)
    (@♭ KB : RelativeShapeOver G dG FB) (@♭ KC : RelativeShapeOver G dG FC)
    (@♭ outB : MapsOver FB (LocalTotal B A))
    (@♭ inB : MapsOver (LocalTotal B A) FB)
    (@♭ secB : SectionOver outB inB) (@♭ retB : SectionOver inB outB)
    (@♭ outC : MapsOver FC (LocalTotal C (Reindexed f A)))
    (@♭ inC : MapsOver (LocalTotal C (Reindexed f A)) FC)
    (@♭ secC : SectionOver outC inC) (@♭ retC : SectionOver inC outC)
    → CapturedDiagram ℓ

module CapturedField {@♭ ℓ : Level} where

  G : (@♭ d : CapturedDiagram ℓ) → Set ℓ
  G (captured-diagram G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = G

  dG : (@♭ d : CapturedDiagram ℓ) → Discrete (G d)
  dG (captured-diagram _ dG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = dG

  dec : (@♭ d : CapturedDiagram ℓ) → DecEq (G d)
  dec (captured-diagram _ _ dec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = dec

  B : (@♭ d : CapturedDiagram ℓ) → G d → Set ℓ
  B (captured-diagram _ _ _ B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = B

  C : (@♭ d : CapturedDiagram ℓ) → G d → Set ℓ
  C (captured-diagram _ _ _ _ C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = C

  dB : (@♭ d : CapturedDiagram ℓ) (@♭ g : G d) → Discrete (B d g)
  dB (captured-diagram _ _ _ _ _ dB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = dB

  B-set : (@♭ d : CapturedDiagram ℓ) (g : G d) → IsSet (B d g)
  B-set (captured-diagram _ _ _ _ _ _ B-set _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = B-set

  dC : (@♭ d : CapturedDiagram ℓ) (@♭ g : G d) → Discrete (C d g)
  dC (captured-diagram _ _ _ _ _ _ _ dC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = dC

  C-set : (@♭ d : CapturedDiagram ℓ) (g : G d) → IsSet (C d g)
  C-set (captured-diagram _ _ _ _ _ _ _ _ C-set _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = C-set

  f : (@♭ d : CapturedDiagram ℓ) (g : G d) → C d g → B d g
  f (captured-diagram _ _ _ _ _ _ _ _ _ f _ _ _ _ _ _ _ _ _ _ _ _ _ _) = f

  A : (@♭ d : CapturedDiagram ℓ) → Σ (G d) (B d) → Set ℓ
  A (captured-diagram _ _ _ _ _ _ _ _ _ _ A _ _ _ _ _ _ _ _ _ _ _ _ _) = A

  point : (@♭ d : CapturedDiagram ℓ) → G d
  point (captured-diagram _ _ _ _ _ _ _ _ _ _ _ g₀ _ _ _ _ _ _ _ _ _ _ _ _) = g₀

  FB : (@♭ d : CapturedDiagram ℓ) → G d → Set ℓ
  FB (captured-diagram _ _ _ _ _ _ _ _ _ _ _ _ FB _ _ _ _ _ _ _ _ _ _ _) = FB

  FC : (@♭ d : CapturedDiagram ℓ) → G d → Set ℓ
  FC (captured-diagram _ _ _ _ _ _ _ _ _ _ _ _ _ FC _ _ _ _ _ _ _ _ _ _) = FC

  KB : (@♭ d : CapturedDiagram ℓ) → RelativeShapeOver (G d) (dG d) (FB d)
  KB (captured-diagram _ _ _ _ _ _ _ _ _ _ _ _ _ _ KB _ _ _ _ _ _ _ _ _) = KB

  KC : (@♭ d : CapturedDiagram ℓ) → RelativeShapeOver (G d) (dG d) (FC d)
  KC (captured-diagram _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KC _ _ _ _ _ _ _ _) = KC

  -- The two local total sources, as families over the context.
  TB : (@♭ d : CapturedDiagram ℓ) → G d → Set ℓ
  TB d = LocalTotal (B d) (A d)

  TC : (@♭ d : CapturedDiagram ℓ) → G d → Set ℓ
  TC d = LocalTotal (C d) (Reindexed (f d) (A d))

  outB : (@♭ d : CapturedDiagram ℓ) (g : G d) → FB d g → TB d g
  outB (captured-diagram _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outB _ _ _ _ _ _ _) = outB

  inB : (@♭ d : CapturedDiagram ℓ) (g : G d) → TB d g → FB d g
  inB (captured-diagram _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inB _ _ _ _ _ _) = inB

  secB : (@♭ d : CapturedDiagram ℓ) (g : G d) (z : TB d g)
       → outB d g (inB d g z) ≡ z
  secB (captured-diagram _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ secB _ _ _ _ _) = secB

  retB : (@♭ d : CapturedDiagram ℓ) (g : G d) (u : FB d g)
       → inB d g (outB d g u) ≡ u
  retB (captured-diagram _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ retB _ _ _ _) = retB

  outC : (@♭ d : CapturedDiagram ℓ) (g : G d) → FC d g → TC d g
  outC (captured-diagram _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outC _ _ _) = outC

  inC : (@♭ d : CapturedDiagram ℓ) (g : G d) → TC d g → FC d g
  inC (captured-diagram _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inC _ _) = inC

  secC : (@♭ d : CapturedDiagram ℓ) (g : G d) (z : TC d g)
       → outC d g (inC d g z) ≡ z
  secC (captured-diagram _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ secC _) = secC

  retC : (@♭ d : CapturedDiagram ℓ) (g : G d) (u : FC d g)
       → inC d g (outC d g u) ≡ u
  retC (captured-diagram _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ retC) = retC

  -- The two wrappers, rebuilt from the stored fields.
  localB : (@♭ d : CapturedDiagram ℓ) → CapturedShape {ℓ = ℓ} (TB d (point d))
  localB d = captured (G d) (dG d) (FB d) (KB d) (point d)
    (inB d (point d)) (outB d (point d)) (secB d (point d)) (retB d (point d))

  localC : (@♭ d : CapturedDiagram ℓ) → CapturedShape {ℓ = ℓ} (TC d (point d))
  localC d = captured (G d) (dG d) (FC d) (KC d) (point d)
    (inC d (point d)) (outC d (point d)) (secC d (point d)) (retC d (point d))

------------------------------------------------------------------------
-- The two native checks of the direct generator (DeclareCapturedDiagram,
-- step S3b; S3-PACKED-DATA-AUDIT-SEAM-01 section 3). Claude (Fable),
-- 13 November 2026. No reflection, no postulate.
--
-- The generator receives the diagram as native typed arguments in the
-- user's context and packs it by reflection, which is lossy. Twice it has
-- Agda check ONE DIRECT CONSTRUCTOR TERM at a type formed from the user's
-- ORIGINAL arguments:
--
--   before any shape is requested:
--     packed G dG dec B̃ C̃ dB̃ B̃-set dC̃ C̃-set f̃ Ã g₀ FB FC <presentations>
--       : PackedDiagramOf dB B-set dC C-set f A
--   after the bundle d is defined:
--     bundled d : CapturedDiagramOf dB B-set dC C-set f A sB sC d
--
-- The constructor `packed` takes every field of the bundle except the two
-- payloads, at the types the bundle gives them. So the first check also
-- has Agda check all the closed fields that the generator has made, at
-- their types, before a shape is requested.
--
-- In both types the user's arguments are INDICES, and the constructor
-- puts there the packed data at the point: B̃ g₀, C̃ g₀ (as the implicit
-- indices), dB̃ g₀, B̃-set g₀, dC̃ g₀, C̃-set g₀, f̃ g₀ and FibreAt Ã g₀, which
-- is λ y → Ã (g₀ , y). So checking the constructor term forces each of
-- them to convert to the argument the user wrote: the map on its own,
-- whatever the family is, and each of the four evidence terms. The second
-- type has, in addition, the two completed captures sB, sC and the bundle
-- as ORDINARY indices (they come out of the reflection monad as ordinary
-- values; no accessor is applied to them), and the constructor, which
-- binds its own crisp bundle, puts the REBUILT wrappers localB d, localC d
-- there: the wrappers that the library reads off the bundle are the two
-- original captures, with their context, discreteness witness, family,
-- payload, point, source maps and laws.
--
-- What is claimed is about those two constructor terms, which Agda has
-- checked. Nothing is claimed about other ways of inhabiting the types;
-- they are not equality axioms and no proof by path is involved. These
-- checks do not replace the closure audit of the packed terms
-- (CaptureShape.auditPacked): a packed term that still mentioned the
-- variables of the context would pass them.

data PackedDiagramOf {@♭ ℓ : Level} :
    {@♭ B C : Set ℓ}
    (@♭ dB : Discrete B) (@♭ B-set : IsSet B)
    (@♭ dC : Discrete C) (@♭ C-set : IsSet C)
    (@♭ f : C → B) (@♭ A : B → Set ℓ) → Set (lsuc ℓ) where
  packed :
    (@♭ G : Set ℓ) (@♭ dG : Discrete G) (@♭ dec : DecEq G)
    (@♭ B C : G → Set ℓ)
    (@♭ dB : DiscreteOver B) (@♭ B-set : AllSets B)
    (@♭ dC : DiscreteOver C) (@♭ C-set : AllSets C)
    (@♭ f : MapsOver C B)
    (@♭ A : Σ G B → Set ℓ)
    (@♭ g₀ : G)
    (@♭ FB FC : G → Set ℓ)
    (@♭ outB : MapsOver FB (LocalTotal B A))
    (@♭ inB : MapsOver (LocalTotal B A) FB)
    (@♭ secB : SectionOver outB inB) (@♭ retB : SectionOver inB outB)
    (@♭ outC : MapsOver FC (LocalTotal C (Reindexed f A)))
    (@♭ inC : MapsOver (LocalTotal C (Reindexed f A)) FC)
    (@♭ secC : SectionOver outC inC) (@♭ retC : SectionOver inC outC)
    → PackedDiagramOf (dB g₀) (B-set g₀) (dC g₀) (C-set g₀) (f g₀)
        (FibreAt A g₀)

data CapturedDiagramOf {@♭ ℓ : Level} :
    {@♭ B C : Set ℓ}
    (@♭ dB : Discrete B) (@♭ B-set : IsSet B)
    (@♭ dC : Discrete C) (@♭ C-set : IsSet C)
    (@♭ f : C → B) (@♭ A : B → Set ℓ)
    → CapturedShape {ℓ = ℓ} (Σ B A) → CapturedShape {ℓ = ℓ} (Σ C (A ∘ f))
    → CapturedDiagram ℓ → Set (lsuc ℓ) where
  bundled :
    (@♭ d : CapturedDiagram ℓ)
    → CapturedDiagramOf
        (CapturedField.dB d (CapturedField.point d))
        (CapturedField.B-set d (CapturedField.point d))
        (CapturedField.dC d (CapturedField.point d))
        (CapturedField.C-set d (CapturedField.point d))
        (CapturedField.f d (CapturedField.point d))
        (FibreAt (CapturedField.A d) (CapturedField.point d))
        (CapturedField.localB d) (CapturedField.localC d) d
