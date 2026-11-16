Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026 (local time); one sentence updated
13 November 2026, after the final audits. Orbifold gate H9 of Fable's
roadmap [1], following Fable's corrected guidance [2, Section 4 D] and
GPT-6 Astra's audits [3].

Refining local homeomorphisms to basic opens
--------------------------------------------

The crisp cover of the bridge 3.9 [1] is obtained by restricting a
local homeomorphism to basic opens. Astra's audit insists that this
restriction must again be a genuine open embedding: injectivity with
open image is only a helper, and does not survive the passage to a
smaller open [2, Section 1, item 2; 3, Section 1]. This module proves
the passage:

  restriction-to-open-subsets-is-open-embedding : if s restricts to a
  homeomorphism from the open U to the open V (subspace topologies),
  and B ⊆ U is open, then s restricted to B is an open embedding: its
  image W is open, and the corestriction from B to W is a homeomorphism
  (continuous, with continuous inverse);

  is-basis, local-homeomorphisms-are-open-embeddings-on-basic-opens :
  for a basis (B n) of the source, every point of the source lies in a
  basic open on which a local homeomorphism is an open embedding.

The image W of B is the set of y in V whose preimage under the inverse
homeomorphism lies in B. It is open in V by continuity of the inverse,
and open in Y because V is (Topology.open-subspaces-have-open-images);
that step uses local openness of Y, which its small basis gives
(Topology.based-topologies-have-local-openness).

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Section 3.9.
    references/F01-orbifolds-roadmap-rev2.md
[2] Claude Fable 5.2. Orbifolds H9 and H10: follow-up to Astra's
    readiness audits, 13 November 2026 (UTC).
    references/F04-orbifolds-h9-h10-followup.md
[3] GPT-6 Astra. Fable H9 follow-up: route and interface audit,
    13 November 2026 (UTC); the H9/H10 release of the same day.
    references/A15-h9-followup-audit.txt

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module gist.Orbifolds.LocalHomeomorphisms
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import UF.Base
open import UF.Equiv
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import gist.Orbifolds.Topology fe pt

module _ {𝓧 𝓨 𝓤 : Universe} {X : 𝓧 ̇ } {Y : 𝓨 ̇ }
         (T : Topology X 𝓤) (T' : Topology Y 𝓤)
         (local-T' : has-local-openness T')
         (s : X → Y)
         (U : Subset X 𝓤) (V : Subset Y 𝓤)
         (m : (u : X) → u ∈ U → s u ∈ V)
         (oU : Topology.is-open T U) (oV : Topology.is-open T' V)
         (H : is-homeomorphism (subspace T U) (subspace T' V)
           (restriction T T' s U V m))
         (B : Subset X 𝓤) (oB : Topology.is-open T B) (B⊆U : B ⊆ U)
       where

 private
  module T = Topology T
  module T' = Topology T'

  h : 𝕊 T U → 𝕊 T' V
  h = restriction T T' s U V m

  e : is-equiv h
  e = pr₁ H

  h-is-continuous : is-continuous (subspace T U) (subspace T' V) h
  h-is-continuous = pr₁ (pr₂ H)

  h⁻¹ : 𝕊 T' V → 𝕊 T U
  h⁻¹ = inverse h e

  h⁻¹-is-continuous : is-continuous (subspace T' V) (subspace T U) h⁻¹
  h⁻¹-is-continuous = pr₂ (pr₂ H)

  retraction : (w : 𝕊 T U) → h⁻¹ (h w) ＝ w
  retraction = inverses-are-retractions h e

  section : (w : 𝕊 T' V) → h (h⁻¹ w) ＝ w
  section = inverses-are-sections h e

 image-of-B : Subset Y 𝓤
 image-of-B y = (Σ v ꞉ y ∈ V , pr₁ (h⁻¹ (y , v)) ∈ B) ,
                Σ-is-prop (∈-is-prop y V)
                 (λ v → ∈-is-prop (pr₁ (h⁻¹ (y , v))) B)

 private
  B-in-U : Subset (𝕊 T U) 𝓤
  B-in-U w = B (pr₁ w)

  B-in-U-is-open : Topology.is-open (subspace T U) B-in-U
  B-in-U-is-open w b = ∣ B , oB , b , (λ w' n → n) ∣

 image-of-B-is-open : T'.is-open image-of-B
 image-of-B-is-open =
  open-subspaces-have-open-images T' local-T' V oV (λ w → B-in-U (h⁻¹ w))
   (h⁻¹-is-continuous B-in-U B-in-U-is-open)

 s-maps-B-into-its-image : (b : X) → b ∈ B → s b ∈ image-of-B
 s-maps-B-into-its-image b β =
  m b (B⊆U b β) ,
  transport (_∈ B) ((ap pr₁ (retraction (b , B⊆U b β)))⁻¹) β

 corestriction-to-image : 𝕊 T B → 𝕊 T' image-of-B
 corestriction-to-image = corestriction (subspace T B) T' (s ∘ pr₁) image-of-B
                           (λ (b , β) → s-maps-B-into-its-image b β)

 private
  c = corestriction-to-image

  d : 𝕊 T' image-of-B → 𝕊 T B
  d (y , v , β) = pr₁ (h⁻¹ (y , v)) , β

  cd : c ∘ d ∼ id
  cd (y , v , β) = to-subtype-＝ (λ y' → ∈-is-prop y' image-of-B) first
   where
    w = h⁻¹ (y , v)

    first : s (pr₁ w) ＝ y
    first = ap pr₁ (section (y , v))

  dc : d ∘ c ∼ id
  dc (b , β) = to-subtype-＝ (λ b' → ∈-is-prop b' B)
                (ap pr₁ (retraction (b , B⊆U b β)))

  c-is-equiv : is-equiv c
  c-is-equiv = qinvs-are-equivs c (d , dc , cd)

  c-is-continuous : is-continuous (subspace T B) (subspace T' image-of-B) c
  c-is-continuous O oO (b , β) cO =
   ∥∥-rec ∃-is-prop
    (λ (U₁ , oU₁ , sbU₁ , U₁O) →
      ∥∥-functor
       (λ (U₂ , oU₂ , bU₂ , U₂U₁) →
         U₂ , oU₂ , bU₂ ,
         (λ (b' , β') b'U₂ → U₁O (c (b' , β')) (U₂U₁ (b' , B⊆U b' β') b'U₂)))
       (h-is-continuous (λ w → U₁ (pr₁ w))
         (λ w n → ∣ U₁ , oU₁ , n , (λ w' k → k) ∣)
         (b , B⊆U b β) sbU₁))
    (oO (c (b , β)) cO)

  d-is-continuous : is-continuous (subspace T' image-of-B) (subspace T B) d
  d-is-continuous O oO (y , v , β) dO =
   ∥∥-rec ∃-is-prop
    (λ (U₃ , oU₃ , uU₃ , U₃O) →
      ∥∥-functor
       (λ (U₄ , oU₄ , yU₄ , U₄U₃) →
         U₄ , oU₄ , yU₄ ,
         (λ (y' , v' , β') y'U₄ → U₃O (d (y' , v' , β')) (U₄U₃ (y' , v') y'U₄)))
       (h⁻¹-is-continuous (λ w → U₃ (pr₁ w))
         (λ w n → ∣ U₃ , oU₃ , n , (λ w' k → k) ∣)
         (y , v) uU₃))
    (oO (d (y , v , β)) dO)

 restriction-to-open-subsets-is-open-embedding
  : is-open-embedding (subspace T B) T' (s ∘ pr₁)
 restriction-to-open-subsets-is-open-embedding =
  ∣ image-of-B , (λ (b , β) → s-maps-B-into-its-image b β) ,
   image-of-B-is-open ,
    c-is-equiv , c-is-continuous , d-is-continuous ∣

\end{code}

Bases, and the cover by basic opens on which a local homeomorphism is
an open embedding.

\begin{code}

local-homeomorphisms-are-open-embeddings-on-basic-opens
 : {𝓧 𝓨 𝓤 𝓘 : Universe} {X : 𝓧 ̇ } {Y : 𝓨 ̇ }
   (T : Topology X 𝓤) (T' : Topology Y 𝓤)
 → has-local-openness T'
 → (s : X → Y) → is-local-homeomorphism T T' s
 → {I : 𝓘 ̇ } (B : I → Subset X 𝓤) → is-basis T B
 → (x : X)
 → ∃ i ꞉ I , x ∈ B i × is-open-embedding (subspace T (B i)) T' (s ∘ pr₁)
local-homeomorphisms-are-open-embeddings-on-basic-opens T T' local-T' s l B
 (oB , b) x =
 ∥∥-rec ∃-is-prop
  (λ (U , V , m , oU , oV , xU , sxV , H) →
    ∥∥-functor
     (λ (i , xBi , Bi⊆U) →
       i , xBi ,
       restriction-to-open-subsets-is-open-embedding T T' local-T' s U V m oU oV
        H
        (B i) (oB i) Bi⊆U)
     (b U oU x xU))
  (l x)

\end{code}

Injective local homeomorphisms (added at the request of GPT-6 Astra's
universe audit, Section 4 (a)). A local homeomorphism that is injective
on an open subset B is a genuine open embedding on B: its image is
open, and the corestriction is a homeomorphism, continuous in both
directions. This lets the chart index of the bridge 3.9 be cut out by
the small proposition "s is injective on B n", while each chart remains
a genuine open embedding. For T1, EtaleSourceMaps proves this crisp
subtype of ℕ to be ♭-discrete from Axiom C1 and ordinary setness,
without excluded middle. The carriers are in 𝓤, so that the image is a
𝓤-valued subset, and the target is a set, so that preimages in B are
unique.

\begin{code}

module _ {𝓤 : Universe} {X Y : 𝓤 ̇ }
         (T : Topology X 𝓤) (T' : Topology Y 𝓤)
         (local-T' : has-local-openness T')
         (Y-is-set : is-set Y)
         (s : X → Y) (l : is-local-homeomorphism T T' s)
         (B : Subset X 𝓤) (oB : Topology.is-open T B)
         (s-is-injective-on-B : (b b' : X) → b ∈ B → b' ∈ B → s b ＝ s b'
          → b ＝ b')
       where

 private
  module T = Topology T
  module T' = Topology T'

 image-on : Subset Y 𝓤
 image-on y = (∃ b ꞉ 𝕊 T B , s (pr₁ b) ＝ y) , ∃-is-prop

 private
  fibre-is-prop : (y : Y) → is-prop (Σ b ꞉ 𝕊 T B , s (pr₁ b) ＝ y)
  fibre-is-prop y ((b , β) , p) ((b' , β') , p') =
   to-subtype-＝ (λ _ → Y-is-set)
    (to-subtype-＝ (λ x → ∈-is-prop x B)
      (s-is-injective-on-B b b' β β' (p ∙ p' ⁻¹)))

  preimage : (w : 𝕊 T' image-on) → Σ b ꞉ 𝕊 T B , s (pr₁ b) ＝ pr₁ w
  preimage (y , m) = ∥∥-rec (fibre-is-prop y) id m

  c : 𝕊 T B → 𝕊 T' image-on
  c (b , β) = s b , ∣ (b , β) , refl ∣

  d : 𝕊 T' image-on → 𝕊 T B
  d w = pr₁ (preimage w)

  cd : c ∘ d ∼ id
  cd w = to-subtype-＝ (λ y → ∈-is-prop y image-on) (pr₂ (preimage w))

  dc : d ∘ c ∼ id
  dc (b , β) =
   ap pr₁ (fibre-is-prop (s b) (preimage (c (b , β))) ((b , β) , refl))

  c-is-equiv : is-equiv c
  c-is-equiv = qinvs-are-equivs c (d , dc , cd)

  chart-image-is-open-neighbourhood
   : (b : X) → b ∈ B → (A : Subset X 𝓤) → T.is-open A → b ∈ A
   → ∃ W ꞉ Subset Y 𝓤 , T'.is-open W × s b ∈ W
                      ×
                      ((y' : Y) → y' ∈ W → Σ u ꞉ X , u ∈ B × u ∈ A × (s u ＝ y'))
  chart-image-is-open-neighbourhood b β A oA bA =
   ∥∥-functor
    (λ (U , V , m , oU , oV , bU , sbV , H) →
      let
       B'' : Subset X 𝓤
       B'' = (B ∩ U) ∩ A
       oB'' : T.is-open B''
       oB'' = T.∩-is-open (B ∩ U) A (T.∩-is-open B U oB oU) oA
       B''⊆U : B'' ⊆ U
       B''⊆U x ((_ , xU) , _) = xU
       W = image-of-B T T' local-T' s U V m oU oV H B'' oB'' B''⊆U
       h⁻¹ = inverse (restriction T T' s U V m) (pr₁ H)
      in
       W ,
       image-of-B-is-open T T' local-T' s U V m oU oV H B'' oB'' B''⊆U ,
       s-maps-B-into-its-image T T' local-T' s U V m oU oV H B'' oB'' B''⊆U
        b ((β , bU) , bA) ,
       (λ y' (v , μ) →
         pr₁ (h⁻¹ (y' , v)) , pr₁ (pr₁ μ) , pr₂ μ ,
         ap pr₁
          (inverses-are-sections (restriction T T' s U V m) (pr₁ H) (y' , v))))
    (l b)

 image-on-is-open : T'.is-open image-on
 image-on-is-open =
  local-T' image-on
   (λ y → ∥∥-rec ∃-is-prop
           (λ ((b , β) , p) →
             ∥∥-functor
              (λ (W , oW , sbW , f) →
                W , oW , transport (_∈ W) p sbW ,
                (λ y' n → ∣ (pr₁ (f y' n) , pr₁ (pr₂ (f y' n))) ,
                           pr₂ (pr₂ (pr₂ (f y' n))) ∣))
              (chart-image-is-open-neighbourhood b β full T.full-is-open ⋆)))

 private
  c-is-continuous : is-continuous (subspace T B) (subspace T' image-on) c
  c-is-continuous O oO (b , β) cO =
   ∥∥-rec ∃-is-prop
    (λ (U₁ , oU₁ , sbU₁ , U₁O) →
      ∥∥-rec ∃-is-prop
       (λ (U , V , m , oU , oV , bU , sbV , H) →
         ∥∥-functor
          (λ (U₂ , oU₂ , bU₂ , U₂U₁) →
            (U ∩ U₂) , T.∩-is-open U U₂ oU oU₂ , (bU , bU₂) ,
            (λ (b' , β') (b'U , b'U₂) →
              U₁O (c (b' , β')) (U₂U₁ (b' , b'U) b'U₂)))
          (pr₁ (pr₂ H) (λ w → U₁ (pr₁ w))
            (λ w n → ∣ U₁ , oU₁ , n , (λ w' k → k) ∣)
            (b , bU) sbU₁))
       (l b))
    (oO (c (b , β)) cO)

  d-is-continuous : is-continuous (subspace T' image-on) (subspace T B) d
  d-is-continuous O oO w dO =
   ∥∥-rec ∃-is-prop
    (λ (U₃ , oU₃ , bU₃ , U₃O) →
      ∥∥-functor
       (λ (W , oW , sbW , f) →
         W , oW , transport (_∈ W) (pr₂ (preimage w)) sbW ,
         (λ w' y'W →
           let
            (u , uB , uU₃ , su) = f (pr₁ w') y'W
            e : (u , uB) ＝ d w'
            e = ap pr₁ (fibre-is-prop (pr₁ w') ((u , uB) , su) (preimage w'))
           in
            transport (_∈ O) e (U₃O (u , uB) uU₃)))
       (chart-image-is-open-neighbourhood (pr₁ (d w)) (pr₂ (d w)) U₃ oU₃ bU₃))
    (oO (d w) dO)

 injective-local-homeomorphisms-are-open-embeddings
  : is-open-embedding (subspace T B) T' (s ∘ pr₁)
 injective-local-homeomorphisms-are-open-embeddings =
  ∣ image-on , (λ b → pr₂ (c b)) , image-on-is-open ,
    c-is-equiv , c-is-continuous , d-is-continuous ∣

\end{code}

