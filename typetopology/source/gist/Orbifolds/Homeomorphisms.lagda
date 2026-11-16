Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026 (local time). Orbifold gate H9 of Fable's
roadmap [1], following Fable's corrected guidance [2, Section 4 C].

Homeomorphisms and final topologies
-----------------------------------

General facts about the topologies of the module Topology, used to make
R an ordinary manifold and to move charts:

  final-topology g T : for a map g : Y → X, the subsets of X whose
  preimage is open; when g is an equivalence, g is a homeomorphism onto
  it (equivalences-are-homeomorphisms-onto-final-topologies);

  identity, composite, inverse and restriction of homeomorphisms
  (restrictions-of-homeomorphisms-to-subspaces: a homeomorphism h
  restricts to a homeomorphism between the subspaces h⁻¹(S) and S);

  regularity, T₀ and local openness are invariant under
  homeomorphisms.

Every statement is about the actual topologies, with continuity in both
directions where a homeomorphism is claimed.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] Claude Fable 5.2. Orbifolds H9 and H10: follow-up to Astra's
    readiness audits, 13 November 2026 (UTC).
    references/F04-orbifolds-h9-h10-followup.md

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module gist.Orbifolds.Homeomorphisms
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open import UF.Base
open import UF.Equiv
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import gist.Orbifolds.Topology fe pt

open PropositionalTruncation pt

\end{code}

Final topologies.

\begin{code}

final-topology : {𝓧 𝓤 : Universe} {X Y : 𝓧 ̇ }
               → (Y → X) → Topology Y 𝓤 → Topology X 𝓤
final-topology {𝓧} {𝓤} {X} {Y} g T = record
 { is-open = λ U → T.is-open (λ y → U (g y))
  ; being-open-is-prop = λ U → T.being-open-is-prop (λ y → U (g y))
  ; openness-is-extensional =
    λ A B A⊆B B⊆A → T.openness-is-extensional (λ y → A (g y)) (λ y → B (g y))
                     (λ y → A⊆B (g y)) (λ y → B⊆A (g y))
  ; full-is-open = T.full-is-open
  ; ∩-is-open = λ U V → T.∩-is-open (λ y → U (g y)) (λ y → V (g y))
  ; ⋃-is-open = λ U o → T.⋃-is-open (λ i y → U i (g y)) o
  }
 where
  module T = Topology T

final-topologies-have-local-openness
 : {𝓧 𝓤 : Universe} {X Y : 𝓧 ̇ } (g : Y → X) (T : Topology Y 𝓤)
 → has-local-openness T → has-local-openness (final-topology g T)
final-topologies-have-local-openness g T l A k =
 l (λ y → A (g y))
  (λ y m → ∥∥-functor
    (λ (U , oU , u , UA) → (λ y' → U (g y')) , oU , u , (λ y' → UA (g y')))
             (k (g y) m))

\end{code}

Continuity is invariant under homotopy, and composes.

\begin{code}

module _ {𝓧 𝓨 𝓤 : Universe} {X : 𝓧 ̇ } {Y : 𝓨 ̇ }
         (T : Topology X 𝓤) (T' : Topology Y 𝓤)
       where

 private
  module T = Topology T
  module T' = Topology T'

 continuity-is-homotopy-invariant : (f g : X → Y) → f ∼ g
                                  → is-continuous T T' f → is-continuous T T' g
 continuity-is-homotopy-invariant f g h c V o =
  T.openness-is-extensional (λ x → V (f x)) (λ x → V (g x))
   (λ x m → transport (_∈ V) (h x) m)
   (λ x m → transport (_∈ V) ((h x)⁻¹) m)
   (c V o)

 inverse-of-homeomorphism : (f : X → Y) → is-homeomorphism T T' f → Y → X
 inverse-of-homeomorphism f (e , _) = inverse f e

 inverses-of-homeomorphisms-are-homeomorphisms
  : (f : X → Y) (h : is-homeomorphism T T' f)
  → is-homeomorphism T' T (inverse-of-homeomorphism f h)
 inverses-of-homeomorphisms-are-homeomorphisms f (e , c , c') =
  inverses-are-equivs f e ,
  c' ,
  continuity-is-homotopy-invariant f
   (inverse (inverse f e) (inverses-are-equivs f e))
   (λ x →
     (inverses-are-retractions (inverse f e) (inverses-are-equivs f e) (f x))⁻¹
          ∙ ap (inverse (inverse f e) (inverses-are-equivs f e))
               (inverses-are-retractions f e x))
   c

∘-is-continuous : {𝓧 𝓨 𝓩 𝓤 : Universe} {X : 𝓧 ̇ } {Y : 𝓨 ̇ } {Z : 𝓩 ̇ }
                  (T : Topology X 𝓤) (T' : Topology Y 𝓤) (T'' : Topology Z 𝓤)
                  (f : X → Y) (g : Y → Z)
                → is-continuous T T' f → is-continuous T' T'' g
                → is-continuous T T'' (g ∘ f)
∘-is-continuous T T' T'' f g c d W o = c (λ y → W (g y)) (d W o)

id-is-homeomorphism : {𝓧 𝓤 : Universe} {X : 𝓧 ̇ } (T : Topology X 𝓤)
                    → is-homeomorphism T T id
id-is-homeomorphism {𝓧} {𝓤} {X} T = id-is-equiv X , (λ V o → o) , (λ V o → o)

∘-is-homeomorphism : {𝓧 𝓨 𝓩 𝓤 : Universe} {X : 𝓧 ̇ } {Y : 𝓨 ̇ } {Z : 𝓩 ̇ }
                     (T : Topology X 𝓤) (T' : Topology Y 𝓤) (T'' : Topology Z 𝓤)
                     (f : X → Y) (g : Y → Z)
                   → is-homeomorphism T T' f → is-homeomorphism T' T'' g
                   → is-homeomorphism T T'' (g ∘ f)
∘-is-homeomorphism T T' T'' f g (e , c , c') (d , k , k') =
 ∘-is-equiv e d ,
 ∘-is-continuous T T' T'' f g c k ,
 continuity-is-homotopy-invariant T'' T (inverse f e ∘ inverse g d)
  (inverse (g ∘ f) (∘-is-equiv e d))
  (λ z → (inverses-are-retractions (g ∘ f) (∘-is-equiv e d) _)⁻¹
         ∙ ap (inverse (g ∘ f) (∘-is-equiv e d))
              (ap g (inverses-are-sections f e (inverse g d z))
               ∙ inverses-are-sections g d z))
  (∘-is-continuous T'' T' T (inverse g d) (inverse f e) k' c')

\end{code}

An equivalence is a homeomorphism onto the final topology it induces.

\begin{code}

equivalences-are-homeomorphisms-onto-final-topologies
 : {𝓧 𝓤 : Universe} {X Y : 𝓧 ̇ } (T : Topology Y 𝓤) (g : Y → X) (e : is-equiv g)
 → is-homeomorphism T (final-topology g T) g
equivalences-are-homeomorphisms-onto-final-topologies T g e =
 e ,
 (λ U o → o) ,
 (λ W o → Topology.openness-is-extensional T W (λ y → W (inverse g e (g y)))
           (λ y m → transport (_∈ W) ((inverses-are-retractions g e y)⁻¹) m)
           (λ y m → transport (_∈ W) (inverses-are-retractions g e y) m)
           o)

\end{code}

Restrictions of homeomorphisms to subspaces: if h : X → Y is a
homeomorphism and S ⊆ Y, then h restricts to a homeomorphism from the
subspace h⁻¹(S) of X to the subspace S of Y.

\begin{code}

module _ {𝓧 𝓨 𝓤 : Universe} {X : 𝓧 ̇ } {Y : 𝓨 ̇ }
         (T : Topology X 𝓤) (T' : Topology Y 𝓤)
         (h : X → Y) (H : is-homeomorphism T T' h)
         (S : Subset Y 𝓤)
       where

 private
  module T = Topology T
  module T' = Topology T'
  e = pr₁ H
  k = inverse h e
  η : (x : X) → k (h x) ＝ x
  η = inverses-are-retractions h e
  ε : (y : Y) → h (k y) ＝ y
  ε = inverses-are-sections h e
  h⁻¹S : Subset X 𝓤
  h⁻¹S x = S (h x)

 restriction-to-preimage : 𝕊 T h⁻¹S → 𝕊 T' S
 restriction-to-preimage (x , m) = h x , m

 restriction-to-preimage-inverse : 𝕊 T' S → 𝕊 T h⁻¹S
 restriction-to-preimage-inverse (y , m) = k y , transport (_∈ S) ((ε y)⁻¹) m

 restrictions-of-homeomorphisms-to-subspaces
  : is-homeomorphism (subspace T h⁻¹S) (subspace T' S) restriction-to-preimage
 restrictions-of-homeomorphisms-to-subspaces =
  qinvs-are-equivs restriction-to-preimage
   (restriction-to-preimage-inverse ,
    (λ (x , m) → to-subtype-＝ (λ x' → ∈-is-prop x' h⁻¹S) (η x)) ,
    (λ (y , m) → to-subtype-＝ (λ y' → ∈-is-prop y' S) (ε y))) ,
  continuous ,
  continuous-inverse
  where
   continuous
    : is-continuous (subspace T h⁻¹S) (subspace T' S) restriction-to-preimage
   continuous W oW (x , m) n =
    ∥∥-functor
     (λ (U , oU , hxU , UW) → (λ x' → U (h x')) , pr₁ (pr₂ H) U oU , hxU ,
                               (λ (x' , m') u → UW (h x' , m') u))
     (oW (h x , m) n)

   continuous-inverse
    : is-continuous (subspace T' S) (subspace T h⁻¹S)
       restriction-to-preimage-inverse
   continuous-inverse W oW (y , m) n =
    ∥∥-functor
     (λ (U , oU , kyU , UW) → (λ y' → U (k y')) , pr₂ (pr₂ H) U oU , kyU ,
                               (λ (y' , m') u → UW (k y' , _) u))
     (oW (k y , _) n)

\end{code}

Regularity, T₀ and local openness are invariant under homeomorphisms.

\begin{code}

module _ {𝓧 𝓨 𝓤 : Universe} {X : 𝓧 ̇ } {Y : 𝓨 ̇ }
         (T : Topology X 𝓤) (T' : Topology Y 𝓤)
         (h : X → Y) (H : is-homeomorphism T T' h)
       where

 private
  module T = Topology T
  module T' = Topology T'
  e = pr₁ H
  k = inverse h e
  ε : (y : Y) → h (k y) ＝ y
  ε = inverses-are-sections h e
  c : is-continuous T T' h
  c = pr₁ (pr₂ H)
  c' : is-continuous T' T k
  c' = pr₂ (pr₂ H)

 regularity-is-invariant : is-regular T → is-regular T'
 regularity-is-invariant r U oU y yU =
  ∥∥-functor
   (λ (V , G , oV , oG , kyV , d , cover) →
     (λ y' → V (k y')) , (λ y' → G (k y')) , c' V oV , c' G oG , kyV ,
     (λ y' m n → d (k y') m n) ,
     (λ y' → ∥∥-functor (cases inl (λ m → inr (transport (_∈ U) (ε y') m)))
              (cover (k y'))))
   (r (λ x → U (h x)) (c U oU) (k y) (transport (_∈ U) ((ε y)⁻¹) yU))

 T₀-is-invariant : is-T₀ T → is-T₀ T'
 T₀-is-invariant t y y' ν =
  ∥∥-functor
   (cases (λ s → inl
     (∥∥-functor (λ (U , oU , m , n) → (λ z → U (k z)) , c' U oU , m , n) s))
          (λ s → inr (∥∥-functor
            (λ (U , oU , m , n) → (λ z → U (k z)) , c' U oU , m , n) s)))
   (t (k y) (k y') (λ p → ν ((ε y)⁻¹ ∙ ap h p ∙ ε y')))

 local-openness-is-invariant : has-local-openness T → has-local-openness T'
 local-openness-is-invariant l A a =
  T'.openness-is-extensional (λ y → A (h (k y))) A
   (λ y m → transport (_∈ A) (ε y) m)
   (λ y m → transport (_∈ A) ((ε y)⁻¹) m)
   (c' (λ x → A (h x))
     (l (λ x → A (h x))
       (λ x m →
         ∥∥-functor (λ (U , oU , hxU , UA) → (λ x' → U (h x')) , c U oU , hxU ,
                                              (λ x' → UA (h x')))
                  (a (h x) m))))

\end{code}
