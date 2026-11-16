Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026 (local time). Orbifold gate H9 of Fable's
roadmap [1], following Fable's corrected guidance [2] and GPT-6
Astra's audits [3].

Ordinary topology
-----------------

The topological notions of the statement layer [1, Section 4, layer
L7; 2, Section 4 B and D; 3, Sections 1 and 4]:

  Topology X 𝓤 : opens are 𝓤-valued subsets of X; the whole space is
  open, binary intersections of opens are open, unions of opens
  indexed by any type in 𝓤 (propositions included) are open, and
  openness respects pointwise equivalence of subsets (so that no
  propositional extensionality is needed to change an open subset
  along a pointwise logical equivalence);

  has-local-openness, based-topologies-have-local-openness : a subset
  each of whose points has an open neighbourhood inside it is open. For
  a topology with a basis indexed by a type in 𝓤₀ (for example ℕ) and
  a carrier in 𝓤, this follows by taking the union of the basic opens
  contained in the subset; the subspace and product topologies have it
  directly;

  is-regular, is-T₀, is-regular-Hausdorff, is-Hausdorff : Myers's
  Definition 5.1.1 [4, p. 42], with "there is" and "either … or" read
  as truncated existence and disjunction;

  regular-Hausdorff-spaces-are-Hausdorff : Myers's Lemma 5.1.2;

  opens-of-regular-spaces-are-infinitesimally-stable : Myers's Lemma
  5.1.3: in a regular space, if x ∈ U open and y ≈ x, then y ∈ U;

  opens-of-regular-spaces-are-Penon-open : Myers's Lemma 6.2.7 [4,
  p. 57];

  subspace, product, is-continuous, is-homeomorphism, is-open-embedding,
  is-local-homeomorphism : the subspace topology, the binary product
  topology, and genuine homeomorphisms, open embeddings and local
  homeomorphisms [2, Section 1, item 2]: every point merely has open
  neighbourhoods U and V of x and of s(x) such that s restricts to a
  homeomorphism from U to V, for the subspace topologies.

Formal reading of "arbitrary unions". Unions are taken over families
indexed by types in 𝓤, the level of the opens. Locality of openness is
not part of the definition: predicatively it is stronger than closure
under such unions, because the union of all opens contained in a
subset would be indexed one universe up. Where it is needed (that an
open subset of an open subspace is open in the whole space,
open-subspaces-have-open-images, used to refine charts to basic opens)
it is a hypothesis, which holds for topologies with a small basis
(based-topologies-have-local-openness, by GPT-6 Astra's argument [3])
and for the subspace and product topologies. The subspace and product
topologies are defined by local conditions, with no choice of
neighbourhoods [3, Section 1].

A typo in Definition 5.1.1(1): "an open neighborhood V of U" is read
"of x", as in the proofs of Lemmas 5.1.2 and 5.1.3 that follow it.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] Claude Fable 5.2. Orbifolds H9 and H10: follow-up to Astra's
    readiness audits, 13 November 2026 (UTC).
    references/F04-orbifolds-h9-h10-followup.md
[3] GPT-6 Astra. Fable H9 follow-up: route and interface audit, and
    the H9 readiness audit, 13 November 2026 (UTC).
    references/A15-h9-followup-audit.txt
[4] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module gist.Orbifolds.Topology
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import UF.Base
open import UF.Equiv
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import gist.Orbifolds.CoverFiniteness fe pt using (is-Penon-open)

\end{code}

Subsets.

\begin{code}

Subset : {𝓧 : Universe} → 𝓧 ̇ → (𝓤 : Universe) → 𝓧 ⊔ 𝓤 ⁺ ̇
Subset X 𝓤 = X → Ω 𝓤

module _ {𝓧 𝓤 : Universe} {X : 𝓧 ̇ } where

 _∈_ : X → Subset X 𝓤 → 𝓤 ̇
 x ∈ U = U x holds

 ∈-is-prop : (x : X) (U : Subset X 𝓤) → is-prop (x ∈ U)
 ∈-is-prop x U = holds-is-prop (U x)

 _⊆_ : Subset X 𝓤 → Subset X 𝓤 → 𝓧 ⊔ 𝓤 ̇
 U ⊆ V = (x : X) → x ∈ U → x ∈ V

 full : Subset X 𝓤
 full x = 𝟙 , 𝟙-is-prop

 _∩_ : Subset X 𝓤 → Subset X 𝓤 → Subset X 𝓤
 (U ∩ V) x = (x ∈ U × x ∈ V) , ×-is-prop (∈-is-prop x U) (∈-is-prop x V)

 ⋃ : {I : 𝓤 ̇ } → (I → Subset X 𝓤) → Subset X 𝓤
 ⋃ {I} U x = (∃ i ꞉ I , x ∈ U i) , ∃-is-prop

 infix 4 _∈_
 infix 4 _⊆_

\end{code}

Topologies.

\begin{code}

record Topology {𝓧 : Universe} (X : 𝓧 ̇ ) (𝓤 : Universe) : 𝓧 ⁺ ⊔ 𝓤 ⁺ ⁺ ̇ where
 field
  is-open : Subset X 𝓤 → 𝓧 ⊔ 𝓤 ⁺ ̇
  being-open-is-prop : (U : Subset X 𝓤) → is-prop (is-open U)
  openness-is-extensional : (A B : Subset X 𝓤) → A ⊆ B → B ⊆ A
                          → is-open A → is-open B
  full-is-open : is-open full
  ∩-is-open : (U V : Subset X 𝓤) → is-open U → is-open V → is-open (U ∩ V)
  ⋃-is-open : {I : 𝓤 ̇ } (U : I → Subset X 𝓤)
            → ((i : I) → is-open (U i)) → is-open (⋃ U)

has-local-openness : {𝓧 𝓤 : Universe} {X : 𝓧 ̇ } → Topology X 𝓤 → 𝓧 ⊔ 𝓤 ⁺ ̇
has-local-openness {𝓧} {𝓤} {X} T =
 (A : Subset X 𝓤)
 → ((x : X) → x ∈ A → ∃ U ꞉ Subset X 𝓤 , Topology.is-open T U × x ∈ U × U ⊆ A)
 → Topology.is-open T A

is-basis : {𝓧 𝓤 𝓘 : Universe} {X : 𝓧 ̇ } → Topology X 𝓤
         → {I : 𝓘 ̇ } → (I → Subset X 𝓤) → 𝓘 ⊔ 𝓧 ⊔ 𝓤 ⁺ ̇
is-basis {𝓧} {𝓤} {𝓘} {X} T {I} B =
 ((i : I) → Topology.is-open T (B i))
 × ((U : Subset X 𝓤) → Topology.is-open T U → (x : X) → x ∈ U
      → ∃ i ꞉ I , x ∈ B i × B i ⊆ U)

module _ {𝓧 𝓤 : Universe} {X : 𝓧 ̇ } (T : Topology X 𝓤) where

 open Topology T

\end{code}

Myers's Definition 5.1.1, and Lemmas 5.1.2, 5.1.3 and 6.2.7.

\begin{code}

 is-regular : 𝓧 ⊔ 𝓤 ⁺ ̇
 is-regular = (U : Subset X 𝓤) → is-open U → (x : X) → x ∈ U
            → ∃ V ꞉ Subset X 𝓤 , Σ G ꞉ Subset X 𝓤 ,
                 is-open V × is-open G × x ∈ V
               × ((y : X) → y ∈ G → y ∈ V → 𝟘 {𝓤₀})
               × ((y : X) → (y ∈ G) ∨ (y ∈ U))

 is-T₀ : 𝓧 ⊔ 𝓤 ⁺ ̇
 is-T₀ = (x y : X) → x ≠ y
       → (∃ U ꞉ Subset X 𝓤 , is-open U × x ∈ U × ¬ (y ∈ U))
       ∨ (∃ U ꞉ Subset X 𝓤 , is-open U × y ∈ U × ¬ (x ∈ U))

 is-regular-Hausdorff : 𝓧 ⊔ 𝓤 ⁺ ̇
 is-regular-Hausdorff = is-regular × is-T₀

 is-Hausdorff : 𝓧 ⊔ 𝓤 ⁺ ̇
 is-Hausdorff = (x y : X) → x ≠ y
              → ∃ U ꞉ Subset X 𝓤 , Σ V ꞉ Subset X 𝓤 ,
                   is-open U × is-open V × x ∈ U × y ∈ V
                 × ((z : X) → z ∈ U → z ∈ V → 𝟘 {𝓤₀})

 regular-Hausdorff-spaces-are-Hausdorff : is-regular-Hausdorff → is-Hausdorff
 regular-Hausdorff-spaces-are-Hausdorff (r , t) x y ν =
  ∥∥-rec ∃-is-prop (cases first second) (t x y ν)
  where
   first : (∃ U ꞉ Subset X 𝓤 , is-open U × x ∈ U × ¬ (y ∈ U))
         → ∃ U ꞉ Subset X 𝓤 , Σ V ꞉ Subset X 𝓤 ,
              is-open U × is-open V × x ∈ U × y ∈ V
            × ((z : X) → z ∈ U → z ∈ V → 𝟘 {𝓤₀})
   first = ∥∥-rec ∃-is-prop
            (λ (U , o , m , n) →
              ∥∥-functor
               (λ (V , G , oV , oG , xV , d , c) →
                 V , G , oV , oG , xV ,
                 ∥∥-rec (∈-is-prop y G) (cases id (λ q → 𝟘-elim (n q))) (c y) ,
                 (λ z zV zG → d z zG zV))
               (r U o x m))

   second : (∃ U ꞉ Subset X 𝓤 , is-open U × y ∈ U × ¬ (x ∈ U))
          → ∃ U ꞉ Subset X 𝓤 , Σ V ꞉ Subset X 𝓤 ,
               is-open U × is-open V × x ∈ U × y ∈ V
             × ((z : X) → z ∈ U → z ∈ V → 𝟘 {𝓤₀})
   second = ∥∥-rec ∃-is-prop
             (λ (U , o , m , n) →
               ∥∥-functor
                (λ (V , G , oV , oG , yV , d , c) →
                  G , V , oG , oV ,
                  ∥∥-rec (∈-is-prop x G) (cases id (λ q → 𝟘-elim (n q))) (c x) ,
                  yV , d)
                (r U o y m))

 opens-of-regular-spaces-are-infinitesimally-stable
  : is-regular
  → (U : Subset X 𝓤) → is-open U
  → (x y : X) → x ∈ U → ¬¬ (y ＝ x) → y ∈ U
 opens-of-regular-spaces-are-infinitesimally-stable r U o x y m ν =
  ∥∥-rec (∈-is-prop y U)
   (λ (V , G , oV , oG , xV , d , c) →
     ∥∥-rec (∈-is-prop y U)
      (cases (λ yG → 𝟘-elim (ν (λ p → d x (transport (_∈ G) p yG) xV))) id)
      (c y))
   (r U o x m)

 opens-of-regular-spaces-are-Penon-open
  : is-regular
  → (U : Subset X 𝓤) → is-open U → is-Penon-open (λ x → x ∈ U)
 opens-of-regular-spaces-are-Penon-open r U o x m y =
  ∥∥-rec ∥∥-is-prop
   (λ (V , G , oV , oG , xV , d , c) →
     ∥∥-functor
      (cases (λ yG → inl (λ p → d y yG (transport (_∈ V) p xV))) inr)
      (c y))
   (r U o x m)

\end{code}

The subspace topology, and open subsets of open subspaces.

\begin{code}

 𝕊 : Subset X 𝓤 → 𝓧 ⊔ 𝓤 ̇
 𝕊 S = Σ x ꞉ X , x ∈ S

 subspace : (S : Subset X 𝓤) → Topology (𝕊 S) 𝓤
 subspace S = record
  { is-open = λ W → (w : 𝕊 S) → w ∈ W
                  → ∃ U ꞉ Subset X 𝓤 , is-open U × pr₁ w ∈ U
                                     × ((w' : 𝕊 S) → pr₁ w' ∈ U → w' ∈ W)
   ; being-open-is-prop = λ W → Π₂-is-prop fe (λ _ _ → ∃-is-prop)
   ; openness-is-extensional = λ A A' AA' A'A oA w m' →
                               ∥∥-functor
                                (λ (U , oU , wU , UA) →
                                  U , oU , wU , (λ w' n → AA' w' (UA w' n)))
                                (oA w (A'A w m'))
   ; full-is-open = λ w _ → ∣ full , full-is-open , ⋆ , (λ _ _ → ⋆) ∣
   ; ∩-is-open = λ W₁ W₂ o₁ o₂ w (m₁ , m₂) →
                 ∥∥-functor₂
                  (λ (U₁ , u₁ , n₁ , f₁) (U₂ , u₂ , n₂ , f₂) →
                    (U₁ ∩ U₂) , ∩-is-open U₁ U₂ u₁ u₂ , (n₁ , n₂) ,
                    (λ w' (k₁ , k₂) → f₁ w' k₁ , f₂ w' k₂))
                  (o₁ w m₁) (o₂ w m₂)
   ; ⋃-is-open = λ W o w m →
                 ∥∥-rec ∃-is-prop
                  (λ (i , n) →
                    ∥∥-functor
                     (λ (U , oU , wU , UW) →
                       U , oU , wU , (λ w' k → ∣ i , UW w' k ∣))
                     (o i w n))
                  m
   }

 subspaces-have-local-openness : (S : Subset X 𝓤)
                               → has-local-openness (subspace S)
 subspaces-have-local-openness S A l w m =
  ∥∥-rec ∃-is-prop
   (λ (W , oW , wW , WA) →
     ∥∥-functor
      (λ (U , oU , wU , UW) → U , oU , wU , (λ w' n → WA w' (UW w' n)))
      (oW w wW))
   (l w m)

 open-subspaces-have-open-images
  : has-local-openness T
  → (S : Subset X 𝓤) → is-open S
  → (W : Subset (𝕊 S) 𝓤) → Topology.is-open (subspace S) W
  → is-open (λ x → (Σ s ꞉ x ∈ S , (x , s) ∈ W) ,
                   Σ-is-prop (∈-is-prop x S) (λ s → ∈-is-prop (x , s) W))
 open-subspaces-have-open-images local-T S oS W oW =
  local-T _
   (λ x (s , m) →
     ∥∥-functor
      (λ (U , oU , xU , UW) →
        (U ∩ S) , ∩-is-open U S oU oS , (xU , s) ,
        (λ y (yU , yS) → yS , UW (y , yS) yU))
      (oW (x , s) m))

\end{code}

Continuity, homeomorphisms, open embeddings and local homeomorphisms.

\begin{code}

is-continuous : {𝓧 𝓨 𝓤 : Universe} {X : 𝓧 ̇ } {Y : 𝓨 ̇ }
              → Topology X 𝓤 → Topology Y 𝓤 → (X → Y) → 𝓧 ⊔ 𝓨 ⊔ 𝓤 ⁺ ̇
is-continuous {𝓧} {𝓨} {𝓤} {X} {Y} T T' f =
 (V : Subset Y 𝓤) → Topology.is-open T' V → Topology.is-open T (λ x → V (f x))

is-homeomorphism : {𝓧 𝓨 𝓤 : Universe} {X : 𝓧 ̇ } {Y : 𝓨 ̇ }
                 → Topology X 𝓤 → Topology Y 𝓤 → (X → Y) → 𝓧 ⊔ 𝓨 ⊔ 𝓤 ⁺ ̇
is-homeomorphism T T' f =
 Σ e ꞉ is-equiv f , is-continuous T T' f × is-continuous T' T (inverse f e)

module _ {𝓧 𝓨 𝓤 : Universe} {X : 𝓧 ̇ } {Y : 𝓨 ̇ }
         (T : Topology X 𝓤) (T' : Topology Y 𝓤)
       where

 private
  module T = Topology T
  module T' = Topology T'

 corestriction : (f : X → Y) (V : Subset Y 𝓤) → ((x : X) → f x ∈ V) → X → 𝕊 T' V
 corestriction f V m x = f x , m x

 is-open-embedding : (X → Y) → 𝓧 ⊔ 𝓨 ⊔ 𝓤 ⁺ ̇
 is-open-embedding f =
  ∃ V ꞉ Subset Y 𝓤 , Σ m ꞉ ((x : X) → f x ∈ V) ,
     T'.is-open V × is-homeomorphism T (subspace T' V) (corestriction f V m)

 restriction : (s : X → Y) (U : Subset X 𝓤) (V : Subset Y 𝓤)
             → ((u : X) → u ∈ U → s u ∈ V) → 𝕊 T U → 𝕊 T' V
 restriction s U V m (u , p) = s u , m u p

 is-local-homeomorphism : (X → Y) → 𝓧 ⊔ 𝓨 ⊔ 𝓤 ⁺ ̇
 is-local-homeomorphism s =
  (x : X) → ∃ U ꞉ Subset X 𝓤 , Σ V ꞉ Subset Y 𝓤 ,
              Σ m ꞉ ((u : X) → u ∈ U → s u ∈ V) ,
                 T.is-open U × T'.is-open V × x ∈ U × s x ∈ V
               × is-homeomorphism (subspace T U) (subspace T' V)
                  (restriction s U V m)

\end{code}

The binary product topology.

\begin{code}

product : {𝓧 𝓨 𝓤 : Universe} {X : 𝓧 ̇ } {Y : 𝓨 ̇ }
        → Topology X 𝓤 → Topology Y 𝓤 → Topology (X × Y) 𝓤
product {𝓧} {𝓨} {𝓤} {X} {Y} T T' = record
 { is-open = λ W → (z : X × Y) → z ∈ W
                 → ∃ U ꞉ Subset X 𝓤 , Σ V ꞉ Subset Y 𝓤 ,
                      T.is-open U × T'.is-open V × pr₁ z ∈ U × pr₂ z ∈ V
                    × ((x : X) (y : Y) → x ∈ U → y ∈ V → (x , y) ∈ W)
  ; being-open-is-prop = λ W → Π₂-is-prop fe (λ _ _ → ∃-is-prop)
  ; openness-is-extensional = λ A A' AA' A'A oA z m' →
                              ∥∥-functor
                               (λ (U , V , u , v , a , b , f) →
                                 U , V , u , v , a , b ,
                                  (λ x y p q → AA' (x , y) (f x y p q)))
                               (oA z (A'A z m'))
  ; full-is-open =
   λ z _ → ∣ full , full , T.full-is-open , T'.full-is-open , ⋆ , ⋆ ,
                             (λ _ _ _ _ → ⋆) ∣
  ; ∩-is-open = λ W₁ W₂ o₁ o₂ z (m₁ , m₂) →
                ∥∥-functor₂
                 (λ (U₁ , V₁ , u₁ , v₁ , a₁ , b₁ , f₁)
                   (U₂ , V₂ , u₂ , v₂ , a₂ , b₂ , f₂) →
                   (U₁ ∩ U₂) , (V₁ ∩ V₂) , T.∩-is-open U₁ U₂ u₁ u₂ ,
                    T'.∩-is-open V₁ V₂ v₁ v₂ ,
                   (a₁ , a₂) , (b₁ , b₂) ,
                   (λ x y (p₁ , p₂) (q₁ , q₂) → f₁ x y p₁ q₁ , f₂ x y p₂ q₂))
                 (o₁ z m₁) (o₂ z m₂)
  ; ⋃-is-open = λ W o z m →
                ∥∥-rec ∃-is-prop
                 (λ (i , n) →
                   ∥∥-functor
                    (λ (U , V , u , v , a , b , f) →
                      U , V , u , v , a , b , (λ x y p q → ∣ i , f x y p q ∣))
                    (o i z n))
                 m
  }
 where
  module T = Topology T
  module T' = Topology T'

\end{code}

Topologies with a basis indexed by a type in 𝓤₀, on a carrier in 𝓤,
have local openness: the union of the basic opens contained in a
locally open subset is open, and has the same points [3].

\begin{code}

based-topologies-have-local-openness
 : {𝓤 : Universe} {X : 𝓤 ̇ } (T : Topology X 𝓤)
   {I : 𝓤₀ ̇ } (B : I → Subset X 𝓤)
 → is-basis T B → has-local-openness T
based-topologies-have-local-openness {𝓤} {X} T {I} B (oB , b) A l =
 Topology.openness-is-extensional T C A C⊆A A⊆C
  (Topology.⋃-is-open T (λ (j : Basic-in-A) → B (pr₁ j)) (λ j → oB (pr₁ j)))
 where
  Basic-in-A : 𝓤 ̇
  Basic-in-A = Σ i ꞉ I , B i ⊆ A

  C : Subset X 𝓤
  C = ⋃ (λ (j : Basic-in-A) → B (pr₁ j))

  C⊆A : C ⊆ A
  C⊆A x = ∥∥-rec (∈-is-prop x A) (λ ((i , h) , m) → h x m)

  A⊆C : A ⊆ C
  A⊆C x a =
   ∥∥-rec ∃-is-prop
    (λ (U , oU , xU , UA) →
      ∥∥-functor
       (λ (i , xBi , BiU) → (i , (λ y yB → UA y (BiU y yB))) , xBi)
       (b U oU x xU))
    (l x a)

products-have-local-openness
 : {𝓧 𝓨 𝓤 : Universe} {X : 𝓧 ̇ } {Y : 𝓨 ̇ }
   (T : Topology X 𝓤) (T' : Topology Y 𝓤)
 → has-local-openness (product T T')
products-have-local-openness T T' A l z m =
 ∥∥-rec ∃-is-prop
  (λ (W , oW , zW , WA) →
    ∥∥-functor
     (λ (U , V , u , v , a , b , f) →
       U , V , u , v , a , b , (λ x y p q → WA (x , y) (f x y p q)))
     (oW z zW))
  (l z m)

\end{code}

