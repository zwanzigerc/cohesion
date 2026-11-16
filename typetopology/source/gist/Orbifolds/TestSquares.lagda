Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. Orbifold gate H2 of Fable's roadmap [2].

Test squares and local types
----------------------------

Myers [1, Definitions 4.2.10–4.2.12] calls a type X microlinear if,
as the roadmap [2, Section 3.4] and Astra's note [3, Section 4] put
it, for every infinitesimal R-pushout, a commuting square

      V₁ ──v₁₂──→ V₂
      │            │
     v₁₃          v₂₄
      ↓            ↓
      V₃ ──v₃₄──→ V₄

of infinitesimal varieties, the canonical map

      X^V₄ → X^V₂ ×_(X^V₁) X^V₃

is an equivalence. This module is about one such square, of arbitrary
types: a test square. Following [2, Section 3.4], X is σ-local if the
map above is an equivalence. Which squares count (the infinitesimal
R-pushouts) is fixed in gate H8; until then everything is stated for
an arbitrary square, or, in AbstractOrbifolds, an arbitrary family of
squares.

Formal reading. The pullback X^V₂ ×_(X^V₁) X^V₃ is formed with
pointwise identifications, a ∘ v₁₂ ∼ b ∘ v₁₃, as in the cones of
TypeTopology's UF.Pullback; the module calls it Cocone X, and the
canonical map is gap X. The lemma local-iff-strictly-local shows that
nothing changes if the pullback is formed with identifications of
functions, a ∘ v₁₂ ＝ b ∘ v₁₃ (TypeTopology's pullback), and the
commutation of the square is turned into one identification by
function extensionality. The roadmap's test squares are pointed; the
points enter only in Lemma G (gate H4), so they are not part of the
record here, and everything below holds for unpointed squares.

What is proved. Local types are closed under

  - equivalence (local-types-are-closed-under-equivalence),
  - Σ over a local base of a local family (Σ-is-local), with the
    converse (local-family-from-Σ),
  - the unit type and binary products,
  - pullbacks (pullbacks-of-local-types-are-local), and
  - inertia, (x : X) × (x ＝ x) (inertia-of-local-types-is-local).

The pullback closure is the part of Myers's 5.0.1 that GPT-6 Astra
proves directly from the definition [3, Section 4], there by
"exponentials preserve pullbacks, and limits preserve equivalences".
Here the same fact is reached through families: a family P over Y is
local if its dependent version of the canonical map is an equivalence
along every map V₄ → Y. Pulling a family back along a map then
preserves locality by definition; the Σ-type of a local family over a
local type is local; and conversely. A pullback B ×_D C is the Σ-type
over B × C of the identity family of D pulled back along f × g, and
the identity family of a local type is local because its Σ-type is
equivalent to D. The inertia type is the identity family of X pulled
back along the diagonal.

Reuse. TypeTopology's UF.Pullback provides the pullback, and its
lemmas on Σ-types, pair-fun and equivalences do most of the work. The
library had no module on test squares. agda-unimath (commit 7551865)
has locality at a single map (types-local-at-maps) and dependent
cocones under spans, the analogue of Cocone-Over below, on a larger
infrastructure of its own; the direct proofs here are shorter than a
transcription, so nothing is transcribed.

[1] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.
[2] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Sections 3.4 and 3.8.
    references/F01-orbifolds-roadmap-rev2.md
[3] GPT-6 Astra. All of Myers Section 6.4 over the adopted five-item
    core, 11 November 2026, Sections 4–6.
    references/A01-section-6-4-over-the-core.txt

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt

module gist.Orbifolds.TestSquares (fe : Fun-Ext) where

open import UF.Base
open import UF.Embeddings using (ap-is-equiv)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PairFun
open import UF.Pullback
open import UF.Singleton-Properties using (Σ-is-singleton)
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties using (props-are-sets)

\end{code}

Two facts about equivalences that are used below.

\begin{code}

postcomposition-is-equiv : {A : 𝓦 ̇ } {X : 𝓤 ̇ } {Y : 𝓤' ̇ } (f : X → Y)
                         → is-equiv f
                         → is-equiv (λ (h : A → X) → f ∘ h)
postcomposition-is-equiv f e =
 qinvs-are-equivs _
  ((λ h → g ∘ h) ,
   (λ h → dfunext fe (λ a → inverses-are-retractions f e (h a))) ,
   (λ h → dfunext fe (λ a → inverses-are-sections f e (h a))))
 where
  g = inverse f e

pair-fun-equiv-gives-fiberwise-equiv
 : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {Y : 𝓦 ̇ } {B : Y → 𝓣 ̇ }
   (f : X → Y) (g : (x : X) → A x → B (f x))
 → is-equiv f
 → is-equiv (pair-fun f g)
 → (x : X) → is-equiv (g x)
pair-fun-equiv-gives-fiberwise-equiv {B = B} f g i j =
 NatΣ-equiv-gives-fiberwise-equiv g
  (≃-2-out-of-3-left
    (pair-fun-is-equiv {A = λ x → B (f x)} {B = B} f (λ x b → b) i
      (λ x → id-is-equiv (B (f x))))
    j)

\end{code}

Test squares, the canonical map, and local types.

\begin{code}

record Test-Square (𝓥 : Universe) : 𝓥 ⁺ ̇ where
 field
  V₁ V₂ V₃ V₄ : 𝓥 ̇
  v₁₂ : V₁ → V₂
  v₁₃ : V₁ → V₃
  v₂₄ : V₂ → V₄
  v₃₄ : V₃ → V₄
  square : v₂₄ ∘ v₁₂ ∼ v₃₄ ∘ v₁₃

module _ {𝓥 : Universe} (σ : Test-Square 𝓥) where

 open Test-Square σ

 Cocone : 𝓤 ̇ → 𝓥 ⊔ 𝓤 ̇
 Cocone X = Σ a ꞉ (V₂ → X) , Σ b ꞉ (V₃ → X) , a ∘ v₁₂ ∼ b ∘ v₁₃

 gap : (X : 𝓤 ̇ ) → (V₄ → X) → Cocone X
 gap X h = h ∘ v₂₄ , h ∘ v₃₄ , (λ z → ap h (square z))

 is-local : 𝓤 ̇ → 𝓥 ⊔ 𝓤 ̇
 is-local X = is-equiv (gap X)

\end{code}

The same with the pullback of TypeTopology, whose third component is
an identification of functions.

\begin{code}

 Strict-Cocone : 𝓤 ̇ → 𝓥 ⊔ 𝓤 ̇
 Strict-Cocone X = pullback.pullback (λ (a : V₂ → X) → a ∘ v₁₂)
                                     (λ (b : V₃ → X) → b ∘ v₁₃)

 strict-gap : (X : 𝓤 ̇ ) → (V₄ → X) → Strict-Cocone X
 strict-gap X h = (h ∘ v₂₄ , h ∘ v₃₄) , ap (λ k → h ∘ k) (dfunext fe square)

 local-iff-strictly-local : (X : 𝓤 ̇ ) → is-local X ↔ is-equiv (strict-gap X)
 local-iff-strictly-local X = (λ i → equiv-closed-under-∼ _ _
                                       (∘-is-equiv i strictify-is-equiv)
                                       (λ h → strictify-gap h ⁻¹)) ,
                              (λ i → ≃-2-out-of-3-left strictify-is-equiv
                                       (equiv-closed-under-∼ _ _ i
                                         strictify-gap))
  where
   strictify : Cocone X → Strict-Cocone X
   strictify (a , b , H) = (a , b) , dfunext fe H

   strictify-is-equiv : is-equiv strictify
   strictify-is-equiv =
    qinvs-are-equivs strictify
     ((λ ((a , b) , p) → a , b , happly p) ,
      (λ (a , b , H) → ap (λ - → a , b , -) (happly-funext fe _ _ H)) ,
      (λ ((a , b) , p) → ap (λ - → (a , b) , -) (funext-happly fe _ _ p)))

   ap-postcomposition : {k k' : V₁ → V₄} (h : V₄ → X) (p : k ＝ k')
                      → ap (λ k → h ∘ k) p
                      ＝ dfunext fe (λ z → ap h (happly p z))
   ap-postcomposition {k} h refl = (dfunext-refl fe (h ∘ k))⁻¹

   strictify-gap : strictify ∘ gap X ∼ strict-gap X
   strictify-gap h =
    ap (λ - → (h ∘ v₂₄ , h ∘ v₃₄) , -)
     (dfunext fe (λ z → ap h (square z))                         ＝⟨ I ⟩
      dfunext fe (λ z → ap h (happly (dfunext fe square) z))     ＝⟨ II ⟩
      ap (λ k → h ∘ k) (dfunext fe square)                       ∎)
    where
     I  = ap (λ - → dfunext fe (λ z → ap h (- z)))
             ((happly-funext fe _ _ square)⁻¹)
     II = (ap-postcomposition h (dfunext fe square))⁻¹

\end{code}

Local families. A family Q over V₄ has a dependent version of the
canonical map, and a family P over any type Y is local if this map is
an equivalence for P ∘ k, for every k : V₄ → Y. Pulling a local family
back along any map gives a local family, by definition.

\begin{code}

 Dependent-Cocone : (Q : V₄ → 𝓦 ̇ ) → 𝓥 ⊔ 𝓦 ̇
 Dependent-Cocone Q =
  Σ a ꞉ ((x : V₂) → Q (v₂₄ x)) ,
  Σ b ꞉ ((y : V₃) → Q (v₃₄ y)) ,
  ((z : V₁) → transport Q (square z) (a (v₁₂ z)) ＝ b (v₁₃ z))

 dependent-gap : (Q : V₄ → 𝓦 ̇ ) → ((w : V₄) → Q w) → Dependent-Cocone Q
 dependent-gap Q s = s ∘ v₂₄ , s ∘ v₃₄ , (λ z → apd s (square z))

 is-local-family : {Y : 𝓤 ̇ } → (Y → 𝓦 ̇ ) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 is-local-family {Y = Y} P = (k : V₄ → Y) → is-equiv (dependent-gap (P ∘ k))

 local-families-are-closed-under-reindexing
  : {Y : 𝓤 ̇ } {Y' : 𝓤' ̇ } (P : Y → 𝓦 ̇ ) (f : Y' → Y)
  → is-local-family P
  → is-local-family (P ∘ f)
 local-families-are-closed-under-reindexing P f i k = i (f ∘ k)

\end{code}

Cocones in a Σ-type are cocones in the base with cocones in the
family over them.

\begin{code}

 module _ {Y : 𝓤 ̇ } (P : Y → 𝓦 ̇ ) where

  Cocone-Over : Cocone Y → 𝓥 ⊔ 𝓦 ̇
  Cocone-Over (a , b , H) =
   Σ a' ꞉ ((x : V₂) → P (a x)) ,
   Σ b' ꞉ ((y : V₃) → P (b y)) ,
   ((z : V₁) → transport P (H z) (a' (v₁₂ z)) ＝ b' (v₁₃ z))

  private
   glue : (a : V₂ → Y) (b : V₃ → Y)
          (a' : (x : V₂) → P (a x)) (b' : (y : V₃) → P (b y))
        → ((z : V₁) → Σ p ꞉ a (v₁₂ z) ＝ b (v₁₃ z) ,
                          transport P p (a' (v₁₂ z)) ＝ b' (v₁₃ z))
        → Σ c ꞉ Cocone Y , Cocone-Over c
   glue a b a' b' K =
    (a , b , (λ z → pr₁ (K z))) , (a' , b' , (λ z → pr₂ (K z)))

  split : Cocone (Σ P) → Σ c ꞉ Cocone Y , Cocone-Over c
  split (a , b , H) = glue (pr₁ ∘ a) (pr₁ ∘ b) (pr₂ ∘ a) (pr₂ ∘ b)
                           (λ z → from-Σ-＝ (H z))

  join : (Σ c ꞉ Cocone Y , Cocone-Over c) → Cocone (Σ P)
  join ((a , b , H) , (a' , b' , H')) =
   (λ x → a x , a' x) , (λ y → b y , b' y) , (λ z → to-Σ-＝ (H z , H' z))

  split-is-equiv : is-equiv split
  split-is-equiv = qinvs-are-equivs split (join , η , ε)
   where
    η : join ∘ split ∼ id
    η (a , b , H) = ap (λ - → a , b , -) (dfunext fe (λ z → tofrom-Σ-＝ (H z)))

    ε : split ∘ join ∼ id
    ε ((a , b , H) , (a' , b' , H')) =
     ap (glue a b a' b') (dfunext fe (λ z → fromto-Σ-＝ (H z , H' z)))

\end{code}

The canonical map of Σ P, read through split, is the canonical map of
Y paired with the dependent canonical maps of the family. The family
P ∘ k transports along square z, the cocone over gap Y k along
ap k (square z); adjust k converts.

\begin{code}

  adjust : (k : V₄ → Y) → Dependent-Cocone (P ∘ k) → Cocone-Over (gap Y k)
  adjust k (a' , b' , H') =
   a' , b' , (λ z → (transport-ap P k (square z))⁻¹ ∙ H' z)

  adjust-is-equiv : (k : V₄ → Y) → is-equiv (adjust k)
  adjust-is-equiv k = qinvs-are-equivs (adjust k) (back , η , ε)
   where
    back : Cocone-Over (gap Y k) → Dependent-Cocone (P ∘ k)
    back (a' , b' , H') = a' , b' , (λ z → transport-ap P k (square z) ∙ H' z)

    cancel : {A : 𝓦 ̇ } {t u w : A} (p : t ＝ u) (q : t ＝ w)
           → p ∙ (p ⁻¹ ∙ q) ＝ q
    cancel refl refl = refl

    cancel' : {A : 𝓦 ̇ } {t u w : A} (p : t ＝ u) (q : u ＝ w)
            → p ⁻¹ ∙ (p ∙ q) ＝ q
    cancel' refl refl = refl

    η : back ∘ adjust k ∼ id
    η (a' , b' , H') =
     ap (λ - → a' , b' , -)
        (dfunext fe (λ z → cancel (transport-ap P k (square z)) (H' z)))

    ε : adjust k ∘ back ∼ id
    ε (a' , b' , H') =
     ap (λ - → a' , b' , -)
        (dfunext fe (λ z → cancel' (transport-ap P k (square z)) (H' z)))

  total-gap : (Σ k ꞉ (V₄ → Y) , ((w : V₄) → P (k w)))
            → Σ c ꞉ Cocone Y , Cocone-Over c
  total-gap = pair-fun (gap Y) (λ k → adjust k ∘ dependent-gap (P ∘ k))

  unpair : (V₄ → Σ P) → Σ k ꞉ (V₄ → Y) , ((w : V₄) → P (k w))
  unpair h = pr₁ ∘ h , pr₂ ∘ h

  unpair-is-equiv : is-equiv unpair
  unpair-is-equiv = qinvs-are-equivs unpair
                     ((λ (k , s) w → k w , s w) , (λ h → refl) ,
                       (λ (k , s) → refl))

  from-Σ-＝-ap : {W : 𝓣 ̇ } (h : W → Σ P) {w w' : W} (p : w ＝ w')
               → from-Σ-＝ (ap h p)
               ＝ (ap (pr₁ ∘ h) p ,
                   ((transport-ap P (pr₁ ∘ h) p)⁻¹ ∙ apd (pr₂ ∘ h) p))
  from-Σ-＝-ap h refl = refl

  gap-of-Σ : split ∘ gap (Σ P) ∼ total-gap ∘ unpair
  gap-of-Σ h = ap (glue (pr₁ ∘ h ∘ v₂₄) (pr₁ ∘ h ∘ v₃₄)
                        (pr₂ ∘ h ∘ v₂₄) (pr₂ ∘ h ∘ v₃₄))
                  (dfunext fe (λ z → from-Σ-＝-ap h (square z)))

  Σ-is-local : is-local Y → is-local-family P → is-local (Σ P)
  Σ-is-local i j =
   ≃-2-out-of-3-left split-is-equiv
    (equiv-closed-under-∼ (total-gap ∘ unpair) (split ∘ gap (Σ P))
      (∘-is-equiv unpair-is-equiv total-gap-is-equiv)
      gap-of-Σ)
   where
    total-gap-is-equiv : is-equiv total-gap
    total-gap-is-equiv =
     pair-fun-is-equiv (gap Y) (λ k → adjust k ∘ dependent-gap (P ∘ k)) i
      (λ k → ∘-is-equiv (j k) (adjust-is-equiv k))

  local-family-from-Σ : is-local Y → is-local (Σ P) → is-local-family P
  local-family-from-Σ i j k =
   ≃-2-out-of-3-left (adjust-is-equiv k)
    (pair-fun-equiv-gives-fiberwise-equiv (gap Y)
      (λ k → adjust k ∘ dependent-gap (P ∘ k)) i
      (≃-2-out-of-3-right unpair-is-equiv
        (equiv-closed-under-∼ (split ∘ gap (Σ P)) (total-gap ∘ unpair)
          (∘-is-equiv j split-is-equiv)
          (λ h → (gap-of-Σ h)⁻¹)))
      k)

\end{code}

Closure under equivalence. Maps act on cocones, the canonical map is
natural, and an equivalence acts on cocones by an equivalence.

\begin{code}

 Cocone-map : {X : 𝓤 ̇ } {X' : 𝓤' ̇ } → (X → X') → Cocone X → Cocone X'
 Cocone-map f (a , b , H) = f ∘ a , f ∘ b , (λ z → ap f (H z))

 gap-is-natural : {X : 𝓤 ̇ } {X' : 𝓤' ̇ } (f : X → X') (h : V₄ → X)
                → Cocone-map f (gap X h) ＝ gap X' (f ∘ h)
 gap-is-natural f h = ap (λ - → f ∘ h ∘ v₂₄ , f ∘ h ∘ v₃₄ , -)
                         (dfunext fe (λ z → ap-ap h f (square z)))

 Cocone-map-is-equiv : {X : 𝓤 ̇ } {X' : 𝓤' ̇ } (f : X → X')
                     → is-equiv f
                     → is-equiv (Cocone-map f)
 Cocone-map-is-equiv {X = X} {X' = X'} f e =
  pair-fun-is-equiv
   {A = λ a → Σ b ꞉ (V₃ → X) , a ∘ v₁₂ ∼ b ∘ v₁₃}
   {B = λ a → Σ b ꞉ (V₃ → X') , a ∘ v₁₂ ∼ b ∘ v₁₃}
   (λ a → f ∘ a)
   (λ a → pair-fun (λ b → f ∘ b) (λ b H z → ap f (H z)))
   (postcomposition-is-equiv f e)
   (λ a → pair-fun-is-equiv
           {A = λ b → a ∘ v₁₂ ∼ b ∘ v₁₃}
           {B = λ b → f ∘ a ∘ v₁₂ ∼ b ∘ v₁₃}
           (λ b → f ∘ b) (λ b H z → ap f (H z))
           (postcomposition-is-equiv f e)
           (λ b → ⌜⌝-is-equiv (Π-cong fe fe (λ z → ap f , ap-is-equiv f e))))

 local-types-are-closed-under-equivalence : {X : 𝓤 ̇ } {X' : 𝓤' ̇ }
                                          → X ≃ X'
                                          → is-local X
                                          → is-local X'
 local-types-are-closed-under-equivalence {X = X} {X' = X'} (f , e) i =
  ≃-2-out-of-3-right (postcomposition-is-equiv f e)
   (equiv-closed-under-∼ (Cocone-map f ∘ gap X) (gap X' ∘ (λ h → f ∘ h))
     (∘-is-equiv i (Cocone-map-is-equiv f e))
     (λ h → (gap-is-natural f h)⁻¹))

\end{code}

The unit type, products, the identity family, pullbacks and inertia.

\begin{code}

 𝟙-is-local : is-local (𝟙 {𝓤})
 𝟙-is-local = maps-of-singletons-are-equivs (gap 𝟙)
               (Π-is-singleton fe (λ _ → 𝟙-is-singleton))
               (Σ-is-singleton (Π-is-singleton fe (λ _ → 𝟙-is-singleton))
                 (λ a →
                   Σ-is-singleton (Π-is-singleton fe (λ _ → 𝟙-is-singleton))
                   (λ b → Π-is-singleton fe
                           (λ z → pointed-props-are-singletons
                                   (𝟙-is-prop (a (v₁₂ z)) (b (v₁₃ z)))
                                   (props-are-sets 𝟙-is-prop)))))

 ×-is-local : {X : 𝓤 ̇ } {X' : 𝓤' ̇ } → is-local X → is-local X'
            → is-local (X × X')
 ×-is-local {X = X} {X' = X'} i j =
  Σ-is-local (λ (_ : X) → X') i
   (local-families-are-closed-under-reindexing (λ (_ : 𝟙 {𝓤₀}) → X') unique-to-𝟙
     (local-family-from-Σ (λ (_ : 𝟙 {𝓤₀}) → X') 𝟙-is-local
       (local-types-are-closed-under-equivalence (≃-sym 𝟙-lneutral) j)))

 identity-family-is-local : {X : 𝓤 ̇ }
                          → is-local X
                          → is-local-family (λ (z : X × X) → pr₁ z ＝ pr₂ z)
 identity-family-is-local {X = X} i =
  local-family-from-Σ (λ (z : X × X) → pr₁ z ＝ pr₂ z) (×-is-local i i)
   (local-types-are-closed-under-equivalence (≃-sym φ) i)
  where
   φ : (Σ z ꞉ X × X , pr₁ z ＝ pr₂ z) ≃ X
   φ = qinveq (λ ((x , _) , _) → x)
              ((λ x → (x , x) , refl) ,
               (λ { ((x , _) , refl) → refl }) ,
               (λ x → refl))

 pullbacks-of-local-types-are-local
  : {B : 𝓤 ̇ } {C : 𝓤' ̇ } {D : 𝓦 ̇ } (f : B → D) (g : C → D)
  → is-local B
  → is-local C
  → is-local D
  → is-local (pullback.pullback f g)
 pullbacks-of-local-types-are-local {B = B} {C = C} {D = D} f g i j k =
  Σ-is-local (λ ((b , c) : B × C) → f b ＝ g c) (×-is-local i j)
   (local-families-are-closed-under-reindexing
     (λ (z : D × D) → pr₁ z ＝ pr₂ z) (λ ((b , c) : B × C) → f b , g c)
     (identity-family-is-local k))

 inertia-of-local-types-is-local : {X : 𝓤 ̇ }
                                 → is-local X
                                 → is-local (Σ x ꞉ X , x ＝ x)
 inertia-of-local-types-is-local {X = X} i =
  Σ-is-local (λ (x : X) → x ＝ x) i
   (local-families-are-closed-under-reindexing
     (λ (z : X × X) → pr₁ z ＝ pr₂ z) (λ x → x , x)
     (identity-family-is-local i))

\end{code}
