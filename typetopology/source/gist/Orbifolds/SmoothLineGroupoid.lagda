Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time); the dual numbers and the end
of the proof of anchor-is-not-DP-proper moved to
gist.Orbifolds.DualNumbers later that day, in the consolidation after
the final audits; the anchor's cover-properness for set-indexed covers
added in its third part [5]. Orbifold gate H10 of Fable's roadmap [1,
Section 3.10]: the target T5a.

T5a: the unit groupoid of the smooth line
-----------------------------------------

The target T5a [1, Section 3.10; 2, item 4; 3]: the unit pregroupoid of
the smooth line R satisfies the hypotheses of T1, but its anchor, the
diagonal, is not Dubuc–Penon proper.

The unit pregroupoid has objects R and morphisms x ＝ y; its arrows form
Σ x y , x ＝ y, and the source map is an equivalence with R, with
inverse x ↦ (x , x , refl). Everything is transported along it.

  _<ᶜ_ : the order defined by the ring alone [3, item 4]: x <ᶜ y when
  y − x is merely the square of an invertible element. It mentions only
  the crisp ring, so it is crisp. ring-order-agrees: it is the order of
  Postulate O, by O, K and Exp; one direction takes the square root
  exp(log(d)/2) of a positive d, so exp and log are used here;

  rational-arrow-basis : the crisp basis of the arrows. The n-th member
  is cut out by the division-free inequalities
    k − l <ᶜ (m + 1)·x   and   (m' + 1)·x <ᶜ k' − l'
  for the two endpoints (k , l , m) and (k' , l' , m') that the pairing
  enumeration assigns to n [3, items 5 and 6]; x is the source of the
  arrow. Its formula is that of SmoothLineManifold's endpoints, written
  again outside the ordinary telescope of O so that it is crisp.
  raw-intervals-agree: pointwise, it is the ordinary rational interval
  of SmoothLineManifold, by O, K and Exp;

  the hypotheses of T1 for the unit pregroupoid, one export each: the
  objects form the ordinary manifold smooth-line-is-an-ordinary-manifold
  of SmoothLineManifold; the arrows, with arrow-topology (transported
  along the source map) and the crisp basis rational-arrow-basis,
  satisfy arrow-manifold-laws, the laws of an ordinary 1-manifold (the
  openness, basis property and chart domains of the basis by
  extensionality from the ordinary intervals); the source map is a
  genuine local homeomorphism, source-is-a-local-homeomorphism (it is a
  homeomorphism); and anchor-is-cover-proper: at a point (x , y),
  choose a member V_i of the crisp cover containing the identity arrow
  of x, take W = {z | identity of z₁ in V_i} × R and the list [i];

  anchor-is-cover-proper-for-set-indices : the same for set-indexed
  covers, the condition of the memo (CoverProperness), by restriction;

  anchor-is-not-DP-proper : by Postulate K and the injectivity half of
  Postulate J for the fixed crisp algebra of dual numbers R[ε]/(ε²): the
  fibre of the anchor over (x , y) is the proposition x ＝ y; if the
  anchor were Dubuc–Penon proper, that proposition would be compact,
  hence decidable; then every nilsquare d would be 0, since d ≠ 0
  contradicts K; so (0 , 1) and (0 , 0) would have the same evaluation
  d ↦ a + b·d on the spectrum, and J would give 1 ＝ 0. These last two
  steps are nilsquares-cannot-all-vanish of gist.Orbifolds.DualNumbers,
  which also proves the corresponding step of T5b. The dual numbers are
  defined there too; dual-numbers, dual-number-evaluation and
  Postulate-J-for-dual-numbers are typed aliases of those definitions,
  with the parameters of this module.

  theorem-T5a : both parts, the first as the conclusion of T1 for the
  unit pregroupoid, under the ambient hypotheses of T1. For the reading
  of "literal" and of ℑ, see gist.Orbifolds.index, the paragraph on
  the scope of the statements.

Dubuc–Penon properness is the predicate of the module DubucPenon at the
universe 𝓤₀ of R, the instance that T5b, stated for every universe,
takes at 𝓤₀.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] GPT-6 Astra. Final H9 universe guidance; original T1/T5 release,
    13 November 2026 (UTC).
    references/A29-h9-t1-t5-release.txt
[3] GPT-6 Astra. Focused manifold crispness release, 13 November 2026
    (UTC), with Claude Fable 5.2's reply on crispness, Section 2.3.
    references/A28-manifold-crispness-release.txt
[4] GPT-6 Astra. H10 T5a implementation preflight, 13 November 2026
    (UTC).
    references/A23-t5a-preflight.txt
[5] GPT-6 Astra. Consolidation implementation, third release
    (OPUS-CONSOLIDATION-RELEASE-03), 13 November 2026, with the review
    COVER-INDEX-PLAN-REVIEW of the same day, and Claude Fable 5.2's
    plan of 13 November 2026
    (references/F20-cover-index-plan.md, SHA-256
    10fb9683…). The adapter is that of its scratch check
    SmoothLineGroupoidSetIndexCheck.lagda (SHA-256 a92ff7cf…); the rest
    of that copy predates the consolidation and is not used.
    references/A33-consolidation-release-03.txt
    references/A34-cover-index-plan-review.txt

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Univalence
open import Modal.Subuniverse
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.SmoothLineGroupoid
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ 𝓡 : Commutative-Ring)
       where

open import Fin.Type
open import UF.Base
open import UF.Equiv
open import UF.ImageAndSurjection pt using (is-surjection)
open import UF.Sets
open import UF.Sets-Properties using (Σ-is-set)
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties using (props-are-sets)
open import UF.SubtypeClassifier
open import gist.CohesiveApartness.Flat using (Axiom-C1)
open import gist.Orbifolds.SmoothOrder
open import gist.Orbifolds.SmoothOrderAlgebra
open import gist.Orbifolds.MetricTopology
open import gist.Orbifolds.RationalPoints
open import gist.Orbifolds.Manifolds
open import gist.Orbifolds.SmoothLineManifold

open PropositionalTruncation pt
open smooth-line fe pt 𝓡
open smooth-order fe pt 𝓡
open smooth-order-algebra fe pt 𝓡
open rational-points fe pt 𝓡
open ordinary-manifolds fe pt 𝓡
open smooth-line-manifold fe pt 𝓡
open import gist.Orbifolds.Topology fe pt
open import gist.Orbifolds.Homeomorphisms fe pt
open import gist.Orbifolds.RezkCompletion fe pt {𝓤₀} {𝓤₀}
open import gist.Orbifolds.CoverFiniteness fe pt using (anchor)
open import gist.Orbifolds.CoverProperness fe pt
open import gist.Orbifolds.DubucPenon fe pt
open import gist.Orbifolds.Microlinearity fe pt 𝓡 {𝓤₁}
 using (ℑ-generator ; ℑ-generator-point)
open import gist.Orbifolds.MyersMicrolinearity fe pt 𝓡 {𝓤₁}
 using (literal-ℑ-generator ; literal-ℑ-generator-point ; is-literal-orbifold ;
        literal-nullifications-are-nullifications ; orbifolds-agree)
open import gist.Orbifolds.Nullification fe using (is-nullification)
open import gist.Orbifolds.OrdinaryEtaleGroupoids fe pt 𝓡 {𝓤₀}
 using (theorem-T1 ; ○-preserves-crisp-pullbacks)
import gist.Orbifolds.DualNumbers

private
 module DN = gist.Orbifolds.DualNumbers fe pt 𝓡

\end{code}

The order defined by the ring, and the crisp basis of rational
intervals.

\begin{code}

_<ᶜ_ : R → R → 𝓤₀ ̇
x <ᶜ y = ∥ Σ u ꞉ R , is-invertible u × (y +ᴿ (-ᴿ x) ＝ u ·ᴿ u) ∥

infix 4 _<ᶜ_

numerator denominator : Rational-Presentation → R
numerator (k , l , m) = ι k +ᴿ (-ᴿ ι l)
denominator (k , l , m) = ι m +ᴿ 1ᴿ

raw-endpoints : ℕ → Rational-Presentation × Rational-Presentation
raw-endpoints c = rational-presentation-of (pr₁ (unpair c)) ,
                  rational-presentation-of (pr₂ (unpair c))

raw-interval : ℕ → R → 𝓤₀ ̇
raw-interval c x =
   (numerator (pr₁ (raw-endpoints c)) <ᶜ denominator (pr₁ (raw-endpoints c))
    ·ᴿ x)
 ×
 (denominator (pr₂ (raw-endpoints c)) ·ᴿ x <ᶜ numerator (pr₂ (raw-endpoints c)))

raw-interval-is-prop : (c : ℕ) (x : R) → is-prop (raw-interval c x)
raw-interval-is-prop c x = ×-is-prop ∥∥-is-prop ∥∥-is-prop

\end{code}

The unit pregroupoid of R, its arrows, and the crisp basis of the
arrows.

\begin{code}

unit-pregroupoid : Pregroupoid
unit-pregroupoid = record
 { ob = R
  ; hom = λ x y → x ＝ y
  ; hom-is-set = λ x y → props-are-sets R-is-set
  ; idn = λ x → refl
  ; comp = λ g f → f ∙ g
  ; unit-left = λ f → R-is-set _ _
  ; unit-right = λ f → R-is-set _ _
  ; comp-assoc = λ h g f → R-is-set _ _
  ; inv = λ f → f ⁻¹
  ; inverse-left = λ f → R-is-set _ _
  ; inverse-right = λ f → R-is-set _ _
  }

Arrow : 𝓤₀ ̇
Arrow = arrows unit-pregroupoid

identity-arrow : R → Arrow
identity-arrow x = x , x , refl

identity-arrows-of-sources : (a : Arrow)
                           → identity-arrow (source unit-pregroupoid a) ＝ a
identity-arrows-of-sources (x , .x , refl) = refl

arrows-form-a-set : is-set Arrow
arrows-form-a-set =
 Σ-is-set R-is-set (λ x → Σ-is-set R-is-set (λ y → props-are-sets R-is-set))

rational-arrow-basis : ℕ → Subset Arrow 𝓤₀
rational-arrow-basis c a = raw-interval c (source unit-pregroupoid a) ,
                           raw-interval-is-prop c (source unit-pregroupoid a)

\end{code}

The dual numbers, and the injectivity half of Postulate J for them:
typed aliases of the definitions in gist.Orbifolds.DualNumbers.

\begin{code}

dual-numbers : Weil-Presentation
dual-numbers = DN.dual-numbers

dual-number-evaluation : R × R → (Spec dual-numbers → R)
dual-number-evaluation = DN.dual-number-evaluation

Postulate-J-for-dual-numbers : 𝓤₀ ̇
Postulate-J-for-dual-numbers = DN.Postulate-J-for-dual-numbers

\end{code}

Everything else is relative to Postulates O, Exp and K.

\begin{code}

module _ (O : Postulate-O) (Exp : Postulate-Exp O) (K : Postulate-K) where

 open Postulate-O O
 open Postulate-Exp Exp

 private
  translation : Translation-Law O
  translation = translation-law-from-Exp O Exp

 open order-lemmas O translation
 open order-algebra O translation

 private
  Eucl : (n : ℕ) → Topology (Fin n → R) 𝓤₀
  Eucl = Euclidean O translation K 𝓤₀

  T-R : Topology R 𝓤₀
  T-R = smooth-line-topology O translation K

\end{code}

The order defined by the ring is the order of O.

\begin{code}

 invertible-elements-are-nonzero : (u : R) → is-invertible u → u ≠ 0ᴿ
 invertible-elements-are-nonzero u (v , p) q =
  zero-is-not-one ((·-zero v)⁻¹ ∙ ap (v ·ᴿ_) (q ⁻¹) ∙ p)

 private
  two-inverse = positive-elements-are-invertible K (1ᴿ +ᴿ 1ᴿ) two-is-positive
  half = pr₁ two-inverse

  halves-add-up : half +ᴿ half ＝ 1ᴿ
  halves-add-up = (ap₂ _+ᴿ_ (·-unit half) (·-unit half))⁻¹
                ∙ (distributivity half 1ᴿ 1ᴿ)⁻¹ ∙ pr₂ two-inverse

 positive-elements-are-invertible-squares
  : (d : R) → 0ᴿ < d → Σ u ꞉ R , is-invertible u × (d ＝ u ·ᴿ u)
 positive-elements-are-invertible-squares d l =
  u , positive-elements-are-invertible K u (exp-is-positive t) , path
  where
   t = log d l ·ᴿ half
   u = exp t
   path : d ＝ u ·ᴿ u
   path = (exp-log d l)⁻¹
        ∙ ap exp ((·-unit (log d l))⁻¹ ∙ ap (log d l ·ᴿ_) (halves-add-up ⁻¹)
                  ∙ distributivity (log d l) half half)
        ∙ exp-is-homomorphism t t

 ring-order-agrees : (x y : R) → (x <ᶜ y) ↔ (x < y)
 ring-order-agrees x y =
  ∥∥-rec (<-is-prop-valued x y)
   (λ (u , i , p) → positive-difference x y
                     (transport (0ᴿ <_) (p ⁻¹)
                       (nonzero-squares-are-positive u
                         (invertible-elements-are-nonzero u i)))) ,
  (λ l → ∣ positive-elements-are-invertible-squares (y +ᴿ (-ᴿ x))
            (difference-is-positive x y l) ∣)

\end{code}

The division-free intervals are the ordinary rational intervals.

\begin{code}

 private
  scaled-below : (a x : R) (m : ℕ)
               → (a < (ι m +ᴿ 1ᴿ) ·ᴿ x) ↔ (a ·ᴿ w O translation K m < x)
  scaled-below a x m =
   (λ l → transport (a ·ᴿ v <_) back
            (products-with-positive-factor-preserve-order a (sm ·ᴿ x) v
              (w-is-positive O translation K m) l)) ,
   (λ l → transport₂ _<_ forth (·-comm x sm)
            (products-with-positive-factor-preserve-order (a ·ᴿ v) x sm
              (s-is-positive O translation K m) l))
   where
    sm = ι m +ᴿ 1ᴿ
    v = w O translation K m
    back : (sm ·ᴿ x) ·ᴿ v ＝ x
    back = ap (_·ᴿ v) (·-comm sm x) ∙ ·-assoc x sm v
         ∙ ap (x ·ᴿ_) (·-comm sm v ∙ w-is-inverse O translation K m) ∙ ·-unit x
    forth : (a ·ᴿ v) ·ᴿ sm ＝ a
    forth =
     ·-assoc a v sm ∙ ap (a ·ᴿ_) (w-is-inverse O translation K m) ∙ ·-unit a

  scaled-above : (b x : R) (m : ℕ)
               → ((ι m +ᴿ 1ᴿ) ·ᴿ x < b) ↔ (x < b ·ᴿ w O translation K m)
  scaled-above b x m =
   (λ l → transport (_< b ·ᴿ v) back
            (products-with-positive-factor-preserve-order (sm ·ᴿ x) b v
              (w-is-positive O translation K m) l)) ,
   (λ l → transport₂ _<_ (·-comm x sm) forth
            (products-with-positive-factor-preserve-order x (b ·ᴿ v) sm
              (s-is-positive O translation K m) l))
   where
    sm = ι m +ᴿ 1ᴿ
    v = w O translation K m
    back : (sm ·ᴿ x) ·ᴿ v ＝ x
    back = ap (_·ᴿ v) (·-comm sm x) ∙ ·-assoc x sm v
         ∙ ap (x ·ᴿ_) (·-comm sm v ∙ w-is-inverse O translation K m) ∙ ·-unit x
    forth : (b ·ᴿ v) ·ᴿ sm ＝ b
    forth =
     ·-assoc b v sm ∙ ap (b ·ᴿ_) (w-is-inverse O translation K m) ∙ ·-unit b

 raw-intervals-agree
  : (c : ℕ) (x : R)
  → raw-interval c x ↔ (x ∈ rational-interval O translation K c)
 raw-intervals-agree c x =
  (λ (r₁ , r₂) →
    lr-implication (scaled-below (numerator p) x (pr₂ (pr₂ p)))
     (lr-implication (ring-order-agrees _ _) r₁) ,
    lr-implication (scaled-above (numerator q) x (pr₂ (pr₂ q)))
     (lr-implication (ring-order-agrees _ _) r₂)) ,
  (λ (l₁ , l₂) →
    rl-implication (ring-order-agrees _ _)
     (rl-implication (scaled-below (numerator p) x (pr₂ (pr₂ p))) l₁) ,
    rl-implication (ring-order-agrees _ _)
     (rl-implication (scaled-above (numerator q) x (pr₂ (pr₂ q))) l₂))
  where
   p = pr₁ (raw-endpoints c)
   q = pr₂ (raw-endpoints c)

\end{code}

The topology of the arrows: transported along the identity arrows.

\begin{code}

 arrow-topology : Topology Arrow 𝓤₀
 arrow-topology = final-topology identity-arrow T-R

 private
  T-A = arrow-topology

  identity-arrow-is-equiv : is-equiv identity-arrow
  identity-arrow-is-equiv =
   qinvs-are-equivs identity-arrow
    (source unit-pregroupoid , (λ x → refl) , identity-arrows-of-sources)

 identity-arrow-is-homeomorphism : is-homeomorphism T-R T-A identity-arrow
 identity-arrow-is-homeomorphism =
  equivalences-are-homeomorphisms-onto-final-topologies T-R identity-arrow
   identity-arrow-is-equiv

 source-is-homeomorphism : is-homeomorphism T-A T-R (source unit-pregroupoid)
 source-is-homeomorphism =
  qinvs-are-equivs (source unit-pregroupoid)
   (identity-arrow , identity-arrows-of-sources , (λ x → refl)) ,
  (λ V oV → oV) ,
  (λ W oW → oW)

 source-is-a-local-homeomorphism
  : is-local-homeomorphism T-A T-R (source unit-pregroupoid)
 source-is-a-local-homeomorphism a =
  ∣ full , full , (λ _ _ → ⋆) , Topology.full-is-open T-A ,
   Topology.full-is-open T-R ,
    ⋆ , ⋆ ,
    restrictions-of-homeomorphisms-to-subspaces T-A T-R
     (source unit-pregroupoid)
     source-is-homeomorphism full ∣

\end{code}

The laws of an ordinary 1-manifold for the arrows and the crisp basis.

\begin{code}

 private
  raw-subset : ℕ → Subset R 𝓤₀
  raw-subset c x = raw-interval c x , raw-interval-is-prop c x

  raw-subsets-are-open : (c : ℕ) → Topology.is-open T-R (raw-subset c)
  raw-subsets-are-open c =
   Topology.openness-is-extensional T-R (rational-interval O translation K c)
    (raw-subset c)
    (λ x → rl-implication (raw-intervals-agree c x))
    (λ x → lr-implication (raw-intervals-agree c x))
    (pr₁ (rational-intervals-form-a-basis O translation K) c)

 rational-arrow-basis-is-basis : is-basis T-A rational-arrow-basis
 rational-arrow-basis-is-basis = raw-subsets-are-open , refine
  where
   refine : (U : Subset Arrow 𝓤₀) → Topology.is-open T-A U → (a : Arrow) → a ∈ U
          → ∃ c ꞉ ℕ , a ∈ rational-arrow-basis c × rational-arrow-basis c ⊆ U
   refine U oU a aU =
    ∥∥-functor
     (λ (c , m , inc) →
       c ,
        rl-implication (raw-intervals-agree c (source unit-pregroupoid a)) m ,
       (λ a' r → transport (_∈ U) (identity-arrows-of-sources a')
                  (inc (source unit-pregroupoid a')
                    (lr-implication
                      (raw-intervals-agree c (source unit-pregroupoid a')) r))))
     (pr₂ (rational-intervals-form-a-basis O translation K)
       (λ x → U (identity-arrow x)) oU
       (source unit-pregroupoid a)
       (transport (_∈ U) ((identity-arrows-of-sources a)⁻¹) aU))

 private
  coordinate-chart : (Fin 1 → R) → Arrow
  coordinate-chart = identity-arrow ∘ coordinate O translation K

  coordinate-chart-is-homeomorphism
   : is-homeomorphism (Eucl 1) T-A coordinate-chart
  coordinate-chart-is-homeomorphism =
   ∘-is-homeomorphism (Eucl 1) T-R T-A (coordinate O translation K)
    identity-arrow
    (coordinate-is-homeomorphism O translation K)
     identity-arrow-is-homeomorphism

  centred-chart : R → (Fin 1 → R) → Arrow
  centred-chart x = identity-arrow ∘ chart-at O translation K x

  centred-charts-are-homeomorphisms : (x : R)
   → is-homeomorphism (Eucl 1) T-A (centred-chart x)
  centred-charts-are-homeomorphisms x =
   ∘-is-homeomorphism (Eucl 1) T-R T-A (chart-at O translation K x)
    identity-arrow
    (charts-are-homeomorphisms O translation K x)
     identity-arrow-is-homeomorphism

 arrow-manifold-laws
  : Ordinary-Manifold-Laws O translation K 1 T-A rational-arrow-basis
 arrow-manifold-laws = record
  { carrier-is-set = arrows-form-a-set
   ; topology-is-regular =
     regularity-is-invariant T-R T-A identity-arrow
      identity-arrow-is-homeomorphism
      (smooth-line-topology-is-regular O translation K)
   ; topology-is-T₀ =
     T₀-is-invariant T-R T-A identity-arrow identity-arrow-is-homeomorphism
      (smooth-line-topology-is-T₀ O translation K)
   ; charts = λ a →
     ∣ full , Topology.full-is-open (Eucl 1) , ⋆ ,
       (λ w → centred-chart (source unit-pregroupoid a) (pr₁ w)) ,
       ∣ full , (λ _ → ⋆) , Topology.full-is-open T-A ,
         restrictions-of-homeomorphisms-to-subspaces (Eucl 1) T-A
          (centred-chart (source unit-pregroupoid a))
          (centred-charts-are-homeomorphisms (source unit-pregroupoid a)) full
           ∣ ,
       (ap identity-arrow (+-unit-left (source unit-pregroupoid a))
        ∙ identity-arrows-of-sources a) ∣
   ; basis-is-basis = rational-arrow-basis-is-basis
   ; basis-consists-of-chart-domains = λ c →
     ∣ (λ v → rational-arrow-basis c (coordinate-chart v)) ,
       pr₁ (pr₂ coordinate-chart-is-homeomorphism) (rational-arrow-basis c)
        (raw-subsets-are-open c) ,
       restriction-to-preimage (Eucl 1) T-A coordinate-chart
        coordinate-chart-is-homeomorphism
        (rational-arrow-basis c) ,
       restrictions-of-homeomorphisms-to-subspaces (Eucl 1) T-A coordinate-chart
        coordinate-chart-is-homeomorphism (rational-arrow-basis c) ∣
   }

\end{code}

The anchor is cover-proper.

\begin{code}

 anchor-is-cover-proper
  : is-cover-proper T-A (product T-R T-R) (anchor unit-pregroupoid)
 anchor-is-cover-proper I V d o c (x , y) =
  ∥∥-functor
   (λ (i , m) →
     W i , W-is-open i , m , 1 , (λ _ → i) ,
     (λ e n → ∣ 𝟎 , transport (_∈ V i) (identity-arrows-of-sources e) n ∣))
   (c (identity-arrow x))
  where
   W : I → Subset (R × R) 𝓤₀
   W i z = V i (identity-arrow (pr₁ z))

   W-is-open : (i : I) → Topology.is-open (product T-R T-R) (W i)
   W-is-open i z n =
    ∣ (λ x' → V i (identity-arrow x')) , full , o i ,
     Topology.full-is-open T-R ,
      n , ⋆ , (λ x' y' p _ → p) ∣

 anchor-is-cover-proper-for-set-indices
  : is-cover-proper-for-set-indices T-A (product T-R T-R)
     (anchor unit-pregroupoid)
 anchor-is-cover-proper-for-set-indices =
  cover-proper-maps-are-cover-proper-for-set-indices T-A (product T-R T-R)
   (anchor unit-pregroupoid) anchor-is-cover-proper

\end{code}

The anchor is not Dubuc–Penon proper.

\begin{code}

 module _ (J : Postulate-J-for-dual-numbers) where

  anchor-is-not-DP-proper : ¬ is-DP-proper (anchor unit-pregroupoid)
  anchor-is-not-DP-proper p =
   DN.nilsquares-cannot-all-vanish K J
    (λ d → nilsquares-are-zero (pr₁ d 𝟎) (pr₂ d 𝟎))
   where
    fibres-are-compact : (x y : R)
                       → is-DP-compact (fiber (anchor unit-pregroupoid) (x , y))
    fibres-are-compact x y =
     DP-proper-maps-have-DP-compact-fibres (anchor unit-pregroupoid)
      (×-is-set R-is-set R-is-set) p (x , y)

    to-equality : (x y : R) → fiber (anchor unit-pregroupoid) (x , y) → x ＝ y
    to-equality x y ((x' , y' , p') , q) = (ap pr₁ q)⁻¹ ∙ p' ∙ ap pr₂ q

    equality-is-decidable : (x y : R) → is-decidable (x ＝ y)
    equality-is-decidable x y =
     DP-compact-propositions-are-decidable R-is-set
      (DP-compactness-is-preserved-by-surjections (to-equality x y)
        (λ p' → ∣ ((x , y , p') , refl) , R-is-set _ _ ∣)
        (fibres-are-compact x y))

    nilsquares-are-zero : (d : R) → d ·ᴿ d ＝ 0ᴿ → d ＝ 0ᴿ
    nilsquares-are-zero d h =
     cases id
      (λ ν → 𝟘-elim (nilpotents-are-infinitesimal K d
                       (2 , (ap (_·ᴿ d) (·-unit-left d) ∙ h)) ν))
      (equality-is-decidable d 0ᴿ)

\end{code}

T5a: under the ambient hypotheses of T1, the unit pregroupoid satisfies
T1, so its Rezk completion is an orbifold, and its anchor is not
Dubuc–Penon proper. The nullification is at Myers's infinitesimal
varieties in the adopted, presentation-based reading of
MyersMicrolinearity, and the conclusion is about literal orbifolds in
that reading, as in OrdinaryEtaleGroupoids.theorem-T1-literal, whose
note on scope applies. The hypothesis that ℑ
preserves crisp pullbacks is stated by the name that
OrdinaryEtaleGroupoids exports, so that it is passed to theorem-T1
without a conversion between two copies of CrispLemmaF.

\begin{code}

module _ (ua : is-univalent 𝓤₀)
         (K : Postulate-K)
         (O : Postulate-O)
         (Exp : Postulate-Exp O)
         {𝓟 : Universe}
         (P : subuniverse 𝓤₁ 𝓟)
         (P-is-reflective : subuniverse-is-reflective P)
         (ν : is-nullification literal-ℑ-generator literal-ℑ-generator-point P)
       where

 private
  translation : Translation-Law O
  translation = translation-law-from-Exp O Exp

  ν' : is-nullification ℑ-generator ℑ-generator-point P
  ν' = lr-implication (literal-nullifications-are-nullifications P) ν

 theorem-T5a
  : ○-preserves-crisp-pullbacks ua K O Exp P P-is-reflective ν'
  → {𝓙 𝓖 : Universe} {J : 𝓙 ̇ } {Gen : J → 𝓖 ̇ } → Axiom-C1 Gen
  → Postulate-J-for-dual-numbers
  → is-literal-orbifold (Rezk-completion unit-pregroupoid)
  × ¬ is-DP-proper (anchor unit-pregroupoid)
 theorem-T5a π c1 J =
  lr-implication (orbifolds-agree (Rezk-completion unit-pregroupoid))
   (theorem-T1 ua K O Exp P P-is-reflective ν' π c1 unit-pregroupoid
     (smooth-line-is-an-ordinary-manifold O translation K)
     (arrow-topology O Exp K) rational-arrow-basis (arrow-manifold-laws O Exp K)
     (source-is-a-local-homeomorphism O Exp K)
     (anchor-is-cover-proper O Exp K)) ,
  anchor-is-not-DP-proper O Exp K J

\end{code}

