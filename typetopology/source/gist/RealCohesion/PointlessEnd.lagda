Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index.

A half-line with a pointless end, as a frame.

The countermodel of [1, §2] adds to the site of Cartesian spaces the
locales X_e, for nonzero e in the complete Boolean algebra
P = RO(2^ℕ), whose frames are [1, Definition 2.1]

 𝒪(X_e) = {(V , d) ∈ 𝒪((0,1)) × ↓e : d ≠ 0 ⇒ (0,ε) ⊆ V for some ε > 0}.

We formalize a generalization of this frame, and some of its
properties that the countermodel uses. In place of 𝒪((0,1)) we take a
frame O with a filter C, where C V stands for "V contains an interval
(0,ε)", and in place of ↓e we take a frame B. The condition
d ≠ 0 ⇒ C V is not preserved by joins constructively, so we use the
condition

 d ≤ ⟦ C V ⟧,

where ⟦ p ⟧ is the join in B of the family that is 𝟏 at each witness
of p. Assuming excluded middle, ⟦ p ⟧ is 𝟏 or 𝟎 according as p holds
or not, and the two conditions agree. The resulting frame Gl is the
Artin gluing of O and B along the finite-meet preserving map
V ↦ ⟦ C V ⟧. Classically, 𝒪(X_e) is its instance for O = 𝒪((0,1)),
B = ↓e and the filter of opens that contain an interval (0,ε). We
call the element (𝟏 , 𝟎) of Gl the collar. The opens below the collar
form a copy of O: the open sublocale given by the open interval. The
opens above it form a copy of B: the closed complement, which is the
pointless end.

We show the following.

 * The collar is not 𝟏 if B is nontrivial. If 𝟎 is not in C, the
   collar is dense: only 𝟎 is disjoint from it.

 * Points of O give points of Gl. If B has no points, every point of
   Gl lies in the collar, up to double negation. Assuming excluded
   middle, the points of Gl are then exactly the points of O
   [1, Lemma 2.2(i)].

 * If every nonzero open of O contains a point and 𝟎 is not in C,
   every nonzero open of Gl contains a point [1, Lemma 2.2(ii)].

 * If O is connected and 𝟎 is not in C, Gl is connected. This is part
   of [1, Lemma 2.2(iii)].

 * Let g : L → O be a frame homomorphism and p a completely prime
   filter on L whose members g sends into C. Then
   t* W = (g W , ⟦ p W ⟧) is a frame homomorphism t* : L → Gl, and
   t* W is the collar if g W = 𝟏 and W is not in p. For L = 𝒪(ℝ),
   with g the restriction to (0,1) and p the point 0, this is the
   coordinate t of [1, Lemma 2.2(iv)], which sends the half-line (0,∞)
   to the collar.

 * Given a cylinder system on B (gist.RealCohesion.Cylinders), the
   opens bar s = (𝟏 , cyl′ s) form a bar: for every sequence α, the
   opens bar (α ↾ n) cover. If B is nontrivial, no cover of Gl is
   uniformly barred. This is the frame-level content of the failure
   of the full fan theorem in [1, Theorem 2.5(ii)]. By
   gist.RealCohesion.Cylinders, such a B has no points.

All results are relative to these hypotheses on O, B, C, L, g and p.
We don't verify them in Agda for 𝒪((0,1)), its filter, ↓e, 𝒪(ℝ), the
restriction map and the point 0; these are standard facts of classical
topology, and TypeTopology has no locale of real numbers. (For e ≠ 𝟏,
the elements e ∧ cyl s form a cylinder system on ↓e.) Nor do we
formalize that the points of 𝒪((0,1)) are the points of the interval,
the rest of [1, Lemma 2.2(iii)], [1, Lemma 2.2(v)], or the passage
from these frame-level facts to the ∞-topos of sheaves on the site.
The frame of gist.RealCohesion.CohenFrame, a constructive stand-in for
RO(2^ℕ), shows that the hypotheses on B can be met with 𝟎 ≠ 𝟏, and
gist.RealCohesion.PointlessEndExample instantiates all the hypotheses
at once. Restating the results for a concrete instance can be slow
without --lossy-unification, which that module uses.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, draft of 25 October 2026.
    references/C01-write-up-2026-10-25.tex

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import MLTT.List hiding ([_])
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.PointlessEnd
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.Frame pt fe hiding (𝟚 ; ₀ ; ₁)
open import Locales.InitialFrame pt fe
 using () renaming
  (f to initial-frame-map ; f-respects-∧ to initial-frame-map-respects-∧)
open import Locales.Point.Definition pt fe
open import Slice.Family
open import UF.Base
open import UF.ClassicalLogic
open import UF.Equiv using (_≃_ ; qinveq)
open import UF.Logic
open import UF.SubtypeClassifier
open import UF.UniverseEmbedding
open import gist.RealCohesion.Cylinders pt fe

open AllCombinators pt fe hiding (_∨_)
open DefnOfCPF
open FrameHomomorphisms
open Locale
open PropositionalTruncation pt

\end{code}

A frame is connected if it can't be split into two disjoint nonzero
opens. (This doesn't ask for the frame to be nontrivial.)

\begin{code}

is-connected-frame : Frame 𝓤 𝓥 𝓦 → 𝓤 ̇
is-connected-frame L = (x y : ⟨ L ⟩)
                     → x ∨[ L ] y ＝ 𝟏[ L ]
                     → x ∧[ L ] y ＝ 𝟎[ L ]
                     → (x ＝ 𝟎[ L ]) ∨ (y ＝ 𝟎[ L ])

\end{code}

The construction.

\begin{code}

module glued-frame
        {𝓤 𝓥 𝓤' 𝓥' 𝓦 : Universe}
        (O : Frame 𝓤 𝓥 𝓦)
        (B : Frame 𝓤' 𝓥' 𝓦)
        (C : ⟨ O ⟩ → Ω 𝓦)
        (C-is-upward-closed : (V W : ⟨ O ⟩)
                            → (V ≤[ poset-of O ] W) holds
                            → C V holds → C W holds)
        (C-contains-𝟏 : C 𝟏[ O ] holds)
        (C-is-closed-under-∧ : (V W : ⟨ O ⟩)
                             → C V holds → C W holds → C (V ∧[ O ] W) holds)
       where

 private
  _≤ᴼ_ : ⟨ O ⟩ → ⟨ O ⟩ → Ω 𝓥
  V ≤ᴼ W = V ≤[ poset-of O ] W

  _≤ᴮ_ : ⟨ B ⟩ → ⟨ B ⟩ → Ω 𝓥'
  d ≤ᴮ e = d ≤[ poset-of B ] e

  ≤ᴮ-trans : {a b c : ⟨ B ⟩} → (a ≤ᴮ b) holds → (b ≤ᴮ c) holds → (a ≤ᴮ c) holds
  ≤ᴮ-trans = ≤-is-transitive (poset-of B) _ _ _

\end{code}

Truth values as elements of B: ⟦ p ⟧ is the join of the family that is 𝟏
at each witness of p, which is TypeTopology's map from the initial
frame Ω 𝓦 to B (Locales.InitialFrame).

\begin{code}

 ⟦_⟧ : Ω 𝓦 → ⟨ B ⟩
 ⟦_⟧ = initial-frame-map pe B

 ⟦⟧-is-monotone : (p q : Ω 𝓦) → (p holds → q holds) → (⟦ p ⟧ ≤ᴮ ⟦ q ⟧) holds
 ⟦⟧-is-monotone p q f =
  ⋁[ B ]-least (p holds , λ _ → 𝟏[ B ])
   (⟦ q ⟧ , λ h → ⋁[ B ]-upper (q holds , λ _ → 𝟏[ B ]) (f h))

 ⟦⟧-of-true : (p : Ω 𝓦) → p holds → ⟦ p ⟧ ＝ 𝟏[ B ]
 ⟦⟧-of-true p h =
  only-𝟏-is-above-𝟏 B ⟦ p ⟧ (⋁[ B ]-upper (p holds , λ _ → 𝟏[ B ]) h)

 ⟦⟧-of-false : (p : Ω 𝓦) → ¬ (p holds) → ⟦ p ⟧ ＝ 𝟎[ B ]
 ⟦⟧-of-false p ν =
  only-𝟎-is-below-𝟎 B ⟦ p ⟧
   (⋁[ B ]-least (p holds , λ _ → 𝟏[ B ]) (𝟎[ B ] , λ h → 𝟘-elim (ν h)))

 ⟦⟧-binary : (p q r : Ω 𝓦)
           → (p holds → q holds → r holds)
           → ((⟦ p ⟧ ∧[ B ] ⟦ q ⟧) ≤ᴮ ⟦ r ⟧) holds
 ⟦⟧-binary p q r f =
  transport (λ - → (- ≤ᴮ ⟦ r ⟧) holds) (initial-frame-map-respects-∧ pe B p q)
   (⟦⟧-is-monotone (p ∧ q) r (λ (h , k) → f h k))

\end{code}

The carrier of the frame, and its two coordinates.

\begin{code}

 is-glued : ⟨ O ⟩ × ⟨ B ⟩ → Ω 𝓥'
 is-glued (V , d) = d ≤ᴮ ⟦ C V ⟧

 Glued : 𝓤 ⊔ 𝓤' ⊔ 𝓥' ̇
 Glued = Σ x ꞉ ⟨ O ⟩ × ⟨ B ⟩ , is-glued x holds

 open-part : Glued → ⟨ O ⟩
 open-part ((V , _) , _) = V

 closed-part : Glued → ⟨ B ⟩
 closed-part ((_ , d) , _) = d

 to-Glued-＝ : {x y : Glued}
             → open-part x ＝ open-part y
             → closed-part x ＝ closed-part y
             → x ＝ y
 to-Glued-＝ p q = to-subtype-＝ (λ z → holds-is-prop (is-glued z)) (to-×-＝ p q)

\end{code}

The order, top, binary meets and joins are computed coordinatewise.

\begin{code}

 _≤ᴳ_ : Glued → Glued → Ω (𝓥 ⊔ 𝓥')
 x ≤ᴳ y = (open-part x ≤ᴼ open-part y) ∧ (closed-part x ≤ᴮ closed-part y)

 𝟏-is-glued : (𝟏[ B ] ≤ᴮ ⟦ C 𝟏[ O ] ⟧) holds
 𝟏-is-glued = ⋁[ B ]-upper (C 𝟏[ O ] holds , λ _ → 𝟏[ B ]) C-contains-𝟏

 𝟏ᴳ : Glued
 𝟏ᴳ = (𝟏[ O ] , 𝟏[ B ]) , 𝟏-is-glued

 _∧ᴳ_ : Glued → Glued → Glued
 x ∧ᴳ y =
  ((open-part x ∧[ O ] open-part y) , (closed-part x ∧[ B ] closed-part y)) , γ
  where
   open PosetReasoning (poset-of B)

   V  = open-part x
   V′ = open-part y
   d  = closed-part x
   d′ = closed-part y

   δ : ((d ∧[ B ] d′) ≤ᴮ ⟦ C V ⟧) holds
   δ = ≤ᴮ-trans (∧[ B ]-lower₁ d d′) (pr₂ x)

   ε : ((d ∧[ B ] d′) ≤ᴮ ⟦ C V′ ⟧) holds
   ε = ≤ᴮ-trans (∧[ B ]-lower₂ d d′) (pr₂ y)

   γ : ((d ∧[ B ] d′) ≤ᴮ ⟦ C (V ∧[ O ] V′) ⟧) holds
   γ = d ∧[ B ] d′
       ≤⟨ ∧[ B ]-greatest ⟦ C V ⟧ ⟦ C V′ ⟧ (d ∧[ B ] d′) δ ε ⟩
       ⟦ C V ⟧ ∧[ B ] ⟦ C V′ ⟧     ≤⟨ ⟦⟧-binary (C V) (C V′) (C (V ∧[ O ] V′))
                                        (C-is-closed-under-∧ V V′) ⟩
       ⟦ C (V ∧[ O ] V′) ⟧         ■

 ⋁ᴳ_ : Fam 𝓦 Glued → Glued
 ⋁ᴳ S =
  ((⋁[ O ] ⁅ open-part x ∣ x ε S ⁆) , (⋁[ B ] ⁅ closed-part x ∣ x ε S ⁆)) , γ
  where
   open PosetReasoning (poset-of B)

   V = ⋁[ O ] ⁅ open-part x ∣ x ε S ⁆

   δ : (i : index S) → (closed-part (S [ i ]) ≤ᴮ ⟦ C V ⟧) holds
   δ i = closed-part (S [ i ])       ≤⟨ pr₂ (S [ i ]) ⟩
         ⟦ C (open-part (S [ i ])) ⟧
          ≤⟨ ⟦⟧-is-monotone (C (open-part (S [ i ]))) (C V)
              (C-is-upward-closed _ _
                (⋁[ O ]-upper ⁅ open-part x ∣ x ε S ⁆ i)) ⟩
         ⟦ C V ⟧                     ■

   γ : ((⋁[ B ] ⁅ closed-part x ∣ x ε S ⁆) ≤ᴮ ⟦ C V ⟧) holds
   γ = ⋁[ B ]-least ⁅ closed-part x ∣ x ε S ⁆ (⟦ C V ⟧ , δ)

 Glued-data : frame-data (𝓥 ⊔ 𝓥') 𝓦 Glued
 Glued-data = _≤ᴳ_ , 𝟏ᴳ , _∧ᴳ_ , ⋁ᴳ_

 Glued-is-partial-order : is-partial-order Glued _≤ᴳ_
 Glued-is-partial-order = (ρ , τ) , α
  where
   ρ : is-reflexive _≤ᴳ_ holds
   ρ x = ≤-is-reflexive (poset-of O) (open-part x) ,
         ≤-is-reflexive (poset-of B) (closed-part x)

   τ : is-transitive _≤ᴳ_ holds
   τ x y z p q = ≤-is-transitive (poset-of O) _ _ _ (pr₁ p) (pr₁ q) ,
                 ≤-is-transitive (poset-of B) _ _ _ (pr₂ p) (pr₂ q)

   α : is-antisymmetric _≤ᴳ_
   α p q = to-Glued-＝ (≤-is-antisymmetric (poset-of O) (pr₁ p) (pr₁ q))
                       (≤-is-antisymmetric (poset-of B) (pr₂ p) (pr₂ q))

 Glued-satisfies-frame-laws : satisfies-frame-laws Glued-data
 Glued-satisfies-frame-laws =
  Glued-is-partial-order , top , meets , joins , distributive
  where
   open Meets _≤ᴳ_
   open Joins _≤ᴳ_

   top : (x : Glued) → (x ≤ᴳ 𝟏ᴳ) holds
   top x = 𝟏-is-top O (open-part x) , 𝟏-is-top B (closed-part x)

   meets : ((x , y) : Glued × Glued) → ((x ∧ᴳ y) is-glb-of (x , y)) holds
   meets (x , y) = ((∧[ O ]-lower₁ _ _ , ∧[ B ]-lower₁ _ _) ,
                    (∧[ O ]-lower₂ _ _ , ∧[ B ]-lower₂ _ _)) ,
                   γ
    where
     γ : ((z , _) : lower-bound (x , y)) → (z ≤ᴳ (x ∧ᴳ y)) holds
     γ (z , p , q) = ∧[ O ]-greatest _ _ _ (pr₁ p) (pr₁ q) ,
                     ∧[ B ]-greatest _ _ _ (pr₂ p) (pr₂ q)

   joins : (S : Fam 𝓦 Glued) → ((⋁ᴳ S) is-lub-of S) holds
   joins S = (λ i → ⋁[ O ]-upper ⁅ open-part x ∣ x ε S ⁆ i ,
                    ⋁[ B ]-upper ⁅ closed-part x ∣ x ε S ⁆ i) ,
             γ
    where
     γ : ((u , _) : upper-bound S) → ((⋁ᴳ S) ≤ᴳ u) holds
     γ (u , h) =
      ⋁[ O ]-least ⁅ open-part x ∣ x ε S ⁆ (open-part u , λ i → pr₁ (h i)) ,
                 ⋁[ B ]-least ⁅ closed-part x
                  ∣ x ε S ⁆ (closed-part u , λ i → pr₂ (h i))

   distributive : ((x , S) : Glued × Fam 𝓦 Glued)
                → x ∧ᴳ (⋁ᴳ (index S , λ i → S [ i ]))
                ＝ ⋁ᴳ (index S , λ i → x ∧ᴳ (S [ i ]))
   distributive (x , S) =
    to-Glued-＝ (distributivity O (open-part x) ⁅ open-part y ∣ y ε S ⁆)
                (distributivity B (closed-part x) ⁅ closed-part y ∣ y ε S ⁆)

 Gl : Frame (𝓤 ⊔ 𝓤' ⊔ 𝓥') (𝓥 ⊔ 𝓥') 𝓦
 Gl = Glued , Glued-data , Glued-satisfies-frame-laws

\end{code}

The coordinate projections are frame homomorphisms, and so are locale
maps from O and from B to Gl. Below we show that they are the
inclusions of the open sublocale given by the collar and of its closed
complement.

\begin{code}

 open-part-is-frame-homomorphism : is-a-frame-homomorphism Gl O open-part holds
 open-part-is-frame-homomorphism =
  refl ,
  (λ x y → refl) ,
  (λ S →
    ⋁[ O ]-upper ⁅ open-part x ∣ x ε S ⁆ , ⋁[ O ]-least ⁅ open-part x ∣ x ε S ⁆)

 closed-part-is-frame-homomorphism
  : is-a-frame-homomorphism Gl B closed-part holds
 closed-part-is-frame-homomorphism =
  refl ,
  (λ x y → refl) ,
  (λ S → ⋁[ B ]-upper ⁅ closed-part x ∣ x ε S ⁆ , ⋁[ B ]-least ⁅ closed-part x
         ∣ x ε S ⁆)

 open-part-of-∨ : (x y : Glued)
                → open-part (x ∨[ Gl ] y) ＝ open-part x ∨[ O ] open-part y
 open-part-of-∨ x y = ap (join-of O) (fmap-binary-family 𝓦 open-part x y)

 closed-part-of-∨ : (x y : Glued)
                  → closed-part (x ∨[ Gl ] y)
                  ＝ closed-part x ∨[ B ] closed-part y
 closed-part-of-∨ x y = ap (join-of B) (fmap-binary-family 𝓦 closed-part x y)

\end{code}

Some elements of the frame: the bottom element, the opens κ V that
don't meet the end, the opens ι d that contain the whole interval,
and the collar.

\begin{code}

 𝟎ᴳ : Glued
 𝟎ᴳ = (𝟎[ O ] , 𝟎[ B ]) , 𝟎-is-bottom B ⟦ C 𝟎[ O ] ⟧

 𝟎ᴳ-is-𝟎 : 𝟎ᴳ ＝ 𝟎[ Gl ]
 𝟎ᴳ-is-𝟎 = 𝟎-is-unique Gl 𝟎ᴳ
            (λ x → 𝟎-is-bottom O (open-part x) , 𝟎-is-bottom B (closed-part x))

 open-part-of-𝟎 : open-part 𝟎[ Gl ] ＝ 𝟎[ O ]
 open-part-of-𝟎 = ap open-part (𝟎ᴳ-is-𝟎 ⁻¹)

 κ : ⟨ O ⟩ → Glued
 κ V = (V , 𝟎[ B ]) , 𝟎-is-bottom B ⟦ C V ⟧

 ι : ⟨ B ⟩ → Glued
 ι d = (𝟏[ O ] , d) , ≤ᴮ-trans (𝟏-is-top B d) 𝟏-is-glued

 collar : Glued
 collar = κ 𝟏[ O ]

\end{code}

The opens below the collar are the opens κ V, and the opens above it
are the opens ι d. Meeting with the collar is the open projection,
and joining with it is the closed projection.

\begin{code}

 κ-is-below-the-collar : (V : ⟨ O ⟩) → (κ V ≤ᴳ collar) holds
 κ-is-below-the-collar V = 𝟏-is-top O V , ≤-is-reflexive (poset-of B) 𝟎[ B ]

 ι-is-above-the-collar : (d : ⟨ B ⟩) → (collar ≤ᴳ ι d) holds
 ι-is-above-the-collar d = ≤-is-reflexive (poset-of O) 𝟏[ O ] , 𝟎-is-bottom B d

 below-the-collar : (x : Glued) → (x ≤ᴳ collar) holds → x ＝ κ (open-part x)
 below-the-collar x l =
  to-Glued-＝ refl (only-𝟎-is-below-𝟎 B (closed-part x) (pr₂ l))

 above-the-collar : (x : Glued) → (collar ≤ᴳ x) holds → x ＝ ι (closed-part x)
 above-the-collar x l =
  to-Glued-＝ (only-𝟏-is-above-𝟏 O (open-part x) (pr₁ l)) refl

 meet-with-the-collar : (x : Glued) → x ∧[ Gl ] collar ＝ κ (open-part x)
 meet-with-the-collar x =
  to-Glued-＝ (𝟏-right-unit-of-∧ O (open-part x))
              (𝟎-right-annihilator-for-∧ B (closed-part x))

 join-with-the-collar : (x : Glued) → x ∨[ Gl ] collar ＝ ι (closed-part x)
 join-with-the-collar x =
  to-Glued-＝
   (open-part-of-∨ x collar ∙ 𝟏-right-annihilator-for-∨ O (open-part x))
              (closed-part-of-∨ x collar ∙ 𝟎-left-unit-of-∨ B (closed-part x))

\end{code}

The collar is not 𝟏, but it is dense.

\begin{code}

 collar-is-not-𝟏 : 𝟎[ B ] ≠ 𝟏[ B ] → collar ≠ 𝟏[ Gl ]
 collar-is-not-𝟏 ν p = ν (ap closed-part p)

 glued-with-empty-open-part : ¬ (C 𝟎[ O ] holds)
                            → (x : Glued)
                            → open-part x ＝ 𝟎[ O ]
                            → x ＝ 𝟎[ Gl ]
 glued-with-empty-open-part ν x e = to-Glued-＝ e γ ∙ 𝟎ᴳ-is-𝟎
  where
   δ : ⟦ C (open-part x) ⟧ ＝ 𝟎[ B ]
   δ = ap (λ V → ⟦ C V ⟧) e ∙ ⟦⟧-of-false (C 𝟎[ O ]) ν

   γ : closed-part x ＝ 𝟎[ B ]
   γ = only-𝟎-is-below-𝟎 B (closed-part x)
        (transport (λ - → (closed-part x ≤ᴮ -) holds) δ (pr₂ x))

 collar-is-dense : ¬ (C 𝟎[ O ] holds)
                 → (x : Glued)
                 → x ∧[ Gl ] collar ＝ 𝟎[ Gl ]
                 → x ＝ 𝟎[ Gl ]
 collar-is-dense ν x p = glued-with-empty-open-part ν x e
  where
   e : open-part x ＝ 𝟎[ O ]
   e = open-part x               ＝⟨ 𝟏-right-unit-of-∧ O (open-part x) ⁻¹ ⟩
       open-part x ∧[ O ] 𝟏[ O ] ＝⟨ ap open-part p ⟩
       open-part 𝟎[ Gl ]         ＝⟨ open-part-of-𝟎 ⟩
       𝟎[ O ]                    ∎

\end{code}

Connectedness [1, Lemma 2.2(iii)].

\begin{code}

 Gl-is-connected : ¬ (C 𝟎[ O ] holds)
                 → is-connected-frame O
                 → is-connected-frame Gl
 Gl-is-connected ν O-is-connected x y p q =
  ∨-functor (glued-with-empty-open-part ν x) (glued-with-empty-open-part ν y)
   (O-is-connected (open-part x) (open-part y) p′ q′)
  where
   p′ : open-part x ∨[ O ] open-part y ＝ 𝟏[ O ]
   p′ = open-part-of-∨ x y ⁻¹ ∙ ap open-part p

   q′ : open-part x ∧[ O ] open-part y ＝ 𝟎[ O ]
   q′ = ap open-part q ∙ open-part-of-𝟎

\end{code}

The coordinate [1, Lemma 2.2(iv)].

\begin{code}

 module coordinate
         {𝓤'' 𝓥'' : Universe}
         (L : Frame 𝓤'' 𝓥'' 𝓦)
         (g : ⟨ L ⟩ → ⟨ O ⟩)
         (g-is-frame-homomorphism : is-a-frame-homomorphism L O g holds)
         (p : ⟨ L ⟩ → Ω 𝓦)
         (p-is-upward-closed : (W W′ : ⟨ L ⟩)
                             → (W ≤[ poset-of L ] W′) holds
                             → p W holds → p W′ holds)
         (p-contains-𝟏 : p 𝟏[ L ] holds)
         (p-is-closed-under-∧ : (W W′ : ⟨ L ⟩)
                              → p W holds → p W′ holds → p (W ∧[ L ] W′) holds)
         (p-is-completely-prime : (S : Fam 𝓦 ⟨ L ⟩)
                                → p (⋁[ L ] S) holds
                                → ∃ i ꞉ index S , p (S [ i ]) holds)
         (members-of-p-are-sent-into-C : (W : ⟨ L ⟩) → p W holds
          → C (g W) holds)
        where

  t* : ⟨ L ⟩ → Glued
  t* W = (g W , ⟦ p W ⟧) ,
         ⟦⟧-is-monotone (p W) (C (g W)) (members-of-p-are-sent-into-C W)

  ⟦p⟧-preserves-∧ : (W W′ : ⟨ L ⟩)
                  → ⟦ p (W ∧[ L ] W′) ⟧ ＝ ⟦ p W ⟧ ∧[ B ] ⟦ p W′ ⟧
  ⟦p⟧-preserves-∧ W W′ = ≤-is-antisymmetric (poset-of B) β γ
   where
    β : (⟦ p (W ∧[ L ] W′) ⟧ ≤ᴮ (⟦ p W ⟧ ∧[ B ] ⟦ p W′ ⟧)) holds
    β = ∧[ B ]-greatest ⟦ p W ⟧ ⟦ p W′ ⟧ ⟦ p (W ∧[ L ] W′) ⟧
         (⟦⟧-is-monotone (p (W ∧[ L ] W′)) (p W)
           (p-is-upward-closed _ _ (∧[ L ]-lower₁ W W′)))
         (⟦⟧-is-monotone (p (W ∧[ L ] W′)) (p W′)
           (p-is-upward-closed _ _ (∧[ L ]-lower₂ W W′)))

    γ : ((⟦ p W ⟧ ∧[ B ] ⟦ p W′ ⟧) ≤ᴮ ⟦ p (W ∧[ L ] W′) ⟧) holds
    γ = ⟦⟧-binary (p W) (p W′) (p (W ∧[ L ] W′)) (p-is-closed-under-∧ W W′)

  t*-is-frame-homomorphism : is-a-frame-homomorphism L Gl t* holds
  t*-is-frame-homomorphism = top , meets , joins
   where
    g-preserves-𝟏 : g 𝟏[ L ] ＝ 𝟏[ O ]
    g-preserves-𝟏 = pr₁ g-is-frame-homomorphism

    g-preserves-∧ : (W W′ : ⟨ L ⟩) → g (W ∧[ L ] W′) ＝ g W ∧[ O ] g W′
    g-preserves-∧ = pr₁ (pr₂ g-is-frame-homomorphism)

    g-preserves-⋁ = pr₂ (pr₂ g-is-frame-homomorphism)

    top : t* 𝟏[ L ] ＝ 𝟏[ Gl ]
    top = to-Glued-＝ g-preserves-𝟏 (⟦⟧-of-true (p 𝟏[ L ]) p-contains-𝟏)

    meets : (W W′ : ⟨ L ⟩) → t* (W ∧[ L ] W′) ＝ t* W ∧[ Gl ] t* W′
    meets W W′ = to-Glued-＝ (g-preserves-∧ W W′) (⟦p⟧-preserves-∧ W W′)

    open Joins _≤ᴳ_

    joins : (S : Fam 𝓦 ⟨ L ⟩) → (t* (⋁[ L ] S) is-lub-of ⁅ t* W ∣ W ε S ⁆) holds
    joins S = upper , least
     where
      upper : (i : index S) → (t* (S [ i ]) ≤ᴳ t* (⋁[ L ] S)) holds
      upper i = pr₁ (g-preserves-⋁ S) i ,
                ⟦⟧-is-monotone (p (S [ i ])) (p (⋁[ L ] S))
                 (p-is-upward-closed _ _ (⋁[ L ]-upper S i))

      least : ((u , _) : upper-bound ⁅ t* W ∣ W ε S ⁆)
            → (t* (⋁[ L ] S) ≤ᴳ u) holds
      least (u , h) = pr₂ (g-preserves-⋁ S) (open-part u , λ i → pr₁ (h i)) ,
                      ⋁[ B ]-least (p (⋁[ L ] S) holds , λ _ → 𝟏[ B ])
                       (closed-part u , δ)
       where
        ε : (Σ i ꞉ index S , p (S [ i ]) holds)
          → (𝟏[ B ] ≤ᴮ closed-part u) holds
        ε (i , k) = ≤ᴮ-trans (⋁[ B ]-upper (p (S [ i ]) holds , λ _ → 𝟏[ B ]) k)
                             (pr₂ (h i))

        δ : (k : p (⋁[ L ] S) holds) → (𝟏[ B ] ≤ᴮ closed-part u) holds
        δ k = ∥∥-rec (holds-is-prop (𝟏[ B ] ≤ᴮ closed-part u)) ε
               (p-is-completely-prime S k)

  open-part-of-t* : (W : ⟨ L ⟩) → open-part (t* W) ＝ g W
  open-part-of-t* W = refl

  t*-sends-to-the-collar : (W : ⟨ L ⟩)
                         → g W ＝ 𝟏[ O ]
                         → ¬ (p W holds)
                         → t* W ＝ collar
  t*-sends-to-the-collar W e ν = to-Glued-＝ e (⟦⟧-of-false (p W) ν)

\end{code}

The failure of the full fan theorem [1, Theorem 2.5(ii)]. For a
cylinder system on B, the opens bar s = (𝟏 , cyl′ s) form a bar, and
an open that lies below the join of bar t over the initial segments t
of u, for every word u of length N, lies in the collar. So a cover by
such opens would put 𝟏 in the collar.

\begin{code}

 module fan (𝒞 : Cylinder-System B) where

  open Cylinder-System 𝒞

  bar : List 𝟚 → Glued
  bar s = ι (cyl′ s)

  bar-is-a-bar : (α : ℕ → 𝟚)
               → ⋁[ Gl ] (Lift 𝓦 ℕ , (λ n → bar (α ↾ lower n))) ＝ 𝟏[ Gl ]
  bar-is-a-bar α = to-Glued-＝ γ (cyl′-cover α)
   where
    γ : ⋁[ O ] (Lift 𝓦 ℕ , (λ _ → 𝟏[ O ])) ＝ 𝟏[ O ]
    γ = only-𝟏-is-above-𝟏 O _
         (⋁[ O ]-upper (Lift 𝓦 ℕ , (λ _ → 𝟏[ O ])) (lift 𝓦 0))

  collar-is-below-the-bar : (s : List 𝟚) → (collar ≤ᴳ bar s) holds
  collar-is-below-the-bar s = ≤-is-reflexive (poset-of O) 𝟏[ O ] ,
                              𝟎-is-bottom B (cyl′ s)

  bar-grows-along-extensions : (s r : List 𝟚) → (bar s ≤ᴳ bar (s ++ r)) holds
  bar-grows-along-extensions s r = ≤-is-reflexive (poset-of O) 𝟏[ O ] ,
                                   complements-grow-along-extensions 𝒞 s r

  below-the-bar-at-level : (N : ℕ) (x : Glued)
                         → ((s : List 𝟚) → length s ＝ N → (x ≤ᴳ bar s) holds)
                         → (x ≤ᴳ collar) holds
  below-the-bar-at-level N x h =
   𝟏-is-top O (open-part x) ,
   reflexivity+ (poset-of B)
    (below-all-complements-of-length 𝒞 N (closed-part x) (λ s e → pr₂ (h s e)))

  initial-segments : List 𝟚 → Fam 𝓦 (List 𝟚)
  initial-segments u = Lift 𝓦 (Σ t ꞉ List 𝟚 , Σ r ꞉ List 𝟚 , u ＝ t ++ r) ,
                       (λ w → pr₁ (lower w))

  bar-over-initial-segments : (u : List 𝟚)
                            → ((⋁[ Gl ] ⁅ bar t ∣ t ε initial-segments u ⁆) ≤ᴳ
                                bar u) holds
  bar-over-initial-segments u =
   ⋁[ Gl ]-least ⁅ bar t ∣ t ε initial-segments u ⁆ (bar u , γ)
   where
    γ : (w : index (initial-segments u))
      → (bar (initial-segments u [ w ]) ≤ᴳ bar u) holds
    γ ((t , r , e) , _) = transport (λ - → (bar t ≤ᴳ bar -) holds) (e ⁻¹)
                           (bar-grows-along-extensions t r)

  no-uniformly-barred-cover
   : 𝟎[ B ] ≠ 𝟏[ B ]
   → (W : Fam 𝓦 Glued)
   → ⋁[ Gl ] W ＝ 𝟏[ Gl ]
   → ((j : index W) → ∃ N ꞉ ℕ , ((u : List 𝟚) → length u ＝ N
                     → ((W [ j ]) ≤ᴳ
                         (⋁[ Gl ] ⁅ bar t ∣ t ε initial-segments u ⁆)) holds))
   → 𝟘
  no-uniformly-barred-cover ν W p h =
   collar-is-not-𝟏 ν (only-𝟏-is-above-𝟏 Gl collar γ)
   where
    δ : (j : index W) → ((W [ j ]) ≤ᴳ collar) holds
    δ j = ∥∥-rec (holds-is-prop ((W [ j ]) ≤ᴳ collar))
           (λ (N , k) → below-the-bar-at-level N (W [ j ])
                         (λ u e → ≤-is-transitive (poset-of Gl)
                                   (W [ j ])
                                   (⋁[ Gl ] ⁅ bar t ∣ t ε initial-segments u ⁆)
                                   (bar u)
                                   (k u e)
                                   (bar-over-initial-segments u)))
           (h j)

    γ : (𝟏[ Gl ] ≤ᴳ collar) holds
    γ = transport (λ - → (- ≤ᴳ collar) holds) p (⋁[ Gl ]-least W (collar , δ))

\end{code}

Points. We use TypeTopology's points of locales, which are defined for
frames whose carrier lives one universe above their order and index
types.

\begin{code}

module glued-points
        {𝓣 : Universe}
        (O B : Frame (𝓣 ⁺) 𝓣 𝓣)
        (C : ⟨ O ⟩ → Ω 𝓣)
        (C-is-upward-closed : (V W : ⟨ O ⟩)
                            → (V ≤[ poset-of O ] W) holds
                            → C V holds → C W holds)
        (C-contains-𝟏 : C 𝟏[ O ] holds)
        (C-is-closed-under-∧ : (V W : ⟨ O ⟩)
                             → C V holds → C W holds → C (V ∧[ O ] W) holds)
       where

 open glued-frame O B C C-is-upward-closed C-contains-𝟏 C-is-closed-under-∧

 Xᴼ Xᴮ X : Locale (𝓣 ⁺) 𝓣 𝓣
 Xᴼ = frame-to-locale O
 Xᴮ = frame-to-locale B
 X  = frame-to-locale Gl

 to-point-＝ : (L : Locale (𝓣 ⁺) 𝓣 𝓣) {x y : Point L}
             → ((U : ⟨ 𝒪 L ⟩) → (pr₁ x U holds → pr₁ y U holds)
                               × (pr₁ y U holds → pr₁ x U holds))
             → x ＝ y
 to-point-＝ L h =
  to-subtype-＝ (λ ϕ → holds-is-prop (is-cpf L ϕ))
   (dfunext fe (λ U → Ω-extensionality pe fe (pr₁ (h U)) (pr₂ (h U))))

\end{code}

Points of O give points of X_e, by composing with the open inclusion.

\begin{code}

 point-from-O : Point Xᴼ → Point X
 point-from-O (χ , (χ-up , χ-top , χ-meet) , χ-prime) =
  (λ x → χ (open-part x)) , (up , χ-top , meet) , prime
  where
   up : is-upwards-closed X (λ x → χ (open-part x)) holds
   up x y l = χ-up (open-part x) (open-part y) (pr₁ l)

   meet : closed-under-binary-meets X (λ x → χ (open-part x)) holds
   meet x y = χ-meet (open-part x) (open-part y)

   prime : is-completely-prime X (λ x → χ (open-part x)) holds
   prime S = χ-prime ⁅ open-part x ∣ x ε S ⁆

\end{code}

If the pointless end has no points, a point of X_e can't avoid the
collar: otherwise it would restrict to a point of B. To see that the
restriction is completely prime, we add the collar to every family.

\begin{code}

 collar-family : Fam 𝓣 ⟨ B ⟩ → Fam 𝓣 Glued
 collar-family S = (𝟙 {𝓤₀} + index S) , cases (λ _ → collar) (λ i → ι (S [ i ]))

 ι-of-join-is-below : (S : Fam 𝓣 ⟨ B ⟩)
                    → (ι (⋁[ B ] S) ≤ᴳ (⋁[ Gl ] collar-family S)) holds
 ι-of-join-is-below S =
  ⋁[ O ]-upper ⁅ open-part x ∣ x ε collar-family S ⁆ (inl ⋆) ,
  ⋁[ B ]-least S
   ((⋁[ B ] ⁅ closed-part x ∣ x ε collar-family S ⁆) ,
    λ i → ⋁[ B ]-upper ⁅ closed-part x ∣ x ε collar-family S ⁆ (inr i))

 points-lie-in-the-collar-¬¬ : ¬ Point Xᴮ → (x : Point X)
                             → ¬¬ (pr₁ x collar holds)
 points-lie-in-the-collar-¬¬ B-has-no-points
  (ϕ , (ϕ-up , ϕ-top , ϕ-meet) , ϕ-prime) ν =
  B-has-no-points (ψ , (ψ-up , ψ-top , ψ-meet) , ψ-prime)
  where
   ψ : ⟨ B ⟩ → Ω 𝓣
   ψ d = ϕ (ι d)

   ψ-up : is-upwards-closed Xᴮ ψ holds
   ψ-up d e l = ϕ-up (ι d) (ι e) (≤-is-reflexive (poset-of O) 𝟏[ O ] , l)

   ψ-top : ψ 𝟏[ B ] holds
   ψ-top = ϕ-up 𝟏[ Gl ] (ι 𝟏[ B ])
            (≤-is-reflexive (poset-of O) 𝟏[ O ] ,
              ≤-is-reflexive (poset-of B) 𝟏[ B ])
            ϕ-top

   ψ-meet : closed-under-binary-meets Xᴮ ψ holds
   ψ-meet d e h k = ϕ-up (ι d ∧[ Gl ] ι e) (ι (d ∧[ B ] e))
                     (𝟏-is-top O _ , ≤-is-reflexive (poset-of B) (d ∧[ B ] e))
                     (ϕ-meet (ι d) (ι e) h k)

   ψ-prime : is-completely-prime Xᴮ ψ holds
   ψ-prime S h = ∥∥-rec ∥∥-is-prop γ
                  (ϕ-prime (collar-family S)
                    (ϕ-up _ _ (ι-of-join-is-below S) h))
    where
     γ : (Σ j ꞉ index (collar-family S) , ϕ (collar-family S [ j ]) holds)
       → ∃ i ꞉ index S , ψ (S [ i ]) holds
     γ (inl ⋆ , k) = 𝟘-elim (ν k)
     γ (inr i , k) = ∣ i , k ∣

 points-lie-in-the-collar : EM 𝓣 → ¬ Point Xᴮ → (x : Point X)
                          → pr₁ x collar holds
 points-lie-in-the-collar em B-has-no-points x =
  EM-gives-DNE em (pr₁ x collar holds) (holds-is-prop (pr₁ x collar))
   (points-lie-in-the-collar-¬¬ B-has-no-points x)

\end{code}

A point of X_e that lies in the collar comes from a point of O.

\begin{code}

 point-to-O : (x : Point X) → pr₁ x collar holds → Point Xᴼ
 point-to-O (ϕ , (ϕ-up , ϕ-top , ϕ-meet) , ϕ-prime) c =
  χ , (χ-up , c , χ-meet) , χ-prime
  where
   χ : ⟨ O ⟩ → Ω 𝓣
   χ V = ϕ (κ V)

   χ-up : is-upwards-closed Xᴼ χ holds
   χ-up V W l = ϕ-up (κ V) (κ W) (l , ≤-is-reflexive (poset-of B) 𝟎[ B ])

   χ-meet : closed-under-binary-meets Xᴼ χ holds
   χ-meet V W h k = ϕ-up (κ V ∧[ Gl ] κ W) (κ (V ∧[ O ] W))
                     (≤-is-reflexive (poset-of O) (V ∧[ O ] W) ,
                      ∧[ B ]-lower₁ 𝟎[ B ] 𝟎[ B ])
                     (ϕ-meet (κ V) (κ W) h k)

   χ-prime : is-completely-prime Xᴼ χ holds
   χ-prime S h = ϕ-prime ⁅ κ V ∣ V ε S ⁆
                  (ϕ-up (κ (⋁[ O ] S)) (⋁[ Gl ] ⁅ κ V ∣ V ε S ⁆)
                    (≤-is-reflexive (poset-of O) (⋁[ O ] S) , 𝟎-is-bottom B _)
                    h)

 point-to-O-is-section : (x : Point X) (c : pr₁ x collar holds) (y : Glued)
                       → (pr₁ x y holds
                          → pr₁ (point-to-O x c) (open-part y) holds)
                       × (pr₁ (point-to-O x c) (open-part y) holds
                          → pr₁ x y holds)
 point-to-O-is-section (ϕ , (ϕ-up , ϕ-top , ϕ-meet) , ϕ-prime) c y = f , g
  where
   f : ϕ y holds → ϕ (κ (open-part y)) holds
   f h = ϕ-up (y ∧[ Gl ] collar) (κ (open-part y))
          (∧[ O ]-lower₁ (open-part y) 𝟏[ O ] ,
            ∧[ B ]-lower₂ (closed-part y) 𝟎[ B ])
          (ϕ-meet y collar h c)

   g : ϕ (κ (open-part y)) holds → ϕ y holds
   g = ϕ-up (κ (open-part y)) y
        (≤-is-reflexive (poset-of O) (open-part y) ,
          𝟎-is-bottom B (closed-part y))

\end{code}

Hence, assuming excluded middle, if the pointless end has no points,
the points of X_e are exactly the points of O [1, Lemma 2.2(i)].

\begin{code}

 points-of-X-are-points-of-O : EM 𝓣 → ¬ Point Xᴮ → Point Xᴼ ≃ Point X
 points-of-X-are-points-of-O em B-has-no-points =
  qinveq point-from-O (back , η , ε)
  where
   collar-has-all-points = points-lie-in-the-collar em B-has-no-points

   back : Point X → Point Xᴼ
   back x = point-to-O x (collar-has-all-points x)

   η : back ∘ point-from-O ∼ id
   η q = to-point-＝ Xᴼ (λ V → id , id)

   ε : point-from-O ∘ back ∼ id
   ε x = to-point-＝ X (λ y → pr₂ (point-to-O-is-section x c y) ,
                              pr₁ (point-to-O-is-section x c y))
    where
     c = collar-has-all-points x

 collar-contains-every-point-but-is-not-𝟏
  : EM 𝓣
  → Cylinder-System B
  → 𝟎[ B ] ≠ 𝟏[ B ]
  → ((x : Point X) → pr₁ x collar holds) × (collar ≠ 𝟏[ Gl ])
 collar-contains-every-point-but-is-not-𝟏 em 𝒞 ν =
  points-lie-in-the-collar em (cylinder-locales-have-no-points 𝒞) ,
  collar-is-not-𝟏 ν

\end{code}

Every nonzero open contains a point [1, Lemma 2.2(ii)].

\begin{code}

 nonzero-opens-contain-points
  : ¬ (C 𝟎[ O ] holds)
  → ((V : ⟨ O ⟩) → V ≠ 𝟎[ O ] → ∃ q ꞉ Point Xᴼ , pr₁ q V holds)
  → (x : Glued) → x ≠ 𝟎[ Gl ] → ∃ p ꞉ Point X , pr₁ p x holds
 nonzero-opens-contain-points ν O-has-enough-points x x-is-nonzero =
  ∥∥-functor (λ (q , h) → point-from-O q , h)
   (O-has-enough-points (open-part x)
     (λ e → x-is-nonzero (glued-with-empty-open-part ν x e)))

\end{code}
