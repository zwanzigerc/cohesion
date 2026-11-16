import ToposPort.ClosedKernelPair

/-!
# Maps invisible to the closed reflection

A map is local here when precomposition induces bijections into every closed
object. Pushouts adding only objects over `P` have this property, as do all
their pullbacks in an adhesive category. In particular this applies to units
and to the diagonal inclusions into their explicitly computed kernel pairs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ToposPort.ClosedSubtopos

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable (P : C)

/-- Precomposition with this map gives a bijection into every closed object. -/
def LocalMap {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ (B : C), IsClosed P B → Function.Bijective (fun g : Y ⟶ B => f ≫ g)

theorem LocalMap.hom_ext {X Y B : C} {f : X ⟶ Y} (hf : LocalMap P f)
    (hB : IsClosed P B) {g h : Y ⟶ B} (e : f ≫ g = f ≫ h) : g = h :=
  (hf B hB).injective e

/-- Extension along a local map into a closed object. -/
def LocalMap.extend {X Y B : C} {f : X ⟶ Y} (hf : LocalMap P f)
    (hB : IsClosed P B) (g : X ⟶ B) : Y ⟶ B :=
  Classical.choose ((hf B hB).surjective g)

@[reassoc (attr := simp)]
theorem LocalMap.comp_extend {X Y B : C} {f : X ⟶ Y} (hf : LocalMap P f)
    (hB : IsClosed P B) (g : X ⟶ B) : f ≫ hf.extend P hB g = g :=
  Classical.choose_spec ((hf B hB).surjective g)

theorem LocalMap.comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : LocalMap P f) (hg : LocalMap P g) : LocalMap P (f ≫ g) := by
  intro B hB
  simpa [Function.comp_def, Category.assoc] using (hf B hB).comp (hg B hB)

/-- A pushout that adds an object over `P` is invisible to all closed objects. -/
theorem localMap_of_isPushout {W X U Y : C} {a : W ⟶ X} {b : W ⟶ U}
    {f : X ⟶ Y} {g : U ⟶ Y} (h : IsPushout a b f g) (p : U ⟶ P) :
    LocalMap P f := by
  intro B hB
  constructor
  · intro k l hk
    apply h.hom_ext hk
    exact closed_hom_ext P hB p _ _
  · intro k
    exact ⟨h.desc k (p ≫ point P hB)
      (closed_hom_ext P hB (b ≫ p) _ _), by simp⟩

variable [HasPullbacks C] [Adhesive C]

/-- The preceding class of maps remains invisible after arbitrary pullback. -/
theorem localMap_pullback_of_isPushout {W X U Y Z : C} {a : W ⟶ X} {b : W ⟶ U}
    {f : X ⟶ Y} {g : U ⟶ Y} [Mono a] (h : IsPushout a b f g)
    (p : U ⟶ P) (k : Z ⟶ Y) : LocalMap P (pullback.snd f k) := by
  have hh := (IsPullback.of_hasPullback f k).flip
  have hi := (IsPullback.of_hasPullback g k).flip
  obtain ⟨W', a', b', w', _, _, h'⟩ :=
    (Adhesive.van_kampen h).exists_cube_filling hh hi
  exact localMap_of_isPushout P h' (pullback.fst g k ≫ p)

variable [HasPushouts C] (hP : IsSubterminal P)

include hP in
/-- Every pullback of a closed-reflection unit is a local map. -/
theorem unit_pullback_local {A Z : C} (k : Z ⟶ object P A) :
    LocalMap P (pullback.snd (unit P A) k) := by
  have := mono_snd P hP A
  exact localMap_pullback_of_isPushout P
    (IsPushout.of_hasPushout (prod.snd : P ⨯ A ⟶ A) prod.fst) (𝟙 P) k

include hP in
/-- Every pullback of the diagonal into the unit kernel pair is a local map. -/
theorem relation_diagonal_pullback_local {A Z : C} (k : Z ⟶ relation P A) :
    LocalMap P (pullback.snd (pushout.inl _ _ : A ⟶ relation P A) k) := by
  have := mono_snd P hP A
  exact localMap_pullback_of_isPushout P
    (IsPushout.of_hasPushout (prod.snd : P ⨯ A ⟶ A) (prod.map (𝟙 P) (diag A)))
    prod.fst k

include hP in
/-- Every generalized point of a reflected object lifts along a local map. -/
theorem unit_locally_lift {A Z : C} (u : Z ⟶ object P A) :
    ∃ (Q : C) (m : Q ⟶ Z), LocalMap P m ∧
      ∃ (p : Q ⟶ A), m ≫ u = p ≫ unit P A := by
  exact ⟨pullback (unit P A) u, pullback.snd _ _, unit_pullback_local P hP u,
    pullback.fst _ _, pullback.condition.symm⟩

include hP in
/-- Two generalized points can be lifted simultaneously along a local map. -/
theorem unit_locally_lift_two {A B Z : C}
    (u : Z ⟶ object P A) (v : Z ⟶ object P B) :
    ∃ (Q : C) (m : Q ⟶ Z), LocalMap P m ∧
      ∃ (p : Q ⟶ A) (q : Q ⟶ B),
        m ≫ u = p ≫ unit P A ∧ m ≫ v = q ≫ unit P B := by
  obtain ⟨Q, m, hm, p, hp⟩ := unit_locally_lift P hP u
  obtain ⟨R, n, hn, q, hq⟩ := unit_locally_lift P hP (m ≫ v)
  refine ⟨R, n ≫ m, hn.comp P hm, n ≫ p, q, ?_, ?_⟩
  · simp [Category.assoc, hp]
  · simpa [Category.assoc] using hq

include hP in
/-- Equality after reflection is equality after passage along a local map. -/
theorem unit_eq_locally {A Z : C} (f g : Z ⟶ A)
    (h : f ≫ unit P A = g ≫ unit P A) :
    ∃ (Q : C) (m : Q ⟶ Z), LocalMap P m ∧ m ≫ f = m ≫ g := by
  let t : Z ⟶ relation P A := (unit_kernelPair P A hP).lift f g h
  let d : A ⟶ relation P A := pushout.inl _ _
  refine ⟨pullback d t, pullback.snd d t, relation_diagonal_pullback_local P hP t, ?_⟩
  have h₁ : pullback.fst d t = pullback.snd d t ≫ f := by
    have hh := pullback.condition_assoc (f := d) (g := t) (relationSnd P A)
    simpa [t, d, relationSnd] using hh
  have h₂ : pullback.fst d t = pullback.snd d t ≫ g := by
    have hh := pullback.condition_assoc (f := d) (g := t) (relationFst P A)
    simpa [t, d, relationFst] using hh
  exact h₁.symm.trans h₂

variable [PreservesColimitsOfShape WalkingSpan (prod.functor.obj P)]

include hP in
/-- The closed reflector preserves monomorphisms. -/
theorem functor_map_mono {A B : C} (f : A ⟶ B) [Mono f] : Mono ((functor P).map f) where
  right_cancellation {Z} u v huv := by
    obtain ⟨Q, m, hm, p, q, hp, hq⟩ := unit_locally_lift_two P hP u v
    have hh : (p ≫ f) ≫ unit P B = (q ≫ f) ≫ unit P B := by
      rw [Category.assoc, Category.assoc, ← unit_map P f,
        ← Category.assoc, ← hp, Category.assoc, huv, ← Category.assoc, hq]
      simp [Category.assoc]
    obtain ⟨R, n, hn, heq⟩ := unit_eq_locally P hP (p ≫ f) (q ≫ f) hh
    have hpq : n ≫ p = n ≫ q := by
      apply (cancel_mono f).1
      simpa [Category.assoc] using heq
    apply hm.hom_ext P (object_isClosed P hP A)
    apply hn.hom_ext P (object_isClosed P hP A)
    rw [hp, hq, ← Category.assoc, hpq, Category.assoc]

end ToposPort.ClosedSubtopos
