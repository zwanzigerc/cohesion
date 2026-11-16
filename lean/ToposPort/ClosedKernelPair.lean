import ToposPort.ClosedConservativity

/-!
# The kernel pair of the closed-reflection unit

The unit identifies exactly pairs that are equal or lie over `P`. Categorically,
its kernel pair is the union of the diagonal and `P × (A × A)` in `A × A`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ToposPort.ClosedSubtopos

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] [HasPushouts C]
variable (P : C) (A : C)

/-- The union of the diagonal of `A` with all pairs over `P`. -/
abbrev relation := pushout (prod.snd : P ⨯ A ⟶ A) (prod.map (𝟙 P) (diag A))

/-- Inclusion of the relation into pairs. -/
def relationMap : relation P A ⟶ A ⨯ A :=
  pushout.desc (diag A) prod.snd (by simp)

abbrev relationFst : relation P A ⟶ A := relationMap P A ≫ prod.fst
abbrev relationSnd : relation P A ⟶ A := relationMap P A ≫ prod.snd

@[reassoc (attr := simp)] theorem relation_inl_map :
    pushout.inl _ _ ≫ relationMap P A = diag A := by simp [relationMap]
@[reassoc (attr := simp)] theorem relation_inr_map :
    pushout.inr _ _ ≫ relationMap P A = (prod.snd : P ⨯ (A ⨯ A) ⟶ _) := by
  simp [relationMap]

variable [Adhesive C] (hP : IsSubterminal P)

include hP in
/-- The union relation embeds into `A × A`. -/
theorem relationMap_mono : Mono (relationMap P A) := by
  have := mono_snd P hP (A ⨯ A)
  convert (IsPushout.of_hasPushout (prod.snd : P ⨯ A ⟶ A)
    (prod.map (𝟙 P) (diag A))).desc_mono_of_isPullback
    (product_snd_isPullback P (diag A)) using 1
  apply pushout.hom_ext <;> simp [relationMap]

include hP in
theorem relation_open_isPullback :
    IsPullback (pushout.inr _ _ : P ⨯ (A ⨯ A) ⟶ relation P A)
      (prod.map (𝟙 P) prod.fst) (relationFst P A) prod.snd := by
  have := relationMap_mono P A hP
  have h : IsPullback (pushout.inr _ _ : P ⨯ (A ⨯ A) ⟶ relation P A)
      (𝟙 _) (relationMap P A) prod.snd :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  simpa using h.paste_vert (product_snd_isPullback P (prod.fst : A ⨯ A ⟶ A))

omit [Adhesive C] in
/-- Collapsing the second-coordinate pairs recovers `A`. -/
theorem relation_projection_isPushout :
    IsPushout (pushout.inr _ _ : P ⨯ (A ⨯ A) ⟶ relation P A)
      (prod.map (𝟙 P) prod.snd) (relationSnd P A) prod.snd := by
  have h : IsPushout
      (prod.map (𝟙 P) (diag A) ≫ prod.map (𝟙 P) prod.snd)
      (prod.snd : P ⨯ A ⟶ A) prod.snd
      ((pushout.inl _ _ : A ⟶ relation P A) ≫ relationSnd P A) := by
    have eq₁ : prod.map (𝟙 P) (diag A) ≫
        prod.map (𝟙 P) (prod.snd : A ⨯ A ⟶ A) = 𝟙 (P ⨯ A) := by ext <;> simp
    rw [eq₁]
    simpa [relationSnd] using
      (IsPushout.of_horiz_isIso (f := 𝟙 (P ⨯ A)) (inr := 𝟙 A)
        (inl := (prod.snd : P ⨯ A ⟶ A)) (g := prod.snd) ⟨by simp⟩)
  exact (h.of_left (by simp [relationSnd])
    (IsPushout.of_hasPushout (prod.snd : P ⨯ A ⟶ A)
      (prod.map (𝟙 P) (diag A))).flip).flip

include hP in
omit [HasPushouts C] [Adhesive C] in
/-- Pairs over a subterminal form the kernel pair of the projection to `P`. -/
theorem open_pair_isPullback :
    IsPullback (prod.map (𝟙 P) (prod.snd : A ⨯ A ⟶ A))
      (prod.map (𝟙 P) prod.fst) prod.fst (prod.fst : P ⨯ A ⟶ P) := by
  refine IsPullback.mk' (by simp) ?_ ?_
  · intro T f g h₁ h₂
    apply prod.hom_ext
    · exact hP _ _
    · apply prod.hom_ext
      · have hh := congrArg (fun k => k ≫ prod.snd) h₂
        simpa using hh
      · have hh := congrArg (fun k => k ≫ prod.snd) h₁
        simpa using hh
  · intro T a b h
    refine ⟨prod.lift (a ≫ prod.fst)
      (prod.lift (b ≫ prod.snd) (a ≫ prod.snd)), ?_, ?_⟩
    · ext <;> simp
    · apply prod.hom_ext
      · simpa using h
      · simp

include hP in
/-- The closed-reflection unit has exactly the relation of equality or membership in `P`. -/
theorem unit_kernelPair : IsKernelPair (unit P A) (relationSnd P A) (relationFst P A) := by
  have := mono_snd P hP A
  have w : relationSnd P A ≫ unit P A = relationFst P A ≫ unit P A := by
    apply pushout.hom_ext
    · simp [relationSnd, relationFst]
    · simp only [Category.assoc, relationSnd, relationFst, relation_inr_map_assoc]
      rw [← prod.map_snd_assoc (𝟙 P) (prod.snd : A ⨯ A ⟶ A)]
      rw [← prod.map_snd_assoc (𝟙 P) (prod.fst : A ⨯ A ⟶ A)]
      simp only [unit, pushout.condition, prod.map_fst_assoc,
        Category.id_comp]
  have h := Adhesive.van_kampen (IsPushout.of_hasPushout
    (prod.snd : P ⨯ A ⟶ A) prod.fst)
  exact ((h (pushout.inr _ _) (prod.map (𝟙 P) prod.snd)
    (relationSnd P A) prod.snd (prod.map (𝟙 P) prod.fst)
    (relationFst P A) prod.fst (unit P A)
    (relation_open_isPullback P A hP) (open_pair_isPullback P A hP)
    ⟨w⟩ ⟨pushout.condition⟩ (relation_projection_isPushout P A).toCommSq).mp
      (relation_projection_isPushout P A)).1

end ToposPort.ClosedSubtopos
