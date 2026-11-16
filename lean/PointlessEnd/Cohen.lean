import PointlessEnd.Words
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.CompleteLattice.Lemmas
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Set.Lattice.Order

/-!
# The Cohen frame `P`

The endpoint frame of the pointless end is the binary-tree Cohen frame of the Agda
development (`gist.RealCohesion.CohenFrame`): regular sets of finite binary words.

For a set `A` of words, `reg A` is the set of words `s` above which `A` is dense: every
extension of `s` has a further extension in `A`. A set is *regular* when `reg A = A`.
Regular sets are upward closed; with inclusion they form a frame, whose joins are
regularized unions and whose meets are intersections. (This is the regular-open algebra
of Cantor space, presented combinatorially; the isomorphism is not needed.)

Cylinders and their complements:

* `cyl s` = words extending `s`; `acyl s` = words incompatible with `s`.
* `cyl [] = ⊤`, `acyl [] = ⊥`, `cyl s ≤ cyl (s⌢0) ⊔ cyl (s⌢1)`, `cyl s ⊓ acyl s = ⊥`;
* `acyl (s⌢0) ⊓ acyl (s⌢1) = acyl s` (splitting), `acyl (s⌢0) ⊔ acyl (s⌢1) = ⊤` (cover);
* `⨆ₙ acyl (wₙ) = ⊤` for every sequence of words of unbounded length, in particular along
  every branch `α ↾ n` (bar);
* the words of a fixed length `N` have `⋂ acyl s = ∅` (no uniform bound).

Consequently `P` has no points (`no_point`): a completely prime filter containing `⊤`
would follow a branch through the cylinders, and the bar identity along that branch
contradicts primeness.
-/

namespace PointlessEnd

open Set

/-! ### Regularization -/

/-- `reg A`: the words above which `A` is dense. -/
def reg (A : Set Word) : Set Word := {s | ∀ w, s <+: w → ∃ v, w <+: v ∧ v ∈ A}

/-- Upward closure under extension. -/
def Upward (A : Set Word) : Prop := ∀ ⦃s w⦄, s ∈ A → s <+: w → w ∈ A

theorem reg_upward (A : Set Word) : Upward (reg A) :=
  fun _ _ hs hsw w hw => hs w (hsw.trans hw)

theorem subset_reg {A : Set Word} (hA : Upward A) : A ⊆ reg A :=
  fun _ hs w hw => ⟨w, List.prefix_refl _, hA hs hw⟩

theorem reg_mono {A B : Set Word} (h : A ⊆ B) : reg A ⊆ reg B := fun _ hs w hw =>
  let ⟨v, hv, hvA⟩ := hs w hw
  ⟨v, hv, h hvA⟩

theorem reg_reg (A : Set Word) : reg (reg A) = reg A := by
  refine Subset.antisymm (fun s hs w hw => ?_) (subset_reg (reg_upward A))
  obtain ⟨v, hwv, hv⟩ := hs w hw
  obtain ⟨v', hvv', hv'⟩ := hv v (List.prefix_refl _)
  exact ⟨v', hwv.trans hvv', hv'⟩

theorem inter_reg_subset {A B : Set Word} (hA : Upward A) : A ∩ reg B ⊆ reg (A ∩ B) := by
  rintro s ⟨hsA, hsB⟩ w hw
  obtain ⟨v, hwv, hv⟩ := hsB w hw
  exact ⟨v, hwv, hA hsA (hw.trans hwv), hv⟩

theorem reg_empty : reg (∅ : Set Word) = ∅ := by
  ext s
  simp only [mem_empty_iff_false, iff_false]
  intro hs
  obtain ⟨v, -, hv⟩ := hs s (List.prefix_refl _)
  exact hv

theorem reg_univ : reg (univ : Set Word) = univ :=
  eq_univ_of_forall fun _ w _ => ⟨w, List.prefix_refl _, trivial⟩

/-! ### The frame -/

/-- **The Cohen frame**: regular sets of finite binary words. -/
@[ext] structure P where
  /-- The underlying set of words. -/
  carrier : Set Word
  reg_eq : reg carrier = carrier

namespace P

theorem upward (a : P) : Upward a.carrier := by
  have := reg_upward a.carrier
  rwa [a.reg_eq] at this

theorem reg_subset {A : Set Word} {b : P} (h : A ⊆ b.carrier) : reg A ⊆ b.carrier := by
  have := reg_mono h
  rwa [b.reg_eq] at this

theorem subset_reg_of {A : Set Word} {a : P} (h : a.carrier ⊆ A) : a.carrier ⊆ reg A := by
  have := reg_mono h
  rwa [a.reg_eq] at this

/-- The regularization of a set, as an element of `P`. -/
def ofReg (A : Set Word) : P := ⟨reg A, reg_reg A⟩

/-- An upward set closed under regularization. -/
def mk' (A : Set Word) (hA : Upward A) (h : reg A ⊆ A) : P :=
  ⟨A, Subset.antisymm h (subset_reg hA)⟩

instance : PartialOrder P where
  le a b := a.carrier ⊆ b.carrier
  le_refl _ := subset_rfl
  le_trans _ _ _ := Subset.trans
  le_antisymm _ _ h₁ h₂ := P.ext (Subset.antisymm h₁ h₂)

theorem le_def {a b : P} : a ≤ b ↔ a.carrier ⊆ b.carrier := Iff.rfl

/-- Intersections of regular sets are regular. -/
def interAll (S : Set P) : P :=
  mk' (⋂ a ∈ S, a.carrier)
    (fun _ _ hs hsw => mem_iInter₂.mpr fun a ha => a.upward (mem_iInter₂.mp hs a ha) hsw)
    (fun _ hs => mem_iInter₂.mpr fun _ ha => reg_subset (biInter_subset_of_mem ha) hs)

/-- Binary intersections. -/
def inter (a b : P) : P :=
  mk' (a.carrier ∩ b.carrier) (fun _ _ hs hsw => ⟨a.upward hs.1 hsw, b.upward hs.2 hsw⟩)
    (fun _ hs => ⟨reg_subset inter_subset_left hs, reg_subset inter_subset_right hs⟩)

instance : CompleteLattice P where
  sup a b := ofReg (a.carrier ∪ b.carrier)
  le_sup_left _ _ := subset_reg_of subset_union_left
  le_sup_right _ _ := subset_reg_of subset_union_right
  sup_le _ _ _ hac hbc := reg_subset (union_subset hac hbc)
  inf := inter
  inf_le_left _ _ := inter_subset_left
  inf_le_right _ _ := inter_subset_right
  le_inf _ _ _ hab hac := subset_inter hab hac
  sSup S := ofReg (⋃ a ∈ S, a.carrier)
  isLUB_sSup _ := ⟨fun _ ha => subset_reg_of (subset_biUnion_of_mem ha),
    fun _ hb => reg_subset (iUnion₂_subset hb)⟩
  sInf := interAll
  isGLB_sInf _ := ⟨fun _ ha => biInter_subset_of_mem ha, fun _ hb => subset_iInter₂ hb⟩
  top := ⟨univ, reg_univ⟩
  bot := ⟨∅, reg_empty⟩
  le_top _ := subset_univ _
  bot_le _ := empty_subset _

@[simp] theorem carrier_inf (a b : P) : (a ⊓ b).carrier = a.carrier ∩ b.carrier := rfl

@[simp] theorem carrier_sup (a b : P) : (a ⊔ b).carrier = reg (a.carrier ∪ b.carrier) := rfl

@[simp] theorem carrier_sSup (S : Set P) : (sSup S).carrier = reg (⋃ a ∈ S, a.carrier) := rfl

@[simp] theorem carrier_sInf (S : Set P) : (sInf S).carrier = ⋂ a ∈ S, a.carrier := rfl

@[simp] theorem carrier_top : (⊤ : P).carrier = univ := rfl

@[simp] theorem carrier_bot : (⊥ : P).carrier = ∅ := rfl

theorem carrier_iSup {ι : Sort*} (f : ι → P) :
    (⨆ i, f i).carrier = reg (⋃ i, (f i).carrier) := by
  change (sSup (range f)).carrier = _
  rw [carrier_sSup]
  congr 1
  ext w
  simp only [mem_iUnion, mem_range, exists_prop]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, hw⟩
    exact ⟨i, hw⟩
  · rintro ⟨i, hw⟩
    exact ⟨f i, ⟨i, rfl⟩, hw⟩

theorem carrier_iInf {ι : Sort*} (f : ι → P) : (⨅ i, f i).carrier = ⋂ i, (f i).carrier := by
  change (sInf (range f)).carrier = _
  rw [carrier_sInf]
  ext w
  simp only [mem_iInter, mem_range, forall_exists_index, forall_apply_eq_imp_iff]

theorem eq_top_iff' {a : P} : a = ⊤ ↔ ∀ w, w ∈ a.carrier := by
  constructor
  · rintro rfl w
    trivial
  · intro h
    exact P.ext (eq_univ_of_forall h)

theorem eq_bot_iff' {a : P} : a = ⊥ ↔ ∀ w, w ∉ a.carrier := by
  constructor
  · rintro rfl w hw
    exact hw
  · intro h
    exact P.ext (eq_empty_of_forall_notMem h)

theorem bot_ne_top : (⊥ : P) ≠ ⊤ := by
  intro h
  have : ([] : Word) ∈ (⊥ : P).carrier := by rw [h]; trivial
  exact this

/-- **`P` is a frame.** -/
instance : Order.Frame P := Order.Frame.ofMinimalAxioms ⟨fun a S => by
  rw [le_def]
  intro s hs
  have hs' : s ∈ a.carrier ∩ reg (⋃ b ∈ S, b.carrier) := hs
  refine reg_subset ?_ (inter_reg_subset a.upward hs')
  rintro w ⟨hwa, hw⟩
  obtain ⟨b, hb, hwb⟩ := mem_iUnion₂.mp hw
  exact (le_iSup₂ (f := fun b (_ : b ∈ S) => a ⊓ b) b hb : a ⊓ b ≤ _) ⟨hwa, hwb⟩⟩

end P

/-! ### Cylinders -/

/-- Words extending `s`. -/
def cylSet (s : Word) : Set Word := {w | s <+: w}

/-- Words incompatible with `s`. -/
def acylSet (s : Word) : Set Word := {w | ¬ Compat s w}

theorem reg_cylSet (s : Word) : reg (cylSet s) = cylSet s := by
  refine Subset.antisymm (fun w hw => ?_) (subset_reg fun _ _ h h' => List.IsPrefix.trans h h')
  by_contra h
  obtain ⟨u, hwu, hu⟩ := exists_ext_incompat h
  obtain ⟨v, huv, hv⟩ := hw u hwu
  exact hu (compat_of_prefix hv huv)

theorem reg_acylSet (s : Word) : reg (acylSet s) = acylSet s := by
  refine Subset.antisymm (fun w hw hc => ?_) (subset_reg fun _ _ h h' => incompat_mono h h')
  rcases hc with hc | hc
  · obtain ⟨v, hwv, hv⟩ := hw w (List.prefix_refl _)
    exact hv (Or.inl (hc.trans hwv))
  · obtain ⟨v, hsv, hv⟩ := hw s hc
    exact hv (Or.inl hsv)

/-- The cylinder of `s`. -/
def cyl (s : Word) : P := ⟨cylSet s, reg_cylSet s⟩

/-- The complement of the cylinder of `s`. -/
def acyl (s : Word) : P := ⟨acylSet s, reg_acylSet s⟩

theorem cyl_nil : cyl [] = ⊤ :=
  P.eq_top_iff'.mpr fun _ => List.nil_prefix

theorem acyl_nil : acyl [] = ⊥ :=
  P.eq_bot_iff'.mpr fun _ hw => hw (Or.inl List.nil_prefix)

theorem cyl_inf_acyl (s : Word) : cyl s ⊓ acyl s = ⊥ :=
  P.eq_bot_iff'.mpr fun _ hw => hw.2 (Or.inl hw.1)

/-- A cylinder is covered by the cylinders of its two children. -/
theorem cyl_le_sup (s : Word) : cyl s ≤ cyl (snoc s false) ⊔ cyl (snoc s true) := by
  rw [P.le_def]
  intro w (hw : s <+: w) w' hww'
  refine ⟨snoc w' false, prefix_snoc _ _, ?_⟩
  have hs : s <+: snoc w' false := hw.trans (hww'.trans (prefix_snoc _ _))
  have hne : snoc w' false ≠ s := by
    intro h
    have h1 := congrArg List.length h
    have h2 := hw.length_le
    have h3 := hww'.length_le
    simp only [length_snoc] at h1
    omega
  obtain ⟨b, hb⟩ := snoc_prefix_of_ne hs hne
  cases b
  · exact Or.inl hb
  · exact Or.inr hb

/-- A word incompatible with `s` is incompatible with every extension of `s`. -/
theorem acyl_mono {s s' : Word} (h : s <+: s') : acyl s ≤ acyl s' := by
  rw [P.le_def]
  intro w hw hc
  rcases hc with hc | hc
  · exact hw (Or.inl (h.trans hc))
  · exact hw (compat_of_prefix h hc)

/-- **Splitting.** -/
theorem acyl_inf_children (s : Word) : acyl (snoc s false) ⊓ acyl (snoc s true) = acyl s := by
  apply le_antisymm
  · rw [P.le_def]
    rintro w ⟨h0, h1⟩ hc
    rcases hc with hc | hc
    · by_cases he : w = s
      · subst he
        exact h0 (Or.inr (prefix_snoc _ _))
      · obtain ⟨b, hb⟩ := snoc_prefix_of_ne hc he
        cases b
        · exact h0 (Or.inl hb)
        · exact h1 (Or.inl hb)
    · exact h0 (Or.inr (hc.trans (prefix_snoc _ _)))
  · exact le_inf (acyl_mono (prefix_snoc _ _)) (acyl_mono (prefix_snoc _ _))

/-- **Sibling cover.** -/
theorem acyl_sup_children (s : Word) : acyl (snoc s false) ⊔ acyl (snoc s true) = ⊤ := by
  refine P.eq_top_iff'.mpr fun w w' hww' => ?_
  by_cases h0 : Compat (snoc s false) w'
  · rcases h0 with h0 | h0
    · -- `w'` extends the left child, so it is incompatible with the right one
      refine ⟨w', List.prefix_refl _, Or.inr fun h1 => ?_⟩
      rcases h1 with h1 | h1
      · exact not_compat_children s (compat_of_prefix h0 h1)
      · exact not_compat_children s (Or.inl (h0.trans h1))
    · -- `w'` is a prefix of the left child: extend it to the left child
      refine ⟨snoc s false, h0, Or.inr fun h1 => ?_⟩
      exact not_compat_children s (compat_symm h1)
  · exact ⟨w', List.prefix_refl _, Or.inl h0⟩

/-- **Bar.** Along any sequence of words of unbounded length, the complements of the
cylinders are jointly dense. -/
theorem iSup_acyl_eq_top (w : ℕ → Word) (hw : ∀ m, ∃ n, m < (w n).length) :
    ⨆ n, acyl (w n) = ⊤ := by
  refine P.eq_top_iff'.mpr fun _ => ?_
  rw [P.carrier_iSup]
  intro u' _
  obtain ⟨n, hn⟩ := hw u'.length
  have hnp : ¬ w n <+: u' := fun h => by
    have := h.length_le
    omega
  obtain ⟨v, hv, hvi⟩ := exists_ext_incompat hnp
  exact ⟨v, hv, mem_iUnion.mpr ⟨n, hvi⟩⟩

theorem iSup_acyl_restrict (α : ℕ → Bool) : ⨆ n, acyl (restrict α n) = ⊤ :=
  iSup_acyl_eq_top _ fun m => ⟨m + 1, by simp⟩

/-- Every word is compatible with some word of length `N`. -/
theorem exists_compat_length (w : Word) (N : ℕ) : ∃ s : Word, s.length = N ∧ Compat s w := by
  rcases Nat.lt_or_ge w.length N with h | h
  · refine ⟨w ++ List.replicate (N - w.length) false, ?_, Or.inr (List.prefix_append _ _)⟩
    simp only [List.length_append, List.length_replicate]
    omega
  · exact ⟨w.take N, by simp [h], Or.inl (List.take_prefix _ _)⟩

/-- **No uniform bound.** No word is incompatible with all words of a fixed length. -/
theorem iInf_acyl_length (N : ℕ) : ⨅ (s : {s : Word // s.length = N}), acyl s.1 = ⊥ := by
  refine P.eq_bot_iff'.mpr fun w hw => ?_
  rw [P.carrier_iInf] at hw
  obtain ⟨s, hs, hc⟩ := exists_compat_length w N
  exact mem_iInter.mp hw ⟨s, hs⟩ hc

/-! ### No points -/

/-- The branch chosen by a predicate on `P`: go left whenever the left cylinder satisfies
it. -/
noncomputable def branch (p : P → Prop) : ℕ → Word
  | 0 => []
  | n + 1 => by
    classical
    exact if p (cyl (snoc (branch p n) false)) then snoc (branch p n) false
      else snoc (branch p n) true

theorem branch_length (p : P → Prop) : ∀ n, (branch p n).length = n
  | 0 => rfl
  | n + 1 => by
    classical
    simp only [branch]
    split_ifs <;> simp [branch_length p n]

/-- **`P` has no points.** A predicate preserving binary meets and arbitrary joins (a
completely prime filter) and containing `⊤` does not exist. -/
theorem no_point (p : P → Prop) (hinf : ∀ a b, p a → p b → p (a ⊓ b))
    (hmono : ∀ a b, a ≤ b → p a → p b)
    (hsup : ∀ S : Set P, p (sSup S) → ∃ a ∈ S, p a) (htop : p ⊤) : False := by
  classical
  have hcyl : ∀ n, p (cyl (branch p n)) := by
    intro n
    induction n with
    | zero => simpa [branch, cyl_nil] using htop
    | succ n ih =>
      have h2 := hmono _ _ (cyl_le_sup (branch p n)) ih
      have h3 : p (sSup {cyl (snoc (branch p n) false), cyl (snoc (branch p n) true)}) := by
        rwa [sSup_pair]
      obtain ⟨a, ha, hpa⟩ := hsup _ h3
      simp only [branch]
      split_ifs with hl
      · exact hl
      · rcases ha with rfl | rfl
        · exact absurd hpa hl
        · exact hpa
  have hbar := iSup_acyl_eq_top (branch p) fun m => ⟨m + 1, by rw [branch_length]; omega⟩
  have : p (sSup (range fun n => acyl (branch p n))) := by
    change p (⨆ n, acyl (branch p n))
    rw [hbar]
    exact htop
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hsup _ this
  have hbot := hinf _ _ (hcyl n) hn
  rw [cyl_inf_acyl, ← sSup_empty] at hbot
  obtain ⟨a, ha, -⟩ := hsup _ hbot
  exact ha

end PointlessEnd
