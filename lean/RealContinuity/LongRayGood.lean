import RealContinuity.LongRayMaps
import RealContinuity.GoodSpaces

/-!
# The primitive spaces are good

`L`, its tails, the Sierpiński space, `ℝ` and the point satisfy the inductive
invariant `Good`: connected, with a neighbourhood basis of connected open sets
of pairwise finite height.

* Order-convex sets of finite points of `L` are path connected.
* A tail `(a, ∞]` is connected and has pairwise height at most two: its finite
  part is dense and path connected.
-/

noncomputable section

open Set Topology Filter unitInterval

namespace RealContinuity

/-! ### Order-convex neighbourhoods in an order topology -/

theorem exists_ordConnected_open {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] {x : α} {N : Set α} (hN : N ∈ 𝓝 x) :
    ∃ W : Set α, IsOpen W ∧ x ∈ W ∧ W ⊆ N ∧ W.OrdConnected := by
  by_cases hl : ∃ l, l < x
  · by_cases hu : ∃ u, x < u
    · obtain ⟨l, u, hxlu, hsub⟩ := (mem_nhds_iff_exists_Ioo_subset' hl hu).mp hN
      exact ⟨Ioo l u, isOpen_Ioo, hxlu, hsub, ordConnected_Ioo⟩
    · push Not at hu
      obtain ⟨l₀, hl₀⟩ := hl
      obtain ⟨l, ⟨-, hlx⟩, hsub⟩ := exists_Ioc_subset_of_mem_nhds' hN hl₀
      have : Ioc l x = Ioi l := by
        ext y; simp only [mem_Ioc, mem_Ioi, and_iff_left_iff_imp]; exact fun _ => hu y
      rw [this] at hsub
      exact ⟨Ioi l, isOpen_Ioi, hlx, hsub, ordConnected_Ioi⟩
  · push Not at hl
    by_cases hu : ∃ u, x < u
    · obtain ⟨u₀, hu₀⟩ := hu
      obtain ⟨u, ⟨hxu, -⟩, hsub⟩ := exists_Ico_subset_of_mem_nhds' hN hu₀
      have : Ico x u = Iio u := by
        ext y; simp only [mem_Ico, mem_Iio, and_iff_right_iff_imp]; exact fun _ => hl y
      rw [this] at hsub
      exact ⟨Iio u, isOpen_Iio, hxu, hsub, ordConnected_Iio⟩
    · push Not at hu
      have huniv : N = univ := by
        ext y; simp only [mem_univ, iff_true]
        have : y = x := le_antisymm (hu y) (hl y)
        rw [this]; exact mem_of_mem_nhds hN
      exact ⟨univ, isOpen_univ, mem_univ x, huniv ▸ subset_rfl, ordConnected_univ⟩

/-! ### Path-connectedness from order-convexity -/

/-- A point of `L` is finite. -/
def IsFin (x : L) : Prop := x ≠ ⊤

theorem isFin_iff {x : L} : IsFin x ↔ ∃ y : L₀, (y : L) = x := WithTop.ne_top_iff_exists

/-- Order-convex sets of finite points of `L` are path connected (when nonempty). -/
theorem isPathConnected_of_ordConnected {S : Set L} (hS : S.OrdConnected)
    (hfin : ∀ x ∈ S, IsFin x) (hne : S.Nonempty) : IsPathConnected S := by
  obtain ⟨x₀, hx₀⟩ := hne
  refine ⟨x₀, hx₀, fun {y} hy => ?_⟩
  obtain ⟨x, rfl⟩ := isFin_iff.mp (hfin _ hx₀)
  obtain ⟨y', rfl⟩ := isFin_iff.mp (hfin _ hy)
  obtain ⟨γ, h0, h1, hγ⟩ := exists_path_between x y'
  refine ⟨⟨γ, h0, h1⟩, fun t => ?_⟩
  have hmin : min (x : L) y' ∈ S := by
    rcases min_choice (x : L) y' with h | h <;> rw [h] <;> assumption
  have hmax : max (x : L) y' ∈ S := by
    rcases max_choice (x : L) y' with h | h <;> rw [h] <;> assumption
  exact hS.out hmin hmax (hγ t)

/-- A path-connected space has pairwise height one. -/
theorem PairwiseFiniteHeight.of_pathConnected {X : TopCat.{0}} [PathConnectedSpace X] :
    PairwiseFiniteHeight X :=
  fun x y => FiniteHeight.of_joined (PathConnectedSpace.joined x y)

/-- A path-connected subset gives a path-connected subspace. -/
theorem pathConnectedSpace_of_isPathConnected {X : Type} [TopologicalSpace X] {S : Set X}
    (h : IsPathConnected S) : PathConnectedSpace S :=
  isPathConnected_iff_pathConnectedSpace.mp h

/-! ### Tails -/

/-- The finite points of `L` are dense. -/
theorem dense_finite : Dense {x : L | IsFin x} := by
  intro x
  by_cases hx : IsFin x
  · exact subset_closure hx
  · have hx' : x = ⊤ := not_not.mp hx
    subst hx'
    rw [mem_closure_iff_nhds]
    intro N hN
    obtain ⟨y, hy⟩ := exists_coe_mem_of_isOpen (isOpen_interior) (mem_interior_iff_mem_nhds.mpr hN)
    exact ⟨_, interior_subset hy, WithTop.coe_ne_top⟩

/-- In a tail `(a, ∞]`, the finite points are dense. -/
theorem tail_finite_dense {a : L} (_ha : a < ⊤) :
    Dense {x : Ioi a | IsFin (x : L)} := by
  rw [dense_iff_inter_open]
  rintro U ⟨V, hV, rfl⟩ ⟨⟨x, hxa⟩, hxV⟩
  by_cases hx : IsFin x
  · exact ⟨⟨x, hxa⟩, hxV, hx⟩
  · have hx' : x = ⊤ := not_not.mp hx
    subst hx'
    have hO : IsOpen (V ∩ Ioi a) := hV.inter isOpen_Ioi
    obtain ⟨y, hy⟩ := exists_coe_mem_of_isOpen hO ⟨hxV, hxa⟩
    exact ⟨⟨y, hy.2⟩, hy.1, WithTop.coe_ne_top⟩

/-- The finite part of a tail is path connected. -/
theorem tail_finite_isPathConnected {a : L} (ha : a < ⊤) :
    IsPathConnected {x : Ioi a | IsFin (x : L)} := by
  have hS : IsPathConnected (Ioo a ⊤) :=
    isPathConnected_of_ordConnected ordConnected_Ioo (fun x hx => hx.2.ne) (by
      obtain ⟨a₀, rfl⟩ := WithTop.ne_top_iff_exists.mp ha.ne
      obtain ⟨b, hb⟩ := exists_ordPt_gt a₀
      exact ⟨ordPt b, hb, ordPt_lt_top b⟩)
  -- transport to the subspace
  have himg : (Subtype.val ⁻¹' Ioo a ⊤ : Set (Ioi a)) = {x : Ioi a | IsFin (x : L)} := by
    ext ⟨x, hx⟩
    simp only [mem_preimage, mem_Ioo, IsFin]
    change a < x ∧ x < ⊤ ↔ x ≠ ⊤
    exact ⟨fun h => h.2.ne, fun h => ⟨hx, lt_top_iff_ne_top.mpr h⟩⟩
  rw [← himg]
  obtain ⟨x₀, hx₀, hjoin⟩ := hS
  refine ⟨⟨x₀, hx₀.1⟩, hx₀, fun {y} hy => ?_⟩
  obtain ⟨γ, hγ⟩ := hjoin hy
  have hγa : ∀ t, a < γ t := fun t => (hγ t).1
  refine ⟨⟨⟨fun t => ⟨γ t, hγa t⟩, γ.continuous.subtype_mk _⟩, ?_, ?_⟩, fun t => hγ t⟩
  · exact Subtype.ext γ.source
  · exact Subtype.ext γ.target

/-- Tails are connected. -/
theorem tail_connectedSpace {a : L} (ha : a < ⊤) : ConnectedSpace (Ioi a) := by
  have hc := (tail_finite_isPathConnected ha).isConnected.closure
  rw [(tail_finite_dense ha).closure_eq] at hc
  exact connectedSpace_iff_univ.mpr hc

/-- Tails have pairwise height at most two. -/
theorem tail_pairwise {a : L} (ha : a < ⊤) : PairwiseFiniteHeight (TopCat.of (Ioi a)) :=
  PairwiseFiniteHeight.of_dense (X := TopCat.of (Ioi a)) (tail_finite_dense ha)
    (tail_finite_isPathConnected ha)

/-! ### Dense path-connected subsets -/

/-- A space with a dense path-connected subset is connected and has pairwise
height at most two. -/
theorem basis_of_dense {X : Type} [TopologicalSpace X] {F : Set X} (hF : Dense F)
    (hpc : IsPathConnected F) : ConnectedSpace X ∧ PairwiseFiniteHeight (TopCat.of X) := by
  refine ⟨?_, PairwiseFiniteHeight.of_dense (X := TopCat.of X) hF hpc⟩
  have hc := hpc.isConnected.closure
  rw [hF.closure_eq] at hc
  exact connectedSpace_iff_univ.mpr hc

/-! ### Good primitive spaces: the long ray -/

/-- A path-connected open set gives a basis element of the invariant. -/
theorem basis_of_isPathConnected {X : Type} [TopologicalSpace X] {W : Set X}
    (hW : IsPathConnected W) : ConnectedSpace W ∧ PairwiseFiniteHeight (TopCat.of W) := by
  have := pathConnectedSpace_of_isPathConnected hW
  exact ⟨inferInstance, PairwiseFiniteHeight.of_pathConnected (X := TopCat.of W)⟩

theorem connectedSpace_L : ConnectedSpace L := by
  have hS : IsPathConnected {x : L | IsFin x} := by
    have : {x : L | IsFin x} = Iio ⊤ := by ext x; simp [IsFin, lt_top_iff_ne_top]
    rw [this]
    refine isPathConnected_of_ordConnected ordConnected_Iio (fun x hx => hx.ne) ?_
    exact ⟨ordPt (Classical.arbitrary W), ordPt_lt_top _⟩
  have hc := hS.isConnected.closure
  rw [dense_finite.closure_eq] at hc
  exact connectedSpace_iff_univ.mpr hc

/-- **The closed long ray is good.** -/
theorem good_L : Good L := by
  refine ⟨connectedSpace_L, fun x N hN => ?_⟩
  by_cases hx : IsFin x
  · have hN' : N ∩ Iio ⊤ ∈ 𝓝 x := inter_mem hN (isOpen_Iio.mem_nhds (lt_top_iff_ne_top.mpr hx))
    obtain ⟨W, hWo, hxW, hWN, hWc⟩ := exists_ordConnected_open hN'
    have hpc : IsPathConnected W :=
      isPathConnected_of_ordConnected hWc (fun y hy => (hWN hy).2.ne) ⟨x, hxW⟩
    exact ⟨W, hWo, hxW, fun y hy => (hWN hy).1, basis_of_isPathConnected hpc⟩
  · have hx' : x = ⊤ := not_not.mp hx
    subst hx'
    obtain ⟨l, hl, hlN⟩ := (nhds_top_basis (α := L)).mem_iff.mp hN
    exact ⟨Ioi l, isOpen_Ioi, hl, hlN, tail_connectedSpace hl, tail_pairwise hl⟩

/-! ### The Sierpiński space, `ℝ` and the point -/

theorem sierpinski_false_specializes {U : Set Prop} (hU : IsOpen U) (h : False ∈ U) :
    True ∈ U := by
  induction hU with
  | basic s hs =>
    rw [mem_singleton_iff] at hs; subst hs
    simp at h
  | univ => trivial
  | inter s t _ _ ihs iht => exact ⟨ihs h.1, iht h.2⟩
  | sUnion S _ ih =>
    obtain ⟨s, hs, hfs⟩ := h
    exact ⟨s, hs, ih s hs hfs⟩

theorem sierpinski_eq_univ {U : Set Prop} (hU : IsOpen U) (h : False ∈ U) : U = univ := by
  ext P
  simp only [mem_univ, iff_true]
  by_cases hP : P
  · rw [eq_true hP]; exact sierpinski_false_specializes hU h
  · rw [eq_false hP]; exact h

theorem joined_false_true : Joined False True := by
  have hc : Continuous fun t : I => (0 : ℝ) < (t : ℝ) := by
    rw [continuous_Prop]
    exact isOpen_lt continuous_const continuous_subtype_val
  exact ⟨Path.mk ⟨fun t : I => (0 : ℝ) < (t : ℝ), hc⟩ (by simp) (by simp)⟩

instance : PathConnectedSpace Prop := by
  refine ⟨⟨True⟩, fun P Q => ?_⟩
  have hT : ∀ R : Prop, Joined R True := by
    intro R
    by_cases hR : R
    · rw [eq_true hR]
    · rw [eq_false hR]; exact joined_false_true
  exact (hT P).trans (hT Q).symm

/-- **The Sierpiński space is good.** -/
theorem good_sierpinski : Good Prop := by
  refine ⟨inferInstance, fun P N hN => ?_⟩
  by_cases hP : P
  · have hP' : P = True := eq_true hP
    subst hP'
    have ho : IsOpen ({True} : Set Prop) := TopologicalSpace.isOpen_generateFrom_of_mem rfl
    refine ⟨{True}, ho, rfl, singleton_subset_iff.mpr (mem_of_mem_nhds hN), ?_⟩
    exact basis_of_isPathConnected (isPathConnected_singleton True)
  · have hP' : P = False := eq_false hP
    subst hP'
    obtain ⟨U, hUN, hUo, hFU⟩ := mem_nhds_iff.mp hN
    have hU : U = univ := sierpinski_eq_univ hUo hFU
    refine ⟨univ, isOpen_univ, mem_univ _, hU ▸ hUN, ?_⟩
    exact basis_of_isPathConnected (isPathConnected_univ (X := Prop))

/-- **The real line is good.** -/
theorem good_real : Good ℝ := by
  refine ⟨inferInstance, fun x N hN => ?_⟩
  obtain ⟨W, hWo, hxW, hWN, hWc⟩ := exists_ordConnected_open hN
  exact ⟨W, hWo, hxW, hWN, basis_of_isPathConnected
    (hWc.convex.isPathConnected ⟨x, hxW⟩)⟩

/-- **The point is good.** -/
theorem good_punit : Good (PUnit : Type) := by
  refine ⟨inferInstance, fun x N hN => ⟨univ, isOpen_univ, mem_univ _, ?_, ?_⟩⟩
  · intro y _; rw [Subsingleton.elim y x]; exact mem_of_mem_nhds hN
  · exact basis_of_isPathConnected (isPathConnected_univ (X := PUnit))

/-! ### The kernel pair `K` -/

/-- Pairs of finite points. -/
def KFin : Set Kset := {p | IsFin p.1.1 ∧ IsFin p.1.2}

theorem joined_pair {x y x' y' : L} (hx : IsFin x) (hy : IsFin y) (hx' : IsFin x')
    (hy' : IsFin y') {S : Set (L × L)}
    (hS : ∀ p : L × L, min x x' ≤ p.1 → p.1 ≤ max x x' → min y y' ≤ p.2 → p.2 ≤ max y y' →
      p ∈ S) :
    JoinedIn S (x, y) (x', y') := by
  obtain ⟨x₀, rfl⟩ := isFin_iff.mp hx
  obtain ⟨y₀, rfl⟩ := isFin_iff.mp hy
  obtain ⟨x₁, rfl⟩ := isFin_iff.mp hx'
  obtain ⟨y₁, rfl⟩ := isFin_iff.mp hy'
  obtain ⟨γ, g0, g1, hγ⟩ := exists_path_between x₀ x₁
  obtain ⟨δ, d0, d1, hδ⟩ := exists_path_between y₀ y₁
  refine ⟨⟨⟨fun t => (γ t, δ t), γ.continuous.prodMk δ.continuous⟩, ?_, ?_⟩, fun t => ?_⟩
  · simp [g0, d0]
  · simp [g1, d1]
  · exact hS _ (hγ t).1 (hγ t).2 (hδ t).1 (hδ t).2

theorem isFin_of_between {x x' z : L} (hx : IsFin x) (hx' : IsFin x') (h : z ≤ max x x') :
    IsFin z := by
  intro hz
  rw [hz, top_le_iff] at h
  rcases max_choice x x' with e | e <;> rw [e] at h
  · exact hx h
  · exact hx' h

theorem KFin_isPathConnected_in {S : Set Kset}
    (hconv : ∀ p q : Kset, p ∈ S ∩ KFin → q ∈ S ∩ KFin → ∀ z : L × L,
      min p.1.1 q.1.1 ≤ z.1 → z.1 ≤ max p.1.1 q.1.1 → min p.1.2 q.1.2 ≤ z.2 →
      z.2 ≤ max p.1.2 q.1.2 → ∀ hz : z ∈ Kset, (⟨z, hz⟩ : Kset) ∈ S)
    (hne : (S ∩ KFin).Nonempty) : IsPathConnected (S ∩ KFin) := by
  obtain ⟨p₀, hp₀⟩ := hne
  refine ⟨p₀, hp₀, fun {q} hq => ?_⟩
  have hfin : ∀ z : L × L, min p₀.1.1 q.1.1 ≤ z.1 → z.1 ≤ max p₀.1.1 q.1.1 →
      min p₀.1.2 q.1.2 ≤ z.2 → z.2 ≤ max p₀.1.2 q.1.2 → IsFin z.1 ∧ IsFin z.2 :=
    fun z _ h2 _ h4 => ⟨isFin_of_between hp₀.2.1 hq.2.1 h2, isFin_of_between hp₀.2.2 hq.2.2 h4⟩
  have hJ := joined_pair hp₀.2.1 hp₀.2.2 hq.2.1 hq.2.2
    (S := {z : L × L | min p₀.1.1 q.1.1 ≤ z.1 ∧ z.1 ≤ max p₀.1.1 q.1.1 ∧
      min p₀.1.2 q.1.2 ≤ z.2 ∧ z.2 ≤ max p₀.1.2 q.1.2})
    (fun z h1 h2 h3 h4 => ⟨h1, h2, h3, h4⟩)
  obtain ⟨γ, hγ⟩ := hJ
  have hK : ∀ t, γ t ∈ Kset := by
    intro t
    obtain ⟨f1, f2⟩ := hfin _ (hγ t).1 (hγ t).2.1 (hγ t).2.2.1 (hγ t).2.2.2
    simp only [Kset, Set.mem_ofPred_eq]
    exact ⟨fun h => absurd h f1, fun h => absurd h f2⟩
  refine ⟨⟨⟨fun t => ⟨γ t, hK t⟩, γ.continuous.subtype_mk _⟩, Subtype.ext γ.source,
    Subtype.ext γ.target⟩, fun t => ⟨?_, ?_⟩⟩
  · exact hconv p₀ q hp₀ hq _ (hγ t).1 (hγ t).2.1 (hγ t).2.2.1 (hγ t).2.2.2 (hK t)
  · exact hfin _ (hγ t).1 (hγ t).2.1 (hγ t).2.2.1 (hγ t).2.2.2

/-- An upper set of `L` containing finite points above every finite point. -/
structure UpperTail (T : Set L) : Prop where
  upper : IsUpperSet T
  top_mem : (⊤ : L) ∈ T
  cofinal : ∀ l : L, l < ⊤ → ∃ z : L₀, (z : L) ∈ T ∧ l < z

theorem upperTail_univ : UpperTail (univ : Set L) :=
  ⟨isUpperSet_univ, mem_univ _, fun l hl => by
    obtain ⟨l₀, rfl⟩ := WithTop.ne_top_iff_exists.mp hl.ne
    obtain ⟨b, hb⟩ := exists_ordPt_gt l₀
    exact ⟨_, mem_univ _, hb⟩⟩

theorem upperTail_Ioi {a : L} (ha : a < ⊤) : UpperTail (Ioi a) :=
  ⟨isUpperSet_Ioi a, ha, fun l hl => by
    have hm : max a l < ⊤ := max_lt ha hl
    obtain ⟨m₀, hm₀⟩ := WithTop.ne_top_iff_exists.mp hm.ne
    obtain ⟨b, hb⟩ := exists_ordPt_gt m₀
    refine ⟨toLex (b, ⟨0, le_rfl, zero_lt_one⟩), ?_, ?_⟩
    · change a < ordPt b
      exact lt_of_le_of_lt (le_max_left a l) (hm₀ ▸ hb)
    · change l < ordPt b
      exact lt_of_le_of_lt (le_max_right a l) (hm₀ ▸ hb)⟩

/-- `K_T`: pairs in `K` with both points in `T`. -/
def KT (T : Set L) : Set Kset := {p | p.1.1 ∈ T ∧ p.1.2 ∈ T}

theorem isOpen_KT {T : Set L} (hT : IsOpen T) : IsOpen (KT T) :=
  ((hT.preimage continuous_fst).inter (hT.preimage continuous_snd)).preimage
    continuous_subtype_val

theorem UpperTail.min_mem {T : Set L} {x y : L} (hx : x ∈ T) (hy : y ∈ T) : min x y ∈ T := by
  rcases min_choice x y with e | e <;> rw [e] <;> assumption

theorem KT_finite_isPathConnected {T : Set L} (hT : UpperTail T) :
    IsPathConnected (Subtype.val ⁻¹' KFin : Set (KT T)) := by
  have h := KFin_isPathConnected_in (S := KT T) (fun p q hp hq z h1 _ h3 _ _ =>
      ⟨hT.upper h1 (UpperTail.min_mem hp.1.1 hq.1.1),
        hT.upper h3 (UpperTail.min_mem hp.1.2 hq.1.2)⟩) (by
      obtain ⟨z, hzT, -⟩ := hT.cofinal (ordPt (Classical.arbitrary W)) (ordPt_lt_top _)
      exact ⟨⟨((z : L), (z : L)), by simp [Kset]⟩, ⟨hzT, hzT⟩,
        WithTop.coe_ne_top, WithTop.coe_ne_top⟩)
  -- transport to the subspace `KT T`
  obtain ⟨p₀, hp₀, hjoin⟩ := h
  refine ⟨⟨p₀, hp₀.1⟩, hp₀.2, fun {q} hq => ?_⟩
  obtain ⟨γ, hγ⟩ := hjoin ⟨q.2, hq⟩
  refine ⟨⟨⟨fun t => ⟨γ t, (hγ t).1⟩, γ.continuous.subtype_mk _⟩, Subtype.ext γ.source,
    Subtype.ext γ.target⟩, fun t => (hγ t).2⟩

theorem KT_finite_dense {T : Set L} (hT : UpperTail T) :
    Dense (Subtype.val ⁻¹' KFin : Set (KT T)) := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨⟨p, hpT⟩, hpU⟩
  by_cases hp : IsFin p.1.1
  · have hp2 : IsFin p.1.2 := fun h => hp (p.2.mpr h)
    exact ⟨⟨p, hpT⟩, hpU, hp, hp2⟩
  · -- `p = (∞, ∞)`: a box around it contains finite pairs
    have h1 : p.1.1 = ⊤ := not_not.mp hp
    have h2 : p.1.2 = ⊤ := p.2.mp h1
    obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
    obtain ⟨M, hM, hMV⟩ := isOpen_induced_iff.mp hV
    have hpM : (p : L × L) ∈ M := by
      have : (⟨p, hpT⟩ : KT T) ∈ U := hpU
      rw [← hVU, ← hMV] at this; exact this
    obtain ⟨A, B, hA, hB, hpA, hpB, hAB⟩ := isOpen_prod_iff.mp hM _ _ hpM
    rw [h1] at hpA; rw [h2] at hpB
    obtain ⟨l₁, hl₁, hl₁A⟩ := (nhds_top_basis (α := L)).mem_iff.mp (hA.mem_nhds hpA)
    obtain ⟨l₂, hl₂, hl₂B⟩ := (nhds_top_basis (α := L)).mem_iff.mp (hB.mem_nhds hpB)
    obtain ⟨z, hzT, hz⟩ := hT.cofinal (max l₁ l₂) (max_lt hl₁ hl₂)
    have hzK : ((z : L), (z : L)) ∈ Kset := by simp [Kset]
    refine ⟨⟨⟨((z : L), (z : L)), hzK⟩, ⟨hzT, hzT⟩⟩, ?_, WithTop.coe_ne_top, WithTop.coe_ne_top⟩
    rw [← hVU, ← hMV]
    exact hAB ⟨hl₁A (lt_of_le_of_lt (le_max_left _ _) hz),
      hl₂B (lt_of_le_of_lt (le_max_right _ _) hz)⟩

/-- `K_T` is connected with pairwise height at most two. -/
theorem KT_basis {T : Set L} (hT : UpperTail T) :
    ConnectedSpace (KT T) ∧ PairwiseFiniteHeight (TopCat.of (KT T)) :=
  basis_of_dense (KT_finite_dense hT) (KT_finite_isPathConnected hT)

/-- A path-connected subset of `L × L` inside `K` gives a path-connected subset of `K`. -/
theorem isPathConnected_preimage_K {S : Set (L × L)} (hS : IsPathConnected S) (hSK : S ⊆ Kset) :
    IsPathConnected (Subtype.val ⁻¹' S : Set Kset) := by
  obtain ⟨x, hx, hjoin⟩ := hS
  refine ⟨⟨x, hSK hx⟩, hx, fun {y} hy => ?_⟩
  obtain ⟨γ, hγ⟩ := hjoin hy
  exact ⟨⟨⟨fun t => ⟨γ t, hSK (hγ t)⟩, γ.continuous.subtype_mk _⟩, Subtype.ext γ.source,
    Subtype.ext γ.target⟩, fun t => hγ t⟩

/-- **The kernel pair `K` is good.** -/
theorem good_K : Good Kset := by
  have e : (KT (univ : Set L)) ≃ₜ Kset :=
    (Homeomorph.setCongr (show KT (univ : Set L) = univ by ext; simp [KT])).trans
      (Homeomorph.Set.univ Kset)
  have hc : ConnectedSpace (KT (univ : Set L)) := (KT_basis upperTail_univ).1
  refine ⟨connectedSpace_of_homeomorph e, fun p N hN => ?_⟩
  · obtain ⟨M, hM, hMN⟩ := (mem_nhds_induced Subtype.val p N).mp hN
    by_cases hp : IsFin p.1.1
    · have hp2 : IsFin p.1.2 := fun h => hp (p.2.mpr h)
      obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hM
      obtain ⟨W₁, hW₁o, hx₁, hW₁A, hW₁c⟩ := exists_ordConnected_open
        (inter_mem hA (isOpen_Iio.mem_nhds (lt_top_iff_ne_top.mpr hp)))
      obtain ⟨W₂, hW₂o, hx₂, hW₂B, hW₂c⟩ := exists_ordConnected_open
        (inter_mem hB (isOpen_Iio.mem_nhds (lt_top_iff_ne_top.mpr hp2)))
      have hfin₁ : ∀ y ∈ W₁, IsFin y := fun y hy => (hW₁A hy).2.ne
      have hfin₂ : ∀ y ∈ W₂, IsFin y := fun y hy => (hW₂B hy).2.ne
      have hpc : IsPathConnected (W₁ ×ˢ W₂) :=
        (isPathConnected_of_ordConnected hW₁c hfin₁ ⟨_, hx₁⟩).prod
          (isPathConnected_of_ordConnected hW₂c hfin₂ ⟨_, hx₂⟩)
      have hsub : W₁ ×ˢ W₂ ⊆ Kset := fun q hq => by
        simp only [Kset, Set.mem_ofPred_eq]
        exact ⟨fun h => absurd h (hfin₁ _ hq.1), fun h => absurd h (hfin₂ _ hq.2)⟩
      refine ⟨Subtype.val ⁻¹' (W₁ ×ˢ W₂), (hW₁o.prod hW₂o).preimage continuous_subtype_val,
        ⟨hx₁, hx₂⟩, fun q hq => hMN (hAB ⟨(hW₁A hq.1).1, (hW₂B hq.2).1⟩), ?_⟩
      exact basis_of_isPathConnected (isPathConnected_preimage_K hpc hsub)
    · have h1 : p.1.1 = ⊤ := not_not.mp hp
      have h2 : p.1.2 = ⊤ := p.2.mp h1
      obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hM
      rw [h1] at hA; rw [h2] at hB
      obtain ⟨l₁, hl₁, hl₁A⟩ := (nhds_top_basis (α := L)).mem_iff.mp hA
      obtain ⟨l₂, hl₂, hl₂B⟩ := (nhds_top_basis (α := L)).mem_iff.mp hB
      set l := max l₁ l₂
      have hl : l < ⊤ := max_lt hl₁ hl₂
      refine ⟨KT (Ioi l), isOpen_KT isOpen_Ioi, ⟨h1 ▸ hl, h2 ▸ hl⟩, ?_, KT_basis (upperTail_Ioi hl)⟩
      intro q hq
      have hq1 : l₁ < q.1.1 := lt_of_le_of_lt (le_max_left l₁ l₂) hq.1
      have hq2 : l₂ < q.1.2 := lt_of_le_of_lt (le_max_right l₁ l₂) hq.2
      exact hMN (hAB ⟨hl₁A hq1, hl₂B hq2⟩)

/-! ### The path space `P` -/

/-- Paths with values in `T`. -/
def PT (T : Set L) : Set C(I, L) := {γ | ∀ t, γ t ∈ T}

theorem isOpen_PT {T : Set L} (hT : IsOpen T) : IsOpen (PT T) := by
  have := ContinuousMap.isOpen_setOfPred_mapsTo (X := I) (Y := L) isCompact_univ hT
  convert this using 1
  ext γ; simp [PT, MapsTo]

/-- Bounded paths. -/
def PB : Set C(I, L) := {γ | ∀ t, IsFin (γ t)}

/-- Two paths below `(b, 0)` are joined, through paths below `(b, 0)` whose values
stay pointwise between theirs, by linear interpolation in the chart. -/
theorem joined_paths_in_chart {b : W} {γ δ : C(I, L)} (hγ : ∀ t, γ t < ordPt b)
    (hδ : ∀ t, δ t < ordPt b) :
    ∃ H : Path γ δ, ∀ s t, min (γ t) (δ t) ≤ H s t ∧ H s t ≤ max (γ t) (δ t) ∧
      H s t < ordPt b := by
  set c := Chart.chart b
  have hγJ : ∀ t, c.Φ (γ t) < c.β := fun t => Chart.Φfun_lt_S_of_lt_ordPt b (hγ t)
  have hδJ : ∀ t, c.Φ (δ t) < c.β := fun t => Chart.Φfun_lt_S_of_lt_ordPt b (hδ t)
  have hmem : ∀ x : I × I, (1 - (x.1 : ℝ)) * c.Φ (γ x.2) + (x.1 : ℝ) * c.Φ (δ x.2) ∈
      Ico (0 : ℝ) c.β := by
    intro x
    have h0 := x.1.2.1; have h1 := x.1.2.2
    have hx0 := c.nonneg (γ x.2); have hy0 := c.nonneg (δ x.2)
    have a := hγJ x.2; have b' := hδJ x.2
    constructor
    · have : 0 ≤ 1 - (x.1 : ℝ) := by linarith
      positivity
    · have m0 : 0 < min (c.β - c.Φ (γ x.2)) (c.β - c.Φ (δ x.2)) :=
        lt_min (by linarith) (by linarith)
      have k1 := mul_le_mul_of_nonneg_left (min_le_left (c.β - c.Φ (γ x.2))
        (c.β - c.Φ (δ x.2))) (show 0 ≤ 1 - (x.1 : ℝ) by linarith)
      have k2 := mul_le_mul_of_nonneg_left (min_le_right (c.β - c.Φ (γ x.2))
        (c.β - c.Φ (δ x.2))) h0
      nlinarith
  let F : I × I → Ico (0 : ℝ) c.β := fun x =>
    ⟨(1 - (x.1 : ℝ)) * c.Φ (γ x.2) + (x.1 : ℝ) * c.Φ (δ x.2), hmem x⟩
  have hF : Continuous F := by
    have : Continuous fun x : I × I =>
        (1 - (x.1 : ℝ)) * c.Φ (γ x.2) + (x.1 : ℝ) * c.Φ (δ x.2) := by fun_prop
    exact this.subtype_mk _
  let G : C(I × I, L) := ⟨fun x => c.ψ (F x), c.ψ.continuous.comp hF⟩
  have hGγ : ∀ t, G (0, t) = γ t := by
    intro t
    change c.ψ (F (0, t)) = γ t
    have : F (0, t) = ⟨c.Φ (γ t), c.nonneg _, hγJ t⟩ := Subtype.ext (by simp [F])
    rw [this, c.ψ_Φ _ (hγJ t)]
  have hGδ : ∀ t, G (1, t) = δ t := by
    intro t
    change c.ψ (F (1, t)) = δ t
    have : F (1, t) = ⟨c.Φ (δ t), c.nonneg _, hδJ t⟩ := Subtype.ext (by simp [F])
    rw [this, c.ψ_Φ _ (hδJ t)]
  refine ⟨⟨G.curry, ?_, ?_⟩, fun s t => ?_⟩
  · ext t; exact hGγ t
  · ext t; exact hGδ t
  · change min (γ t) (δ t) ≤ c.ψ (F (s, t)) ∧ c.ψ (F (s, t)) ≤ max (γ t) (δ t) ∧
      c.ψ (F (s, t)) < ordPt b
    have hψγ : c.ψ ⟨c.Φ (γ t), c.nonneg _, hγJ t⟩ = γ t := c.ψ_Φ _ (hγJ t)
    have hψδ : c.ψ ⟨c.Φ (δ t), c.nonneg _, hδJ t⟩ = δ t := c.ψ_Φ _ (hδJ t)
    have h0 := s.2.1; have h1 := s.2.2
    refine ⟨?_, ?_, ?_⟩
    · rcases le_total (c.Φ (γ t)) (c.Φ (δ t)) with hxy | hxy
      · have l : (⟨c.Φ (γ t), c.nonneg _, hγJ t⟩ : Ico (0 : ℝ) c.β) ≤ F (s, t) := by
          change c.Φ (γ t) ≤ (1 - (s : ℝ)) * c.Φ (γ t) + (s : ℝ) * c.Φ (δ t); nlinarith
        have l' := Chart.ψ_mono b l; rw [hψγ] at l'
        exact (min_le_left _ _).trans l'
      · have l : (⟨c.Φ (δ t), c.nonneg _, hδJ t⟩ : Ico (0 : ℝ) c.β) ≤ F (s, t) := by
          change c.Φ (δ t) ≤ (1 - (s : ℝ)) * c.Φ (γ t) + (s : ℝ) * c.Φ (δ t); nlinarith
        have l' := Chart.ψ_mono b l; rw [hψδ] at l'
        exact (min_le_right _ _).trans l'
    · rcases le_total (c.Φ (γ t)) (c.Φ (δ t)) with hxy | hxy
      · have r : F (s, t) ≤ (⟨c.Φ (δ t), c.nonneg _, hδJ t⟩ : Ico (0 : ℝ) c.β) := by
          change (1 - (s : ℝ)) * c.Φ (γ t) + (s : ℝ) * c.Φ (δ t) ≤ c.Φ (δ t); nlinarith
        have r' := Chart.ψ_mono b r; rw [hψδ] at r'
        exact r'.trans (le_max_right _ _)
      · have r : F (s, t) ≤ (⟨c.Φ (γ t), c.nonneg _, hγJ t⟩ : Ico (0 : ℝ) c.β) := by
          change (1 - (s : ℝ)) * c.Φ (γ t) + (s : ℝ) * c.Φ (δ t) ≤ c.Φ (γ t); nlinarith
        have r' := Chart.ψ_mono b r; rw [hψγ] at r'
        exact r'.trans (le_max_left _ _)
    · apply Chart.lt_ordPt_of_Φfun_lt_S
      change c.Φ (c.ψ (F (s, t))) < c.β
      rw [c.Φ_ψ]
      exact (F (s, t)).2.2

/-- Every bounded path lies below some ordinal point. -/
theorem exists_bound_of_PB {γ : C(I, L)} (hγ : γ ∈ PB) : ∃ b : W, ∀ t, γ t < ordPt b := by
  rcases path_const_top_or_bounded γ with h | h
  · exact absurd (h 0) (hγ 0)
  · exact h

theorem exists_common_bound {γ δ : C(I, L)} (hγ : γ ∈ PB) (hδ : δ ∈ PB) :
    ∃ b : W, (∀ t, γ t < ordPt b) ∧ ∀ t, δ t < ordPt b := by
  obtain ⟨b₁, h₁⟩ := exists_bound_of_PB hγ
  obtain ⟨b₂, h₂⟩ := exists_bound_of_PB hδ
  exact ⟨max b₁ b₂, fun t => (h₁ t).trans_le (ordPt_le_ordPt (le_max_left _ _)),
    fun t => (h₂ t).trans_le (ordPt_le_ordPt (le_max_right _ _))⟩

/-- The bounded part of `P_T` is path connected. -/
theorem PT_bounded_isPathConnected {T : Set L} (hT : UpperTail T) :
    IsPathConnected (Subtype.val ⁻¹' PB : Set (PT T)) := by
  obtain ⟨z, hzT, -⟩ := hT.cofinal (ordPt (Classical.arbitrary W)) (ordPt_lt_top _)
  let γ₀ : C(I, L) := ContinuousMap.const _ (z : L)
  have hγ₀ : γ₀ ∈ PT T := fun _ => hzT
  have hγ₀B : γ₀ ∈ PB := fun _ => WithTop.coe_ne_top
  refine ⟨⟨γ₀, hγ₀⟩, hγ₀B, fun {δ} hδ => ?_⟩
  obtain ⟨b, hb₀, hbδ⟩ := exists_common_bound hγ₀B hδ
  obtain ⟨H, hH⟩ := joined_paths_in_chart hb₀ hbδ
  have hmemT : ∀ s, H s ∈ PT T := by
    intro s t
    have h1 : γ₀ t ∈ T := hzT
    have h2 : (δ : C(I, L)) t ∈ T := δ.2 t
    exact hT.upper (hH s t).1 (UpperTail.min_mem h1 h2)
  refine ⟨⟨⟨fun s => ⟨H s, hmemT s⟩, H.continuous.subtype_mk _⟩, Subtype.ext H.source,
    Subtype.ext H.target⟩, fun s t => ?_⟩
  exact ((hH s t).2.2.trans (ordPt_lt_top b)).ne

/-- The bounded part of `P_T` is dense in `P_T`. -/
theorem PT_bounded_dense {T : Set L} (hT : UpperTail T) :
    Dense (Subtype.val ⁻¹' PB : Set (PT T)) := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨⟨γ, hγT⟩, hγU⟩
  by_cases hγ : γ ∈ PB
  · exact ⟨⟨γ, hγT⟩, hγU, hγ⟩
  · -- `γ` is the constant path at `∞`
    have hγ' : γ = constTop := by
      rcases path_const_top_or_bounded γ with h | ⟨b, hb⟩
      · exact ContinuousMap.ext h
      · exact absurd (fun t => ((hb t).trans (ordPt_lt_top b)).ne) hγ
    subst hγ'
    obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
    have hVmem : constTop ∈ V := by
      have : (⟨constTop, hγT⟩ : PT T) ∈ U := hγU
      rw [← hVU] at this; exact this
    obtain ⟨a, ha, haV⟩ := exists_tail_subset (hV.mem_nhds hVmem)
    obtain ⟨z, hzT, hz⟩ := hT.cofinal a ha
    let δ : C(I, L) := ContinuousMap.const _ (z : L)
    refine ⟨⟨δ, fun _ => hzT⟩, ?_, fun _ => WithTop.coe_ne_top⟩
    rw [← hVU]
    exact haV fun _ => hz

theorem PT_basis {T : Set L} (hT : UpperTail T) :
    ConnectedSpace (PT T) ∧ PairwiseFiniteHeight (TopCat.of (PT T)) :=
  basis_of_dense (PT_bounded_dense hT) (PT_bounded_isPathConnected hT)

/-- **Chart balls form a neighbourhood basis at bounded paths.** -/
theorem exists_chartBall_subset {b : W} {γ : C(I, L)} (hγ : ∀ t, γ t < ordPt b)
    {N : Set C(I, L)} (hN : N ∈ 𝓝 γ) :
    ∃ ε, (Chart.chart b).Admissible γ ε ∧ (Chart.chart b).V γ ε ⊆ N := by
  obtain ⟨ε₀, h₀⟩ := exists_admissible hγ
  set c := Chart.chart b
  let sec : C(C(I, ℝ), C(I, L)) :=
    ⟨fun f => (c.ψ.comp (BottomChart.clampTo h₀)).comp f, ContinuousMap.continuous_postcomp _⟩
  have hsec : ∀ δ ∈ c.V γ ε₀, sec (c.coord δ) = δ := by
    intro δ hδ
    ext t
    change c.ψ (BottomChart.clampTo h₀ (c.Φ (δ t))) = δ t
    apply BottomChart.ψ_of_val_eq
    rw [BottomChart.clampTo_val_of_le h₀ (BottomChart.coord_le_top' h₀ hδ t).le,
      max_eq_right (c.nonneg _)]
  have hγV : γ ∈ c.V γ ε₀ := by
    change dist (c.coord γ) (c.coord γ) < ε₀
    rw [dist_self]; exact h₀.pos
  have hsecγ : sec (c.coord γ) = γ := hsec γ hγV
  have hpre : sec ⁻¹' N ∈ 𝓝 (c.coord γ) :=
    sec.continuous.continuousAt.preimage_mem_nhds (hsecγ.symm ▸ hN)
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨min ε₀ ε₁, ⟨lt_min h₀.pos hε₁, ?_⟩, fun δ hδ => ?_⟩
  · have := h₀.fits
    have hm := min_le_left ε₀ ε₁
    linarith
  · have hδ' : dist (c.coord δ) (c.coord γ) < min ε₀ ε₁ := hδ
    have hδ₀ : δ ∈ c.V γ ε₀ := lt_of_lt_of_le hδ' (min_le_left _ _)
    have hδ₁ : c.coord δ ∈ Metric.ball (c.coord γ) ε₁ := lt_of_lt_of_le hδ' (min_le_right _ _)
    rw [← hsec δ hδ₀]
    exact hball hδ₁

/-- **The path space `P` is good.** -/
theorem good_P : Good C(I, L) := by
  have e : (PT (univ : Set L)) ≃ₜ C(I, L) :=
    (Homeomorph.setCongr (show PT (univ : Set L) = univ by ext; simp [PT])).trans
      (Homeomorph.Set.univ _)
  have hc : ConnectedSpace (PT (univ : Set L)) := (PT_basis upperTail_univ).1
  refine ⟨connectedSpace_of_homeomorph e, fun γ N hN => ?_⟩
  by_cases hγ : γ ∈ PB
  · obtain ⟨b, hb⟩ := exists_bound_of_PB hγ
    obtain ⟨ε, hε, hV⟩ := exists_chartBall_subset hb hN
    refine ⟨(Chart.chart b).V γ ε, (Chart.chart b).isOpen_V γ ε, ?_, hV,
      basis_of_isPathConnected ((Chart.chart b).isPathConnected_V hε)⟩
    change dist _ _ < ε
    rw [dist_self]; exact hε.pos
  · have hγ' : γ = constTop := by
      rcases path_const_top_or_bounded γ with h | ⟨b, hb⟩
      · exact ContinuousMap.ext h
      · exact absurd (fun t => ((hb t).trans (ordPt_lt_top b)).ne) hγ
    subst hγ'
    obtain ⟨a, ha, haN⟩ := exists_tail_subset hN
    refine ⟨PT (Ioi a), isOpen_PT isOpen_Ioi, fun _ => ha, fun δ hδ => haN hδ,
      PT_basis (upperTail_Ioi ha)⟩

end RealContinuity
