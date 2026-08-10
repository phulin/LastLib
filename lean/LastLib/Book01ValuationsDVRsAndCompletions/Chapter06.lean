import Mathlib

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter06

open Set Filter Function
open scoped BigOperators Pointwise Topology WithZero NNReal Valued PowerSeries

noncomputable section

/-! ### 6.1 Balls and the strong triangle inequality -/

section Balls

variable {K : Type*} [Field K]

/-- The metric expression attached to a real-valued absolute value. -/
def chapter06Distance (v : AbsoluteValue K ℝ) (x y : K) : ℝ :=
  v (x - y)

/-- The open ball used throughout §6.1. -/
def chapter06OpenBall (v : AbsoluteValue K ℝ) (a : K) (r : ℝ) : Set K :=
  {x | chapter06Distance v x a < r}

/-- The closed ball used throughout §6.1. -/
def chapter06ClosedBall (v : AbsoluteValue K ℝ) (a : K) (r : ℝ) : Set K :=
  {x | chapter06Distance v x a ≤ r}

/-- Nontriviality of an absolute value, in Mathlib's bundled language. -/
def chapter06AbsoluteValueIsNontrivial (v : AbsoluteValue K ℝ) : Prop :=
  v.IsNontrivial

/-- A real-valued formulation of discreteness of the possible radii. -/
def chapter06DiscreteValueSet (v : AbsoluteValue K ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ s : ℝ, r < s ∧ ∀ x : K, v x ≤ r ↔ v x < s

/-- The metric structure induced by a bundled absolute value. -/
noncomputable def chapter06MetricSpace (v : AbsoluteValue K ℝ) : MetricSpace K :=
  letI : NormedField K := v.toNormedField
  inferInstance

/-- The induced metric has the displayed formula `d(x,y) = |x-y|`. -/
theorem chapter06MetricSpace_dist (v : AbsoluteValue K ℝ) (x y : K) :
    @dist K (chapter06MetricSpace v).toPseudoMetricSpace.toDist x y =
      chapter06Distance v x y := by
  change v (-x + y) = v (x - y)
  simpa [sub_eq_add_neg, add_comm] using v.map_sub y x

private theorem chapter06_openBall_isOpen
    (v : AbsoluteValue K ℝ) (a : K) (r : ℝ) :
    @IsOpen K v.uniformSpace.toTopologicalSpace (chapter06OpenBall v a r) := by
  letI : UniformSpace K := v.uniformSpace
  rw [isOpen_iff_mem_nhds]
  intro x hx
  change v (x - a) < r at hx
  rw [UniformSpace.mem_nhds_iff]
  let δ : ℝ := r - v (x - a)
  have hδ : 0 < δ := sub_pos.mpr hx
  refine ⟨{p : K × K | v (p.2 - p.1) < δ}, ?_, ?_⟩
  · exact (v.hasBasis_uniformity).mem_iff.mpr ⟨δ, hδ, Subset.rfl⟩
  · intro y hy
    change v (y - x) < δ at hy
    change v (y - a) < r
    calc
      v (y - a) ≤ v (y - x) + v (x - a) := v.sub_le y x a
      _ < δ + v (x - a) := by linarith
      _ = r := sub_add_cancel _ _

/-- A nontrivial absolute value gives the metric asserted at the start of §6.1. -/
theorem chapter06_nontrivial_absolute_value_gives_metric
    (v : AbsoluteValue K ℝ) (hv : chapter06AbsoluteValueIsNontrivial v) :
    ∃ m : MetricSpace K,
      ∀ x y : K, @dist K m.toPseudoMetricSpace.toDist x y = chapter06Distance v x y := by
  refine ⟨chapter06MetricSpace v, ?_⟩
  intro x y
  exact chapter06MetricSpace_dist v x y

/-- The strong triangle inequality in distance form. -/
theorem chapter06_strong_triangle_inequality
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (x y z : K) :
    chapter06Distance v x z ≤
      max (chapter06Distance v x y) (chapter06Distance v y z) := by
  simpa [chapter06Distance, sub_add_sub_cancel] using hv (x - y) (y - z)

/-- A point of an open ball is a center for the same ball. -/
theorem chapter06_openBall_center_invariance
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a y : K} {r : ℝ} (hy : y ∈ chapter06OpenBall v a r) :
    chapter06OpenBall v y r = chapter06OpenBall v a r := by
  ext x
  change v (x - y) < r ↔ v (x - a) < r
  change v (y - a) < r at hy
  have hy' : v (a - y) < r := by simpa only [v.map_sub] using hy
  constructor
  · intro hx
    simpa [sub_add_sub_cancel] using
      (hv (x - y) (y - a)).trans_lt (max_lt hx hy)
  · intro hx
    simpa [sub_add_sub_cancel] using
      (hv (x - a) (a - y)).trans_lt (max_lt hx hy')

/-- Two open balls of the same radius are disjoint or equal. -/
theorem chapter06_openBall_same_radius_disjoint_or_equal
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a b : K} {r : ℝ} :
    Disjoint (chapter06OpenBall v a r) (chapter06OpenBall v b r) ∨
      chapter06OpenBall v a r = chapter06OpenBall v b r := by
  rcases Set.disjoint_or_nonempty_inter (chapter06OpenBall v a r)
    (chapter06OpenBall v b r) with h | h
  · exact Or.inl h
  · right
    obtain ⟨z, hza, hzb⟩ := h
    exact (chapter06_openBall_center_invariance v hv hza).symm.trans
      (chapter06_openBall_center_invariance v hv hzb)

/-- Meeting balls with comparable radii are nested. -/
theorem chapter06_openBall_nested_of_meeting
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a b : K} {r s : ℝ}
    (hmeet : (chapter06OpenBall v a r ∩ chapter06OpenBall v b s).Nonempty)
    (hcomp : r ≤ s ∨ s ≤ r) :
    chapter06OpenBall v a r ⊆ chapter06OpenBall v b s ∨
      chapter06OpenBall v b s ⊆ chapter06OpenBall v a r := by
  obtain ⟨z, hza, hzb⟩ := hmeet
  rcases hcomp with hrs | hsr
  · left
    intro x hx
    have hzr : x ∈ chapter06OpenBall v z r := by
      rw [chapter06_openBall_center_invariance v hv hza]
      exact hx
    have hzs : x ∈ chapter06OpenBall v z s := by
      change v (x - z) < s
      change v (x - z) < r at hzr
      exact lt_of_lt_of_le hzr hrs
    rw [← chapter06_openBall_center_invariance v hv hzb]
    exact hzs
  · right
    intro x hx
    have hzs : x ∈ chapter06OpenBall v z s := by
      rw [chapter06_openBall_center_invariance v hv hzb]
      exact hx
    have hzr : x ∈ chapter06OpenBall v z r := by
      change v (x - z) < r
      change v (x - z) < s at hzs
      exact lt_of_lt_of_le hzs hsr
    rw [← chapter06_openBall_center_invariance v hv hza]
    exact hzr

/-- The complement of an open ball is covered by balls of the same radius. -/
theorem chapter06_openBall_complement_iUnion
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a : K} {r : ℝ} (hr : 0 < r) :
    (chapter06OpenBall v a r)ᶜ =
      ⋃ x : {x : K // x ∉ chapter06OpenBall v a r},
        chapter06OpenBall v (x : K) r := by
  ext y
  constructor
  · intro hy
    refine mem_iUnion.2 ⟨⟨y, hy⟩, ?_⟩
    change v (y - y) < r
    simpa using hr
  · intro hy
    rcases mem_iUnion.1 hy with ⟨x, hyx⟩
    intro hya
    change v (y - (x : K)) < r at hyx
    change v (y - a) < r at hya
    apply x.property
    change v ((x : K) - a) < r
    have hxy : v ((x : K) - y) < r := by simpa only [v.map_sub] using hyx
    simpa [sub_add_sub_cancel] using
      (hv ((x : K) - y) (y - a)).trans_lt (max_lt hxy hya)

/-- Open balls are closed in the absolute-value topology. -/
theorem chapter06_openBall_isClosed
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a : K} {r : ℝ} (hr : 0 < r) :
    @IsClosed K v.uniformSpace.toTopologicalSpace (chapter06OpenBall v a r) := by
  letI : UniformSpace K := v.uniformSpace
  rw [← isOpen_compl_iff, chapter06_openBall_complement_iUnion v hv hr]
  exact isOpen_iUnion (fun x => chapter06_openBall_isOpen v (x : K) r)

/-- Discreteness supplies the next radius and makes closed balls open. -/
theorem chapter06_closedBall_isOpen_of_discrete_values
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hdisc : chapter06DiscreteValueSet v) {a : K} {r : ℝ} (hr : 0 < r) :
    @IsOpen K v.uniformSpace.toTopologicalSpace (chapter06ClosedBall v a r) := by
  obtain ⟨s, hrs, hs⟩ := hdisc r hr
  have heq : chapter06ClosedBall v a r = chapter06OpenBall v a s := by
    ext x
    change v (x - a) ≤ r ↔ v (x - a) < s
    exact hs (x - a)
  rw [heq]
  exact chapter06_openBall_isOpen v a s

/-- Every connected subset of a nonarchimedean metric space is a singleton. -/
theorem chapter06_connected_subset_is_singleton
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) {s : Set K}
    (hs : @IsConnected K v.uniformSpace.toTopologicalSpace s) :
    ∀ x ∈ s, ∀ y ∈ s, x = y := by
  letI : UniformSpace K := v.uniformSpace
  intro x hx y hy
  by_contra hxy
  let r : ℝ := v (x - y)
  have hr : 0 < r := v.pos (sub_ne_zero.mpr hxy)
  let U := chapter06OpenBall v x r
  have hclopen : @IsClopen K v.uniformSpace.toTopologicalSpace U :=
    ⟨chapter06_openBall_isClosed v hv hr, chapter06_openBall_isOpen v x r⟩
  have hxU : x ∈ U := by
    change v (x - x) < r
    simpa using hr
  have hsub : s ⊆ U :=
    hs.isPreconnected.subset_isClopen hclopen ⟨x, hx, hxU⟩
  have hyU := hsub hy
  change v (y - x) < r at hyU
  have hxy' : v (x - y) < r := by simpa only [v.map_sub] using hyU
  exact (lt_irrefl r) (by simpa [r] using hxy')

/-- The adic coset corresponding to a power of an ideal. -/
def chapter06AdicCoset {A : Type*} [CommRing A]
    (m : Ideal A) (a : A) (n : ℕ) : Set A :=
  {x | x - a ∈ ((m ^ n : Ideal A) : Set A)}

/-- The topology on a subring induced from a valuation topology on its fraction field. -/
def chapter06InducedValuationTopology (v : AbsoluteValue K ℝ) (A : Subring K) :
    TopologicalSpace A :=
  TopologicalSpace.induced ((↑) : A → K) v.uniformSpace.toTopologicalSpace

/-- Strict valuation balls in a subring. -/
def chapter06StrictValuationNeighborhood
    (v : AbsoluteValue K ℝ) (A : Subring K) (r : ℝ) : Set A :=
  {x | v (x : K) < r}

/-- Weak valuation balls in a subring. -/
def chapter06WeakValuationNeighborhood
    (v : AbsoluteValue K ℝ) (A : Subring K) (r : ℝ) : Set A :=
  {x | v (x : K) ≤ r}

/-- Strict balls in a discrete valuation are the expected powers of the maximal ideal. -/
theorem chapter06_strict_ball_eq_adic_coset
    {A : Subring K} (v : AbsoluteValue K ℝ) (m : Ideal A) (c : ℝ)
    (n : ℕ) (a : A)
    (hball : ∀ x : A, v (x : K) < c ^ n ↔
      x ∈ ((m ^ (n + 1) : Ideal A) : Set A)) :
    {x : A | v ((x : K) - (a : K)) < c ^ n} =
      chapter06AdicCoset m a (n + 1) := by
  ext x
  simp only [Set.mem_setOf_eq, chapter06AdicCoset]
  change v ((x : K) - (a : K)) < c ^ n ↔
    x - a ∈ ((m ^ (n + 1) : Ideal A) : Set A)
  simpa [sub_eq_add_neg] using hball (x - a)

/-- Weak balls have the corresponding alternative indexing by powers of the maximal ideal. -/
theorem chapter06_weak_ball_eq_adic_coset
    {A : Subring K} (v : AbsoluteValue K ℝ) (m : Ideal A) (c : ℝ)
    (n : ℕ) (a : A)
    (hball : ∀ x : A, v (x : K) ≤ c ^ n ↔
      x ∈ ((m ^ n : Ideal A) : Set A)) :
    {x : A | v ((x : K) - (a : K)) ≤ c ^ n} =
      chapter06AdicCoset m a n := by
  ext x
  simp only [Set.mem_setOf_eq, chapter06AdicCoset]
  change v ((x : K) - (a : K)) ≤ c ^ n ↔
    x - a ∈ ((m ^ n : Ideal A) : Set A)
  simpa [sub_eq_add_neg] using hball (x - a)

/-- With a discrete value scale, the valuation topology on a DVR is the `m`-adic topology. -/
theorem chapter06_valuation_topology_eq_adic_topology
    {A : Subring K} (v : AbsoluteValue K ℝ) (m : Ideal A) (c : ℝ)
    (hc : 0 < c) (hc1 : c < 1)
    (hball : ∀ n : ℕ, {x : A | v (x : K) < c ^ n} =
      ((m ^ (n + 1) : Ideal A) : Set A)) :
    chapter06InducedValuationTopology v A = m.adicTopology := by
  letI : UniformSpace K := v.uniformSpace
  apply TopologicalSpace.ext_nhds
  intro x
  have hval :
      (@nhds A (chapter06InducedValuationTopology v A) x).HasBasis
        (fun r : ℝ => 0 < r)
        (fun r => {y : A | v ((x : K) - (y : K)) < r}) := by
    rw [chapter06InducedValuationTopology, nhds_induced]
    simpa only [Set.preimage_setOf_eq, Set.mem_preimage, Set.mem_setOf_eq] using
      ((nhds_basis_uniformity (x := (x : K)) v.hasBasis_uniformity).comap
        ((↑) : A → K))
  have hadic :
      (@nhds A m.adicTopology x).HasBasis
        (fun _n : ℕ => True)
        (fun n => (fun y : A => x + y) ''
          ((m ^ (n + 1) : Ideal A) : Set A)) := by
    refine ⟨fun U => ?_⟩
    rw [(m.hasBasis_nhds_adic x).mem_iff]
    constructor
    · rintro ⟨n, -, hU⟩
      cases n with
      | zero =>
          refine ⟨0, trivial, ?_⟩
          intro y hy
          rcases hy with ⟨z, hz, rfl⟩
          exact hU ⟨z, by simp, rfl⟩
      | succ n =>
          refine ⟨n, trivial, ?_⟩
          simpa [Nat.succ_eq_add_one] using hU
    · rintro ⟨n, -, hU⟩
      exact ⟨n + 1, trivial, by simpa using hU⟩
  apply hval.ext hadic
  · intro r hr
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr hc1
    refine ⟨n, trivial, ?_⟩
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    have hz' : v (z : K) < c ^ n := by
      have : z ∈ {u : A | v (u : K) < c ^ n} := by
        rw [hball n]
        exact hz
      exact this
    simpa [sub_eq_add_neg, v.map_neg, add_comm, add_left_comm, add_assoc] using
      lt_trans hz' hn
  · intro n hn
    refine ⟨c ^ n, pow_pos hc n, ?_⟩
    intro y hy
    refine ⟨y - x, ?_, ?_⟩
    · have hz' : y - x ∈ {u : A | v (u : K) < c ^ n} := by
        change v ((y - x : A) : K) < c ^ n
        change v ((y : K) - (x : K)) < c ^ n
        have heq : (y : K) - (x : K) = - ((x : K) - (y : K)) := by ring
        rw [heq, v.map_neg]
        exact hy
      rw [hball n] at hz'
      exact hz'
    · ring

/-- If two adjacent side lengths differ, the third side is their maximum. -/
theorem chapter06_isosceles_triangle
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {x y z : K} (hne : v (x - y) ≠ v (y - z)) :
    v (x - z) = max (v (x - y)) (v (y - z)) := by
  simpa [sub_add_sub_cancel] using IsNonarchimedean.add_eq_max_of_ne hv hne

end Balls

/-! ### 6.2 Continuity of algebraic operations -/

section Operations

variable {K : Type*} [Field K]

/-- Translation is an isometry. -/
theorem chapter06_translation_isometry
    (v : AbsoluteValue K ℝ) (a x y : K) :
    chapter06Distance v (a + x) (a + y) = chapter06Distance v x y := by
  change v ((a + x) - (a + y)) = v (x - y)
  congr 1
  ring

/-- Multiplication by `a` scales distances by `|a|`. -/
theorem chapter06_multiplication_scales_distance
    (v : AbsoluteValue K ℝ) (a x y : K) :
    chapter06Distance v (a * x) (a * y) = v a * chapter06Distance v x y := by
  change v (a * x - a * y) = v a * v (x - y)
  rw [← mul_sub, v.map_mul]

/-- Addition is uniformly continuous with the displayed ultrametric estimate. -/
theorem chapter06_addition_uniform_estimate
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (x x' y y' : K) :
    chapter06Distance v (x + y) (x' + y') ≤
      max (chapter06Distance v x x') (chapter06Distance v y y') := by
  change v ((x + y) - (x' + y')) ≤ max (v (x - x')) (v (y - y'))
  calc
    v ((x + y) - (x' + y')) = v ((x - x') + (y - y')) := by
      congr 1 <;> ring
    _ ≤ max (v (x - x')) (v (y - y')) := hv _ _

/-- The algebraic difference identity used to control multiplication. -/
theorem chapter06_multiplication_difference_identity (x x' y y' : K) :
    x * y - x' * y' = x * (y - y') + y' * (x - x') := by
  ring

/-- Multiplication is uniformly controlled on bounded sets. -/
theorem chapter06_multiplication_bounded_estimate
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {C : ℝ} (hC : 0 ≤ C) {x x' y y' : K}
    (hx : v x ≤ C) (hy' : v y' ≤ C) :
    chapter06Distance v (x * y) (x' * y') ≤
      C * max (chapter06Distance v x x') (chapter06Distance v y y') := by
  change v (x * y - x' * y') ≤ C * max (v (x - x')) (v (y - y'))
  rw [chapter06_multiplication_difference_identity]
  calc
    v (x * (y - y') + y' * (x - x')) ≤
        max (v x * v (y - y')) (v y' * v (x - x')) := by
      calc
        v (x * (y - y') + y' * (x - x')) ≤
            max (v (x * (y - y'))) (v (y' * (x - x'))) := hv _ _
        _ = max (v x * v (y - y')) (v y' * v (x - x')) := by
          rw [v.map_mul, v.map_mul]
    _ ≤ max (C * v (y - y')) (C * v (x - x')) := by
      apply max_le
      · exact (mul_le_mul_of_nonneg_right hx (v.nonneg (y - y'))).trans
          (le_max_left _ _)
      · exact (mul_le_mul_of_nonneg_right hy' (v.nonneg (x - x'))).trans
          (le_max_right _ _)
    _ = C * max (v (y - y')) (v (x - x')) :=
      (mul_max_of_nonneg _ _ hC).symm
    _ = C * max (v (x - x')) (v (y - y')) := by rw [max_comm]

/-- The inversion difference formula away from zero. -/
theorem chapter06_inversion_difference_formula
    (v : AbsoluteValue K ℝ) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    chapter06Distance v x⁻¹ y⁻¹ =
      chapter06Distance v x y / (v x * v y) := by
  change v (x⁻¹ - y⁻¹) = v (x - y) / (v x * v y)
  have hxy : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by
    field_simp [hx, hy]
  rw [hxy]
  simp [div_eq_mul_inv, v.map_sub, v.map_mul, hx, hy]

/-- Inversion is continuous at every nonzero point, in epsilon form. -/
theorem chapter06_inversion_continuous_away_from_zero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {x : K} (hx : x ≠ 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ y : K,
      chapter06Distance v y x < δ →
        chapter06Distance v y⁻¹ x⁻¹ < ε := by
  intro ε hε
  have hxpos : 0 < v x := v.pos hx
  let δ : ℝ := min (v x) (ε * (v x * v x))
  have hδ : 0 < δ := lt_min hxpos (mul_pos hε (mul_pos hxpos hxpos))
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have hy0 : y ≠ 0 := by
    intro hy0
    subst y
    have : v x < δ := by simpa [chapter06Distance, v.map_neg] using hy
    exact (not_lt_of_ge (min_le_left _ _)) this
  change v (y - x) < δ at hy
  have hyx : v (y - x) < v x := lt_of_lt_of_le hy (min_le_left _ _)
  have hval : v y = v x := by
    calc
      v y = v ((y - x) + x) := by rw [sub_add_cancel]
      _ = v x := IsNonarchimedean.add_eq_right_of_lt hv hyx
  rw [chapter06_inversion_difference_formula v hy0 hx, hval]
  apply (div_lt_iff₀ (mul_pos hxpos hxpos)).2
  exact lt_of_lt_of_le hy (min_le_right _ _)

/-- Sufficient closeness to a nonzero point forces equality of absolute values. -/
theorem chapter06_abs_value_locally_constant_at_nonzero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {x y : K} (hx : x ≠ 0)
    (hxy : chapter06Distance v y x < v x) :
    v y = v x := by
  change v (y - x) < v x at hxy
  calc
    v y = v ((y - x) + x) := by rw [sub_add_cancel]
    _ = v x := IsNonarchimedean.add_eq_right_of_lt hv hxy

/-- The absolute value is continuous for its induced topology. -/
theorem chapter06_absolute_value_continuous (v : AbsoluteValue K ℝ) :
    @Continuous K ℝ v.uniformSpace.toTopologicalSpace inferInstance v := by
  letI : UniformSpace K := v.uniformSpace
  have huv : UniformContinuous v := by
    refine ((v.hasBasis_uniformity).uniformContinuous_iff
      Metric.uniformity_basis_dist).2 ?_
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro x y hxy
    change dist (v x) (v y) < ε
    have hy : v y ≤ v (y - x) + v x := by
      calc
        v y = v (y - 0) := by simp
        _ ≤ v (y - (y - x)) + v ((y - x) - 0) := v.sub_le y (y - x) 0
        _ = v (y - x) + v x := by ring_nf
    have hx : v x ≤ v (y - x) + v y := by
      calc
        v x = v (x - 0) := by simp
        _ ≤ v (x - (x - y)) + v ((x - y) - 0) := v.sub_le x (x - y) 0
        _ = v y + v (x - y) := by ring_nf
        _ = v (y - x) + v y := by rw [v.map_sub]; ring
    have habs : |v y - v x| ≤ v (y - x) := by
      rw [abs_le]
      constructor <;> linarith
    rw [Real.dist_eq]
    simpa [abs_sub_comm] using habs.trans_lt hxy
  exact huv.continuous

/-- The valuation topology makes a valued field a topological division ring. -/
theorem chapter06_valued_field_is_topological_division_ring
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    @IsTopologicalDivisionRing K (inferInstance : DivisionRing K)
      inferInstance := by
  infer_instance

/-- The valuation subring is open and closed. -/
theorem chapter06_valuation_subring_is_clopen
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] :
    IsClopen (((Valued.v : Valuation K Γ₀).valuationSubring : Set K)) := by
  exact Valued.isClopen_valuationSubring K

/-- Mathlib's open-units interface records that the unit group is open. -/
theorem chapter06_unit_group_is_open
    {A : Type*} [Monoid A] [TopologicalSpace A] [IsOpenUnits A] :
    IsOpen (Set.range (Units.val : Aˣ → A)) := by
  exact IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_range

/-- The residue/reduction map of a local ring. -/
def chapter06ReductionMap (A : Type*) [CommRing A] [IsLocalRing A] :
    A →+* IsLocalRing.ResidueField A :=
  IsLocalRing.residue A

/-- Fibers of reduction are cosets of the maximal ideal. -/
theorem chapter06_reduction_fiber_eq_maximalIdeal_coset
    {A : Type*} [CommRing A] [IsLocalRing A] (a : A) :
    chapter06ReductionMap A ⁻¹' ({chapter06ReductionMap A a} : Set (IsLocalRing.ResidueField A)) =
      chapter06AdicCoset (IsLocalRing.maximalIdeal A) a 1 := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, chapter06AdicCoset]
  change IsLocalRing.residue A x = IsLocalRing.residue A a ↔
    x - a ∈ (((IsLocalRing.maximalIdeal A) ^ 1 : Ideal A) : Set A)
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  simp

/-- Reduction to a discrete residue field is continuous once the maximal ideal is open. -/
theorem chapter06_reduction_continuous
    {A : Type*} [CommRing A] [IsLocalRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TopologicalSpace (IsLocalRing.ResidueField A)]
    [DiscreteTopology (IsLocalRing.ResidueField A)]
    (hm : @IsOpen A inferInstance (IsLocalRing.maximalIdeal A : Set A)) :
    @Continuous A (IsLocalRing.ResidueField A) inferInstance inferInstance (chapter06ReductionMap A) := by
  rw [continuous_discrete_rng]
  intro c
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
  change @IsOpen A inferInstance
    (chapter06ReductionMap A ⁻¹' ({chapter06ReductionMap A a} : Set _))
  rw [chapter06_reduction_fiber_eq_maximalIdeal_coset a]
  have heq : chapter06AdicCoset (IsLocalRing.maximalIdeal A) a 1 =
      a +ᵥ ((IsLocalRing.maximalIdeal A : Ideal A) : Set A) := by
    ext x
    simp only [chapter06AdicCoset, Set.mem_setOf_eq]
    change x - a ∈ (((IsLocalRing.maximalIdeal A) ^ 1 : Ideal A) : Set A) ↔
      x ∈ a +ᵥ ((IsLocalRing.maximalIdeal A : Ideal A) : Set A)
    simpa [pow_one, mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add, add_comm]
  rw [heq]
  exact hm.left_addCoset a

/-- Reduction modulo a power of an ideal. -/
def chapter06ReductionModPowMap {A : Type*} [CommRing A]
    (m : Ideal A) (n : ℕ) : A →+* A ⧸ (m ^ n) :=
  Ideal.Quotient.mk (m ^ n)

/-- Reduction modulo an open power of an ideal has discrete-target continuity. -/
theorem chapter06_reduction_mod_pow_continuous
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (m : Ideal A) (n : ℕ) [TopologicalSpace (A ⧸ (m ^ n))]
    [DiscreteTopology (A ⧸ (m ^ n))]
    (hmn : @IsOpen A inferInstance ((m ^ n : Ideal A) : Set A)) :
    @Continuous A (A ⧸ (m ^ n)) inferInstance inferInstance
      (chapter06ReductionModPowMap m n) := by
  rw [continuous_discrete_rng]
  intro c
  let a : A := Quotient.out c
  have ha : Ideal.Quotient.mk (m ^ n) a = c := Quotient.out_eq c
  have hfiber :
      (chapter06ReductionModPowMap m n) ⁻¹' ({c} : Set (A ⧸ (m ^ n))) =
        chapter06AdicCoset (m) a n := by
    ext x
    change Ideal.Quotient.mk (m ^ n) x = c ↔ x - a ∈ m ^ n
    rw [← ha, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  rw [hfiber]
  have heq : chapter06AdicCoset m a n =
      a +ᵥ ((m ^ n : Ideal A) : Set A) := by
    ext x
    simp only [chapter06AdicCoset, Set.mem_setOf_eq]
    change x - a ∈ ((m ^ n : Ideal A) : Set A) ↔
      x ∈ a +ᵥ ((m ^ n : Ideal A) : Set A)
    simpa [mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add, add_comm]
  rw [heq]
  exact hmn.left_addCoset a

end Operations

/-! ### 6.3 Cauchy sequences -/

section CauchySequences

variable {K : Type*} [Field K]

/-- Epsilon definition of a Cauchy sequence for an absolute value. -/
def chapter06CauchySeq (v : AbsoluteValue K ℝ) (x : ℕ → K) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
    N ≤ m → N ≤ n → chapter06Distance v (x m) (x n) < ε

/-- Epsilon definition of convergence in the valuation metric. -/
def chapter06ConvergesTo (v : AbsoluteValue K ℝ) (x : ℕ → K) (l : K) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ,
    N ≤ n → chapter06Distance v (x n) l < ε

/-- The terms of a sequence tend to zero. -/
def chapter06TendsToZero (v : AbsoluteValue K ℝ) (a : ℕ → K) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → v (a n) < ε

/-- Completeness stated only in terms of the chapter's valuation metric. -/
def chapter06CompleteValuedSpace (v : AbsoluteValue K ℝ) : Prop :=
  ∀ x : ℕ → K, chapter06CauchySeq v x → ∃ l : K, chapter06ConvergesTo v x l

/-- Convergent sequences are Cauchy. -/
theorem chapter06_convergent_is_cauchy
    (v : AbsoluteValue K ℝ) {x : ℕ → K} {l : K}
    (h : chapter06ConvergesTo v x l) : chapter06CauchySeq v x := by
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
  refine ⟨N, ?_⟩
  intro m n hm hn
  change v (x m - x n) < ε
  calc
    v (x m - x n) ≤ v (x m - l) + v (l - x n) := v.sub_le (x m) l (x n)
    _ = v (x m - l) + v (x n - l) := by
      congr 1
      exact v.map_sub l (x n)
    _ < ε := by
      have hm' : v (x m - l) < ε / 2 := by simpa [chapter06Distance] using hN m hm
      have hn' : v (x n - l) < ε / 2 := by simpa [chapter06Distance] using hN n hn
      linarith

/-- Limits in the valuation metric are unique. -/
theorem chapter06_limit_unique
    (v : AbsoluteValue K ℝ) {x : ℕ → K} {l l' : K}
    (hl : chapter06ConvergesTo v x l) (hl' : chapter06ConvergesTo v x l') :
    l = l' := by
  by_contra hne
  have hpos : 0 < v (l - l') := v.pos (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := hl (v (l - l') / 2) (half_pos hpos)
  obtain ⟨N', hN'⟩ := hl' (v (l - l') / 2) (half_pos hpos)
  let M := max N N'
  have hm : v (x M - l) < v (l - l') / 2 := by
    simpa [chapter06Distance] using hN M (le_max_left _ _)
  have hm' : v (x M - l') < v (l - l') / 2 := by
    simpa [chapter06Distance] using hN' M (le_max_right _ _)
  have hbound : v (l - l') ≤ v (l - x M) + v (x M - l') :=
    v.sub_le l (x M) l'
  have hsum : v (l - x M) + v (x M - l') < v (l - l') := by
    calc
      v (l - x M) + v (x M - l') =
          v (x M - l) + v (x M - l') := by
        congr 1
        exact v.map_sub l (x M)
      _ < v (l - l') / 2 + v (l - l') / 2 := add_lt_add hm hm'
      _ = v (l - l') := by ring
  exact (not_lt_of_ge hbound) hsum

/-- The finite-tail maximum estimate for consecutive increments. -/
theorem chapter06_consecutive_increment_tail_bound
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {x : ℕ → K} {n m : ℕ} (hnm : n < m)
    (hs : (Finset.Ico n m).Nonempty) :
    chapter06Distance v (x m) (x n) ≤
      (Finset.Ico n m).sup' hs
        (fun i => chapter06Distance v (x (i + 1)) (x i)) := by
  change v (x m - x n) ≤ _
  have hsum : ∀ k, n ≤ k →
      (Finset.sum (Finset.Ico n k) (fun i => x (i + 1) - x i)) = x k - x n := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
        rw [Finset.sum_Ico_succ_top hk, ih]
        ring
  rw [← hsum m hnm.le]
  change v (Finset.sum (Finset.Ico n m) (fun i => x (i + 1) - x i)) ≤
    (Finset.Ico n m).sup' hs (fun i => v (x (i + 1) - x i))
  exact IsNonarchimedean.apply_sum_le_sup hv hs

/-- Vanishing consecutive differences imply that a sequence is Cauchy. -/
theorem chapter06_cauchy_of_consecutive_differences_tend_to_zero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) {x : ℕ → K}
    (hinc : chapter06TendsToZero v (fun n => x (n + 1) - x n)) :
    chapter06CauchySeq v x := by
  intro ε hε
  obtain ⟨N, hN⟩ := hinc ε hε
  refine ⟨N, ?_⟩
  intro m n hm hn
  change v (x m - x n) < ε
  by_cases hmn : m < n
  · have htail₀ := chapter06_consecutive_increment_tail_bound (x := x) v hv hmn
      ⟨m, Finset.mem_Ico.mpr ⟨le_rfl, hmn⟩⟩
    have htail : v (x m - x n) ≤
        (Finset.Ico m n).sup'
          ⟨m, Finset.mem_Ico.mpr ⟨le_rfl, hmn⟩⟩
          (fun i => v (x (i + 1) - x i)) := by
      simpa only [chapter06Distance, v.map_sub] using htail₀
    apply lt_of_le_of_lt htail
    apply (Finset.sup'_lt_iff _).2
    intro i hi
    exact hN i (hm.trans (Finset.mem_Ico.mp hi).1)
  · by_cases hnm : n < m
    · have htail₀ := chapter06_consecutive_increment_tail_bound (x := x) v hv hnm
        ⟨n, Finset.mem_Ico.mpr ⟨le_rfl, hnm⟩⟩
      have htail : v (x m - x n) ≤
          (Finset.Ico n m).sup'
            ⟨n, Finset.mem_Ico.mpr ⟨le_rfl, hnm⟩⟩
            (fun i => v (x (i + 1) - x i)) := by
        simpa [chapter06Distance] using htail₀
      apply lt_of_le_of_lt htail
      apply (Finset.sup'_lt_iff _).2
      intro i hi
      exact hN i (hn.trans (Finset.mem_Ico.mp hi).1)
    · have heq : m = n := by omega
      subst n
      simpa [chapter06Distance] using hε

/-- A valuation-language version of “tends uniformly to infinity”. -/
def chapter06ValuationTendsToInfinity
    {Γ : Type*} [LinearOrder Γ] (w : K → Γ) (x : ℕ → K) : Prop :=
  ∀ M : Γ, ∃ N : ℕ, ∀ m n : ℕ,
    N ≤ m → N ≤ n → M < w (x m - x n)

/-- Compatibility of an absolute value and an additive valuation at their neighborhoods of zero. -/
def chapter06AbsoluteValueValuationCompatibility
    {Γ : Type*} [LinearOrder Γ] (v : AbsoluteValue K ℝ) (w : K → Γ) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ M : Γ, ∀ z : K,
      M < w z → v z < ε) ∧
    (∀ M : Γ, ∃ ε : ℝ, 0 < ε ∧ ∀ z : K,
      v z < ε → M < w z)

/-- Cauchy convergence is equivalent to valuation differences tending to infinity. -/
theorem chapter06_cauchy_iff_valuation_tends_to_infinity
    {Γ : Type*} [LinearOrder Γ]
    (v : AbsoluteValue K ℝ) (w : K → Γ)
    (hcompat : chapter06AbsoluteValueValuationCompatibility v w) (x : ℕ → K) :
    chapter06CauchySeq v x ↔ chapter06ValuationTendsToInfinity w x := by
  constructor
  · intro hc M
    obtain ⟨ε, hε, hεw⟩ := hcompat.2 M
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, ?_⟩
    intro m n hm hn
    exact hεw (x m - x n) (hN m n hm hn)
  · intro hw ε hε
    obtain ⟨M, hM⟩ := hcompat.1 ε hε
    obtain ⟨N, hN⟩ := hw M
    refine ⟨N, ?_⟩
    intro m n hm hn
    exact hM (x m - x n) (hN m n hm hn)

/-- A convergent sequence approaching a nonzero point eventually has constant absolute value. -/
theorem chapter06_eventual_absolute_value_eq_of_converges_to_nonzero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {x : ℕ → K} {l : K} (hl : chapter06ConvergesTo v x l) (hl0 : l ≠ 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → v (x n) = v l := by
  obtain ⟨N, hN⟩ := hl (v l) (v.pos hl0)
  refine ⟨N, ?_⟩
  intro n hn
  exact chapter06_abs_value_locally_constant_at_nonzero v hv hl0 (hN n hn)

/-- In the discrete-value case, the absolute value is locally constant on `Kˣ`. -/
theorem chapter06_absolute_value_locally_constant_on_nonzero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hdisc : chapter06DiscreteValueSet v) :
    ∀ x : K, x ≠ 0 →
      ∃ U : Set K, @IsOpen K v.uniformSpace.toTopologicalSpace U ∧ x ∈ U ∧
        ∀ y ∈ U, v y = v x := by
  intro x hx
  let U := chapter06OpenBall v x (v x)
  refine ⟨U, chapter06_openBall_isOpen v x (v x), ?_, ?_⟩
  · change v (x - x) < v x
    simp [hx]
  · intro y hy
    exact chapter06_abs_value_locally_constant_at_nonzero v hv hx hy

end CauchySequences

/-! ### 6.4 Series -/

section Series

variable {K : Type*} [Field K]

/-- The `n`th partial sum of a series indexed from zero. -/
def chapter06PartialSums (a : ℕ → K) (n : ℕ) : K :=
  Finset.sum (Finset.range n) (fun i => a i)

/-- A series has sum `s` in the valuation metric. -/
def chapter06SeriesConverges
    (v : AbsoluteValue K ℝ) (a : ℕ → K) (s : K) : Prop :=
  chapter06ConvergesTo v (chapter06PartialSums a) s

/-- Existential form of convergence of a series. -/
def chapter06SeriesHasSum (v : AbsoluteValue K ℝ) (a : ℕ → K) : Prop :=
  ∃ s : K, chapter06SeriesConverges v a s

/-- Finite tails of a nonarchimedean series are bounded by their largest term. -/
theorem chapter06_series_tail_bound
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a : ℕ → K} {n m : ℕ} (hnm : n < m)
    (hs : (Finset.Ico n m).Nonempty) :
    v (Finset.sum (Finset.Ico n m) (fun i => a i)) ≤
      (Finset.Ico n m).sup' hs (fun i => v (a i)) := by
  exact IsNonarchimedean.apply_sum_le_sup hv hs

/-- The difference of two partial sums is the corresponding finite tail sum. -/
theorem chapter06_partial_sum_difference_eq_tail
    (a : ℕ → K) {n m : ℕ} (hnm : n ≤ m) :
    chapter06PartialSums a m - chapter06PartialSums a n =
      Finset.sum (Finset.Ico n m) (fun i => a i) := by
  simp only [chapter06PartialSums]
  simpa using (Finset.sum_Ico_eq_sub (fun i => a i) hnm).symm

/-- Convergence of a series forces its terms to tend to zero. -/
theorem chapter06_series_convergence_implies_terms_tend_to_zero
    (v : AbsoluteValue K ℝ) {a : ℕ → K} {s : K}
    (h : chapter06SeriesConverges v a s) : chapter06TendsToZero v a := by
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
  refine ⟨N, ?_⟩
  intro n hn
  have hn1 : N ≤ n + 1 := hn.trans (Nat.le_succ n)
  have hterm : chapter06PartialSums a (n + 1) - chapter06PartialSums a n = a n := by
    rw [chapter06_partial_sum_difference_eq_tail a (Nat.le_succ n)]
    simp
  have h1 : v (chapter06PartialSums a (n + 1) - s) < ε / 2 := by
    simpa [chapter06Distance] using hN (n + 1) hn1
  have h2 : v (chapter06PartialSums a n - s) < ε / 2 := by
    simpa [chapter06Distance] using hN n hn
  calc
    v (a n) = v (chapter06PartialSums a (n + 1) - chapter06PartialSums a n) := by
      rw [hterm]
    _ ≤ v (chapter06PartialSums a (n + 1) - s) +
          v (s - chapter06PartialSums a n) :=
      v.sub_le (chapter06PartialSums a (n + 1)) s (chapter06PartialSums a n)
    _ = v (chapter06PartialSums a (n + 1) - s) +
          v (chapter06PartialSums a n - s) := by
      congr 1
      exact v.map_sub s (chapter06PartialSums a n)
    _ < ε := by linarith

/-- In a complete nonarchimedean field, a series converges exactly when its terms vanish. -/
theorem chapter06_series_converges_iff_terms_tend_to_zero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v) (a : ℕ → K) :
    chapter06SeriesHasSum v a ↔ chapter06TendsToZero v a := by
  constructor
  · rintro ⟨s, hs⟩
    exact chapter06_series_convergence_implies_terms_tend_to_zero v hs
  · intro hzero
    have hpc : chapter06CauchySeq v (chapter06PartialSums a) := by
      intro ε hε
      obtain ⟨N, hN⟩ := hzero ε hε
      refine ⟨N, ?_⟩
      intro m n hm hn
      by_cases hmn : m < n
      · have htail := chapter06_partial_sum_difference_eq_tail a hmn.le
        have hbound := chapter06_series_tail_bound (a := a) v hv hmn
          ⟨m, Finset.mem_Ico.mpr ⟨le_rfl, hmn⟩⟩
        have hsmall :
              (Finset.Ico m n).sup'
              ⟨m, Finset.mem_Ico.mpr ⟨le_rfl, hmn⟩⟩ (fun i => v (a i)) < ε := by
          apply (Finset.sup'_lt_iff _).2
          intro i hi
          exact hN i (hm.trans (Finset.mem_Ico.mp hi).1)
        have hdiff : v (chapter06PartialSums a n - chapter06PartialSums a m) < ε := by
          rw [htail]
          exact hbound.trans_lt hsmall
        simpa [chapter06Distance, v.map_sub] using hdiff
      · by_cases hnm : n < m
        · have htail := chapter06_partial_sum_difference_eq_tail a hnm.le
          have hbound := chapter06_series_tail_bound (a := a) v hv hnm
            ⟨n, Finset.mem_Ico.mpr ⟨le_rfl, hnm⟩⟩
          have hsmall :
                (Finset.Ico n m).sup'
                ⟨n, Finset.mem_Ico.mpr ⟨le_rfl, hnm⟩⟩ (fun i => v (a i)) < ε := by
            apply (Finset.sup'_lt_iff _).2
            intro i hi
            exact hN i (hn.trans (Finset.mem_Ico.mp hi).1)
          have hdiff : v (chapter06PartialSums a m - chapter06PartialSums a n) < ε := by
            rw [htail]
            exact hbound.trans_lt hsmall
          exact hdiff
        · have heq : m = n := by omega
          subst n
          simpa [chapter06Distance] using hε
    obtain ⟨s, hs⟩ := hcomplete (chapter06PartialSums a) hpc
    exact ⟨s, hs⟩

/-- The geometric series converges to `(1-x)⁻¹` when `|x| < 1`. -/
theorem chapter06_geometric_series
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v) {x : K} (hx : v x < 1) :
    chapter06SeriesConverges v (fun n => x ^ n) (1 - x)⁻¹ := by
  have hpow : chapter06TendsToZero v (fun n => x ^ n) := by
    intro ε hε
    have hev := (tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg x) hx).eventually
      (Iio_mem_nhds hε)
    rcases (eventually_atTop.1 hev) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    simpa [v.map_pow] using hN n hn
  have hne : 1 - x ≠ 0 := by
    intro h
    have hx1 : x = 1 := (sub_eq_zero.mp h).symm
    subst x
    simp at hx
  intro ε hε
  have hden : 0 < v ((1 - x)⁻¹) := v.pos (inv_ne_zero hne)
  have hev := (tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg x) hx).eventually
    (Iio_mem_nhds (div_pos hε hden))
  rcases (eventually_atTop.1 hev) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hgeom : chapter06PartialSums (fun n => x ^ n) n - (1 - x)⁻¹ =
      -x ^ n * (1 - x)⁻¹ := by
    simp only [chapter06PartialSums]
    field_simp [hne]
    rw [geom_sum_mul_neg]
    ring
  change v (chapter06PartialSums (fun n => x ^ n) n - (1 - x)⁻¹) < ε
  rw [hgeom]
  simp only [chapter06Distance, v.map_neg, v.map_mul, v.map_pow]
  exact (lt_div_iff₀ hden).1 (hN n hn)

/-- The principal-unit set of a local ring. -/
def chapter06PrincipalUnitSet (A : Type*) [CommRing A] [IsLocalRing A] : Set A :=
  {x | ∃ y ∈ (IsLocalRing.maximalIdeal A : Set A), x = 1 + y}

/-- `1 + 𝔪` lies in the unit group. -/
theorem chapter06_principal_units_are_units
    {A : Type*} [CommRing A] [IsLocalRing A] :
    chapter06PrincipalUnitSet A ⊆ Set.range (Units.val : Aˣ → A) := by
  rintro x ⟨y, hy, rfl⟩
  have hnot : (1 + y : A) ∉ IsLocalRing.maximalIdeal A := by
    intro hmem
    have hone : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      have := (IsLocalRing.maximalIdeal A).sub_mem hmem hy
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      ((IsLocalRing.maximalIdeal A).eq_top_iff_one.mpr hone)
  have hu : IsUnit (1 + y : A) := IsLocalRing.notMem_maximalIdeal.mp hnot
  rcases hu with ⟨u, hu⟩
  exact ⟨u, hu⟩

/-- The geometric identity accompanies the algebraic principal-unit assertion. -/
theorem chapter06_geometric_inverse_identity
    (v : AbsoluteValue K ℝ) {x : K} (hx : v x < 1) :
    (1 - x) * (1 - x)⁻¹ = 1 := by
  have hne : 1 - x ≠ 0 := by
    intro h
    have hx1 : x = 1 := (sub_eq_zero.mp h).symm
    subst x
    simp at hx
  exact mul_inv_cancel₀ hne

/-- A permutation of the natural numbers used to reorder a series. -/
def chapter06SeriesPermutation (σ : ℕ → ℕ) : Prop :=
  Function.Bijective σ

private theorem chapter06_comp_tendsToZero_of_finite_threshold
    {ι : Type*} (v : AbsoluteValue K ℝ) (a : ι → K)
    (hfinite : ∀ ε : ℝ, 0 < ε → ({i : ι | ε ≤ v (a i)} : Set ι).Finite)
    {σ : ℕ → ι} (hσ : Function.Injective σ) :
    chapter06TendsToZero v (a ∘ σ) := by
  intro ε hε
  have hbad := hfinite ε hε
  have hev : ∀ᶠ n : ℕ in (atTop : Filter ℕ), v (a (σ n)) < ε := by
    rw [← Nat.cofinite_eq_atTop]
    filter_upwards [hσ.tendsto_cofinite.eventually hbad.compl_mem_cofinite] with n hn
    change ¬ ε ≤ v (a (σ n)) at hn
    exact lt_of_not_ge hn
  exact eventually_atTop.1 hev

private theorem chapter06_reindexed_series_converges
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a : ℕ → K} (hzero : chapter06TendsToZero v a)
    {σ : ℕ → ℕ} (hσ : Function.Bijective σ) {s : K}
    (hs : chapter06SeriesConverges v a s) :
    chapter06SeriesConverges v (a ∘ σ) s := by
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨M₀, hM₀⟩ := hs δ hδ
  obtain ⟨N₀, hN₀⟩ := hzero δ hδ
  let g : ℕ → ℕ := fun k => Classical.choose (hσ.2 k)
  have hg : ∀ k : ℕ, σ (g k) = k := fun k => Classical.choose_spec (hσ.2 k)
  let P : Finset ℕ := (Finset.range N₀).image g
  obtain ⟨N, hNP⟩ := Finset.exists_nat_subset_range P
  refine ⟨N, ?_⟩
  intro n hn
  let t : Finset ℕ := (Finset.range n).image σ
  have hlow : Finset.range N₀ ⊆ t := by
    intro k hk
    have hkg : g k ∈ P := by
      dsimp [P]
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    have hgN : g k ∈ Finset.range N := hNP hkg
    have hgn : g k ∈ Finset.range n :=
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hgN) hn)
    dsimp [t]
    exact Finset.mem_image.mpr ⟨g k, hgn, hg k⟩
  obtain ⟨M₁, hM₁⟩ := Finset.exists_nat_subset_range t
  let M := max M₀ M₁
  have hMt : t ⊆ Finset.range M :=
    hM₁.trans (Finset.range_mono (le_max_right _ _))
  have hM₀M : M₀ ≤ M := le_max_left _ _
  have hsumσ : chapter06PartialSums (a ∘ σ) n = Finset.sum t a := by
    dsimp [chapter06PartialSums, t]
    simpa [Function.comp_def] using
      (Finset.sum_image (s := Finset.range n) (f := a) (g := σ)
        hσ.1.injOn).symm
  have hdiff_eq :
      chapter06PartialSums a M - chapter06PartialSums (a ∘ σ) n =
        Finset.sum (Finset.range M \ t) a := by
    rw [hsumσ]
    unfold chapter06PartialSums
    rw [← Finset.sum_sdiff hMt]
    ring
  have htail : v (Finset.sum (Finset.range M \ t) a) < δ := by
    by_cases hne : (Finset.range M \ t).Nonempty
    · apply lt_of_le_of_lt (IsNonarchimedean.apply_sum_le_sup hv hne)
      apply (Finset.sup'_lt_iff _).2
      intro i hi
      have hiN₀ : N₀ ≤ i := by
        apply Nat.le_of_not_gt
        intro hi'
        exact (Finset.mem_sdiff.mp hi).2 (hlow (Finset.mem_range.mpr hi'))
      exact hN₀ i hiN₀
    · have hempty : Finset.range M \ t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hempty, δ, hδ]
  have hclose : v (chapter06PartialSums (a ∘ σ) n - chapter06PartialSums a M) < δ := by
    simpa only [v.map_sub] using (show v (chapter06PartialSums a M -
      chapter06PartialSums (a ∘ σ) n) < δ from by simpa [hdiff_eq] using htail)
  have hlimit : v (chapter06PartialSums a M - s) < δ := by
    simpa [chapter06Distance] using hM₀ M hM₀M
  change v (chapter06PartialSums (a ∘ σ) n - s) < ε
  calc
    v (chapter06PartialSums (a ∘ σ) n - s) ≤
        v (chapter06PartialSums (a ∘ σ) n - chapter06PartialSums a M) +
          v (chapter06PartialSums a M - s) :=
      v.sub_le _ _ _
    _ < ε := by
      dsimp [δ] at hclose hlimit ⊢
      linarith

/-- Reordering a nonarchimedean series with vanishing terms preserves its sum. -/
theorem chapter06_series_reordering_invariant
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v) {a : ℕ → K}
    (hzero : chapter06TendsToZero v a) {σ : ℕ → ℕ}
    (hσ : chapter06SeriesPermutation σ) {s : K}
    (hs : chapter06SeriesConverges v a s) :
    chapter06SeriesConverges v (a ∘ σ) s := by
  change Function.Bijective σ at hσ
  exact chapter06_reindexed_series_converges v hv hzero hσ hs

/-- Threshold-finiteness of a doubly indexed family. -/
def chapter06DoubleSeriesThresholdFinite
    (v : AbsoluteValue K ℝ) (a : ℕ × ℕ → K) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ({p : ℕ × ℕ | ε ≤ v (a p)} : Set (ℕ × ℕ)).Finite

/-- Rearrangements of a threshold-finite double series have the same sum. -/
theorem chapter06_double_series_rearrangement
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v)
    {a : ℕ × ℕ → K} (hfinite : chapter06DoubleSeriesThresholdFinite v a)
    {e₁ e₂ : ℕ ≃ ℕ × ℕ} {s₁ s₂ : K}
    (h₁ : chapter06SeriesConverges v (a ∘ e₁) s₁)
    (h₂ : chapter06SeriesConverges v (a ∘ e₂) s₂) :
    s₁ = s₂ := by
  have hzero₁ : chapter06TendsToZero v (a ∘ e₁) := by
    apply chapter06_comp_tendsToZero_of_finite_threshold v a (σ := e₁)
    · exact fun ε hε => hfinite ε hε
    · exact e₁.injective
  let σe : ℕ ≃ ℕ := e₂.trans e₁.symm
  have hσ : chapter06SeriesPermutation σe := σe.bijective
  have hrel : (a ∘ e₁) ∘ σe = a ∘ e₂ := by
    funext n
    simp [σe, Function.comp_def]
  have hconv := chapter06_series_reordering_invariant v hv hcomplete hzero₁ hσ h₁
  have hconv' : chapter06SeriesConverges v (a ∘ e₂) s₁ := by
    simpa [hrel] using hconv
  exact chapter06_limit_unique v hconv' h₂

/-- A threshold-finite double series admits a common sum along every enumeration. -/
theorem chapter06_double_series_has_rearrangement_invariant_sum
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v)
    {a : ℕ × ℕ → K} (hfinite : chapter06DoubleSeriesThresholdFinite v a) :
    ∃ s : K, ∀ e : ℕ ≃ ℕ × ℕ,
      chapter06SeriesConverges v (a ∘ e) s := by
  let e₀ : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  have hzero₀ : chapter06TendsToZero v (a ∘ e₀) := by
    apply chapter06_comp_tendsToZero_of_finite_threshold v a (σ := e₀)
    · exact fun ε hε => hfinite ε hε
    · exact e₀.injective
  obtain ⟨s, hs⟩ :=
    (chapter06_series_converges_iff_terms_tend_to_zero v hv hcomplete (a ∘ e₀)).2 hzero₀
  refine ⟨s, ?_⟩
  intro e
  let σe : ℕ ≃ ℕ := e.trans e₀.symm
  have hσ : chapter06SeriesPermutation σe := σe.bijective
  have hrel : (a ∘ e₀) ∘ σe = a ∘ e := by
    funext n
    simp [σe, Function.comp_def]
  have hconv := chapter06_series_reordering_invariant v hv hcomplete hzero₀ hσ hs
  simpa [hrel] using hconv

/-- The geometric identity in Laurent series `k((t))`. -/
theorem chapter06_laurentSeries_geometric_example
    {k : Type*} [Field k]
    (v : AbsoluteValue (LaurentSeries k) ℝ)
    (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v)
    (hX : v ((PowerSeries.X : PowerSeries k) : LaurentSeries k) < 1) :
    chapter06SeriesConverges v
      (fun n => (((PowerSeries.X : PowerSeries k) : LaurentSeries k) ^ n))
      (1 - ((PowerSeries.X : PowerSeries k) : LaurentSeries k))⁻¹ := by
  exact chapter06_geometric_series v hv hcomplete hX

/-- The same geometric formula applies in `ℚ_p` for `|x|ₚ < 1`. -/
theorem chapter06_padic_geometric_example
    {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : ‖x‖ < 1) :
    chapter06SeriesConverges (NormedField.toAbsoluteValue ℚ_[p])
      (fun n => x ^ n) (1 - x)⁻¹ := by
  apply chapter06_geometric_series (NormedField.toAbsoluteValue ℚ_[p])
    (fun a b => IsUltrametricDist.norm_add_le_max a b)
  · intro u hu
    have hstd : CauchySeq u := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hu ε hε
      refine ⟨N, ?_⟩
      intro m hm n hn
      simpa [dist_eq_norm, chapter06Distance, NormedField.toAbsoluteValue] using hN m n hm hn
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hstd
    refine ⟨l, ?_⟩
    rw [Metric.tendsto_atTop] at hl
    intro ε hε
    obtain ⟨N, hN⟩ := hl ε hε
    exact ⟨N, fun n hn => by
      simpa [chapter06Distance, dist_eq_norm, NormedField.toAbsoluteValue] using hN n hn⟩
  · simpa [NormedField.toAbsoluteValue] using hx

/-- The geometric expression `1+p⁻¹+p⁻²+⋯` cannot converge p-adically. -/
theorem chapter06_padic_growing_geometric_series_diverges
    {p : ℕ} [Fact p.Prime] :
    ¬ chapter06SeriesHasSum (NormedField.toAbsoluteValue ℚ_[p])
      (fun n => (p : ℚ_[p]) ^ (-(n : ℤ))) := by
  intro h
  obtain ⟨s, hs⟩ := h
  have hzero := chapter06_series_convergence_implies_terms_tend_to_zero
    (NormedField.toAbsoluteValue ℚ_[p]) hs
  obtain ⟨N, hN⟩ := hzero 1 zero_lt_one
  have hp : (1 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hterm := hN N le_rfl
  have hnorm : ‖(p : ℚ_[p]) ^ (-(N : ℤ))‖ = (p : ℝ) ^ N := by
    simpa using (Padic.norm_p_zpow (p := p) (-(N : ℤ)))
  change ‖(p : ℚ_[p]) ^ (-(N : ℤ))‖ < 1 at hterm
  rw [hnorm] at hterm
  exact (not_lt_of_ge (one_le_pow₀ (le_of_lt hp))) hterm

end Series

/-! ### 6.5 Infinite products -/

section Products

variable {K : Type*} [Field K]

/-- The `n`th partial product of factors `1 + aₙ`. -/
def chapter06PartialProducts (a : ℕ → K) (n : ℕ) : K :=
  Finset.prod (Finset.range n) (fun i => (1 + a i))

/-- Convergence of the infinite product `∏ (1+aₙ)`. -/
def chapter06InfiniteProductConverges
    (v : AbsoluteValue K ℝ) (a : ℕ → K) (p : K) : Prop :=
  chapter06ConvergesTo v (chapter06PartialProducts a) p

/-- The finite tail product between two indices. -/
def chapter06ProductTail (a : ℕ → K) (n m : ℕ) : K :=
  Finset.prod (Finset.Ico n m) (fun i => (1 + a i))

/-- The product-tail analogue of the ultrametric maximum estimate. -/
theorem chapter06_product_tail_minus_one_bound
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a : ℕ → K} {n m : ℕ} (hnm : n < m)
    (hsmall : ∀ i ∈ Finset.Ico n m, v (a i) < 1)
    (hs : (Finset.Ico n m).Nonempty) :
    v (chapter06ProductTail a n m - 1) ≤
      (Finset.Ico n m).sup' hs (fun i => v (a i)) := by
  classical
  have hunit : ∀ i ∈ Finset.Ico n m, v (1 + a i) = 1 := by
    intro i hi
    have hi' := hsmall i hi
    have hi'' : v (a i) < v (1 : K) := by simpa using hi'
    simpa using IsNonarchimedean.add_eq_left_of_lt hv hi''
  have hmain : ∀ (s : Finset ℕ) (hs : s.Nonempty),
      s ⊆ Finset.Ico n m → (∀ i ∈ s, v (a i) < 1) →
      v ((Finset.prod s (fun i => 1 + a i)) - 1) ≤ s.sup' hs
        (fun i => v (a i)) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty =>
        exact (Finset.not_nonempty_empty hs).elim
    | @insert i s his ih =>
        intro hsubset hsmall'
        have hiI : i ∈ Finset.Ico n m := hsubset (Finset.mem_insert_self i s)
        have hunit_s : ∀ j ∈ s, v (1 + a j) = 1 := fun j hj =>
          hunit j (hsubset (Finset.mem_insert_of_mem hj))
        have hprod_s : v (Finset.prod s (fun j => 1 + a j)) = 1 := by
          rw [map_prod]
          apply Finset.prod_eq_one
          intro j hj
          exact hunit_s j hj
        by_cases hsne : s.Nonempty
        · have hsmall_s : ∀ j ∈ s, v (a j) < 1 := fun j hj => hsmall' j
            (Finset.mem_insert_of_mem hj)
          have hind := ih hsne (fun j hj => hsubset (Finset.mem_insert_of_mem hj)) hsmall_s
          have hid : (Finset.prod (insert i s) (fun j => 1 + a j)) - 1 =
              a i * (Finset.prod s (fun j => 1 + a j)) +
                ((Finset.prod s (fun j => 1 + a j)) - 1) := by
            rw [Finset.prod_insert his]
            ring
          calc
            v ((Finset.prod (insert i s) (fun j => 1 + a j)) - 1) ≤
                max (v (a i * (Finset.prod s (fun j => 1 + a j))))
                  (v ((Finset.prod s (fun j => 1 + a j)) - 1)) := by
              rw [hid]
              exact hv _ _
            _ = max (v (a i))
                (v ((Finset.prod s (fun j => 1 + a j)) - 1)) := by
              rw [v.map_mul, hprod_s, mul_one]
            _ ≤ (insert i s).sup' hs (fun j => v (a j)) := by
              exact max_le
                (Finset.le_sup' (fun j : ℕ => v (a j))
                  (Finset.mem_insert_self i s))
                (hind.trans (Finset.sup'_mono
                  (fun j : ℕ => v (a j))
                  (fun j hj => Finset.mem_insert_of_mem hj) hsne))
        · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsne
          subst s
          simpa [Finset.prod_singleton, Finset.sup'_singleton]
  simpa [chapter06ProductTail] using
    hmain (Finset.Ico n m) hs (Subset.rfl) hsmall

/-- Eventually, factors in a product with `aₙ → 0` are units of absolute value one. -/
theorem chapter06_eventual_product_factors_are_units
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) {a : ℕ → K}
    (hzero : chapter06TendsToZero v a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → v (a n) < 1 ∧ v (1 + a n) = 1 := by
  obtain ⟨N, hN⟩ := hzero 1 zero_lt_one
  refine ⟨N, ?_⟩
  intro n hn
  have hn' := hN n hn
  have hn'' : v (a n) < v (1 : K) := by simpa using hn'
  exact ⟨hn', by simpa using IsNonarchimedean.add_eq_left_of_lt hv hn''⟩

/-- In a complete nonarchimedean field, `aₙ → 0` makes the product converge. -/
theorem chapter06_infinite_product_converges_of_terms_tend_to_zero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v) {a : ℕ → K}
    (hzero : chapter06TendsToZero v a) :
    ∃ p : K, chapter06InfiniteProductConverges v a p := by
  obtain ⟨N, hN⟩ := chapter06_eventual_product_factors_are_units v hv hzero
  have hnorm : ∀ q : ℕ, N ≤ q →
      v (chapter06PartialProducts a q) = v (chapter06PartialProducts a N) := by
    intro q hq
    have hdecomp : chapter06PartialProducts a q =
        chapter06PartialProducts a N * chapter06ProductTail a N q := by
      unfold chapter06PartialProducts chapter06ProductTail
      rw [← Finset.prod_range_mul_prod_Ico _ hq]
    have htail : v (chapter06ProductTail a N q) = 1 := by
      unfold chapter06ProductTail
      rw [map_prod]
      apply Finset.prod_eq_one
      intro i hi
      exact (hN i (Finset.mem_Ico.mp hi).1).2
    rw [hdecomp, v.map_mul, htail, mul_one]
  have hinc : chapter06TendsToZero v
      (fun n => chapter06PartialProducts a (n + 1) - chapter06PartialProducts a n) := by
    intro ε hε
    by_cases hC : v (chapter06PartialProducts a N) = 0
    · refine ⟨N, ?_⟩
      intro n hn
      have hident : chapter06PartialProducts a (n + 1) - chapter06PartialProducts a n =
          chapter06PartialProducts a n * a n := by
        unfold chapter06PartialProducts
        rw [Finset.prod_range_succ]
        ring
      change v (chapter06PartialProducts a (n + 1) - chapter06PartialProducts a n) < ε
      rw [hident, v.map_mul, hnorm n hn, hC, zero_mul]
      exact hε
    · have hCpos : 0 < v (chapter06PartialProducts a N) :=
        have hP0 : chapter06PartialProducts a N ≠ 0 := by
          intro hP
          apply hC
          simp [hP]
        v.pos hP0
      obtain ⟨N', hN'⟩ := hzero (ε / v (chapter06PartialProducts a N))
        (div_pos hε hCpos)
      refine ⟨max N N', ?_⟩
      intro n hn
      have hnN : N ≤ n := le_trans (le_max_left _ _) hn
      have hnN' : N' ≤ n := le_trans (le_max_right _ _) hn
      have hident : chapter06PartialProducts a (n + 1) - chapter06PartialProducts a n =
          chapter06PartialProducts a n * a n := by
        unfold chapter06PartialProducts
        rw [Finset.prod_range_succ]
        ring
      change v (chapter06PartialProducts a (n + 1) - chapter06PartialProducts a n) < ε
      rw [hident, v.map_mul, hnorm n hnN]
      simpa [mul_comm] using (lt_div_iff₀ hCpos).1 (hN' n hnN')
  obtain ⟨p, hp⟩ := hcomplete (chapter06PartialProducts a)
    (chapter06_cauchy_of_consecutive_differences_tend_to_zero v hv hinc)
  exact ⟨p, hp⟩

/-- A product with vanishing corrections is nonzero when no factor is zero. -/
theorem chapter06_infinite_product_nonzero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a : ℕ → K} (hzero : chapter06TendsToZero v a)
    {p : K} (hp : chapter06InfiniteProductConverges v a p)
    (hfactor : ∀ n : ℕ, 1 + a n ≠ 0) :
    p ≠ 0 := by
  obtain ⟨N, hN⟩ := chapter06_eventual_product_factors_are_units v hv hzero
  have hPN : chapter06PartialProducts a N ≠ 0 := by
    intro hP
    have hP' : ∃ i ∈ Finset.range N, 1 + a i = 0 := by
      simpa [chapter06PartialProducts, Finset.prod_eq_zero_iff] using hP
    rcases hP' with ⟨i, hi, hfac⟩
    exact hfactor i (by simpa [chapter06PartialProducts] using hfac)
  have hCpos : 0 < v (chapter06PartialProducts a N) := v.pos hPN
  obtain ⟨M, hM⟩ := hp (v (chapter06PartialProducts a N)) hCpos
  let q := max N M
  have hqN : N ≤ q := le_max_left _ _
  have hqM : M ≤ q := le_max_right _ _
  have hnorm : v (chapter06PartialProducts a q) =
      v (chapter06PartialProducts a N) := by
    have hdecomp : chapter06PartialProducts a q =
        chapter06PartialProducts a N * chapter06ProductTail a N q := by
      unfold chapter06PartialProducts chapter06ProductTail
      rw [← Finset.prod_range_mul_prod_Ico _ hqN]
    have htail : v (chapter06ProductTail a N q) = 1 := by
      unfold chapter06ProductTail
      rw [map_prod]
      apply Finset.prod_eq_one
      intro i hi
      exact (hN i (Finset.mem_Ico.mp hi).1).2
    rw [hdecomp, v.map_mul, htail, mul_one]
  intro hp0
  have hdist := hM q hqM
  have hdist' : v (chapter06PartialProducts a q) <
      v (chapter06PartialProducts a N) := by
    simpa [chapter06Distance, hp0] using hdist
  exact (lt_irrefl _) (hnorm ▸ hdist')

/-- The convergence criterion for products needs vanishing corrections, not real summability. -/
theorem chapter06_product_criterion_is_vanishing_not_summability
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v) {a : ℕ → K} :
    chapter06TendsToZero v a →
      ∃ p : K, chapter06InfiniteProductConverges v a p := by
  intro hzero
  exact chapter06_infinite_product_converges_of_terms_tend_to_zero v hv hcomplete hzero

end Products

/-! ### 6.6 Compactness and local compactness -/

section Compactness

variable {A : Type*} [CommRing A]

/-- A residue-class cover modulo an ideal. -/
def chapter06ResidueClassCover (m : Ideal A) :
    (A ⧸ m) → Set A := fun c =>
      (Ideal.Quotient.mk m) ⁻¹' ({c} : Set (A ⧸ m))

/-- Finite quotients permit a subsequence constant in one residue class. -/
theorem chapter06_subsequence_constant_mod_ideal
    (m : Ideal A) [Finite (A ⧸ m)] (x : ℕ → A) :
    ∃ c : A ⧸ m, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n : ℕ, Ideal.Quotient.mk m (x (φ n)) = c := by
  classical
  let f : ℕ → A ⧸ m := fun n => Ideal.Quotient.mk m (x n)
  obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber f
  have htail : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ f n = c := by
    intro N
    obtain ⟨n, hn, hn'⟩ :=
      (Set.infinite_coe_iff.mp hc).exists_notMem_finset (Finset.range (N + 1))
    refine ⟨n, ?_, ?_⟩
    · have hnle : N + 1 ≤ n := Nat.le_of_not_gt (by
        simpa [Finset.mem_range] using hn')
      omega
    · simpa [f] using hn
  obtain ⟨φ, hφ, hφc⟩ := Nat.exists_strictMono_subsequence htail
  refine ⟨c, φ, hφ, ?_⟩
  intro n
  simpa [f] using hφc n

/-- Finite residue fields give finite quotients modulo all powers in a DVR. -/
theorem chapter06_dvr_power_quotient_finite
    [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] (n : ℕ) :
    Finite (A ⧸ ((IsLocalRing.maximalIdeal A) ^ n)) := by
  letI : Finite (A ⧸ IsLocalRing.maximalIdeal A) := by
    exact (inferInstance : Finite (IsLocalRing.ResidueField A))
  exact Ideal.finite_quotient_pow
    (IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal A)).fg n

/-- The diagonal subsequence construction is eventually constant modulo every power. -/
theorem chapter06_dvr_diagonal_subsequence
    [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)]
    (x : ℕ → A) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n : ℕ, ∃ a : A, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        x (φ k) - a ∈ (IsLocalRing.maximalIdeal A) ^ n := by
  classical
  let m := IsLocalRing.maximalIdeal A
  letI : Finite (A ⧸ m) := by
    dsimp [m]
    exact (inferInstance : Finite (IsLocalRing.ResidueField A))
  let H (n : ℕ) (g : ℕ → ℕ) :
      ∃ c : A ⧸ (m ^ (n + 1)), ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ k : ℕ,
          Ideal.Quotient.mk (m ^ (n + 1)) (x (g (ψ k))) = c :=
    by
      letI : Finite (A ⧸ (m ^ (n + 1))) :=
        chapter06_dvr_power_quotient_finite (n + 1)
      exact chapter06_subsequence_constant_mod_ideal
        (m := m ^ (n + 1)) (x := x ∘ g)
  let c (n : ℕ) (g : ℕ → ℕ) : A ⧸ (m ^ (n + 1)) := Classical.choose (H n g)
  let ψ (n : ℕ) (g : ℕ → ℕ) : ℕ → ℕ :=
    Classical.choose (Classical.choose_spec (H n g))
  let f : ℕ → (ℕ → ℕ) :=
    Nat.rec (fun k => k) (fun n g => g ∘ ψ n g)
  have hH (n : ℕ) (g : ℕ → ℕ) :
      StrictMono (ψ n g) ∧
        ∀ k : ℕ,
          Ideal.Quotient.mk (m ^ (n + 1)) (x (g (ψ n g k))) = c n g := by
    exact Classical.choose_spec (Classical.choose_spec (H n g))
  have hf_succ (n : ℕ) : f (n + 1) = f n ∘ ψ n (f n) := by
    rfl
  have hf_strict : ∀ n : ℕ, StrictMono (f n) := by
    intro n
    induction n with
    | zero => exact strictMono_id
    | succ n ih =>
        rw [hf_succ n]
        exact ih.comp (hH n (f n)).1
  have hf_const : ∀ n : ℕ, ∃ a : A, ∀ k : ℕ,
      x (f n k) - a ∈ m ^ n := by
    intro n
    induction n with
    | zero =>
        refine ⟨0, fun k => ?_⟩
        simp [m]
    | succ n ih =>
        obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (c n (f n))
        refine ⟨a, fun k => ?_⟩
        have hk := (hH n (f n)).2 k
        have hmk :
            Ideal.Quotient.mk (m ^ (n + 1)) (x (f (n + 1) k)) =
              Ideal.Quotient.mk (m ^ (n + 1)) a := by
          rw [hf_succ n]
          exact (hk.trans ha.symm)
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub, hmk]
        simp
  have hf_mem : ∀ {n j : ℕ}, n ≤ j → ∀ k : ℕ, ∃ l : ℕ, f j k = f n l := by
    intro n j hnj
    induction hnj with
    | refl =>
        intro k
        exact ⟨k, rfl⟩
    | @step j hnj ih =>
        intro k
        obtain ⟨l, hl⟩ := ih (ψ j (f j) k)
        refine ⟨l, ?_⟩
        rw [hf_succ j]
        simpa [Function.comp_apply] using hl
  have hdiag : StrictMono (fun n => f n n) := by
    intro i j hij
    have hfirst : f i i < f i (i + 1) := hf_strict i (Nat.lt_succ_self i)
    have hmid : f i (i + 1) ≤ f j (i + 1) := by
      induction hij with
      | refl =>
          rw [hf_succ i]
          exact (hf_strict i).monotone ((hH i (f i)).1.le_apply)
      | @step j hij ih =>
          exact ih.trans (by
            rw [hf_succ j]
            exact (hf_strict j).monotone ((hH j (f j)).1.le_apply))
    have hlast : f j (i + 1) ≤ f j j :=
      (hf_strict j).monotone (Nat.succ_le_iff.mpr hij)
    exact hfirst.trans_le (hmid.trans hlast)
  refine ⟨fun n => f n n, hdiag, ?_⟩
  intro n
  obtain ⟨a, ha⟩ := hf_const n
  refine ⟨a, n, fun k hk => ?_⟩
  obtain ⟨l, hl⟩ := hf_mem hk k
  simpa [hl] using ha l

/-- The diagonal subsequence is Cauchy in the maximal-ideal filtration. -/
def chapter06AdicCauchySeq (m : Ideal A) (x : ℕ → A) : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ i j : ℕ,
    N ≤ i → N ≤ j → x i - x j ∈ m ^ n

/-- The diagonal construction yields an adically Cauchy subsequence. -/
theorem chapter06_dvr_diagonal_subsequence_is_adic_cauchy
    [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)]
    (x : ℕ → A) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      chapter06AdicCauchySeq (IsLocalRing.maximalIdeal A) (x ∘ φ) := by
  obtain ⟨φ, hφ, hφc⟩ := chapter06_dvr_diagonal_subsequence x
  refine ⟨φ, hφ, ?_⟩
  intro n
  obtain ⟨a, N, hN⟩ := hφc n
  refine ⟨N, fun i j hi hj => ?_⟩
  simpa [Function.comp_apply, sub_eq_add_neg, sub_add_sub_cancel] using
    (IsLocalRing.maximalIdeal A ^ n).sub_mem (hN i hi) (hN j hj)

/-- A complete DVR with finite residue field has compact valuation ring. -/
theorem chapter06_complete_dvr_integer_compact
    [IsDomain A] [IsDiscreteValuationRing A]
    [Finite (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    @CompactSpace A (IsLocalRing.maximalIdeal A).adicTopology := by
  classical
  let m := IsLocalRing.maximalIdeal A
  let B := m.ringFilterBasis.toAddGroupFilterBasis
  letI : UniformSpace A := B.uniformSpace
  letI : IsUniformAddGroup A := B.isUniformAddGroup
  have hbasis :
      (@uniformity A B.uniformSpace).HasBasis (fun _ : ℕ => True)
        (fun n => {p : A × A |
          p.2 - p.1 ∈ ((m ^ n : Ideal A) : Set A)}) := by
    simpa [B] using (m.hasBasis_nhds_zero_adic.uniformity_of_nhds_zero)
  have htb : TotallyBounded (Set.univ : Set A) := by
    rw [hbasis.totallyBounded_iff]
    intro n _
    letI : Finite (A ⧸ m ^ n) := chapter06_dvr_power_quotient_finite n
    letI := Fintype.ofFinite (A ⧸ m ^ n)
    let rep : A ⧸ m ^ n → A := fun c => Classical.choose (Ideal.Quotient.mk_surjective c)
    have hrep (c : A ⧸ m ^ n) :
        Ideal.Quotient.mk (m ^ n) (rep c) = c :=
      Classical.choose_spec (Ideal.Quotient.mk_surjective c)
    refine ⟨Set.range rep, Set.finite_range rep, ?_⟩
    intro x _
    let c : A ⧸ m ^ n := Ideal.Quotient.mk (m ^ n) x
    refine Set.mem_iUnion.2 ⟨rep c, Set.mem_iUnion.2 ⟨Set.mem_range_self c, ?_⟩⟩
    change rep c - x ∈ ((m ^ n : Ideal A) : Set A)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hrep]
    simp [c]
  have hcomplete : CompleteSpace A := by
    exact ((IsAdic.isAdicComplete_iff (I := m) (by rfl)).mp
      (inferInstance : IsAdicComplete m A)).1
  refine ⟨?_⟩
  exact (isCompact_iff_totallyBounded_isComplete).2
    ⟨htb, completeSpace_iff_isComplete_univ.mp hcomplete⟩

/-- Infinite residue classes give an infinite disjoint open cover, hence noncompactness. -/
theorem chapter06_infinite_residue_field_integer_not_compact
    [IsDomain A] [IsDiscreteValuationRing A]
    [Infinite (IsLocalRing.ResidueField A)] :
    ¬ @CompactSpace A (IsLocalRing.maximalIdeal A).adicTopology := by
  classical
  let m := IsLocalRing.maximalIdeal A
  letI : Infinite (A ⧸ m) := by
    dsimp [m]
    exact (inferInstance : Infinite (IsLocalRing.ResidueField A))
  let B := m.ringFilterBasis.toAddGroupFilterBasis
  letI : UniformSpace A := B.uniformSpace
  letI : IsUniformAddGroup A := B.isUniformAddGroup
  have hm : @IsOpen A m.adicTopology (m : Set A) := by
    change @IsOpen A (IsLocalRing.maximalIdeal A).adicTopology
      (IsLocalRing.maximalIdeal A : Set A)
    convert ((IsLocalRing.maximalIdeal A).openAddSubgroup 1).isOpen' using 1
    simp [Ideal.openAddSubgroup, pow_one]
  have hcoset (c : A ⧸ m) :
      chapter06ResidueClassCover m c = c.out +ᵥ (m : Set A) := by
    ext x
    change Ideal.Quotient.mk m x = c ↔ x ∈ c.out +ᵥ (m : Set A)
    constructor
    · intro hx
      have hz : Ideal.Quotient.mk m (x - c.out) = 0 := by
        rw [map_sub, hx, Ideal.Quotient.mk_out]
        simp
      refine Set.mem_vadd_set.2 ⟨x - c.out,
        Ideal.Quotient.eq_zero_iff_mem.mp hz, ?_⟩
      simp only [vadd_eq_add]
      abel
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_vadd_set.1 hx
      rw [← hxy]
      simp only [vadd_eq_add, map_add, Ideal.Quotient.mk_out,
        Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero]
  have hopen : ∀ c : A ⧸ m, @IsOpen A m.adicTopology
      (chapter06ResidueClassCover m c) :=
    fun c => (hcoset c ▸ hm.left_addCoset c.out)
  have hcover : (Set.univ : Set A) ⊆ ⋃ c : A ⧸ m,
      chapter06ResidueClassCover m c := by
    intro a _
    exact Set.mem_iUnion.2 ⟨Ideal.Quotient.mk m a, by
      change Ideal.Quotient.mk m a = Ideal.Quotient.mk m a
      rfl⟩
  intro hcompact
  letI : CompactSpace A := hcompact
  obtain ⟨t, ht⟩ :=
    isCompact_univ.elim_finite_subcover
      (fun c : A ⧸ m => chapter06ResidueClassCover m c) hopen hcover
  have hfinite : (Set.univ : Set (A ⧸ m)).Finite := by
    refine t.finite_toSet.subset ?_
    intro c _
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨d, hd⟩ := Set.mem_iUnion.1 (ht (Set.mem_univ a))
    obtain ⟨hdt, had⟩ := Set.mem_iUnion.1 hd
    change Ideal.Quotient.mk m a = d at had
    exact ha ▸ (had ▸ hdt)
  exact (not_finite_iff_infinite.mpr (inferInstance : Infinite (A ⧸ m)))
    (Finite.of_finite_univ hfinite)

/-- The residue-class cover modulo the maximal ideal is exhaustive and pairwise disjoint. -/
theorem chapter06_maximalIdeal_residue_class_cover
    [IsLocalRing A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DiscreteTopology (A ⧸ IsLocalRing.maximalIdeal A)]
    (hm : @IsOpen A inferInstance (IsLocalRing.maximalIdeal A : Set A)) :
    (∀ c : A ⧸ IsLocalRing.maximalIdeal A,
        @IsOpen A inferInstance (chapter06ResidueClassCover (IsLocalRing.maximalIdeal A) c)) ∧
      (⋃ c : A ⧸ IsLocalRing.maximalIdeal A,
        chapter06ResidueClassCover (IsLocalRing.maximalIdeal A) c) = Set.univ ∧
      Pairwise (Disjoint on
        (chapter06ResidueClassCover (IsLocalRing.maximalIdeal A))) := by
  classical
  let m := IsLocalRing.maximalIdeal A
  have hcoset (c : A ⧸ m) :
      chapter06ResidueClassCover m c = c.out +ᵥ (m : Set A) := by
    ext x
    change Ideal.Quotient.mk m x = c ↔ x ∈ c.out +ᵥ (m : Set A)
    constructor
    · intro hx
      have hz : Ideal.Quotient.mk m (x - c.out) = 0 := by
        rw [map_sub, hx, Ideal.Quotient.mk_out]
        simp
      refine Set.mem_vadd_set.2 ⟨x - c.out,
        Ideal.Quotient.eq_zero_iff_mem.mp hz, ?_⟩
      simp only [vadd_eq_add]
      abel
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_vadd_set.1 hx
      rw [← hxy]
      simp only [vadd_eq_add, map_add, Ideal.Quotient.mk_out,
        Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero]
  have hopen : ∀ c : A ⧸ m, @IsOpen A inferInstance
      (chapter06ResidueClassCover m c) := by
    intro c
    rw [hcoset]
    exact hm.left_addCoset c.out
  refine ⟨hopen, ?_, ?_⟩
  · ext x
    simp [chapter06ResidueClassCover]
  · intro c d hcd
    change Disjoint (chapter06ResidueClassCover (IsLocalRing.maximalIdeal A) c)
      (chapter06ResidueClassCover (IsLocalRing.maximalIdeal A) d)
    rw [Set.disjoint_left]
    intro x hxc hxd
    apply hcd
    change Ideal.Quotient.mk m x = c at hxc
    change Ideal.Quotient.mk m x = d at hxd
    exact hxc.symm.trans hxd

/- The following theorem is the valued-field form of the compactness criterion. -/
section ValuedCompactness

variable {K : Type*} [Field K]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [(Valued.v : Valuation K Γ₀).RankOne]

/-- Compactness of the valuation ring is equivalent to completeness, DVR, and finite residue field. -/
theorem chapter06_integer_compact_iff_complete_dvr_finite_residue :
    CompactSpace ((Valued.v : Valuation K Γ₀).valuationSubring) ↔
      CompleteSpace ((Valued.v : Valuation K Γ₀).valuationSubring) ∧
        IsDiscreteValuationRing ((Valued.v : Valuation K Γ₀).valuationSubring) ∧
          Finite (IsLocalRing.ResidueField ((Valued.v : Valuation K Γ₀).valuationSubring)) := by
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField

/-- A complete discretely valued field is locally compact exactly when its residue field is finite. -/
theorem chapter06_complete_dv_field_locallyCompact_iff_finite_residue
    [CompleteSpace ((Valued.v : Valuation K Γ₀).valuationSubring)]
    [IsDiscreteValuationRing ((Valued.v : Valuation K Γ₀).valuationSubring)] :
    LocallyCompactSpace K ↔
      Finite (IsLocalRing.ResidueField ((Valued.v : Valuation K Γ₀).valuationSubring)) := by
  constructor
  · intro _
    letI : ProperSpace K :=
      ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
    exact
      (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
        (K := K) (Γ₀ := Γ₀)).mp (inferInstance : ProperSpace K) |>.2.2
  · intro hfinite
    letI : Finite (IsLocalRing.ResidueField
        ((Valued.v : Valuation K Γ₀).valuationSubring)) := hfinite
    have hc : CompactSpace ((Valued.v : Valuation K Γ₀).valuationSubring) :=
      (chapter06_integer_compact_iff_complete_dvr_finite_residue).mpr
        ⟨inferInstance, inferInstance, hfinite⟩
    letI : CompactSpace ((Valued.v : Valuation K Γ₀).valuationSubring) := hc
    letI : ProperSpace K :=
      (Valued.integer.properSpace_iff_compactSpace_integer (K := K) (Γ₀ := Γ₀)).mpr
        hc
    infer_instance

/-- Fractional valuation balls exhaust the field. -/
def chapter06FractionalDVRBall (A : Subring K) (π : A) (n : ℕ) : Set K :=
  {x | ∃ a : A, x = (a : K) * (π : K) ^ (-(n : ℤ))}

/-- The usual `K = ⋃ₙ π⁻ⁿ A` description. -/
theorem chapter06_field_is_union_fractional_dvr_balls
    (A : Subring K) (π : A)
    (hdecomp : ∀ x : K, ∃ n : ℕ, ∃ a : A,
      x = (a : K) * (π : K) ^ (-(n : ℤ))) :
    (Set.univ : Set K) = ⋃ n : ℕ, chapter06FractionalDVRBall A π n := by
  ext x
  constructor
  · intro _
    obtain ⟨n, a, ha⟩ := hdecomp x
    exact Set.mem_iUnion.2 ⟨n, ⟨a, ha⟩⟩
  · intro _
    trivial

/-- In the finite-residue case the field is locally compact but not compact. -/
theorem chapter06_complete_dv_field_locally_compact_not_compact
    [CompleteSpace ((Valued.v : Valuation K Γ₀).valuationSubring)]
    [IsDiscreteValuationRing ((Valued.v : Valuation K Γ₀).valuationSubring)]
    [Finite (IsLocalRing.ResidueField ((Valued.v : Valuation K Γ₀).valuationSubring))] :
    LocallyCompactSpace K ∧ ¬ CompactSpace K := by
  refine ⟨(chapter06_complete_dv_field_locallyCompact_iff_finite_residue).mpr inferInstance, ?_⟩
  intro hcompact
  have hfiniteK : Finite K :=
    DivisionRing.finite_of_compactSpace_of_t2Space
  exact (not_finite_iff_infinite.mpr (inferInstance : Infinite K)) hfiniteK

end ValuedCompactness

/-- The p-adic numbers are locally compact. -/
theorem chapter06_padic_numbers_locally_compact
    {p : ℕ} [Fact p.Prime] : LocallyCompactSpace ℚ_[p] := by
  infer_instance

/-- Finite extensions of p-adic fields are locally compact. -/
theorem chapter06_finite_extension_of_padic_field_locally_compact
    {p : ℕ} {L : Type*} [Fact p.Prime] [NormedField L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] :
    LocallyCompactSpace L := by
  exact LocallyCompactSpace.of_finiteDimensional_of_complete ℚ_[p] L

private noncomputable def chapter06LaurentUnitBallEquiv
    (k : Type*) [Field k] :
    k⟦X⟧ ≃+* (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring :=
  { toFun := fun F =>
      ⟨(F : LaurentSeries k), by
        rw [Valuation.mem_valuationSubring_iff]
        exact (LaurentSeries.val_le_one_iff_eq_coe k _).2 ⟨F, rfl⟩⟩
    invFun := fun x =>
      Classical.choose
        ((LaurentSeries.val_le_one_iff_eq_coe k (x : LaurentSeries k)).1
          ((Valuation.mem_valuationSubring_iff
            (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰) (x : LaurentSeries k)).1
            x.property))
    left_inv := by
      intro F
      apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k)
      simpa using
        (Classical.choose_spec
          ((LaurentSeries.val_le_one_iff_eq_coe k (F : LaurentSeries k)).1
            ((LaurentSeries.val_le_one_iff_eq_coe k (F : LaurentSeries k)).2 ⟨F, rfl⟩)))
    right_inv := by
      intro x
      apply Subtype.ext
      exact (Classical.choose_spec
        ((LaurentSeries.val_le_one_iff_eq_coe k (x : LaurentSeries k)).1
          ((Valuation.mem_valuationSubring_iff
            (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰) (x : LaurentSeries k)).1
            x.property)))
    map_add' := by
      intro F G
      apply Subtype.ext
      exact PowerSeries.coe_add F G
    map_mul' := by
      intro F G
      apply Subtype.ext
      exact PowerSeries.coe_mul F G }

private theorem chapter06LaurentUnitBallMaximalIdealComap
    (k : Type*) [Field k] :
    IsLocalRing.maximalIdeal k⟦X⟧ =
      (IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)).comap
        (chapter06LaurentUnitBallEquiv k) := by
  let e := chapter06LaurentUnitBallEquiv k
  ext F
  constructor
  · intro hF
    change e F ∈ IsLocalRing.maximalIdeal
      ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)
    apply (Valuation.mem_maximalIdeal_iff
      (K := LaurentSeries k)
      (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰)).2
    have hzero : PowerSeries.constantCoeff F = 0 := by
      rw [← PowerSeries.ker_coeff_eq_max_ideal] at hF
      exact RingHom.mem_ker.mp hF
    obtain ⟨G, hG⟩ := PowerSeries.X_dvd_iff.mpr hzero
    change (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰) (F : LaurentSeries k) < 1
    rw [hG, PowerSeries.coe_mul, map_mul]
    have hX :
        (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰)
            ((PowerSeries.X : k⟦X⟧) : LaurentSeries k) = WithZero.exp (-(1 : ℤ)) := by
      simpa using (LaurentSeries.valuation_X_pow (K := k) 1)
    rw [hX]
    have hGle :
        (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰) (G : LaurentSeries k) ≤
          (1 : ℤᵐ⁰) :=
      (LaurentSeries.val_le_one_iff_eq_coe k _).2 ⟨G, rfl⟩
    calc
      WithZero.exp (-(1 : ℤ)) *
          (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰) (G : LaurentSeries k) ≤
        WithZero.exp (-(1 : ℤ)) * 1 :=
        mul_le_mul_of_nonneg_left hGle WithZero.exp_pos.le
      _ = WithZero.exp (-(1 : ℤ)) := by simp
      _ < (1 : ℤᵐ⁰) := by
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        norm_num
  · intro hF
    change e F ∈ IsLocalRing.maximalIdeal
      ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring) at hF
    by_contra hzero
    have hu : IsUnit F := IsLocalRing.notMem_maximalIdeal.mp hzero
    have hue : IsUnit (e F) := hu.map e
    exact (IsLocalRing.notMem_maximalIdeal.mpr hue) hF

/-- `k((t))` is locally compact when `k` is finite. -/
theorem chapter06_laurentSeries_locally_compact_of_finite_residue
    {k : Type*} [Field k] [Finite k] :
    LocallyCompactSpace (LaurentSeries k) := by
  let e := chapter06LaurentUnitBallEquiv k
  have he : IsLocalRing.maximalIdeal k⟦X⟧ =
      (IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)).comap e :=
    chapter06LaurentUnitBallMaximalIdealComap k
  letI : (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).IsRankOneDiscrete := by
    change Valuation.IsRankOneDiscrete ((PowerSeries.idealX k).valuation (LaurentSeries k))
    infer_instance
  letI : (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne (v := Valued.v) (by norm_num : 1 < (2 : ℝ≥0))
  letI : CompleteSpace (LaurentSeries k) := inferInstance
  letI : CompleteSpace
      ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring) := by
    exact IsComplete.completeSpace_coe
      ((Valued.isClosed_valuationSubring (LaurentSeries k) (Γ₀ := ℤᵐ⁰)).isComplete)
  letI : Finite ( (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring ⧸
      IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)) := by
    apply Finite.of_surjective
      (fun a : k => Ideal.Quotient.mk _ (e (PowerSeries.C a)))
    intro x
    obtain ⟨F, hF⟩ := Ideal.Quotient.mk_surjective x
    let F' : k⟦X⟧ := e.symm F
    refine ⟨PowerSeries.constantCoeff F', ?_⟩
    have hmem : PowerSeries.C (PowerSeries.constantCoeff F') - F' ∈
        IsLocalRing.maximalIdeal k⟦X⟧ := by
      rw [← PowerSeries.ker_coeff_eq_max_ideal]
      simp
    have hmem' : e (PowerSeries.C (PowerSeries.constantCoeff F') - F') ∈
        IsLocalRing.maximalIdeal
          ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring) := by
      change PowerSeries.C (PowerSeries.constantCoeff F') - F' ∈
        (IsLocalRing.maximalIdeal
          ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)).comap e
      rw [← he]
      exact hmem
    have hF' : e F' = F := by
      dsimp [F']
      exact e.apply_symm_apply F
    rw [← hF, ← hF', ← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using hmem')
  letI : Finite (IsLocalRing.ResidueField
      ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)) := by
    change Finite ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring ⧸
      IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring))
    infer_instance
  exact (chapter06_complete_dv_field_locallyCompact_iff_finite_residue
    (K := LaurentSeries k) (Γ₀ := ℤᵐ⁰)).mpr inferInstance

/-- `k((t))` is not locally compact when `k` is infinite. -/
theorem chapter06_laurentSeries_not_locally_compact_of_infinite_residue
    {k : Type*} [Field k] [Infinite k] :
    ¬ LocallyCompactSpace (LaurentSeries k) := by
  intro hloc
  let e := chapter06LaurentUnitBallEquiv k
  have he : IsLocalRing.maximalIdeal k⟦X⟧ =
      (IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)).comap e :=
    chapter06LaurentUnitBallMaximalIdealComap k
  letI : (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).IsRankOneDiscrete := by
    change Valuation.IsRankOneDiscrete ((PowerSeries.idealX k).valuation (LaurentSeries k))
    infer_instance
  letI : (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne (v := Valued.v) (by norm_num : 1 < (2 : ℝ≥0))
  letI : CompleteSpace
      ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring) := by
    exact IsComplete.completeSpace_coe
      ((Valued.isClosed_valuationSubring (LaurentSeries k) (Γ₀ := ℤᵐ⁰)).isComplete)
  have hfin : Finite (IsLocalRing.ResidueField
      ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)) :=
    (chapter06_complete_dv_field_locallyCompact_iff_finite_residue
      (K := LaurentSeries k) (Γ₀ := ℤᵐ⁰)).mp hloc
  letI : Finite (IsLocalRing.ResidueField k⟦X⟧) := by
    letI : Finite (IsLocalRing.ResidueField
        ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring)) := hfin
    exact Finite.of_equiv
      (IsLocalRing.ResidueField
        ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).valuationSubring))
      (by
        simpa only [IsLocalRing.ResidueField] using
          (IsLocalRing.ResidueField.mapEquiv e).symm.toEquiv)
  letI : Finite k := by
    exact Finite.of_equiv (IsLocalRing.ResidueField k⟦X⟧)
      (PowerSeries.residueFieldOfPowerSeries (k := k)).toEquiv
  exact (not_finite_iff_infinite.mpr (inferInstance : Infinite k)) inferInstance

end Compactness

/-! ### 6.7 Nondiscrete topology -/

section Nondiscrete

variable {K : Type*} [Field K]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The real absolute value associated to a rank-one valuation. -/
noncomputable def chapter06RankOneAbsoluteValue
    (v : Valuation K Γ₀) [v.RankOne] : AbsoluteValue K ℝ :=
  { toMulHom :=
      { toFun := v.norm
        map_mul' := by
          intro x y
          simp only [Valuation.norm, ← NNReal.coe_mul, map_mul] }
    nonneg' := v.norm_nonneg
    eq_zero' := by
      intro x
      exact ⟨v.norm_eq_zero, fun hx => by simp [hx, Valuation.norm]⟩
    add_le' := by
      intro x y
      exact (v.norm_add_le x y).trans
        (max_le_add_of_nonneg (v.norm_nonneg x) (v.norm_nonneg y)) }

/-- A dense range of radii for the rank-one norm. -/
def chapter06DenseRankOneValueRange (v : Valuation K Γ₀) [v.RankOne] : Prop :=
  ∀ r s : ℝ, 0 < r → r < s →
    ∃ x : K, x ≠ 0 ∧ r < v.norm x ∧ v.norm x < s

/-- The rank-one valuation ring is the closed unit ball. -/
def chapter06RankOneValuationRingSet (v : Valuation K Γ₀) [v.RankOne] : Set K :=
  {x | v.norm x ≤ 1}

/-- The rank-one maximal ideal is the open unit ball, after coercion to the field. -/
def chapter06RankOneMaximalIdealImage (v : Valuation K Γ₀) [v.RankOne] : Set K :=
  ((fun x : v.valuationSubring => (x : K)) ''
    (IsLocalRing.maximalIdeal v.valuationSubring : Set v.valuationSubring))

/-- Closed-unit-ball and open-unit-ball descriptions of the valuation ring and maximal ideal. -/
theorem chapter06_rank_one_unit_ball_and_maximal_ball
    (v : Valuation K Γ₀) [v.RankOne] :
    (v.valuationSubring : Set K) = chapter06RankOneValuationRingSet v ∧
      chapter06RankOneMaximalIdealImage v = {x | v.norm x < 1} := by
  letI : Valued K Γ₀ := Valued.mk' v
  constructor
  · ext x
    change x ∈ v.valuationSubring ↔ v.norm x ≤ 1
    rw [Valuation.mem_valuationSubring_iff]
    exact (Valued.toNormedField.norm_le_one_iff (x := x)).symm
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Valued.toNormedField.norm_lt_one_iff (x := (y : K))).2
        ((Valuation.mem_maximalIdeal_iff (K := K) v).1 hy)
    · intro hx
      have hy : v x ≤ 1 :=
        ((Valued.toNormedField.norm_lt_one_iff (x := x)).1 hx).le
      let y : v.valuationSubring := ⟨x, by
        exact (Valuation.mem_valuationSubring_iff v x).2 hy⟩
      refine ⟨y, ?_, rfl⟩
      exact (Valuation.mem_maximalIdeal_iff (K := K) v).2
        ((Valued.toNormedField.norm_lt_one_iff (x := x)).1 hx)

/-- Valuation neighborhoods inside the valuation ring. -/
def chapter06RankOneValuationNeighborhood
    (v : Valuation K Γ₀) [v.RankOne] (r : ℝ) : Set v.valuationSubring :=
  {x | v.norm (x : K) < r}

/-- Cofinality of powers of the maximal ideal among valuation neighborhoods. -/
def chapter06PowersCofinalAmongValuationNeighborhoods
    (v : Valuation K Γ₀) [v.RankOne] : Prop :=
  ∀ r : ℝ, 0 < r → ∃ n : ℕ,
    (((IsLocalRing.maximalIdeal v.valuationSubring) ^ n :
      Ideal v.valuationSubring) : Set v.valuationSubring) ⊆
      chapter06RankOneValuationNeighborhood v r

/-- A factorization hypothesis expressing divisibility of positive values. -/
def chapter06MaximalIdealFactors
    (v : Valuation K Γ₀) : Prop :=
  ∀ x : v.valuationSubring,
    x ∈ IsLocalRing.maximalIdeal v.valuationSubring →
      ∃ y z : v.valuationSubring,
        y ∈ IsLocalRing.maximalIdeal v.valuationSubring ∧
          z ∈ IsLocalRing.maximalIdeal v.valuationSubring ∧ y * z = x

/-- Factoring every maximal-ideal element gives `𝔪² = 𝔪`. -/
theorem chapter06_maximalIdeal_idempotent_of_factors
    (v : Valuation K Γ₀) (hfactor : chapter06MaximalIdealFactors v) :
    IsLocalRing.maximalIdeal v.valuationSubring ^ 2 =
      IsLocalRing.maximalIdeal v.valuationSubring := by
  let m := IsLocalRing.maximalIdeal v.valuationSubring
  apply le_antisymm
  · simpa [pow_two] using (Ideal.mul_le_left : m * m ≤ m)
  · intro x hx
    obtain ⟨y, z, hy, hz, hxy⟩ := hfactor x hx
    rw [← hxy]
    simpa [pow_two] using (Ideal.mul_mem_mul hy hz)

/-- In a divisible value group, positive values can be split into smaller positive values. -/
def chapter06PositiveValueSplitting (v : Valuation K Γ₀) [v.RankOne] : Prop :=
  ∀ x : K, 0 < v x → v x < 1 →
    ∃ y z : K, 0 < v y ∧ 0 < v z ∧ v y < 1 ∧ v z < 1 ∧ v x = v y * v z

/-- Idempotent maximal ideals obstruct cofinality of powers in a dense valuation topology. -/
theorem chapter06_idempotent_maximalIdeal_not_power_cofinal
    (v : Valuation K Γ₀) [v.RankOne]
    (hid : IsLocalRing.maximalIdeal v.valuationSubring ^ 2 =
      IsLocalRing.maximalIdeal v.valuationSubring)
    (hnot : ∃ r : ℝ, 0 < r ∧
      ¬ ((IsLocalRing.maximalIdeal v.valuationSubring : Set v.valuationSubring) ⊆
        chapter06RankOneValuationNeighborhood v r)) :
    ¬ chapter06PowersCofinalAmongValuationNeighborhoods v := by
  intro hcofinal
  obtain ⟨r, hr, hmr⟩ := hnot
  obtain ⟨n, hn⟩ := hcofinal r hr
  have hp : ∀ n : ℕ, 0 < n →
      IsLocalRing.maximalIdeal v.valuationSubring ^ n =
        IsLocalRing.maximalIdeal v.valuationSubring := by
    intro n hnpos
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
    induction q with
    | zero => simp
    | succ q ih =>
        rw [pow_succ, ih (Nat.succ_pos q)]
        simpa [pow_two] using hid
  by_cases hnzero : n = 0
  · apply hmr
    subst n
    intro x hx
    exact hn (by
      change x ∈ ((IsLocalRing.maximalIdeal v.valuationSubring ^ 0 :
        Ideal v.valuationSubring) : Set v.valuationSubring)
      simp)
  · apply hmr
    intro x hx
    have : x ∈ ((IsLocalRing.maximalIdeal v.valuationSubring ^ n :
        Ideal v.valuationSubring) : Set v.valuationSubring) := by
      rw [hp n (Nat.pos_of_ne_zero hnzero)]
      exact hx
    exact hn this

/-- The valuation topology may be strictly finer than the `𝔪`-adic topology. -/
theorem chapter06_nondiscrete_madic_topology_can_be_coarser
    (v : Valuation K Γ₀) [v.RankOne]
    (hnotcofinal : ¬ chapter06PowersCofinalAmongValuationNeighborhoods v) :
    TopologicalSpace.induced ((↑) : v.valuationSubring → K)
        (chapter06RankOneAbsoluteValue v).uniformSpace.toTopologicalSpace ≠
      (IsLocalRing.maximalIdeal v.valuationSubring).adicTopology := by
  intro heq
  apply hnotcofinal
  intro r hr
  have hopen : @IsOpen K (chapter06RankOneAbsoluteValue v).uniformSpace.toTopologicalSpace
      {x | v.norm x < r} := by
    convert chapter06_openBall_isOpen (chapter06RankOneAbsoluteValue v) 0 r using 1
    ext x
    change v.norm x < r ↔ v.norm (x - 0) < r
    simp
  letI : TopologicalSpace v.valuationSubring :=
    TopologicalSpace.induced ((↑) : v.valuationSubring → K)
      (chapter06RankOneAbsoluteValue v).uniformSpace.toTopologicalSpace
  have hopen' : @IsOpen v.valuationSubring
      (TopologicalSpace.induced ((↑) : v.valuationSubring → K)
        (chapter06RankOneAbsoluteValue v).uniformSpace.toTopologicalSpace)
      (chapter06RankOneValuationNeighborhood v r) := by
    refine (isOpen_induced_iff
      (t := (chapter06RankOneAbsoluteValue v).uniformSpace.toTopologicalSpace)
      (f := fun x : v.valuationSubring => (x : K))).2 ?_
    refine ⟨{x | v.norm x < r}, hopen, ?_⟩
    ext x
    rfl
  have hzero : (0 : v.valuationSubring) ∈
      chapter06RankOneValuationNeighborhood v r := by
    change v.norm (0 : K) < r
    simpa [Valuation.norm] using hr
  have hmem := hopen'.mem_nhds hzero
  rw [heq] at hmem
  obtain ⟨n, -, hn⟩ :=
    (IsLocalRing.maximalIdeal v.valuationSubring).hasBasis_nhds_zero_adic.mem_iff.mp hmem
  exact ⟨n, hn⟩

/-- The compatible-family description of the adic completion. -/
theorem chapter06_adic_completion_is_compatible_family
    {A : Type*} [CommRing A] (m : Ideal A) (x : AdicCompletion m A)
    {i j : ℕ} (hij : i ≤ j) :
    AdicCompletion.transitionMap m A hij (x.val j) = x.val i := by
  exact x.property hij

/-- Completion notation for the topology induced by a real absolute value. -/
noncomputable def chapter06ValuationCompletion
    {A : Subring K} (v : AbsoluteValue K ℝ) :=
  @UniformSpace.Completion A
    (UniformSpace.comap ((↑) : A → K) v.uniformSpace)

/-- The inverse-limit topology on compatible families, with discrete coordinates. -/
def chapter06AdicCompletionTopology
    {A : Type*} [CommRing A] (m : Ideal A) :
    TopologicalSpace (AdicCompletion m A) :=
    TopologicalSpace.induced (fun x : AdicCompletion m A => x.1)
    (@Pi.topologicalSpace ℕ
      (fun n : ℕ => A ⧸ (m ^ n • (⊤ : Submodule A A))) (fun _ => ⊥))

/-- A topological equivalence between the valuation-ring completion and the adic completion. -/
structure Chapter06ValuationCompletionIdentification
    {A : Subring K} (v : AbsoluteValue K ℝ) (m : Ideal A) where
  toEquiv : chapter06ValuationCompletion (A := A) v ≃ AdicCompletion m A
  continuous_toEquiv :
    @Continuous (chapter06ValuationCompletion (A := A) v) (AdicCompletion m A)
      (@UniformSpace.Completion.uniformSpace A
        (UniformSpace.comap ((↑) : A → K) v.uniformSpace)).toTopologicalSpace
      (chapter06AdicCompletionTopology m) toEquiv
  continuous_inv :
    @Continuous (AdicCompletion m A) (chapter06ValuationCompletion (A := A) v)
      (chapter06AdicCompletionTopology m)
      (@UniformSpace.Completion.uniformSpace A
        (UniformSpace.comap ((↑) : A → K) v.uniformSpace)).toTopologicalSpace
      toEquiv.symm

/-- A proposition recording an identification of valuation and adic completions. -/
def chapter06ValuationCompletionIsAdic
    {A : Subring K} (v : AbsoluteValue K ℝ) (m : Ideal A) : Prop :=
  Nonempty (Chapter06ValuationCompletionIdentification (A := A) v m)

/-- The discrete/cofinal hypothesis used to compare a valuation completion with an adic one. -/
def chapter06CompletionIdentificationHypothesis
    {A : Subring K} (v : AbsoluteValue K ℝ) (m : Ideal A) : Prop :=
  (∀ x : K, x ∈ (A : Set K) ↔ v x ≤ 1) ∧
    (∀ x : K, ∃ a b : A, (b : K) ≠ 0 ∧
      x * (b : K) = (a : K)) ∧
    ((IsDiscreteValuationRing A ∧ m.IsMaximal) ∨
      ((∀ r : ℝ, 0 < r → ∃ n : ℕ,
          ((m ^ n : Ideal A) : Set A) ⊆ {x : A | v (x : K) < r}) ∧
        (∀ n : ℕ, ∃ r : ℝ, 0 < r ∧
          {x : A | v (x : K) < r} ⊆ ((m ^ n : Ideal A) : Set A))))

/-- An inverse-limit identification needs a discrete valuation or a cofinal chosen ideal. -/
theorem chapter06_completion_is_inverse_limit_under_discrete_or_cofinal
    {A : Subring K} (v : AbsoluteValue K ℝ) (m : Ideal A)
    (hallowed : chapter06CompletionIdentificationHypothesis v m) :
    chapter06ValuationCompletionIsAdic (A := A) v m := by
  classical
  rcases hallowed with ⟨hA, hfrac, hcase⟩
  have hcof1 : ∀ r : ℝ, 0 < r → ∃ n : ℕ,
      ((m ^ n : Ideal A) : Set A) ⊆ {x : A | v (x : K) < r} := by
    intro r hr
    rcases hcase with hD | hC
    · have hle : ∀ x y : K, v x ≤ v y → v (x + y) ≤ v y := by
        intro x y hxy
        by_cases hy : y = 0
        · simpa [hy] using hxy
        · have hratio : v (x / y) ≤ 1 := by
            rw [map_div₀, div_le_one₀ (v.pos hy)]
            exact hxy
          have hmem : x / y ∈ (A : Set K) := (hA (x / y)).2 hratio
          have hsum : x / y + 1 ∈ (A : Set K) := A.add_mem hmem A.one_mem
          have hsum_le : v (x / y + 1) ≤ 1 := (hA _).1 hsum
          have hident : x + y = y * (x / y + 1) := by
            field_simp [hy]
          rw [hident, v.map_mul]
          exact (mul_le_mul_of_nonneg_left hsum_le (v.nonneg y)).trans_eq (mul_one _)
      have hna : ∀ x y : K, v (x + y) ≤ max (v x) (v y) := by
        intro x y
        rcases le_total (v x) (v y) with hxy | hyx
        · simpa [max_eq_right hxy] using hle x y hxy
        · simpa [add_comm, max_eq_left hyx] using hle y x hyx
      let w : Valuation K ℝ≥0 :=
        { toMonoidWithZeroHom :=
            { toFun := fun x => ⟨v x, v.nonneg x⟩
              map_one' := by
                apply Subtype.ext
                simp
              map_zero' := by
                apply Subtype.ext
                simp
              map_mul' := by
                intro x y
                apply Subtype.ext
                change v (x * y) = v x * v y
                exact v.map_mul x y }
          map_add_le_max' := by
            intro x y
            change v (x + y) ≤ max (v x) (v y)
            exact hna x y }
      have hw : w.Integers A :=
        { hom_inj := by
            intro a b hab
            apply Subtype.ext
            exact hab
          map_le_one := by
            intro a
            apply NNReal.coe_le_coe.2
            change v (a : K) ≤ 1
            exact (hA (a : K)).1 a.property
          exists_of_le_one := by
            intro x hx
            have hx' : v x ≤ 1 := by
              exact NNReal.coe_le_coe.1 hx
            exact ⟨⟨x, (hA x).2 hx'⟩, rfl⟩ }
      letI : IsFractionRing A K := hw.isFractionRing
      letI : IsDiscreteValuationRing A := hD.1
      obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
      have hm_eq : m = IsLocalRing.maximalIdeal A :=
        IsLocalRing.eq_maximalIdeal hD.2
      have hm_pow (n : ℕ) : m ^ n = Ideal.span {(π : A) ^ n} := by
        rw [hm_eq, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
      have hpowset (n : ℕ) :
          ((m ^ n : Ideal A) : Set A) = {x : A | v (x : K) ≤ (v (π : K)) ^ n} := by
        rw [hm_pow, hw.coe_span_singleton_eq_setOfPred_le_v_algebraMap]
        ext x
        change v (x : K) ≤ v ((π : K) ^ n) ↔
          v (x : K) ≤ (v (π : K)) ^ n
        simp
      have hπ0 : (π : K) ≠ 0 := by
        intro h
        apply hπ.ne_zero
        apply Subtype.ext
        exact h
      have hπpos : 0 < v (π : K) := v.pos hπ0
      have hπlt : v (π : K) < 1 := by
        have hπlt' : w (algebraMap A K π) < 1 :=
          hw.valuation_irreducible_lt_one hπ
        change v (π : K) < 1 at hπlt'
        exact hπlt'
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr hπlt
      refine ⟨n, ?_⟩
      intro x hx
      rw [hpowset n] at hx
      exact hx.trans_lt hn
    · exact hC.1 r hr
  have hcof2 : ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧
      {x : A | v (x : K) < r} ⊆ ((m ^ n : Ideal A) : Set A) := by
    intro n
    rcases hcase with hD | hC
    · have hle : ∀ x y : K, v x ≤ v y → v (x + y) ≤ v y := by
        intro x y hxy
        by_cases hy : y = 0
        · simpa [hy] using hxy
        · have hratio : v (x / y) ≤ 1 := by
            rw [map_div₀, div_le_one₀ (v.pos hy)]
            exact hxy
          have hmem : x / y ∈ (A : Set K) := (hA (x / y)).2 hratio
          have hsum : x / y + 1 ∈ (A : Set K) := A.add_mem hmem A.one_mem
          have hsum_le : v (x / y + 1) ≤ 1 := (hA _).1 hsum
          have hident : x + y = y * (x / y + 1) := by
            field_simp [hy]
          rw [hident, v.map_mul]
          exact (mul_le_mul_of_nonneg_left hsum_le (v.nonneg y)).trans_eq (mul_one _)
      have hna : ∀ x y : K, v (x + y) ≤ max (v x) (v y) := by
        intro x y
        rcases le_total (v x) (v y) with hxy | hyx
        · simpa [max_eq_right hxy] using hle x y hxy
        · simpa [add_comm, max_eq_left hyx] using hle y x hyx
      let w : Valuation K ℝ≥0 :=
        { toMonoidWithZeroHom :=
            { toFun := fun x => ⟨v x, v.nonneg x⟩
              map_one' := by
                apply Subtype.ext
                simp
              map_zero' := by
                apply Subtype.ext
                simp
              map_mul' := by
                intro x y
                apply Subtype.ext
                change v (x * y) = v x * v y
                exact v.map_mul x y }
          map_add_le_max' := by
            intro x y
            change v (x + y) ≤ max (v x) (v y)
            exact hna x y }
      have hw : w.Integers A :=
        { hom_inj := by
            intro a b hab
            apply Subtype.ext
            exact hab
          map_le_one := by
            intro a
            apply NNReal.coe_le_coe.2
            change v (a : K) ≤ 1
            exact (hA (a : K)).1 a.property
          exists_of_le_one := by
            intro x hx
            have hx' : v x ≤ 1 := by
              exact NNReal.coe_le_coe.1 hx
            exact ⟨⟨x, (hA x).2 hx'⟩, rfl⟩ }
      letI : IsFractionRing A K := hw.isFractionRing
      letI : IsDiscreteValuationRing A := hD.1
      obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
      have hm_eq : m = IsLocalRing.maximalIdeal A :=
        IsLocalRing.eq_maximalIdeal hD.2
      have hm_pow (n : ℕ) : m ^ n = Ideal.span {(π : A) ^ n} := by
        rw [hm_eq, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
      have hpowset (n : ℕ) :
          ((m ^ n : Ideal A) : Set A) = {x : A | v (x : K) ≤ (v (π : K)) ^ n} := by
        rw [hm_pow, hw.coe_span_singleton_eq_setOfPred_le_v_algebraMap]
        ext x
        change v (x : K) ≤ v ((π : K) ^ n) ↔
          v (x : K) ≤ (v (π : K)) ^ n
        simp
      have hπ0 : (π : K) ≠ 0 := by
        intro h
        apply hπ.ne_zero
        apply Subtype.ext
        exact h
      have hπpos : 0 < v (π : K) := v.pos hπ0
      have hπlt : v (π : K) < 1 := by
        have hπlt' : w (algebraMap A K π) < 1 :=
          hw.valuation_irreducible_lt_one hπ
        change v (π : K) < 1 at hπlt'
        exact hπlt'
      refine ⟨(v (π : K)) ^ n, pow_pos hπpos n, ?_⟩
      intro x hx
      rw [hpowset n]
      change v (x : K) < (v (π : K)) ^ n at hx
      exact hx.le
    · exact hC.2 n
  let Q : ℕ → Type _ := fun n =>
    @Quotient (↥A)
      (Submodule.quotientRel (m ^ n • (⊤ : Submodule (↥A) (↥A))))
  let P := ∀ n, Q n
  let C := AdicCompletion m (↥A)
  letI (n : ℕ) : TopologicalSpace (Q n) := ⊥
  letI (n : ℕ) : UniformSpace (Q n) := ⊥
  letI (n : ℕ) : DiscreteTopology (Q n) := by infer_instance
  letI : TopologicalSpace P := inferInstance
  let uP : UniformSpace P := Pi.uniformSpace Q
  letI : UniformSpace P := uP
  let uC : UniformSpace C := UniformSpace.comap (fun x : C => x.1) uP
  letI : TopologicalSpace C := uC.toTopologicalSpace
  letI : UniformSpace C := uC
  let uVal : UniformSpace A :=
    UniformSpace.comap ((↑) : A → K) v.uniformSpace
  let f : A → C := AdicCompletion.of m (↥A)
  let S : Set P :=
    {z | ∀ {i j : ℕ} (hij : i ≤ j),
      AdicCompletion.transitionMap m (↥A) hij (z j) = z i}
  have hclosed : @IsClosed P uP.toTopologicalSpace S := by
    rw [show S = ⋂ i : ℕ, ⋂ j : ℕ, ⋂ hij : i ≤ j,
        {z : P | AdicCompletion.transitionMap m (↥A) hij (z j) = z i} by
      ext z
      simp [S]]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun hij =>
        isClosed_eq
          (continuous_of_discreteTopology.comp (continuous_apply j))
          (continuous_apply i)
  have hcomplete : @CompleteSpace C uC := by
    change CompleteSpace {z : P // z ∈ S}
    exact hclosed.completeSpace_coe
  have hdense : @DenseRange C uC.toTopologicalSpace A f := by
    rw [denseRange_iff_closure_range]
    apply eq_univ_iff_forall.mpr
    intro x
    rw [mem_closure_iff_nhds]
    intro U hU
    rw [nhds_induced] at hU
    rcases Filter.mem_comap.mp hU with ⟨V, hV, hVU⟩
    rw [nhds_pi] at hV
    rcases Filter.mem_pi'.mp hV with ⟨I, t, ht, hsub⟩
    have hsub' : Set.pi (↑I) (fun i => {x.1 i}) ⊆ V := by
      intro z hz
      apply hsub
      intro i hi
      rw [Set.mem_singleton_iff.mp (hz i hi)]
      exact mem_of_mem_nhds (ht i)
    let N : ℕ := I.sup id
    obtain ⟨a, ha⟩ :=
      Submodule.Quotient.mk_surjective
        (m ^ N • (⊤ : Submodule A A)) (x.1 N)
    have hcoord : ∀ i : ℕ, i ∈ I →
        (AdicCompletion.of m (↥A) a).1 i = x.1 i := by
      intro i hi
      have hiN : i ≤ N := Finset.le_sup (f := id) hi
      calc
        (AdicCompletion.of m (↥A) a).1 i =
            AdicCompletion.transitionMap m (↥A) hiN
              ((AdicCompletion.of m (↥A) a).1 N) := by
                rw [AdicCompletion.of_apply]
                symm
                exact Submodule.factor_mk
                  (Submodule.smul_mono_left (Ideal.pow_le_pow_right hiN)) a
        _ = AdicCompletion.transitionMap m (↥A) hiN (x.1 N) := by
              rw [AdicCompletion.of_apply, Submodule.mkQ_apply, ha]
        _ = x.1 i := x.property hiN
    have haV : (AdicCompletion.of m (↥A) a).1 ∈ V := by
      apply hsub'
      intro i hi
      exact Set.mem_singleton_iff.mpr (hcoord i hi)
    have haU : AdicCompletion.of m (↥A) a ∈ U := hVU haV
    exact ⟨AdicCompletion.of m (↥A) a, ⟨haU, ⟨a, rfl⟩⟩⟩
  have hsmul (n : ℕ) :
      (m ^ n • (⊤ : Submodule A A)) = (m ^ n : Submodule A A) := by
    simpa using (Ideal.smul_top_eq_map (m ^ n))
  have hval :
      (@uniformity A uVal).HasBasis
        (fun r : ℝ => 0 < r)
        (fun r => {p : A × A | v ((p.2 : K) - (p.1 : K)) < r}) := by
    simpa [uVal, uniformity_comap, Prod.map_apply', Set.preimage_ofPred_eq] using
      ((v.hasBasis_uniformity).comap
        (Prod.map ((↑) : A → K) ((↑) : A → K)))
  have hQ (n : ℕ) :
      (@uniformity (Q n) (⊥ : UniformSpace (Q n))).HasBasis
        (fun _ : Unit => True) (fun _ => SetRel.id) := by
    simpa only [bot_uniformity] using
      (Filter.hasBasis_principal (SetRel.id : SetRel (Q n) (Q n)))
  have hP :
      (@uniformity P uP).HasBasis
        (fun I : Set ℕ × (∀ _ : ℕ, Unit) =>
          I.1.Finite ∧ ∀ i ∈ I.1, True)
        (fun I => ⋂ i ∈ I.1,
          {p : P × P | p.1 i = p.2 i}) := by
    rw [Pi.uniformity]
    simpa [SetRel.id] using
      (Filter.HasBasis.iInf' (fun n =>
        (hQ n).comap (fun p : P × P => (p.1 n, p.2 n))))
  have hC :
      (@uniformity C uC).HasBasis
        (fun I : Set ℕ × (∀ _ : ℕ, Unit) => I.1.Finite)
        (fun I => ⋂ i ∈ I.1,
          {p : C × C | p.1.1 i = p.2.1 i}) := by
    change
      (Filter.comap (fun p : C × C => (p.1.1, p.2.1))
          (@uniformity P uP)).HasBasis _ _
    have h := hP.comap (fun p : C × C => (p.1.1, p.2.1))
    have hset :
        (fun I : Set ℕ × (∀ _ : ℕ, Unit) =>
            (fun p : C × C => (p.1.1, p.2.1)) ⁻¹'
              (⋂ i ∈ I.1, {p : P × P | p.1 i = p.2 i})) =
          (fun I : Set ℕ × (∀ _ : ℕ, Unit) =>
            ⋂ i ∈ I.1, {p : C × C | p.1.1 i = p.2.1 i}) := by
      funext I
      ext p
      simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h i hi
        have hp := h i hi
        change p.1.1 i = p.2.1 i at hp
        exact hp
      · intro h i hi
        change p.1.1 i = p.2.1 i
        exact h i hi
    rw [hset] at h
    simpa using h
  have huf : @IsUniformInducing A C uVal uC f := by
    apply (Filter.HasBasis.isUniformInducing_iff hval hC).2
    constructor
    · intro I hI
      let J : Finset ℕ := hI.toFinset
      let N : ℕ := J.sup id
      obtain ⟨r, hr, hrball⟩ := hcof2 N
      refine ⟨r, hr, ?_⟩
      intro x y hxy
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro i hi
      have hiN : i ≤ N := Finset.le_sup (f := id) (hI.mem_toFinset.mpr hi)
      have hdiffN : y - x ∈ ((m ^ N : Ideal A) : Set A) := hrball hxy
      have hdiffi : y - x ∈ ((m ^ i : Ideal A) : Set A) :=
        (Ideal.pow_le_pow_right hiN) hdiffN
      have hdiffi' : x - y ∈ ((m ^ i : Ideal A) : Set A) := by
        simpa [sub_eq_add_neg, add_comm] using (m ^ i).neg_mem hdiffi
      change (AdicCompletion.of m (↥A) x).1 i =
        (AdicCompletion.of m (↥A) y).1 i
      rw [AdicCompletion.of_apply, AdicCompletion.of_apply,
        hsmul i, Submodule.mkQ_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq]
      exact hdiffi'
    · intro r hr
      obtain ⟨n, hn⟩ := hcof1 r hr
      let I : Set ℕ := {n}
      refine ⟨⟨I, fun _ => ()⟩, finite_singleton n, ?_⟩
      intro x y hxy
      simp only [Set.mem_iInter, Set.mem_setOf_eq] at hxy
      have hxy' : (AdicCompletion.of m (↥A) x).1 n =
          (AdicCompletion.of m (↥A) y).1 n := by
        exact hxy n (by simp [I])
      have hdiff' : x - y ∈ ((m ^ n : Ideal A) : Set A) := by
        rw [AdicCompletion.of_apply, AdicCompletion.of_apply,
          Submodule.mkQ_apply, Submodule.mkQ_apply,
          Submodule.Quotient.eq] at hxy'
        simpa [hsmul n] using hxy'
      change v ((y : K) - (x : K)) < r
      have hmem := hn (by
        simpa [sub_eq_add_neg, add_comm] using (m ^ n).neg_mem hdiff')
      simpa [sub_eq_add_neg] using hmem
  letI : T0Space C := by
    exact
      (isUniformEmbedding_subtype_val (α := P) (p := fun z : P => z ∈ S)).isEmbedding.t0Space
  let pkg : @AbstractCompletion A uVal :=
    { space := C
      coe := f
      uniformStruct := uC
      complete := hcomplete
      separation := by infer_instance
      isUniformInducing := huf
      dense := hdense }
  let cpkg : @AbstractCompletion A uVal :=
    @UniformSpace.Completion.cPkg A uVal
  letI : UniformSpace cpkg.space := cpkg.uniformStruct
  let e : cpkg.space ≃ᵤ pkg.space := cpkg.compareEquiv pkg
  have htop : @UniformSpace.toTopologicalSpace C uC =
      chapter06AdicCompletionTopology m := by
    rfl
  refine ⟨{
    toEquiv := e.toEquiv
    continuous_toEquiv := ?_
    continuous_inv := ?_
  }⟩
  · rw [← htop]
    change @Continuous (UniformSpace.Completion A) C
      (@UniformSpace.Completion.uniformSpace A uVal).toTopologicalSpace
      (@UniformSpace.toTopologicalSpace C uC) e.toEquiv
    exact e.continuous
  · rw [← htop]
    change @Continuous C (UniformSpace.Completion A)
      (@UniformSpace.toTopologicalSpace C uC)
      (@UniformSpace.Completion.uniformSpace A uVal).toTopologicalSpace e.symm.toEquiv
    exact e.symm.continuous


end Nondiscrete

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter06
