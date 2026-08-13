import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter06

open Set Filter Function
open scoped BigOperators Pointwise Topology WithZero NNReal

noncomputable section

/-! # Book 1, Chapter 6, Section 6.1: Balls and the Strong Triangle Inequality
-/

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
@[instance_reducible]
noncomputable def chapter06MetricSpace (v : AbsoluteValue K ℝ) : MetricSpace K :=
  letI : NormedField K := v.toNormedField
  inferInstance

/-- The induced metric has the displayed formula `d(x,y) = |x-y|`. -/
theorem chapter06MetricSpace_dist (v : AbsoluteValue K ℝ) (x y : K) :
    @dist K (chapter06MetricSpace v).toPseudoMetricSpace.toDist x y =
      chapter06Distance v x y := by
  change v (-x + y) = v (x - y)
  simpa [sub_eq_add_neg, add_comm] using v.map_sub y x

theorem chapter06_openBall_isOpen
    (v : AbsoluteValue K ℝ) (a : K) (r : ℝ) :
    @IsOpen K v.uniformSpace.toTopologicalSpace (chapter06OpenBall v a r) := by
  let _ : UniformSpace K := v.uniformSpace
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
    (v : AbsoluteValue K ℝ) (_hv : chapter06AbsoluteValueIsNontrivial v) :
    ∃ m : MetricSpace K,
      ∀ x y : K, @dist K m.toPseudoMetricSpace.toDist x y = chapter06Distance v x y := by
  refine ⟨chapter06MetricSpace v, ?_⟩
  intro x y
  exact chapter06MetricSpace_dist v x y

/-- A bundled absolute value, including the trivial one, supplies the metric used
    in the chapter. -/
theorem chapter06_absolute_value_gives_metric
    (v : AbsoluteValue K ℝ) :
    ∃ m : MetricSpace K,
      ∀ x y : K, @dist K m.toPseudoMetricSpace.toDist x y = chapter06Distance v x y := by
  refine ⟨chapter06MetricSpace v, ?_⟩
  intro x y
  exact chapter06MetricSpace_dist v x y

/-- In the trivial case this metric is the discrete metric off the diagonal. -/
theorem chapter06_trivial_absolute_value_is_discrete_distance
    (v : AbsoluteValue K ℝ) (hv : ¬ chapter06AbsoluteValueIsNontrivial v)
    {x y : K} (hxy : x ≠ y) :
    chapter06Distance v x y = 1 := by
  change v (x - y) = 1
  exact v.not_isNontrivial_apply hv (sub_ne_zero.mpr hxy)

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
  let _ : UniformSpace K := v.uniformSpace
  rw [← isOpen_compl_iff, chapter06_openBall_complement_iUnion v hv hr]
  exact isOpen_iUnion (fun x => chapter06_openBall_isOpen v (x : K) r)

/-- Discreteness supplies the next radius and makes closed balls open. -/
theorem chapter06_closedBall_isOpen_of_discrete_values
    (v : AbsoluteValue K ℝ) (_hv : IsNonarchimedean v)
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
  let _ : UniformSpace K := v.uniformSpace
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
  exact (lt_irrefl r) (by change v (x - y) < r; exact hxy')

/-- The adic coset corresponding to a power of an ideal. -/
def chapter06AdicCoset {A : Type*} [CommRing A]
    (m : Ideal A) (a : A) (n : ℕ) : Set A :=
  {x | x - a ∈ ((m ^ n : Ideal A) : Set A)}

/-- The topology on a subring induced from a valuation topology on its fraction field. -/
@[instance_reducible]
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
  simp only [Set.mem_ofPred_eq, chapter06AdicCoset]
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
  simp only [Set.mem_ofPred_eq, chapter06AdicCoset]
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
  let _ : UniformSpace K := v.uniformSpace
  apply TopologicalSpace.ext_nhds
  intro x
  have hval :
      (@nhds A (chapter06InducedValuationTopology v A) x).HasBasis
        (fun r : ℝ => 0 < r)
        (fun r => {y : A | v ((x : K) - (y : K)) < r}) := by
    rw [chapter06InducedValuationTopology, nhds_induced]
    simpa only [Set.preimage_ofPred_eq, Set.mem_preimage, Set.mem_ofPred_eq] using
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
  have hxy : v (x - z) ≤ max (v (x - y)) (v (y - z)) := by
    simpa [chapter06Distance] using
      (chapter06_strong_triangle_inequality v hv x y z)
  have hyz : v (y - z) ≤ max (v (x - y)) (v (x - z)) := by
    simpa only [chapter06Distance, v.map_sub] using
      (chapter06_strong_triangle_inequality v hv y x z)
  have hxy' : v (x - y) ≤ max (v (x - z)) (v (y - z)) := by
    simpa only [chapter06Distance, v.map_sub] using
      (chapter06_strong_triangle_inequality v hv x z y)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hzy : v (y - z) ≤ v (x - z) := by
      by_contra hnot
      have hlt' : v (x - z) < v (y - z) := lt_of_not_ge hnot
      exact (not_lt_of_ge hyz) (max_lt hlt hlt')
    have hupper : v (x - z) ≤ v (y - z) := by
      simpa [max_eq_right (le_of_lt hlt)] using hxy
    exact (max_eq_right (le_of_lt hlt)).symm ▸ le_antisymm hupper hzy
  · have hzx : v (x - y) ≤ v (x - z) := by
      by_contra hnot
      have hlt' : v (x - z) < v (x - y) := lt_of_not_ge hnot
      exact (not_lt_of_ge hxy') (max_lt hlt' hgt)
    have hupper : v (x - z) ≤ v (x - y) := by
      simpa [max_eq_left (le_of_lt hgt)] using hxy
    exact (max_eq_left (le_of_lt hgt)).symm ▸ le_antisymm hupper hzx

end Balls

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter06
