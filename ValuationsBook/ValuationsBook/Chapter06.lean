import Mathlib

namespace ValuationsBook.Chapter06

open Set Filter Function
open scoped BigOperators Pointwise Topology

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
  sorry

/-- A nontrivial absolute value gives the metric asserted at the start of §6.1. -/
theorem chapter06_nontrivial_absolute_value_gives_metric
    (v : AbsoluteValue K ℝ) (hv : chapter06AbsoluteValueIsNontrivial v) :
    ∃ m : MetricSpace K,
      ∀ x y : K, @dist K m.toPseudoMetricSpace.toDist x y = chapter06Distance v x y := by
  sorry

/-- The strong triangle inequality in distance form. -/
theorem chapter06_strong_triangle_inequality
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (x y z : K) :
    chapter06Distance v x z ≤
      max (chapter06Distance v x y) (chapter06Distance v y z) := by
  sorry

/-- A point of an open ball is a center for the same ball. -/
theorem chapter06_openBall_center_invariance
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a y : K} {r : ℝ} (hy : y ∈ chapter06OpenBall v a r) :
    chapter06OpenBall v y r = chapter06OpenBall v a r := by
  sorry

/-- Two open balls of the same radius are disjoint or equal. -/
theorem chapter06_openBall_same_radius_disjoint_or_equal
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a b : K} {r : ℝ} :
    Disjoint (chapter06OpenBall v a r) (chapter06OpenBall v b r) ∨
      chapter06OpenBall v a r = chapter06OpenBall v b r := by
  sorry

/-- Meeting balls with comparable radii are nested. -/
theorem chapter06_openBall_nested_of_meeting
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a b : K} {r s : ℝ}
    (hmeet : (chapter06OpenBall v a r ∩ chapter06OpenBall v b s).Nonempty)
    (hcomp : r ≤ s ∨ s ≤ r) :
    chapter06OpenBall v a r ⊆ chapter06OpenBall v b s ∨
      chapter06OpenBall v b s ⊆ chapter06OpenBall v a r := by
  sorry

/-- The complement of an open ball is covered by balls of the same radius. -/
theorem chapter06_openBall_complement_iUnion
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a : K} {r : ℝ} (hr : 0 < r) :
    (chapter06OpenBall v a r)ᶜ =
      ⋃ x : {x : K // x ∉ chapter06OpenBall v a r},
        chapter06OpenBall v (x : K) r := by
  sorry

/-- Open balls are closed in the absolute-value topology. -/
theorem chapter06_openBall_isClosed
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a : K} {r : ℝ} (hr : 0 < r) :
    @IsClosed K v.uniformSpace.toTopologicalSpace (chapter06OpenBall v a r) := by
  sorry

/-- Discreteness supplies the next radius and makes closed balls open. -/
theorem chapter06_closedBall_isOpen_of_discrete_values
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hdisc : chapter06DiscreteValueSet v) {a : K} {r : ℝ} (hr : 0 < r) :
    @IsOpen K v.uniformSpace.toTopologicalSpace (chapter06ClosedBall v a r) := by
  sorry

/-- Every connected subset of a nonarchimedean metric space is a singleton. -/
theorem chapter06_connected_subset_is_singleton
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) {s : Set K}
    (hs : @IsConnected K v.uniformSpace.toTopologicalSpace s) :
    ∀ x ∈ s, ∀ y ∈ s, x = y := by
  sorry

/-- The adic coset corresponding to a power of an ideal. -/
def chapter06AdicCoset {A : Type*} [CommRing A]
    (m : Ideal A) (a : A) (n : ℕ) : Set A :=
  {x | x - a ∈ m ^ n}

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
    (hball : ∀ x : A, v (x : K) < c ^ n ↔ x ∈ (m ^ (n + 1) : Set A)) :
    {x : A | v ((x : K) - (a : K)) < c ^ n} =
      chapter06AdicCoset m a (n + 1) := by
  sorry

/-- Weak balls have the corresponding alternative indexing by powers of the maximal ideal. -/
theorem chapter06_weak_ball_eq_adic_coset
    {A : Subring K} (v : AbsoluteValue K ℝ) (m : Ideal A) (c : ℝ)
    (n : ℕ) (a : A)
    (hball : ∀ x : A, v (x : K) ≤ c ^ n ↔ x ∈ (m ^ n : Set A)) :
    {x : A | v ((x : K) - (a : K)) ≤ c ^ n} =
      chapter06AdicCoset m a n := by
  sorry

/-- With a discrete value scale, the valuation topology on a DVR is the `m`-adic topology. -/
theorem chapter06_valuation_topology_eq_adic_topology
    {A : Subring K} (v : AbsoluteValue K ℝ) (m : Ideal A) (c : ℝ)
    (hc : 0 < c) (hc1 : c < 1)
    (hball : ∀ n : ℕ, {x : A | v (x : K) < c ^ n} = (m ^ (n + 1) : Set A)) :
    chapter06InducedValuationTopology v A = m.adicTopology := by
  sorry

/-- If two adjacent side lengths differ, the third side is their maximum. -/
theorem chapter06_isosceles_triangle
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {x y z : K} (hne : v (x - y) ≠ v (y - z)) :
    v (x - z) = max (v (x - y)) (v (y - z)) := by
  sorry

end Balls

/-! ### 6.2 Continuity of algebraic operations -/

section Operations

variable {K : Type*} [Field K]

/-- Translation is an isometry. -/
theorem chapter06_translation_isometry
    (v : AbsoluteValue K ℝ) (a x y : K) :
    chapter06Distance v (a + x) (a + y) = chapter06Distance v x y := by
  sorry

/-- Multiplication by `a` scales distances by `|a|`. -/
theorem chapter06_multiplication_scales_distance
    (v : AbsoluteValue K ℝ) (a x y : K) :
    chapter06Distance v (a * x) (a * y) = v a * chapter06Distance v x y := by
  sorry

/-- Addition is uniformly continuous with the displayed ultrametric estimate. -/
theorem chapter06_addition_uniform_estimate
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (x x' y y' : K) :
    chapter06Distance v (x + y) (x' + y') ≤
      max (chapter06Distance v x x') (chapter06Distance v y y') := by
  sorry

/-- The algebraic difference identity used to control multiplication. -/
theorem chapter06_multiplication_difference_identity (x x' y y' : K) :
    x * y - x' * y' = x * (y - y') + y' * (x - x') := by
  sorry

/-- Multiplication is uniformly controlled on bounded sets. -/
theorem chapter06_multiplication_bounded_estimate
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {C : ℝ} (hC : 0 ≤ C) {x x' y y' : K}
    (hx : v x ≤ C) (hy' : v y' ≤ C) :
    chapter06Distance v (x * y) (x' * y') ≤
      C * max (chapter06Distance v x x') (chapter06Distance v y y') := by
  sorry

/-- The inversion difference formula away from zero. -/
theorem chapter06_inversion_difference_formula
    (v : AbsoluteValue K ℝ) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    chapter06Distance v x⁻¹ y⁻¹ =
      chapter06Distance v x y / (v x * v y) := by
  sorry

/-- Inversion is continuous at every nonzero point, in epsilon form. -/
theorem chapter06_inversion_continuous_away_from_zero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {x : K} (hx : x ≠ 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ y : K,
      chapter06Distance v y x < δ →
        chapter06Distance v y⁻¹ x⁻¹ < ε := by
  sorry

/-- Sufficient closeness to a nonzero point forces equality of absolute values. -/
theorem chapter06_abs_value_locally_constant_at_nonzero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {x y : K} (hx : x ≠ 0)
    (hxy : chapter06Distance v y x < v x) :
    v y = v x := by
  sorry

/-- The absolute value is continuous for its induced topology. -/
theorem chapter06_absolute_value_continuous (v : AbsoluteValue K ℝ) :
    @Continuous K ℝ v.uniformSpace.toTopologicalSpace inferInstance v := by
  sorry

/-- The valuation topology makes a valued field a topological division ring. -/
theorem chapter06_valued_field_is_topological_division_ring
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    @IsTopologicalDivisionRing K (inferInstance : DivisionRing K)
      inferInstance := by
  sorry

/-- The valuation subring is open and closed. -/
theorem chapter06_valuation_subring_is_clopen
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] :
    IsClopen (((Valued.v : Valuation K Γ₀).valuationSubring : Set K)) := by
  sorry

/-- Mathlib's open-units interface records that the unit group is open. -/
theorem chapter06_unit_group_is_open
    {A : Type*} [Monoid A] [TopologicalSpace A] [IsOpenUnits A] :
    IsOpen (Set.range (Units.val : Aˣ → A)) := by
  sorry

/-- The residue/reduction map of a local ring. -/
def chapter06ReductionMap (A : Type*) [CommRing A] [IsLocalRing A] :
    A →+* IsLocalRing.ResidueField A :=
  IsLocalRing.residue A

/-- Fibers of reduction are cosets of the maximal ideal. -/
theorem chapter06_reduction_fiber_eq_maximalIdeal_coset
    {A : Type*} [CommRing A] [IsLocalRing A] (a : A) :
    chapter06ReductionMap A ⁻¹' ({chapter06ReductionMap A a} : Set (IsLocalRing.ResidueField A)) =
      chapter06AdicCoset (IsLocalRing.maximalIdeal A) a 1 := by
  sorry

/-- Reduction to a discrete residue field is continuous once the maximal ideal is open. -/
theorem chapter06_reduction_continuous
    {A : Type*} [CommRing A] [IsLocalRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TopologicalSpace (IsLocalRing.ResidueField A)]
    [DiscreteTopology (IsLocalRing.ResidueField A)]
    (hm : @IsOpen A inferInstance (IsLocalRing.maximalIdeal A : Set A)) :
    @Continuous A (IsLocalRing.ResidueField A) inferInstance inferInstance (chapter06ReductionMap A) := by
  sorry

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
  sorry

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
  sorry

/-- Limits in the valuation metric are unique. -/
theorem chapter06_limit_unique
    (v : AbsoluteValue K ℝ) {x : ℕ → K} {l l' : K}
    (hl : chapter06ConvergesTo v x l) (hl' : chapter06ConvergesTo v x l') :
    l = l' := by
  sorry

/-- The finite-tail maximum estimate for consecutive increments. -/
theorem chapter06_consecutive_increment_tail_bound
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {x : ℕ → K} {n m : ℕ} (hnm : n < m)
    (hs : (Finset.Ico n m).Nonempty) :
    chapter06Distance v (x m) (x n) ≤
      (Finset.Ico n m).sup' hs
        (fun i => chapter06Distance v (x (i + 1)) (x i)) := by
  sorry

/-- Vanishing consecutive differences imply that a sequence is Cauchy. -/
theorem chapter06_cauchy_of_consecutive_differences_tend_to_zero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) {x : ℕ → K}
    (hinc : chapter06TendsToZero v (fun n => x (n + 1) - x n)) :
    chapter06CauchySeq v x := by
  sorry

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
  sorry

/-- A convergent sequence approaching a nonzero point eventually has constant absolute value. -/
theorem chapter06_eventual_absolute_value_eq_of_converges_to_nonzero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {x : ℕ → K} {l : K} (hl : chapter06ConvergesTo v x l) (hl0 : l ≠ 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → v (x n) = v l := by
  sorry

/-- In the discrete-value case, the absolute value is locally constant on `Kˣ`. -/
theorem chapter06_absolute_value_locally_constant_on_nonzero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hdisc : chapter06DiscreteValueSet v) :
    ∀ x : K, x ≠ 0 →
      ∃ U : Set K, @IsOpen K v.uniformSpace.toTopologicalSpace U ∧ x ∈ U ∧
        ∀ y ∈ U, v y = v x := by
  sorry

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
  sorry

/-- The difference of two partial sums is the corresponding finite tail sum. -/
theorem chapter06_partial_sum_difference_eq_tail
    (a : ℕ → K) {n m : ℕ} (hnm : n ≤ m) :
    chapter06PartialSums a m - chapter06PartialSums a n =
      Finset.sum (Finset.Ico n m) (fun i => a i) := by
  sorry

/-- Convergence of a series forces its terms to tend to zero. -/
theorem chapter06_series_convergence_implies_terms_tend_to_zero
    (v : AbsoluteValue K ℝ) {a : ℕ → K} {s : K}
    (h : chapter06SeriesConverges v a s) : chapter06TendsToZero v a := by
  sorry

/-- In a complete nonarchimedean field, a series converges exactly when its terms vanish. -/
theorem chapter06_series_converges_iff_terms_tend_to_zero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v) (a : ℕ → K) :
    chapter06SeriesHasSum v a ↔ chapter06TendsToZero v a := by
  sorry

/-- The geometric series converges to `(1-x)⁻¹` when `|x| < 1`. -/
theorem chapter06_geometric_series
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v) {x : K} (hx : v x < 1) :
    chapter06SeriesConverges v (fun n => x ^ n) (1 - x)⁻¹ := by
  sorry

/-- The principal-unit set of a local ring. -/
def chapter06PrincipalUnitSet (A : Type*) [CommRing A] [IsLocalRing A] : Set A :=
  {x | ∃ y ∈ (IsLocalRing.maximalIdeal A : Set A), x = 1 + y}

/-- `1 + 𝔪` lies in the unit group. -/
theorem chapter06_principal_units_are_units
    {A : Type*} [CommRing A] [IsLocalRing A] :
    chapter06PrincipalUnitSet A ⊆ Set.range (Units.val : Aˣ → A) := by
  sorry

/-- The geometric identity accompanies the algebraic principal-unit assertion. -/
theorem chapter06_geometric_inverse_identity
    (v : AbsoluteValue K ℝ) {x : K} (hx : v x < 1) :
    (1 - x) * (1 - x)⁻¹ = 1 := by
  sorry

/-- A permutation of the natural numbers used to reorder a series. -/
def chapter06SeriesPermutation (σ : ℕ → ℕ) : Prop :=
  Function.Bijective σ

/-- Reordering a nonarchimedean series with vanishing terms preserves its sum. -/
theorem chapter06_series_reordering_invariant
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v) {a : ℕ → K}
    (hzero : chapter06TendsToZero v a) {σ : ℕ → ℕ}
    (hσ : chapter06SeriesPermutation σ) {s : K}
    (hs : chapter06SeriesConverges v a s) :
    chapter06SeriesConverges v (a ∘ σ) s := by
  sorry

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
  sorry

/-- A threshold-finite double series admits a common sum along every enumeration. -/
theorem chapter06_double_series_has_rearrangement_invariant_sum
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v)
    {a : ℕ × ℕ → K} (hfinite : chapter06DoubleSeriesThresholdFinite v a) :
    ∃ s : K, ∀ e : ℕ ≃ ℕ × ℕ,
      chapter06SeriesConverges v (a ∘ e) s := by
  sorry

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
  sorry

/-- The same geometric formula applies in `ℚ_p` for `|x|ₚ < 1`. -/
theorem chapter06_padic_geometric_example
    {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : ‖x‖ < 1) :
    chapter06SeriesConverges (NormedField.toAbsoluteValue ℚ_[p])
      (fun n => x ^ n) (1 - x)⁻¹ := by
  sorry

/-- The geometric expression `1+p⁻¹+p⁻²+⋯` cannot converge p-adically. -/
theorem chapter06_padic_growing_geometric_series_diverges
    {p : ℕ} [Fact p.Prime] :
    ¬ chapter06SeriesHasSum (NormedField.toAbsoluteValue ℚ_[p])
      (fun n => (p : ℚ_[p]) ^ (-(n : ℤ))) := by
  sorry

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
  sorry

/-- Eventually, factors in a product with `aₙ → 0` are units of absolute value one. -/
theorem chapter06_eventual_product_factors_are_units
    (v : AbsoluteValue K ℝ) {a : ℕ → K}
    (hzero : chapter06TendsToZero v a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → v (a n) < 1 ∧ v (1 + a n) = 1 := by
  sorry

/-- In a complete nonarchimedean field, `aₙ → 0` makes the product converge. -/
theorem chapter06_infinite_product_converges_of_terms_tend_to_zero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v) {a : ℕ → K}
    (hzero : chapter06TendsToZero v a) :
    ∃ p : K, chapter06InfiniteProductConverges v a p := by
  sorry

/-- A product with vanishing corrections is nonzero when no factor is zero. -/
theorem chapter06_infinite_product_nonzero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a : ℕ → K} (hzero : chapter06TendsToZero v a)
    {p : K} (hp : chapter06InfiniteProductConverges v a p)
    (hfactor : ∀ n : ℕ, 1 + a n ≠ 0) :
    p ≠ 0 := by
  sorry

/-- The convergence criterion for products needs vanishing corrections, not real summability. -/
theorem chapter06_product_criterion_is_vanishing_not_summability
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v) {a : ℕ → K} :
    chapter06TendsToZero v a →
      ∃ p : K, chapter06InfiniteProductConverges v a p := by
  sorry

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
  sorry

/-- Finite residue fields give finite quotients modulo all powers in a DVR. -/
theorem chapter06_dvr_power_quotient_finite
    [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] (n : ℕ) :
    Finite (A ⧸ ((IsLocalRing.maximalIdeal A) ^ n)) := by
  sorry

/-- The diagonal subsequence construction is eventually constant modulo every power. -/
theorem chapter06_dvr_diagonal_subsequence
    [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)]
    (x : ℕ → A) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n : ℕ, ∃ a : A, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        x (φ k) - a ∈ (IsLocalRing.maximalIdeal A) ^ n := by
  sorry

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
  sorry

/-- A complete DVR with finite residue field has compact valuation ring. -/
theorem chapter06_complete_dvr_integer_compact
    [IsDomain A] [IsDiscreteValuationRing A]
    [Finite (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    @CompactSpace A (IsLocalRing.maximalIdeal A).adicTopology := by
  sorry

/-- Infinite residue classes give an infinite disjoint open cover, hence noncompactness. -/
theorem chapter06_infinite_residue_field_integer_not_compact
    [IsDomain A] [IsDiscreteValuationRing A]
    [Infinite (IsLocalRing.ResidueField A)] :
    ¬ @CompactSpace A (IsLocalRing.maximalIdeal A).adicTopology := by
  sorry

/-- The residue-class cover modulo the maximal ideal is exhaustive and pairwise disjoint. -/
theorem chapter06_maximalIdeal_residue_class_cover
    [IsLocalRing A] [TopologicalSpace A] [DiscreteTopology (A ⧸ IsLocalRing.maximalIdeal A)]
    (hm : @IsOpen A inferInstance (IsLocalRing.maximalIdeal A : Set A)) :
    (∀ c : A ⧸ IsLocalRing.maximalIdeal A,
        @IsOpen A inferInstance (chapter06ResidueClassCover (IsLocalRing.maximalIdeal A) c)) ∧
      (⋃ c : A ⧸ IsLocalRing.maximalIdeal A,
        chapter06ResidueClassCover (IsLocalRing.maximalIdeal A) c) = Set.univ ∧
      Pairwise (Disjoint on
        (chapter06ResidueClassCover (IsLocalRing.maximalIdeal A))) := by
  sorry

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
  sorry

/-- A complete discretely valued field is locally compact exactly when its residue field is finite. -/
theorem chapter06_complete_dv_field_locallyCompact_iff_finite_residue
    [CompleteSpace ((Valued.v : Valuation K Γ₀).valuationSubring)]
    [IsDiscreteValuationRing ((Valued.v : Valuation K Γ₀).valuationSubring)] :
    LocallyCompactSpace K ↔
      Finite (IsLocalRing.ResidueField ((Valued.v : Valuation K Γ₀).valuationSubring)) := by
  sorry

/-- Fractional valuation balls exhaust the field. -/
def chapter06FractionalDVRBall (A : Subring K) (π : A) (n : ℕ) : Set K :=
  {x | ∃ a : A, x = (a : K) * (π : K) ^ (-(n : ℤ))}

/-- The usual `K = ⋃ₙ π⁻ⁿ A` description. -/
theorem chapter06_field_is_union_fractional_dvr_balls
    (A : Subring K) (π : A)
    (hdecomp : ∀ x : K, ∃ n : ℕ, ∃ a : A,
      x = (a : K) * (π : K) ^ (-(n : ℤ))) :
    (Set.univ : Set K) = ⋃ n : ℕ, chapter06FractionalDVRBall A π n := by
  sorry

/-- In the finite-residue case the field is locally compact but not compact. -/
theorem chapter06_complete_dv_field_locally_compact_not_compact
    [CompleteSpace ((Valued.v : Valuation K Γ₀).valuationSubring)]
    [IsDiscreteValuationRing ((Valued.v : Valuation K Γ₀).valuationSubring)]
    [Finite (IsLocalRing.ResidueField ((Valued.v : Valuation K Γ₀).valuationSubring))] :
    LocallyCompactSpace K ∧ ¬ CompactSpace K := by
  sorry

end ValuedCompactness

/-- The p-adic numbers are locally compact. -/
theorem chapter06_padic_numbers_locally_compact
    {p : ℕ} [Fact p.Prime] : LocallyCompactSpace ℚ_[p] := by
  sorry

/-- Finite extensions of p-adic fields are locally compact. -/
theorem chapter06_finite_extension_of_padic_field_locally_compact
    {p : ℕ} {L : Type*} [Fact p.Prime] [NormedField L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] :
    LocallyCompactSpace L := by
  sorry

/-- `k((t))` is locally compact when `k` is finite. -/
theorem chapter06_laurentSeries_locally_compact_of_finite_residue
    {k : Type*} [Field k] [Finite k] :
    LocallyCompactSpace (LaurentSeries k) := by
  sorry

/-- `k((t))` is not locally compact when `k` is infinite. -/
theorem chapter06_laurentSeries_not_locally_compact_of_infinite_residue
    {k : Type*} [Field k] [Infinite k] :
    ¬ LocallyCompactSpace (LaurentSeries k) := by
  sorry

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
  sorry

/-- Valuation neighborhoods inside the valuation ring. -/
def chapter06RankOneValuationNeighborhood
    (v : Valuation K Γ₀) [v.RankOne] (r : ℝ) : Set v.valuationSubring :=
  {x | v.norm (x : K) < r}

/-- Cofinality of powers of the maximal ideal among valuation neighborhoods. -/
def chapter06PowersCofinalAmongValuationNeighborhoods
    (v : Valuation K Γ₀) [v.RankOne] : Prop :=
  ∀ r : ℝ, 0 < r → ∃ n : ℕ,
    ((IsLocalRing.maximalIdeal v.valuationSubring) ^ n : Set v.valuationSubring) ⊆
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
  sorry

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
  sorry

/-- The valuation topology may be strictly finer than the `𝔪`-adic topology. -/
theorem chapter06_nondiscrete_madic_topology_can_be_coarser
    (v : Valuation K Γ₀) [v.RankOne]
    (hnotcofinal : ¬ chapter06PowersCofinalAmongValuationNeighborhoods v) :
    TopologicalSpace.induced ((↑) : v.valuationSubring → K)
        (chapter06RankOneAbsoluteValue v).uniformSpace.toTopologicalSpace ≠
      (IsLocalRing.maximalIdeal v.valuationSubring).adicTopology := by
  sorry

/-- The compatible-family description of the adic completion. -/
theorem chapter06_adic_completion_is_compatible_family
    {A : Type*} [CommRing A] (m : Ideal A) (x : AdicCompletion m A)
    {i j : ℕ} (hij : i ≤ j) :
    AdicCompletion.transitionMap m A hij (x.val j) = x.val i := by
  sorry

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
      (fun n : ℕ => A ⧸ (m ^ n • (⊤ : Submodule A A))) (fun _ => ⊤))

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
          (m ^ n : Set A) ⊆ {x : A | v (x : K) < r}) ∧
        (∀ n : ℕ, ∃ r : ℝ, 0 < r ∧
          {x : A | v (x : K) < r} ⊆ (m ^ n : Set A))))

/-- An inverse-limit identification needs a discrete valuation or a cofinal chosen ideal. -/
theorem chapter06_completion_is_inverse_limit_under_discrete_or_cofinal
    {A : Subring K} (v : AbsoluteValue K ℝ) (m : Ideal A)
    (hallowed : chapter06CompletionIdentificationHypothesis v m) :
    chapter06ValuationCompletionIsAdic (A := A) v m := by
  sorry


end Nondiscrete

end

end ValuationsBook.Chapter06
