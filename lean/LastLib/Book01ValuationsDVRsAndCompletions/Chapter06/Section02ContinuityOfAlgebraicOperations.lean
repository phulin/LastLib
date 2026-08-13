import LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.Section01BallsAndTheStrongTriangleInequality
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter06

open Set Filter Function
open scoped BigOperators Pointwise Topology WithZero NNReal Valued

noncomputable section

/-! # Book 1, Chapter 6, Section 6.2: Continuity of Algebraic Operations
-/

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
      congr 1; ring
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
  simp [div_eq_mul_inv, v.map_sub, v.map_mul]

/-- Inversion is continuous at every nonzero point, in epsilon form. -/
theorem chapter06_inversion_continuous_away_from_zero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {x : K} (hx : x ≠ 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ y : K,
      chapter06Distance v y x < δ →
        chapter06Distance v y⁻¹ x⁻¹ < ε := by
  intro ε hε
  let δ : ℝ := min (v x) (ε * (v x) ^ 2)
  have hxpos : 0 < v x := v.pos hx
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hxpos (mul_pos hε (sq_pos_of_pos hxpos))
  refine ⟨δ, hδ, ?_⟩
  intro y hxy
  have hδx : δ ≤ v x := min_le_left _ _
  have hy0 : y ≠ 0 := by
    intro hy
    subst y
    have : v x < δ := by
      simpa [chapter06Distance, v.map_neg] using hxy
    exact (not_lt_of_ge hδx) this
  have hxyv : v (y - x) < v x := by
    exact (show v (y - x) < δ by simpa [chapter06Distance] using hxy).trans_le hδx
  have hy_le : v y ≤ v x := by
    have h := chapter06_strong_triangle_inequality v hv y x 0
    have h' : v y ≤ max (v (y - x)) (v x) := by
      simpa [chapter06Distance] using h
    exact h'.trans_eq (max_eq_right hxyv.le)
  have hx_le : v x ≤ v y := by
    have h := chapter06_strong_triangle_inequality v hv x y 0
    have h' : v x ≤ max (v (x - y)) (v y) := by
      simpa [chapter06Distance] using h
    by_contra hnot
    have hy_lt : v y < v x := lt_of_not_ge hnot
    have hxyv' : v (x - y) < v x := by
      simpa only [v.map_sub] using hxyv
    exact (not_lt_of_ge h') (max_lt hxyv' hy_lt)
  have hyv : v y = v x := le_antisymm hy_le hx_le
  rw [chapter06_inversion_difference_formula v hy0 hx, hyv]
  apply (div_lt_iff₀ (mul_pos hxpos hxpos)).2
  calc
    chapter06Distance v y x < δ := hxy
    _ ≤ ε * (v x) ^ 2 := min_le_right _ _
    _ = ε * (v x * v x) := by ring

/-- Sufficient closeness to a nonzero point forces equality of absolute values. -/
theorem chapter06_abs_value_locally_constant_at_nonzero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {x y : K} (_hx : x ≠ 0)
    (hxy : chapter06Distance v y x < v x) :
    v y = v x := by
  change v (y - x) < v x at hxy
  have hy_le : v y ≤ v x := by
    have h := chapter06_strong_triangle_inequality v hv y x 0
    have h' : v y ≤ max (v (y - x)) (v x) := by
      simpa [chapter06Distance] using h
    exact h'.trans_eq (max_eq_right hxy.le)
  have hx_le : v x ≤ v y := by
    have h := chapter06_strong_triangle_inequality v hv x y 0
    have h' : v x ≤ max (v (x - y)) (v y) := by
      simpa [chapter06Distance] using h
    by_contra hnot
    have hy_lt : v y < v x := lt_of_not_ge hnot
    have hxy' : v (x - y) < v x := by
      simpa only [v.map_sub] using hxy
    exact (not_lt_of_ge h') (max_lt hxy' hy_lt)
  exact le_antisymm hy_le hx_le

/-- The absolute value is continuous for its induced topology. -/
theorem chapter06_absolute_value_continuous (v : AbsoluteValue K ℝ) :
    @Continuous K ℝ v.uniformSpace.toTopologicalSpace inferInstance v := by
  let : UniformSpace K := v.uniformSpace
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

/-- The unit group of a valuation subring is open in its induced topology. -/
theorem chapter06_unit_group_is_open
    {K : Type*} [Field K]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] :
    IsOpen (Set.range (Units.val :
      (Valued.v : Valuation K Γ₀).valuationSubringˣ →
        (Valued.v : Valuation K Γ₀).valuationSubring)) := by
  let A := (Valued.v : Valuation K Γ₀).valuationSubring
  have hsphere : IsOpen {x : K | (Valued.v : Valuation K Γ₀) x = 1} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    change (Valued.v : Valuation K Γ₀) x = 1 at hx
    have hx0 : (Valued.v : Valuation K Γ₀) x ≠ 0 := by
      rw [hx]
      exact one_ne_zero
    simpa only [hx] using (Valued.locally_const (R := K) (Γ₀ := Γ₀) hx0)
  have hunit : Set.range (Units.val : Aˣ → A) =
      (fun a : A => (a : K)) ⁻¹' {x : K | (Valued.v : Valuation K Γ₀) x = 1} := by
    ext a
    constructor
    · rintro ⟨u, rfl⟩
      have hnot : (u : A) ∉ IsLocalRing.maximalIdeal A :=
        IsLocalRing.notMem_maximalIdeal.mpr (Units.isUnit u)
      have hnotlt : ¬ (Valued.v : Valuation K Γ₀) (u : K) < 1 := by
        intro hlt
        apply hnot
        exact (Valuation.mem_maximalIdeal_iff
          (K := K) (Valued.v : Valuation K Γ₀)).2 hlt
      have hle : (Valued.v : Valuation K Γ₀) (u : K) ≤ 1 := by
        exact (Valuation.mem_valuationSubring_iff
          (Valued.v : Valuation K Γ₀) (u : K)).1 (u : A).property
      exact le_antisymm hle (le_of_not_gt hnotlt)
    · intro ha
      change (Valued.v : Valuation K Γ₀) (a : K) = 1 at ha
      have hnot : a ∉ IsLocalRing.maximalIdeal A := by
        intro hmem
        have hlt : (Valued.v : Valuation K Γ₀) (a : K) < 1 :=
          (Valuation.mem_maximalIdeal_iff
            (K := K) (Valued.v : Valuation K Γ₀)).1 hmem
        exact (lt_irrefl (1 : Γ₀)) (ha ▸ hlt)
      rcases IsLocalRing.notMem_maximalIdeal.mp hnot with ⟨u, hu⟩
      exact ⟨u, hu⟩
  rw [hunit]
  exact hsphere.preimage continuous_subtype_val

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
    simp only [chapter06AdicCoset, Set.mem_ofPred_eq]
    simp [pow_one, mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add, add_comm]
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
    simp only [chapter06AdicCoset, Set.mem_ofPred_eq]
    simp [mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add, add_comm]
  rw [heq]
  exact hmn.left_addCoset a

end Operations

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter06
