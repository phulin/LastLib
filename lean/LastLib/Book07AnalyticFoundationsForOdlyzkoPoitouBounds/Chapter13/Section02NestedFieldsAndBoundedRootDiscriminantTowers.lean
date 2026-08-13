import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13

noncomputable section

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01

/-! ### 13.2 Nested fields and bounded-root-discriminant towers -/

/-
The ambient field is deliberately not required to be a number field: an
infinite algebraic tower cannot in general sit inside one finite extension of
`ℚ`.  Each member is required to be finite over `ℚ`, which is exactly what is
needed to recover the number-field API locally.
-/
abbrev Chapter13NestedFieldTower
    (Ω : Type*) [Field Ω] [Algebra ℚ Ω] :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.Chapter01NestedFieldChain Ω

theorem chapter13_tower_field_numberField
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (j : ℕ) :
    NumberField (T.field j) := by
  exact @NumberField.of_module_finite ℚ (T.field j) _ _ _
    (IntermediateField.algebra' (T.field j)) (T.finiteDimensional j)

noncomputable instance chapter13NestedFieldTowerNumberField
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (j : ℕ) :
    NumberField (T.field j) :=
  chapter13_tower_field_numberField T j

noncomputable def chapter13TowerDegree
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (j : ℕ) : ℕ :=
  Module.finrank ℚ (T.field j)

noncomputable def chapter13TowerRootDiscriminant
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (j : ℕ) : ℝ := by
  haveI : NumberField (T.field j) := chapter13_tower_field_numberField T j
  exact chapter13RootDiscriminant (T.field j)

noncomputable def chapter13TowerRealProportion
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (j : ℕ) : ℝ := by
  haveI : NumberField (T.field j) := chapter13_tower_field_numberField T j
  exact chapter13RealProportion (T.field j)

theorem chapter13_tower_rootDiscriminant_eq_canonical
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (j : ℕ) :
    chapter13TowerRootDiscriminant T j =
      NumberField.rootDiscr (T.field j) := by
  exact chapter13_rootDiscriminant_eq_canonical (T.field j)

theorem chapter13_tower_realProportion_eq_canonical
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (j : ℕ) :
    chapter13TowerRealProportion T j =
      (NumberField.InfinitePlace.nrRealPlaces (T.field j) : ℝ) /
        (chapter13TowerDegree T j : ℝ) := by
  let : NumberField (T.field j) := chapter13_tower_field_numberField T j
  have hmodule : @Algebra.toModule ℚ (T.field j) _ _ _ =
      IntermediateField.module' (T.field j) := Subsingleton.elim _ _
  change chapter13RealProportion (T.field j) = _
  simp only [chapter13RealProportion, chapter01RealProportion, chapter01Degree,
    chapter13TowerDegree]
  rw [hmodule]
  congr 1

@[simp]
theorem chapter13_tower_degree_eq_finrank
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (j : ℕ) :
    chapter13TowerDegree T j = Module.finrank ℚ (T.field j) :=
  rfl

theorem chapter13_tower_degree_pos
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (j : ℕ) :
    0 < chapter13TowerDegree T j := by
  let hfinite : Module.Finite ℚ (T.field j) := T.finiteDimensional j
  exact @Module.finrank_pos ℚ (T.field j) _ _ _ _ hfinite _ _ _

theorem chapter13_tower_realProportion_mem_Icc
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (j : ℕ) :
    chapter13TowerRealProportion T j ∈ Set.Icc (0 : ℝ) 1 := by
  let : NumberField (T.field j) := chapter13_tower_field_numberField T j
  exact ⟨chapter13_realProportion_nonneg (T.field j),
    chapter13_realProportion_le_one (T.field j)⟩

theorem chapter13_tower_rootDiscriminant_pos
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (j : ℕ) :
    0 < chapter13TowerRootDiscriminant T j := by
  exact chapter13_rootDiscriminant_pos (T.field j)

theorem chapter13_tower_field_mono
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) :
    Monotone T.field := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | @succ j hij ih => exact ih.trans (T.nested j)

theorem chapter13_tower_degree_mono
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) :
    Monotone (chapter13TowerDegree T) := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | @succ j hij ih =>
      let : FiniteDimensional ℚ (T.field (j + 1)) := T.finiteDimensional (j + 1)
      exact ih.trans (IntermediateField.finrank_le_of_le_right (T.nested j))

/- The finite-field equality step used in stabilization: an inclusion of
   finite extensions with equal absolute degree is equality as intermediate
   fields of the common ambient field. -/
theorem chapter13_tower_field_eq_of_degree_eq
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) {i j : ℕ} (hij : i ≤ j)
    (hdegree : chapter13TowerDegree T i = chapter13TowerDegree T j) :
    T.field i = T.field j := by
  have hfield_mono : T.field i ≤ T.field j :=
    (chapter13_tower_field_mono T) hij
  let : FiniteDimensional ℚ (T.field j) := T.finiteDimensional j
  apply chapter01_intermediateField_eq_of_le_of_degree_eq Ω
    (T.field i) (T.field j) hfield_mono
  · exact hdegree

def chapter13TowerBoundedBy
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (U α₀ : ℝ) : Prop :=
  ∀ j, chapter13TowerRootDiscriminant T j ≤ U ∧
    α₀ ≤ chapter13TowerRealProportion T j

def chapter13TowerStabilizes
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) : Prop :=
  ∃ J : ℕ, ∀ j, J ≤ j → T.field j = T.field J

theorem chapter13_tower_degree_eventually_constant
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) {N : ℕ}
    (hbound : ∀ j, chapter13TowerDegree T j < N) :
    ∃ J : ℕ, ∀ j, J ≤ j →
      chapter13TowerDegree T j = chapter13TowerDegree T J := by
  have hbounded : ∀ j, chapter13TowerDegree T j ≤ N := fun j =>
    (hbound j).le
  obtain ⟨b, J, hJ⟩ := converges_of_monotone_of_bounded
    (chapter13_tower_degree_mono T) hbounded
  refine ⟨J, ?_⟩
  intro j hj
  exact (hJ j hj).trans (hJ J le_rfl).symm

theorem chapter13_tower_has_uniform_degree_cap
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) {U α₀ : ℝ}
    (hthreshold : U < 4 * Real.pi * Real.exp
      (Real.eulerMascheroniConstant + α₀))
    (hbound : chapter13TowerBoundedBy T U α₀) :
    ∃ N : ℕ, ∀ j, chapter13TowerDegree T j < N := by
  obtain ⟨N, hN⟩ := chapter13_threshold_principle_general hthreshold
  refine ⟨N, ?_⟩
  intro j
  let : Module ℚ (T.field j) := IntermediateField.module' (T.field j)
  have hmodule : @Algebra.toModule ℚ (T.field j) _ _ _ =
      IntermediateField.module' (T.field j) := Subsingleton.elim _ _
  have h := hN (T.field j) (hbound j).1 (hbound j).2
  have hdegree : chapter13Degree (T.field j) = chapter13TowerDegree T j := by
    unfold chapter13Degree chapter01Degree chapter13TowerDegree
    rw [hmodule]
  rw [← hdegree]
  exact h

theorem chapter13_tower_stabilizes_of_uniform_degree_cap
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) {N : ℕ}
    (hbound : ∀ j, chapter13TowerDegree T j < N) :
    chapter13TowerStabilizes T := by
  obtain ⟨J, hJ⟩ := chapter13_tower_degree_eventually_constant T hbound
  refine ⟨J, ?_⟩
  intro j hj
  exact (chapter13_tower_field_eq_of_degree_eq T hj (hJ j hj).symm).symm

/-! Theorem 13.2 (tower stabilization). -/
theorem chapter13_tower_stabilization
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) {U α₀ : ℝ}
    (hbound : chapter13TowerBoundedBy T U α₀)
    (hthreshold : U < 4 * Real.pi * Real.exp
      (Real.eulerMascheroniConstant + α₀)) :
    chapter13TowerStabilizes T := by
  rcases chapter13_tower_has_uniform_degree_cap T hthreshold hbound with
    ⟨N, hN⟩
  exact chapter13_tower_stabilizes_of_uniform_degree_cap T hN

/- The analytic compatibility package records the constant-root-discriminant
   consequence of a stepwise unramified tower.  The arithmetic unramifiedness
   predicate itself is supplied separately by the relative discriminant API. -/
def chapter13ConstantRootDiscriminantTower
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) : Prop :=
  ∀ j, chapter13TowerRootDiscriminant T (j + 1) =
    chapter13TowerRootDiscriminant T j

def chapter13ConstantRootDiscriminantTowerAboveThreshold
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (U α₀ : ℝ) : Prop :=
  chapter13ConstantRootDiscriminantTower T ∧
    chapter13TowerRootDiscriminant T 0 ≤ U ∧
    (∀ j, α₀ ≤ chapter13TowerRealProportion T j) ∧
    4 * Real.pi * Real.exp
      (Real.eulerMascheroniConstant + α₀) ≤
        chapter13TowerRootDiscriminant T 0

theorem chapter13_constant_rootDiscriminant_tower_below_ceiling
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) {U : ℝ}
    (hconstant : chapter13ConstantRootDiscriminantTower T)
    (hzero : chapter13TowerRootDiscriminant T 0 ≤ U) :
    ∀ j, chapter13TowerRootDiscriminant T j ≤ U := by
  intro j
  induction j with
  | zero => exact hzero
  | succ j ih =>
      rw [hconstant j]
      exact ih

theorem chapter13_constant_rootDiscriminant_tower_compatibility_gives_uniform_bounds
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) {U α₀ : ℝ}
    (hcompat : chapter13ConstantRootDiscriminantTowerAboveThreshold T U α₀) :
    chapter13TowerBoundedBy T U α₀ := by
  rcases hcompat with ⟨hconstant, hzero, halpha, _⟩
  refine fun j => ⟨?_, halpha j⟩
  exact chapter13_constant_rootDiscriminant_tower_below_ceiling
    T hconstant hzero j

/- The source's final statement is a compatibility warning conditional on the
existence of an infinite unramified tower, not an existence assertion.  The
precise compatibility condition is recorded in
`chapter13ConstantRootDiscriminantTowerAboveThreshold`. -/

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13
