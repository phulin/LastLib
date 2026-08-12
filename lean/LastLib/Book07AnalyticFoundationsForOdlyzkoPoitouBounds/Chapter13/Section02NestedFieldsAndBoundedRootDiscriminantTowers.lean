import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13

noncomputable section

/-! ### 13.2 Nested fields and bounded-root-discriminant towers -/

/-
The ambient field is deliberately not required to be a number field: an
infinite algebraic tower cannot in general sit inside one finite extension of
`ℚ`.  Each member is required to be finite over `ℚ`, which is exactly what is
needed to recover the number-field API locally.
-/
structure Chapter13NestedFieldTower
    (Ω : Type*) [Field Ω] [Algebra ℚ Ω] where
  field : ℕ → IntermediateField ℚ Ω
  finite : ∀ j, FiniteDimensional ℚ (field j)
  nested : ∀ j, field j ≤ field (j + 1)

theorem chapter13_tower_field_numberField
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (j : ℕ) :
    NumberField (T.field j) := by
  exact @NumberField.of_module_finite ℚ (T.field j) _ _ _
    (IntermediateField.algebra' (T.field j)) (T.finite j)

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
  sorry

theorem chapter13_tower_realProportion_eq_canonical
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (j : ℕ) :
    chapter13TowerRealProportion T j =
      (NumberField.InfinitePlace.nrRealPlaces (T.field j) : ℝ) /
        (chapter13TowerDegree T j : ℝ) := by
  sorry

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
  let hfinite : Module.Finite ℚ (T.field j) := T.finite j
  exact @Module.finrank_pos ℚ (T.field j) _ _ _ _ hfinite _ _ _

theorem chapter13_tower_realProportion_mem_Icc
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (j : ℕ) :
    chapter13TowerRealProportion T j ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

theorem chapter13_tower_rootDiscriminant_pos
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (j : ℕ) :
    0 < chapter13TowerRootDiscriminant T j := by
  sorry

theorem chapter13_tower_field_mono
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) :
    Monotone T.field := by
  sorry

theorem chapter13_tower_degree_mono
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) :
    Monotone (chapter13TowerDegree T) := by
  sorry

/- The finite-field equality step used in stabilization: an inclusion of
   finite extensions with equal absolute degree is equality as intermediate
   fields of the common ambient field. -/
theorem chapter13_tower_field_eq_of_degree_eq
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) {i j : ℕ} (hij : i ≤ j)
    (hdegree : chapter13TowerDegree T i = chapter13TowerDegree T j) :
    T.field i = T.field j := by
  sorry

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
  sorry

theorem chapter13_tower_has_uniform_degree_cap
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) {U α₀ : ℝ}
    (hthreshold : U < 4 * Real.pi * Real.exp
      (Real.eulerMascheroniConstant + α₀))
    (hbound : chapter13TowerBoundedBy T U α₀) :
    ∃ N : ℕ, ∀ j, chapter13TowerDegree T j < N := by
  sorry

theorem chapter13_tower_stabilizes_of_uniform_degree_cap
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) {N : ℕ}
    (hbound : ∀ j, chapter13TowerDegree T j < N) :
    chapter13TowerStabilizes T := by
  sorry

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

/- A tower whose successive relative different ideals are trivial has
   constant root discriminant, by the relative formula in Dependencies. -/
def chapter13ConstantRootDiscriminantTower
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) : Prop :=
  ∀ j, chapter13TowerRootDiscriminant T (j + 1) =
    chapter13TowerRootDiscriminant T j

def chapter13UnramifiedTowerAboveThreshold
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) (U α₀ : ℝ) : Prop :=
  chapter13ConstantRootDiscriminantTower T ∧
    chapter13TowerRootDiscriminant T 0 ≤ U ∧
    (∀ j, α₀ ≤ chapter13TowerRealProportion T j) ∧
    4 * Real.pi * Real.exp
      (Real.eulerMascheroniConstant + α₀) ≤ U

theorem chapter13_constant_rootDiscriminant_tower_below_ceiling
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) {U : ℝ}
    (hconstant : chapter13ConstantRootDiscriminantTower T)
    (hzero : chapter13TowerRootDiscriminant T 0 ≤ U) :
    ∀ j, chapter13TowerRootDiscriminant T j ≤ U := by
  sorry

theorem chapter13_unramified_tower_compatibility_gives_uniform_bounds
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (T : Chapter13NestedFieldTower Ω) {U α₀ : ℝ}
    (hcompat : chapter13UnramifiedTowerAboveThreshold T U α₀) :
    chapter13TowerBoundedBy T U α₀ := by
  rcases hcompat with ⟨hconstant, hzero, halpha, _⟩
  refine fun j => ⟨?_, halpha j⟩
  exact chapter13_constant_rootDiscriminant_tower_below_ceiling
    T hconstant hzero j

/- The source's final statement is a compatibility warning conditional on the
existence of an infinite unramified tower, not an existence assertion.  The
precise compatibility condition is recorded in
`chapter13UnramifiedTowerAboveThreshold`. -/

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13
