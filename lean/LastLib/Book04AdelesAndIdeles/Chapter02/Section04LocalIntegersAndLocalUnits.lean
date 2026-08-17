import LastLib.Book04AdelesAndIdeles.Chapter02.Core
import LastLib.Book04AdelesAndIdeles.Chapter01.Section02NumberFieldsAndIntegers
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

namespace LastLib.Book04AdelesAndIdeles.Chapter02

noncomputable section

open NumberField
open scoped BigOperators Topology WithZero

/-! ## 2.4. Local integers and local units -/

abbrev Chapter02LocalField
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Type _ :=
  v.adicCompletion K

abbrev Chapter02LocalIntegerRing
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Type _ :=
  v.adicCompletionIntegers K

def Chapter02LocalMaximalIdeal
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Ideal (Chapter02LocalIntegerRing v) :=
  IsLocalRing.maximalIdeal (Chapter02LocalIntegerRing v)

/-- The integer ball in the completed local field. -/
def Chapter02LocalIntegerSet
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Set (Chapter02LocalField v) :=
  (v.adicCompletionIntegers K : Set (Chapter02LocalField v))

/-- The open maximal-ideal ball in the local field. -/
def Chapter02LocalMaximalIdealSet
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Set (Chapter02LocalField v) :=
  {x | Valued.v x < 1}

/-- The unit locus in the completed local field. -/
def Chapter02LocalUnitSet
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Set (Chapter02LocalField v) :=
  {x | x ≠ 0 ∧ Valued.v x = 1}

/-- The group of units of the local valuation subring. -/
def Chapter02LocalUnitGroup
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Subgroup (Chapter02LocalField v)ˣ :=
  (v.adicCompletionIntegers K).unitGroup

theorem chapter02_local_unit_group_mem_iff
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (u : (Chapter02LocalField v)ˣ) :
    u ∈ Chapter02LocalUnitGroup v ↔
      (u : Chapter02LocalField v) ∈ Chapter02LocalUnitSet v := by
  simpa [Chapter02LocalUnitGroup, Chapter02LocalUnitSet,
    IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers] using
    (Valuation.mem_unitGroup_iff (K := Chapter02LocalField v) (Γ := ℤᵐ⁰)
      (v := (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰)) (x := u))

theorem chapter02_local_integer_mem_iff
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Chapter02LocalField v) :
    x ∈ Chapter02LocalIntegerSet v ↔ Valued.v x ≤ 1 := by
  rfl

theorem chapter02_local_maximal_ideal_mem_iff
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Chapter02LocalField v) :
    x ∈ Chapter02LocalMaximalIdealSet v ↔ Valued.v x < 1 := by
  rfl

theorem chapter02_local_maximal_ideal_set_eq_coe_image
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Chapter02LocalMaximalIdealSet v =
      (fun y : Chapter02LocalIntegerRing v =>
        (y : Chapter02LocalField v)) ''
        (Chapter02LocalMaximalIdeal v : Set (Chapter02LocalIntegerRing v)) := by
  sorry

theorem chapter02_local_unit_mem_iff
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Chapter02LocalField v) :
    x ∈ Chapter02LocalUnitSet v ↔ x ≠ 0 ∧ Valued.v x = 1 := by
  rfl

theorem chapter02_local_integer_ring_is_discrete_valuation_ring
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsDiscreteValuationRing (Chapter02LocalIntegerRing v) := by
  infer_instance

theorem chapter02_local_integer_ring_is_complete
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    CompleteSpace (Chapter02LocalIntegerRing v) := by
  exact (Valued.isClosed_valuationSubring (v.adicCompletion K)).isComplete.completeSpace_coe

theorem chapter02_local_units_are_exactly_the_norm_one_elements
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Chapter02LocalField v)
    (hx : x ≠ 0) :
    x ∈ Chapter02LocalUnitSet v ↔ Valued.v x = 1 := by
  simp [Chapter02LocalUnitSet, hx]

/-- A uniformizer is an element whose value generates the discrete value group. -/
def Chapter02LocalUniformizer
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : Chapter02LocalField v) : Prop :=
  (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰).IsUniformizer π

def Chapter02LocalResidueCardinality
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℕ :=
  v.asIdeal.absNorm

theorem chapter02_local_exists_uniformizer
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ∃ π : Chapter02LocalField v, Chapter02LocalUniformizer v π := by
  rcases Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial
      (v := (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰)) with ⟨π, hπ⟩
  exact ⟨π, hπ⟩

theorem chapter02_uniformizer_has_residue_cardinality_norm
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : Chapter02LocalField v) (hπ : Chapter02LocalUniformizer v π) :
    ‖π‖ = (Chapter02LocalResidueCardinality v : ℝ)⁻¹ := by
  have hgen :
      Valuation.IsRankOneDiscrete.generator
          (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰) =
        Units.mk0 (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) (by simp) := by
    apply Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
    rcases v.intValuation_exists_uniformizer with ⟨ϖ, hϖ⟩
    refine ⟨(ϖ : Chapter02LocalField v), ?_⟩
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v,
      v.valuation_of_algebraMap, hϖ]
  have hπval : Valued.v π =
      Valuation.IsRankOneDiscrete.generator
        (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰) := hπ
  rw [NumberField.FinitePlace.norm_def, hπval, hgen]
  rw [WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
  change (Ideal.absNorm v.asIdeal : ℝ) ^
      (WithZero.unzero (by simp : (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) ≠ 0)).toAdd =
    (Chapter02LocalResidueCardinality v : ℝ)⁻¹
  have hexp :
      (WithZero.unzero (by simp : (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) ≠ 0)).toAdd = -1 := by
    apply (WithZero.toAdd_unzero_eq_iff (by simp) (-1)).2
    rfl
  rw [hexp]
  simp [Chapter02LocalResidueCardinality]

/-- The local multiplicative decomposition after choosing a uniformizer. -/
def Chapter02LocalMultiplicativeDecomposition
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : Chapter02LocalField v) : Prop :=
  ∀ x : Chapter02LocalField v, x ≠ 0 →
    ∃ n : ℤ, ∃ u : Chapter02LocalUnitGroup v,
      x = π ^ n * ((u : (Chapter02LocalField v)ˣ) : Chapter02LocalField v)

theorem chapter02_local_multiplicative_decomposition
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : Chapter02LocalField v) (hπ : Chapter02LocalUniformizer v π) :
    Chapter02LocalMultiplicativeDecomposition v π := by
  intro x hx
  let P : Valuation.Uniformizer
      (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰) :=
    Valuation.Uniformizer.mk' hπ
  rcases (Valued.v.valuationSubring.mem_or_inv_mem x) with hxA | hxA
  · let r : Valued.v.valuationSubring := ⟨x, hxA⟩
    have hr : r ≠ 0 := by
      intro hr
      apply hx
      exact congrArg Subtype.val hr
    obtain ⟨n, u, hu⟩ :=
      Valuation.exists_pow_Uniformizer hr P
    let U : Chapter02LocalUnitGroup v :=
      Valued.v.valuationSubring.unitGroupMulEquiv.symm u
    have hP : (P.val : Chapter02LocalField v) = π := by
      rfl
    refine ⟨(n : ℤ), U, ?_⟩
    simpa [r, U, P, hP, zpow_natCast] using hu
  · let r : Valued.v.valuationSubring := ⟨x⁻¹, hxA⟩
    have hr : r ≠ 0 := by
      intro hr
      apply hx
      exact inv_eq_zero.mp (congrArg Subtype.val hr)
    obtain ⟨n, u, hu⟩ :=
      Valuation.exists_pow_Uniformizer hr P
    let U : Chapter02LocalUnitGroup v :=
      Valued.v.valuationSubring.unitGroupMulEquiv.symm u
    have hP : (P.val : Chapter02LocalField v) = π := by
      rfl
    refine ⟨-(n : ℤ), U⁻¹, ?_⟩
    have hu' : x⁻¹ = π ^ (n : ℤ) *
        ((U : (Chapter02LocalField v)ˣ) : Chapter02LocalField v) := by
      simpa [r, U, P, hP, zpow_natCast] using hu
    calc
      x = (x⁻¹)⁻¹ := by simp
      _ = (π ^ (n : ℤ) * ((U : (Chapter02LocalField v)ˣ) : Chapter02LocalField v))⁻¹ := by
        rw [hu']
      _ = π ^ (-(n : ℤ)) *
          (((U⁻¹ : Chapter02LocalUnitGroup v) : (Chapter02LocalField v)ˣ) :
            Chapter02LocalField v) := by
         simp [mul_comm]

/-- The exponent of a unit-normalized nonzero local element, defined from its
valuation value rather than from a chosen splitting of `Kᵥˣ`. -/
noncomputable def Chapter02LocalCanonicalOrder
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (Chapter02LocalField v)ˣ) : ℤ :=
  if h : Valued.v (x : Chapter02LocalField v) = 0 then 0 else
    -((WithZero.unzero h).toAdd)

theorem chapter02_local_canonical_order_is_additive
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x y : (Chapter02LocalField v)ˣ) :
    Chapter02LocalCanonicalOrder v (x * y) =
      Chapter02LocalCanonicalOrder v x + Chapter02LocalCanonicalOrder v y := by
  have hxv : Valued.v (x : Chapter02LocalField v) ≠ 0 := by simp
  have hyv : Valued.v (y : Chapter02LocalField v) ≠ 0 := by simp
  have hxyv : Valued.v ((x * y : (Chapter02LocalField v)ˣ) : Chapter02LocalField v) ≠ 0 := by
    simp
  simp only [Chapter02LocalCanonicalOrder, dif_neg hxyv, dif_neg hxv, dif_neg hyv]
  have hmul :
      Valued.v ((x * y : (Chapter02LocalField v)ˣ) : Chapter02LocalField v) =
        Valued.v (x : Chapter02LocalField v) * Valued.v (y : Chapter02LocalField v) := by
    simp
  have hprod :
      Valued.v (x : Chapter02LocalField v) * Valued.v (y : Chapter02LocalField v) ≠ 0 :=
    mul_ne_zero hxv hyv
  have hunzero :
      WithZero.unzero hxyv = WithZero.unzero hxv * WithZero.unzero hyv := by
    convert WithZero.unzero_mul hprod using 1; simp
  rw [hunzero, toAdd_mul]
  ring

/-- Powers of the maximal ideal, viewed as subsets of the completed field. -/
def Chapter02LocalIdealPower
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    Ideal (Chapter02LocalIntegerRing v) :=
  Chapter02LocalMaximalIdeal v ^ m

def Chapter02LocalIdealPowerSet
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    Set (Chapter02LocalField v) :=
  {x | ∃ y : Chapter02LocalIntegerRing v,
      y ∈ Chapter02LocalIdealPower v m ∧ x = (y : Chapter02LocalField v)}

private theorem chapter02_local_ideal_power_set_eq_mul_image
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : Chapter02LocalField v) (hπ : Chapter02LocalUniformizer v π) (m : ℕ) :
    Chapter02LocalIdealPowerSet v m =
      (fun z : Chapter02LocalField v => π ^ m * z) '' Chapter02LocalIntegerSet v := by
  let πA : Chapter02LocalIntegerRing v := ⟨π, le_of_lt hπ.val_lt_one⟩
  have hπA : (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰) (πA : Chapter02LocalField v) =
      Valuation.IsRankOneDiscrete.generator
        (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰) := by
    change (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰) π =
      Valuation.IsRankOneDiscrete.generator
        (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰) at hπ
    simpa [πA] using hπ
  have hP : (πA : Chapter02LocalField v) = π := by
    rfl
  have hgen : Chapter02LocalMaximalIdeal v = Ideal.span {πA} := by
    change IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {πA}
    exact Valuation.IsUniformizer.is_generator hπA
  have hpow : Chapter02LocalIdealPower v m = Ideal.span {πA ^ m} := by
    rw [Chapter02LocalIdealPower, hgen, ← Ideal.span_singleton_pow]
  ext x
  change (∃ y : Chapter02LocalIntegerRing v,
      y ∈ Chapter02LocalIdealPower v m ∧ x = (y : Chapter02LocalField v)) ↔
    x ∈ (fun z : Chapter02LocalField v => π ^ m * z) '' Chapter02LocalIntegerSet v
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hpow] at hy
    rcases (Ideal.mem_span_singleton').mp hy with ⟨z, hz⟩
    refine ⟨(z : Chapter02LocalField v), z.property, ?_⟩
    have hz' := congrArg (fun t : Chapter02LocalIntegerRing v =>
      (t : Chapter02LocalField v)) hz
    simpa [hP, mul_comm] using hz'
  · rintro ⟨z, hz, hzx⟩
    let zA : Chapter02LocalIntegerRing v := ⟨z, hz⟩
    refine ⟨πA ^ m * zA, ?_, ?_⟩
    rw [hpow]
    exact Ideal.mem_span_singleton'.2 ⟨zA, by simp [mul_comm]⟩
    rw [← hzx]
    change π ^ m * z = π ^ m * z
    rfl

theorem chapter02_local_ideal_powers_are_neighborhoods
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    Chapter02LocalIdealPowerSet v m ∈ 𝓝 (0 : Chapter02LocalField v) := by
  obtain ⟨π, hπ⟩ := chapter02_local_exists_uniformizer v
  rw [chapter02_local_ideal_power_set_eq_mul_image v π hπ m]
  have hzero : (0 : Chapter02LocalField v) ∈ Chapter02LocalIntegerSet v := by
    simp [Chapter02LocalIntegerSet]
  have hA : Chapter02LocalIntegerSet v ∈ 𝓝 (0 : Chapter02LocalField v) :=
    (show IsOpen (Chapter02LocalIntegerSet v) from
      Valued.isOpen_valuationSubring (Chapter02LocalField v)).mem_nhds hzero
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h] at hπ
    change Valued.v (0 : Chapter02LocalField v) =
      Valuation.IsRankOneDiscrete.generator
        (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰) at hπ
    rw [map_zero] at hπ
    exact (Units.ne_zero _ hπ.symm)
  simpa using
    (Homeomorph.mulLeft₀ (π ^ m) (pow_ne_zero m hπ0)).isOpenMap.image_mem_nhds hA

theorem chapter02_local_ideal_powers_form_a_neighborhood_basis
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (U : Set (Chapter02LocalField v)) (hU : U ∈ 𝓝 0) :
    ∃ m : ℕ, Chapter02LocalIdealPowerSet v m ⊆ U := by
  rw [Valued.mem_nhds_zero] at hU
  rcases hU with ⟨γ, hγ⟩
  obtain ⟨π, hπ⟩ := chapter02_local_exists_uniformizer v
  have hgen :
      Valuation.IsRankOneDiscrete.generator
          (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰) =
        Units.mk0 (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) (by simp) := by
    apply Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
    rcases v.intValuation_exists_uniformizer with ⟨ϖ, hϖ⟩
    refine ⟨(ϖ : Chapter02LocalField v), ?_⟩
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v,
      v.valuation_of_algebraMap, hϖ]
  have hπval : Valued.v π =
      Valuation.IsRankOneDiscrete.generator
        (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰) := hπ
  have hπle : Valued.v π ≤ WithZero.exp (-1 : ℤ) := by
    rw [hπval, hgen]
    rfl
  let γ' : ℤᵐ⁰ˣ :=
    Units.map
      (MonoidWithZeroHom.ValueGroup₀.embedding
        (f := (.ofClass (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰)))) γ
  obtain ⟨m, hm⟩ := Valued.exists_pow_lt_of_le_exp_neg_one hπle γ'
  refine ⟨m, ?_⟩
  rw [chapter02_local_ideal_power_set_eq_mul_image v π hπ m]
  rintro x ⟨z, hz, rfl⟩
  apply hγ
  change Valued.v.restrict (π ^ m * z) < γ
  rw [Valuation.restrict_lt_iff_lt_embedding, map_mul, map_pow]
  exact mul_lt_of_lt_of_le_one hm (chapter02_local_integer_mem_iff v z |>.mp hz)

theorem chapter02_local_integer_ring_is_compact_and_open
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsCompact (Chapter02LocalIntegerSet v) ∧
      IsOpen (Chapter02LocalIntegerSet v) := by
  refine ⟨?_, ?_⟩
  · have hcompact : IsCompact (Set.univ : Set (Chapter02LocalIntegerRing v)) :=
      isCompact_univ_iff.mpr
        (LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_completion_integers_compact K v)
    have himage := hcompact.image
      (show Continuous (fun x : Chapter02LocalIntegerRing v =>
        (x : Chapter02LocalField v)) from continuous_subtype_val)
    simpa [Chapter02LocalIntegerSet] using himage
  · exact Valued.isOpen_valuationSubring (Chapter02LocalField v)

theorem chapter02_local_ideal_powers_are_compact_and_open
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    IsCompact (Chapter02LocalIdealPowerSet v m) ∧
      IsOpen (Chapter02LocalIdealPowerSet v m) := by
  obtain ⟨π, hπ⟩ := chapter02_local_exists_uniformizer v
  rw [chapter02_local_ideal_power_set_eq_mul_image v π hπ m]
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h] at hπ
    change Valued.v (0 : Chapter02LocalField v) =
      Valuation.IsRankOneDiscrete.generator
        (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰) at hπ
    rw [map_zero] at hπ
    exact (Units.ne_zero _ hπ.symm)
  have hA := chapter02_local_integer_ring_is_compact_and_open v
  constructor
  · exact hA.1.image (continuous_const.mul continuous_id)
  · exact
      (Homeomorph.mulLeft₀ (π ^ m) (pow_ne_zero m hπ0)).isOpenMap _ hA.2

/-- The principal units `1 + pᵐ` as a subgroup of the local multiplicative group. -/
def Chapter02HigherPrincipalUnitGroup
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    Subgroup (Chapter02LocalField v)ˣ :=
  if hm : m = 0 then
    (v.adicCompletionIntegers K).unitGroup
  else
    { carrier := {u | ∃ y : Chapter02LocalIntegerRing v,
          y ∈ Chapter02LocalIdealPower v m ∧
            (u : Chapter02LocalField v) = 1 + (y : Chapter02LocalField v)}
      one_mem' := by
        refine ⟨0, (Chapter02LocalIdealPower v m).zero_mem, ?_⟩
        simp
      mul_mem' := by
        rintro u w ⟨y, hy, huy⟩ ⟨z, hz, hwz⟩
        have hyz : y * z ∈ Chapter02LocalIdealPower v m :=
          by simpa [mul_comm] using (Chapter02LocalIdealPower v m).mul_mem_left z hy
        refine ⟨y + z + y * z,
          (Chapter02LocalIdealPower v m).add_mem
            ((Chapter02LocalIdealPower v m).add_mem hy hz) hyz, ?_⟩
        change (u : Chapter02LocalField v) * (w : Chapter02LocalField v) =
          1 + ((y + z + y * z : Chapter02LocalIntegerRing v) : Chapter02LocalField v)
        rw [huy, hwz]
        push_cast
        ring
      inv_mem' := by
        intro u hu
        rcases hu with ⟨y, hy, huy⟩
        have hymax : y ∈ Chapter02LocalMaximalIdeal v := by
          exact (Ideal.pow_le_self hm) hy
        have hylt : Valued.v (y : Chapter02LocalField v) < 1 := by
          apply (Valuation.mem_maximalIdeal_iff (v :=
            (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰))).mp
          exact hymax
        have huval : Valued.v (u : Chapter02LocalField v) = 1 := by
          rw [huy]
          exact (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰).map_one_add_of_lt hylt
        have huinvA : (u : Chapter02LocalField v)⁻¹ ∈ Chapter02LocalIntegerSet v := by
          apply (chapter02_local_integer_mem_iff v _).2
          rw [map_inv₀, huval]
          simp
        let uinvA : Chapter02LocalIntegerRing v :=
          ⟨(u : Chapter02LocalField v)⁻¹, huinvA⟩
        have hmul : uinvA * y ∈ Chapter02LocalIdealPower v m :=
          (Chapter02LocalIdealPower v m).mul_mem_left uinvA hy
        have hw : -uinvA * y ∈ Chapter02LocalIdealPower v m := by
          simpa [neg_mul] using (Chapter02LocalIdealPower v m).neg_mem hmul
        refine ⟨-uinvA * y, hw, ?_⟩
        change ((u⁻¹ : (Chapter02LocalField v)ˣ) : Chapter02LocalField v) =
          1 + ((-uinvA * y : Chapter02LocalIntegerRing v) : Chapter02LocalField v)
        rw [Units.val_inv_eq_inv_val]
        calc
          (u : Chapter02LocalField v)⁻¹ = (u : Chapter02LocalField v)⁻¹ * 1 := by simp
          _ = (u : Chapter02LocalField v)⁻¹ *
              ((1 + (y : Chapter02LocalField v)) - (y : Chapter02LocalField v)) := by
            rw [add_sub_cancel_right]
          _ = 1 - (u : Chapter02LocalField v)⁻¹ * (y : Chapter02LocalField v) := by
            rw [← huy, mul_sub, inv_mul_cancel₀ (Units.ne_zero u)]
          _ = 1 + ((-uinvA * y : Chapter02LocalIntegerRing v) : Chapter02LocalField v) := by
            simp [uinvA, sub_eq_add_neg]
    }

theorem chapter02_higher_principal_units_are_local_units
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    Chapter02HigherPrincipalUnitGroup v m ≤ Chapter02LocalUnitGroup v := by
  sorry

theorem chapter02_higher_principal_units_are_open
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (m : ℕ) (hm : 1 ≤ m) :
    IsOpen (Chapter02HigherPrincipalUnitGroup v m : Set (Chapter02LocalField v)ˣ) := by
  have hm0 : m ≠ 0 := by omega
  have himage :
      Units.val '' (Chapter02HigherPrincipalUnitGroup v m : Set (Chapter02LocalField v)ˣ) =
        (fun y : Chapter02LocalField v => 1 + y) '' Chapter02LocalIdealPowerSet v m := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : ∃ y : Chapter02LocalIntegerRing v,
          y ∈ Chapter02LocalIdealPower v m ∧
            (u : Chapter02LocalField v) = 1 + (y : Chapter02LocalField v) := by
        simpa [Chapter02HigherPrincipalUnitGroup, hm0] using hu
      rcases hu' with ⟨y, hy, huy⟩
      refine ⟨(u : Chapter02LocalField v) - 1, ?_, ?_⟩
      · exact ⟨y, hy, by rw [huy]; ring⟩
      · change 1 + ((u : Chapter02LocalField v) - 1) =
          (u : Chapter02LocalField v)
        ring
    · rintro ⟨x, ⟨y, hy, hyx⟩, rfl⟩
      have hymax : y ∈ Chapter02LocalMaximalIdeal v := by
        exact (Ideal.pow_le_self hm0) hy
      have hylt : Valued.v (y : Chapter02LocalField v) < 1 := by
        apply (Valuation.mem_maximalIdeal_iff (v :=
          (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰))).mp
        exact hymax
      have hval : Valued.v (1 + (y : Chapter02LocalField v)) = 1 :=
        (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰).map_one_add_of_lt hylt
      have hne : (1 + (y : Chapter02LocalField v)) ≠ 0 := by
        intro h
        rw [h, map_zero] at hval
        exact zero_ne_one hval
      let u : (Chapter02LocalField v)ˣ := Units.mk0 (1 + (y : Chapter02LocalField v)) hne
      have hu : u ∈ Chapter02HigherPrincipalUnitGroup v m := by
        simpa [Chapter02HigherPrincipalUnitGroup, hm0] using
          (show ∃ y : Chapter02LocalIntegerRing v,
              y ∈ Chapter02LocalIdealPower v m ∧
                (u : Chapter02LocalField v) = 1 + (y : Chapter02LocalField v) from
            ⟨y, hy, rfl⟩)
      refine ⟨u, hu, ?_⟩
      rw [hyx]
      rfl
  apply (IsOpenUnits.isOpenEmbedding_unitsVal (M := Chapter02LocalField v)).isOpen_iff_image_isOpen.mpr
  rw [himage]
  exact isOpenMap_add_left (1 : Chapter02LocalField v) _
    (chapter02_local_ideal_powers_are_compact_and_open v m).2

theorem chapter02_principal_units_match_valuation_subring_api
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Chapter02HigherPrincipalUnitGroup v 1 =
      (v.adicCompletionIntegers K).principalUnitGroup := by
  have hrel :
      (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰).IsEquiv
        (v.adicCompletionIntegers K).valuation :=
    Valuation.isEquiv_valuation_valuationSubring
      (v := (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰))
  have hm0 : (1 : ℕ) ≠ 0 := by norm_num
  ext u
  simp only [Chapter02HigherPrincipalUnitGroup, dif_neg hm0]
  rw [ValuationSubring.mem_principalUnitGroup_iff]
  constructor
  · rintro ⟨y, hy, huy⟩
    have hymax : y ∈ Chapter02LocalMaximalIdeal v := by
      simpa [Chapter02LocalIdealPower] using hy
    have hylt : Valued.v (y : Chapter02LocalField v) < 1 := by
      apply (Valuation.mem_maximalIdeal_iff (v :=
        (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰))).mp
      exact hymax
    apply (Valuation.IsEquiv.val_sub_one_lt_one_iff hrel).mp
    rw [huy]
    simpa using hylt
  · intro hu
    have hfull : Valued.v ((u : Chapter02LocalField v) - 1) < 1 :=
      (Valuation.IsEquiv.val_sub_one_lt_one_iff hrel).mpr hu
    let y : Chapter02LocalIntegerRing v :=
      ⟨(u : Chapter02LocalField v) - 1,
        (chapter02_local_integer_mem_iff v _).2 hfull.le⟩
    have hymax : y ∈ Chapter02LocalMaximalIdeal v := by
      apply (Valuation.mem_maximalIdeal_iff (v :=
        (Valued.v : Valuation (Chapter02LocalField v) ℤᵐ⁰))).2
      exact hfull
    have hy : y ∈ Chapter02LocalIdealPower v 1 := by
      simpa [Chapter02LocalIdealPower] using hymax
    refine ⟨y, hy, ?_⟩
    change (u : Chapter02LocalField v) =
      1 + ((u : Chapter02LocalField v) - 1)
    ring

/-! The archimedean warning: compact balls are not the open compact additive
subgroups that occur at finite places. -/

def Chapter02RealClosedUnitInterval : Set ℝ := Set.Icc (-1) 1

def Chapter02ComplexClosedUnitDisk : Set ℂ := {z | ‖z‖ ≤ 1}

def Chapter02ComplexUnitCircle : Set ℂ := {z | ‖z‖ = 1}

def Chapter02ComplexUnitCircleInUnits : Set ℂˣ :=
  {u | ‖(u : ℂ)‖ = 1}

theorem chapter02_real_closed_unit_interval_is_compact :
    IsCompact Chapter02RealClosedUnitInterval := by
  simpa [Chapter02RealClosedUnitInterval] using
    (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1))

theorem chapter02_complex_closed_unit_disk_is_compact :
    IsCompact Chapter02ComplexClosedUnitDisk := by
  simpa [Chapter02ComplexClosedUnitDisk, Metric.closedBall, dist_eq_norm] using
    (isCompact_closedBall (0 : ℂ) 1)

theorem chapter02_real_closed_unit_interval_is_not_an_additive_subgroup :
    ¬ ∃ H : AddSubgroup ℝ, (H : Set ℝ) = Chapter02RealClosedUnitInterval := by
  rintro ⟨H, hH⟩
  have h1 : (1 : ℝ) ∈ (H : Set ℝ) := by
    rw [hH]
    constructor <;> norm_num
  have h2 : (2 : ℝ) ∈ (H : Set ℝ) := by
    convert H.add_mem h1 h1 using 1; norm_num
  rw [hH] at h2
  norm_num [Chapter02RealClosedUnitInterval] at h2

theorem chapter02_complex_closed_unit_disk_is_not_an_additive_subgroup :
    ¬ ∃ H : AddSubgroup ℂ, (H : Set ℂ) = Chapter02ComplexClosedUnitDisk := by
  rintro ⟨H, hH⟩
  have h1 : (1 : ℂ) ∈ (H : Set ℂ) := by
    rw [hH]
    norm_num [Chapter02ComplexClosedUnitDisk]
  have h2 : (2 : ℂ) ∈ (H : Set ℂ) := by
    convert H.add_mem h1 h1 using 1; norm_num
  rw [hH] at h2
  norm_num [Chapter02ComplexClosedUnitDisk] at h2

theorem chapter02_complex_unit_circle_is_not_open :
    ¬IsOpen Chapter02ComplexUnitCircle := by
  intro hopen
  have h1 : (1 : ℂ) ∈ Chapter02ComplexUnitCircle := by
    norm_num [Chapter02ComplexUnitCircle]
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen 1 h1
  have hz : ((1 + ε / 2 : ℝ) : ℂ) ∈ Metric.ball (1 : ℂ) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    norm_num [Complex.norm_real, Complex.ofReal_sub, Complex.ofReal_one]
    rw [abs_of_pos hε]
    linarith
  have hzcircle : ((1 + ε / 2 : ℝ) : ℂ) ∈ Chapter02ComplexUnitCircle := hεsub hz
  have hzcircle' : ‖1 + (ε : ℂ) / 2‖ = 1 := by
    simpa [Chapter02ComplexUnitCircle] using hzcircle
  have heq : (1 + (ε : ℂ) / 2) = ((1 + ε / 2 : ℝ) : ℂ) := by
    norm_num [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one]
  have hnorm : ‖1 + (ε : ℂ) / 2‖ = 1 + ε / 2 := by
    rw [heq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < 1 + ε / 2)]
  rw [hnorm] at hzcircle'
  linarith

theorem chapter02_complex_unit_circle_is_not_open_in_C_units :
    ¬IsOpen Chapter02ComplexUnitCircleInUnits := by
  intro hopen
  have hem := IsOpenUnits.isOpenEmbedding_unitsVal (M := ℂ)
  have himage : IsOpen (Units.val '' Chapter02ComplexUnitCircleInUnits) :=
    hem.isOpen_iff_image_isOpen.mp hopen
  have heq : Units.val '' Chapter02ComplexUnitCircleInUnits = Chapter02ComplexUnitCircle := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hz
      refine ⟨Units.mk0 z ?_, ?_, ?_⟩
      · intro hz0
        rw [hz0] at hz
        norm_num [Chapter02ComplexUnitCircle] at hz
      · exact hz
      · rfl
  rw [heq] at himage
  exact chapter02_complex_unit_circle_is_not_open himage

end

end LastLib.Book04AdelesAndIdeles.Chapter02
