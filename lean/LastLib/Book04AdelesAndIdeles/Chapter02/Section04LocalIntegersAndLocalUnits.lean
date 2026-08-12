import LastLib.Book04AdelesAndIdeles.Chapter02.Core

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

theorem chapter02_local_integer_mem_iff
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Chapter02LocalField v) :
    x ∈ Chapter02LocalIntegerSet v ↔ Valued.v x ≤ 1 := by
  sorry

theorem chapter02_local_maximal_ideal_mem_iff
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Chapter02LocalField v) :
    x ∈ Chapter02LocalMaximalIdealSet v ↔ Valued.v x < 1 := by
  rfl

theorem chapter02_local_unit_mem_iff
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Chapter02LocalField v) :
    x ∈ Chapter02LocalUnitSet v ↔ x ≠ 0 ∧ Valued.v x = 1 := by
  rfl

theorem chapter02_local_integer_ring_is_discrete_valuation_ring
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsDiscreteValuationRing (Chapter02LocalIntegerRing v) := by
  sorry

theorem chapter02_local_integer_ring_is_complete
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    CompleteSpace (Chapter02LocalIntegerRing v) := by
  sorry

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
  sorry

theorem chapter02_uniformizer_has_residue_cardinality_norm
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : Chapter02LocalField v) (hπ : Chapter02LocalUniformizer v π) :
    ‖π‖ = (Chapter02LocalResidueCardinality v : ℝ)⁻¹ := by
  sorry

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
  sorry

/-- The exponent of a unit-normalized nonzero local element, defined from its
valuation value rather than from a chosen splitting of `Kᵥˣ`. -/
noncomputable def Chapter02LocalCanonicalOrder
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (Chapter02LocalField v)ˣ) : ℤ :=
  if h : Valued.v (x : Chapter02LocalField v) = 0 then 0 else
    (WithZero.unzero h).toAdd

theorem chapter02_local_canonical_order_is_additive
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x y : (Chapter02LocalField v)ˣ) :
    Chapter02LocalCanonicalOrder v (x * y) =
      Chapter02LocalCanonicalOrder v x + Chapter02LocalCanonicalOrder v y := by
  sorry

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

theorem chapter02_local_ideal_powers_are_neighborhoods
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    Chapter02LocalIdealPowerSet v m ∈ 𝓝 (0 : Chapter02LocalField v) := by
  sorry

theorem chapter02_local_ideal_powers_form_a_neighborhood_basis
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (U : Set (Chapter02LocalField v)) (hU : U ∈ 𝓝 0) :
    ∃ m : ℕ, Chapter02LocalIdealPowerSet v m ⊆ U := by
  sorry

theorem chapter02_local_integer_ring_is_compact_and_open
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsCompact (Chapter02LocalIntegerSet v) ∧
      IsOpen (Chapter02LocalIntegerSet v) := by
  sorry

theorem chapter02_local_ideal_powers_are_compact_and_open
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    IsCompact (Chapter02LocalIdealPowerSet v m) ∧
      IsOpen (Chapter02LocalIdealPowerSet v m) := by
  sorry

/-- The principal units `1 + pᵐ` as a subgroup of the local multiplicative group. -/
def Chapter02HigherPrincipalUnitGroup
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    Subgroup (Chapter02LocalField v)ˣ :=
  { carrier := {u | ∃ y : Chapter02LocalIntegerRing v,
        y ∈ Chapter02LocalIdealPower v m ∧
          (u : Chapter02LocalField v) = 1 + (y : Chapter02LocalField v)}
    one_mem' := by sorry
    mul_mem' := by sorry
    inv_mem' := by sorry }

theorem chapter02_higher_principal_units_are_open
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (m : ℕ) (hm : 1 ≤ m) :
    IsOpen (Chapter02HigherPrincipalUnitGroup v m : Set (Chapter02LocalField v)ˣ) := by
  sorry

theorem chapter02_principal_units_match_valuation_subring_api
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Chapter02HigherPrincipalUnitGroup v 1 =
      (v.adicCompletionIntegers K).principalUnitGroup := by
  sorry

/-! The archimedean warning: compact balls are not the open compact additive
subgroups that occur at finite places. -/

def Chapter02RealClosedUnitInterval : Set ℝ := Set.Icc (-1) 1

def Chapter02ComplexClosedUnitDisk : Set ℂ := {z | ‖z‖ ≤ 1}

def Chapter02ComplexUnitCircle : Set ℂ := {z | ‖z‖ = 1}

def Chapter02ComplexUnitCircleInUnits : Set ℂˣ :=
  {u | ‖(u : ℂ)‖ = 1}

theorem chapter02_real_closed_unit_interval_is_compact :
    IsCompact Chapter02RealClosedUnitInterval := by
  sorry

theorem chapter02_complex_closed_unit_disk_is_compact :
    IsCompact Chapter02ComplexClosedUnitDisk := by
  sorry

theorem chapter02_real_closed_unit_interval_is_not_an_additive_subgroup :
    ¬ ∃ H : AddSubgroup ℝ, (H : Set ℝ) = Chapter02RealClosedUnitInterval := by
  sorry

theorem chapter02_complex_closed_unit_disk_is_not_an_additive_subgroup :
    ¬ ∃ H : AddSubgroup ℂ, (H : Set ℂ) = Chapter02ComplexClosedUnitDisk := by
  sorry

theorem chapter02_complex_unit_circle_is_not_open :
    ¬IsOpen Chapter02ComplexUnitCircle := by
  sorry

theorem chapter02_complex_unit_circle_is_not_open_in_C_units :
    ¬IsOpen Chapter02ComplexUnitCircleInUnits := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter02
