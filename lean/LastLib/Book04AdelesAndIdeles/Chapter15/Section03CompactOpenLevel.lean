import LastLib.Book04AdelesAndIdeles.Chapter15.Section01MatricesOverTheAdeles
import LastLib.Book04AdelesAndIdeles.Chapter01.Section02NumberFieldsAndIntegers
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.Section06CompactnessAndLocalCompactness

namespace LastLib.Book04AdelesAndIdeles.Chapter15

noncomputable section

open Set Filter NumberField
open scoped RestrictedProduct

/-! ## 15.3. Compact open level -/

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The standard level as a level datum, not just its underlying subgroup. -/
def chapter15StandardFiniteMatrixLevelData (n : ℕ) [NumberField K] :
    Chapter15FiniteMatrixLevel (R := 𝓞 K) (K := K) n where
  localSubgroup := fun v => chapter15FiniteMatrixIntegralSubgroup n v
  subgroup := chapter15StandardFiniteMatrixLevel n
  mem_iff := fun g => Iff.rfl
  isCompact := chapter15_standard_finite_matrix_level_is_compact n
  isOpen := chapter15_standard_finite_matrix_level_is_open n
  standard_outside_finite := by
    refine ⟨∅, ?_⟩
    intro v hv
    simp

/-- The compact-open-level predicate used for arbitrary finite subgroups. -/
def chapter15IsCompactOpenMatrixLevel
    (n : ℕ) (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K)) : Prop :=
  IsCompact (Kf : Set (Chapter15FiniteMatrixGroup n R K)) ∧
    IsOpen (Kf : Set (Chapter15FiniteMatrixGroup n R K))

theorem chapter15FiniteMatrixLevel_is_compact_open
    (n : ℕ) (L : Chapter15FiniteMatrixLevel (R := R) (K := K) n) :
    chapter15IsCompactOpenMatrixLevel n L.subgroup :=
  ⟨L.isCompact, L.isOpen⟩

/-! ### Local reduction and principal congruence subgroups -/

/-- Reduction of integral matrices modulo `𝔭_v^m`. -/
def chapter15LocalMatrixReduction (n : ℕ) (v : Chapter15FinitePlace R) (m : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers K) →*
      Matrix.GeneralLinearGroup (Fin n)
        ((v.adicCompletionIntegers K) ⧸ (IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K)) ^ m) :=
  Matrix.GeneralLinearGroup.map
    (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal
      (v.adicCompletionIntegers K)) ^ m))

/-- The local principal congruence subgroup is the kernel of reduction. -/
def chapter15LocalMatrixCongruenceKernel
    (n : ℕ) (v : Chapter15FinitePlace R) (m : ℕ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers K)) :=
  (chapter15LocalMatrixReduction (R := R) (K := K) n v m).ker

/-- The corresponding subgroup inside the field-valued local GL group. -/
def chapter15LocalMatrixCongruenceSubgroup
    (n : ℕ) (v : Chapter15FinitePlace R) (m : ℕ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :=
  Subgroup.map
    (Matrix.GeneralLinearGroup.map (v.adicCompletionIntegers K).subtype)
    (chapter15LocalMatrixCongruenceKernel (R := R) (K := K) n v m)

theorem chapter15_local_matrix_congruence_mem_iff
    (n : ℕ) (v : Chapter15FinitePlace R) (m : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers K)) :
    g ∈ chapter15LocalMatrixCongruenceKernel n v m ↔
      chapter15LocalMatrixReduction n v m g = 1 := by
  exact MonoidHom.mem_ker

theorem chapter15_local_matrix_congruence_subgroup_mem_iff
    (n : ℕ) (v : Chapter15FinitePlace R) (m : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :
    g ∈ chapter15LocalMatrixCongruenceSubgroup n v m ↔
      ∃ h : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers K),
        h ∈ chapter15LocalMatrixCongruenceKernel n v m ∧
        Matrix.GeneralLinearGroup.map
              (v.adicCompletionIntegers K).subtype h = g := by
  rfl

theorem chapter15_local_matrix_congruence_subgroup_entries_iff
    (n : ℕ) (v : Chapter15FinitePlace R) (m : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :
    g ∈ chapter15LocalMatrixCongruenceSubgroup n v m ↔
      ∃ h : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers K),
        Matrix.GeneralLinearGroup.map
              (v.adicCompletionIntegers K).subtype h = g ∧
        ∀ i j : Fin n,
          (h i j - if i = j then 1 else 0) ∈
            (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m := by
  rw [chapter15_local_matrix_congruence_subgroup_mem_iff]
  constructor
  · rintro ⟨h, hh, heq⟩
    refine ⟨h, heq, ?_⟩
    rw [chapter15_local_matrix_congruence_mem_iff] at hh
    intro i j
    have hhij := congrArg
      (fun z : Matrix.GeneralLinearGroup (Fin n)
          ((v.adicCompletionIntegers K) ⧸
            (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m) => z i j) hh
    change (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m)) (h i j) =
      (1 : Matrix (Fin n) (Fin n)
        ((v.adicCompletionIntegers K) ⧸
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m)) i j at hhij
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    calc
      (Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m))
          (h i j - if i = j then 1 else 0) =
        (Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m)) (h i j) -
          (Ideal.Quotient.mk
            ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m))
            (if i = j then 1 else 0) := by rw [map_sub]
      _ = (1 : Matrix (Fin n) (Fin n)
          ((v.adicCompletionIntegers K) ⧸
            (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m)) i j -
          (Ideal.Quotient.mk
            ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m))
            (if i = j then 1 else 0) := by
            rw [hhij]
      _ = 0 := by simp [Matrix.one_apply]
  · rintro ⟨h, heq, hentries⟩
    refine ⟨h, ?_, heq⟩
    rw [chapter15_local_matrix_congruence_mem_iff]
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr (hentries i j)
    rw [map_sub] at hzero
    change (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m)) (h i j) =
      (1 : Matrix (Fin n) (Fin n)
        ((v.adicCompletionIntegers K) ⧸
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m)) i j
    rw [← sub_eq_zero]
    simpa [Matrix.one_apply] using hzero

/-- Reduction of integral units modulo `𝔭_v^m`. -/
def chapter15LocalUnitReduction (v : Chapter15FinitePlace R) (m : ℕ) :
    (v.adicCompletionIntegers K)ˣ →*
      ((v.adicCompletionIntegers K) ⧸ (IsLocalRing.maximalIdeal
        (v.adicCompletionIntegers K)) ^ m)ˣ :=
  Units.map
    (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal
      (v.adicCompletionIntegers K)) ^ m)).toMonoidHom

/-- The local principal unit congruence subgroup is the kernel of unit reduction. -/
def chapter15LocalUnitCongruenceKernel (v : Chapter15FinitePlace R) (m : ℕ) :
    Subgroup (v.adicCompletionIntegers K)ˣ :=
  (chapter15LocalUnitReduction (R := R) (K := K) v m).ker

/-- The corresponding principal congruence subgroup in the local field units. -/
def chapter15LocalFieldUnitCongruenceSubgroup
    (v : Chapter15FinitePlace R) (m : ℕ) : Subgroup ((v.adicCompletion K)ˣ) :=
  Subgroup.map (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom)
    (chapter15LocalUnitCongruenceKernel (R := R) (K := K) v m)

theorem chapter15_local_unit_congruence_mem_iff
    (v : Chapter15FinitePlace R) (m : ℕ)
    (u : (v.adicCompletionIntegers K)ˣ) :
    u ∈ chapter15LocalUnitCongruenceKernel v m ↔
      chapter15LocalUnitReduction v m u = 1 := by
  exact MonoidHom.mem_ker

theorem chapter15_local_field_unit_congruence_subgroup_mem_iff
    (v : Chapter15FinitePlace R) (m : ℕ) (u : (v.adicCompletion K)ˣ) :
    u ∈ chapter15LocalFieldUnitCongruenceSubgroup v m ↔
      ∃ w : (v.adicCompletionIntegers K)ˣ,
        w ∈ chapter15LocalUnitCongruenceKernel v m ∧
          Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom w = u := by
  rfl

theorem chapter15_local_field_unit_congruence_subgroup_mem_iff_entries
    (v : Chapter15FinitePlace R) (m : ℕ) (u : (v.adicCompletion K)ˣ) :
    u ∈ chapter15LocalFieldUnitCongruenceSubgroup v m ↔
      ∃ w : (v.adicCompletionIntegers K)ˣ,
        Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom w = u ∧
          (w : v.adicCompletionIntegers K) - 1 ∈
            (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m := by
  rw [chapter15_local_field_unit_congruence_subgroup_mem_iff]
  constructor
  · rintro ⟨w, hw, heq⟩
    refine ⟨w, heq, ?_⟩
    rw [chapter15_local_unit_congruence_mem_iff] at hw
    have hwval := congrArg
      (fun z : (((v.adicCompletionIntegers K) ⧸
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m)ˣ) =>
        (z : (v.adicCompletionIntegers K) ⧸
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m)) hw
    change (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m))
        (w : v.adicCompletionIntegers K) = 1 at hwval
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    calc
      (Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m))
          ((w : v.adicCompletionIntegers K) - 1) =
        (Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m))
            (w : v.adicCompletionIntegers K) -
          (Ideal.Quotient.mk
            ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m)) 1 := by
              rw [map_sub]
      _ = 1 - 1 := by rw [hwval]; simp
      _ = 0 := sub_self _
  · rintro ⟨w, heq, hw⟩
    refine ⟨w, ?_, heq⟩
    apply (chapter15_local_unit_congruence_mem_iff (R := R) (K := K) v m w).2
    apply Units.ext
    change (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ m))
        (w : v.adicCompletionIntegers K) = 1
    apply sub_eq_zero.mp
    have hwzero := Ideal.Quotient.eq_zero_iff_mem.mpr hw
    rw [map_sub] at hwzero
    simpa using hwzero

/-! ### The finite targets and compact-open consequences -/

theorem chapter15_local_matrix_reduction_target_finite
    (n : ℕ) {L : Type*} [Field L] [NumberField L]
    (v : Chapter15FinitePlace (𝓞 L)) (m : ℕ) :
    Finite (Matrix.GeneralLinearGroup (Fin n)
      ((v.adicCompletionIntegers L) ⧸
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ m)) := by
  let : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers L)) :=
    Chapter07.chapter07_finite_local_residueField_finite (𝓞 L) L v
  let : IsDiscreteValuationRing (v.adicCompletionIntegers L) :=
    LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_completion_integers_is_dvr L v
  let : Finite ((v.adicCompletionIntegers L) ⧸
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ m) :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.chapter06_dvr_power_quotient_finite m
  infer_instance

theorem chapter15_local_unit_reduction_target_finite
    {L : Type*} [Field L] [NumberField L]
    (v : Chapter15FinitePlace (𝓞 L)) (m : ℕ) :
    Finite (((v.adicCompletionIntegers L) ⧸
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ m)ˣ) := by
  let : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers L)) :=
    Chapter07.chapter07_finite_local_residueField_finite (𝓞 L) L v
  let : IsDiscreteValuationRing (v.adicCompletionIntegers L) :=
    LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_completion_integers_is_dvr L v
  let : Finite ((v.adicCompletionIntegers L) ⧸
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ m) :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.chapter06_dvr_power_quotient_finite m
  infer_instance

private theorem chapter15_local_integer_compactSpace
    {L : Type*} [Field L] [NumberField L]
    (v : Chapter15FinitePlace (𝓞 L)) :
    CompactSpace (v.adicCompletionIntegers L) := by
  constructor
  rw [Subtype.isCompact_iff]
  convert Chapter07.chapter07_finite_local_integer_isCompact (𝓞 L) L v using 1
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩

private theorem chapter15_local_reduction_quotient_discrete
    {L : Type*} [Field L] [NumberField L]
    (v : Chapter15FinitePlace (𝓞 L)) (m : ℕ) :
    DiscreteTopology ((v.adicCompletionIntegers L) ⧸
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ m) := by
  let : IsDiscreteValuationRing (v.adicCompletionIntegers L) :=
    LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_completion_integers_is_dvr L v
  let : CompactSpace (v.adicCompletionIntegers L) :=
    chapter15_local_integer_compactSpace v
  exact QuotientAddGroup.discreteTopology
    (IsLocalRing.isOpen_maximalIdeal_pow (v.adicCompletionIntegers L) m)

theorem chapter15_local_matrix_congruence_is_compact_open
    (n : ℕ) {L : Type*} [Field L] [NumberField L]
    (v : Chapter15FinitePlace (𝓞 L)) (m : ℕ) :
    IsCompact
        (chapter15LocalMatrixCongruenceSubgroup (R := 𝓞 L) (K := L) n v m :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L))) ∧
      IsOpen
        (chapter15LocalMatrixCongruenceSubgroup (R := 𝓞 L) (K := L) n v m :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L))) := by
  classical
  let : IsDiscreteValuationRing (v.adicCompletionIntegers L) :=
    LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_completion_integers_is_dvr L v
  let : CompactSpace (v.adicCompletionIntegers L) :=
    chapter15_local_integer_compactSpace v
  let : DiscreteTopology ((v.adicCompletionIntegers L) ⧸
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ m) :=
    chapter15_local_reduction_quotient_discrete v m
  have hred : Continuous
      (chapter15LocalMatrixReduction (R := 𝓞 L) (K := L) n v m) := by
    change Continuous (Matrix.GeneralLinearGroup.map
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal
        (v.adicCompletionIntegers L)) ^ m)))
    exact continuous_quot_mk.generalLinearGroup_map
  have hker :
      (chapter15LocalMatrixCongruenceKernel (R := 𝓞 L) (K := L) n v m :
        Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers L))) =
        (chapter15LocalMatrixReduction (R := 𝓞 L) (K := L) n v m ⁻¹'
          ({1} : Set (Matrix.GeneralLinearGroup (Fin n)
            ((v.adicCompletionIntegers L) ⧸
              (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ m)))) := by
    ext g
    exact MonoidHom.mem_ker
  have hA : IsCompact
      (Set.univ : Set (v.adicCompletionIntegers L)) :=
    isCompact_univ_iff.mpr inferInstance
  have hmatrix_eq :
      (Set.matrix (Set.univ : Set (v.adicCompletionIntegers L)) :
        Set (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L))) = Set.univ := by
    ext M
    simp [Set.mem_matrix]
  have hmatrix : IsCompact
      (Set.univ : Set (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L))) := by
    rw [← hmatrix_eq]
    exact hA.matrix
  have hunit_eq :
      ((⊤ : Submonoid (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L))).units :
        Set (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L))ˣ) = Set.univ := by
    ext u
    simp
  have hunit : IsCompact
      (Set.univ : Set (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L))ˣ) := by
    rw [← hunit_eq]
    exact Submonoid.units_isCompact hmatrix
  have hgl : IsCompact
      (Set.univ : Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers L))) := by
    change IsCompact
      (Set.univ : Set (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L))ˣ)
    exact hunit
  have hker_closed : IsClosed
      (chapter15LocalMatrixCongruenceKernel (R := 𝓞 L) (K := L) n v m :
        Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers L))) := by
    rw [hker]
    exact isClosed_singleton.preimage hred
  have hker_compact : IsCompact
      (chapter15LocalMatrixCongruenceKernel (R := 𝓞 L) (K := L) n v m :
        Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers L))) :=
    hgl.of_isClosed_subset hker_closed (Set.subset_univ _)
  have hmap : Continuous
      (Matrix.GeneralLinearGroup.map (n := Fin n) (v.adicCompletionIntegers L).subtype) :=
    (continuous_subtype_val :
      Continuous ((↑) : v.adicCompletionIntegers L → v.adicCompletion L)).generalLinearGroup_map
  have hval : Topology.IsOpenEmbedding
      ((↑) : v.adicCompletionIntegers L → v.adicCompletion L) :=
    (Valued.isOpen_valuationSubring _).isOpenEmbedding_subtypeVal
  have hemb : Topology.IsEmbedding
      (Matrix.GeneralLinearGroup.map (n := Fin n) (v.adicCompletionIntegers L).subtype) :=
    hval.toIsEmbedding.generalLinearGroup_map
  have hrange : Set.range
      (Matrix.GeneralLinearGroup.map (n := Fin n) (v.adicCompletionIntegers L).subtype) =
      (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 L) (K := L) n v :
        Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L))) := by
    rfl
  have hopenEmbedding : Topology.IsOpenEmbedding
      (Matrix.GeneralLinearGroup.map (n := Fin n) (v.adicCompletionIntegers L).subtype) :=
    { toIsEmbedding := hemb
      isOpen_range := by
        rw [hrange]
        exact chapter15_finite_integral_matrix_group_is_open n v }
  constructor
  · rw [chapter15LocalMatrixCongruenceSubgroup, Subgroup.coe_map]
    exact hker_compact.image hmap
  · have hker_open : IsOpen
        (chapter15LocalMatrixCongruenceKernel (R := 𝓞 L) (K := L) n v m :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers L))) := by
      rw [hker]
      exact hred.isOpen_preimage {1}
        ((discreteTopology_iff_isOpen_singleton.mp inferInstance) 1)
    rw [chapter15LocalMatrixCongruenceSubgroup, Subgroup.coe_map]
    exact hopenEmbedding.isOpenMap _ hker_open

theorem chapter15_local_field_unit_congruence_is_compact_open
    {L : Type*} [Field L] [NumberField L]
    (v : Chapter15FinitePlace (𝓞 L)) (m : ℕ) :
    IsCompact
        (chapter15LocalFieldUnitCongruenceSubgroup (R := 𝓞 L) (K := L) v m :
          Set ((v.adicCompletion L)ˣ)) ∧
      IsOpen
        (chapter15LocalFieldUnitCongruenceSubgroup (R := 𝓞 L) (K := L) v m :
          Set ((v.adicCompletion L)ˣ)) := by
  classical
  let : IsDiscreteValuationRing (v.adicCompletionIntegers L) :=
    LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_completion_integers_is_dvr L v
  let : CompactSpace (v.adicCompletionIntegers L) :=
    chapter15_local_integer_compactSpace v
  let : DiscreteTopology ((v.adicCompletionIntegers L) ⧸
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ m) :=
    chapter15_local_reduction_quotient_discrete v m
  have hred : Continuous
      (chapter15LocalUnitReduction (R := 𝓞 L) (K := L) v m) := by
    change Continuous (Units.map
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal
        (v.adicCompletionIntegers L)) ^ m)).toMonoidHom)
    exact continuous_quot_mk.units_map _
  have hker :
      (chapter15LocalUnitCongruenceKernel (R := 𝓞 L) (K := L) v m :
        Set (v.adicCompletionIntegers L)ˣ) =
        (chapter15LocalUnitReduction (R := 𝓞 L) (K := L) v m ⁻¹'
          ({1} : Set (((v.adicCompletionIntegers L) ⧸
            (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ m)ˣ))) := by
    ext u
    exact MonoidHom.mem_ker
  have hA : IsCompact
      (Set.univ : Set (v.adicCompletionIntegers L)) :=
    isCompact_univ_iff.mpr inferInstance
  have hunit_eq :
      ((⊤ : Submonoid (v.adicCompletionIntegers L)).units :
        Set (v.adicCompletionIntegers L)ˣ) = Set.univ := by
    ext u
    simp
  have hunit : IsCompact (Set.univ : Set (v.adicCompletionIntegers L)ˣ) := by
    rw [← hunit_eq]
    exact Submonoid.units_isCompact hA
  have hker_closed : IsClosed
      (chapter15LocalUnitCongruenceKernel (R := 𝓞 L) (K := L) v m :
        Set (v.adicCompletionIntegers L)ˣ) := by
    rw [hker]
    exact isClosed_singleton.preimage hred
  have hker_compact : IsCompact
      (chapter15LocalUnitCongruenceKernel (R := 𝓞 L) (K := L) v m :
        Set (v.adicCompletionIntegers L)ˣ) :=
    hunit.of_isClosed_subset hker_closed (Set.subset_univ _)
  have hmap : Continuous
      (Units.map (v.adicCompletionIntegers L).subtype.toMonoidHom) :=
    continuous_subtype_val.units_map _
  have hval : Topology.IsOpenEmbedding
      ((↑) : v.adicCompletionIntegers L → v.adicCompletion L) :=
    (Valued.isOpen_valuationSubring _).isOpenEmbedding_subtypeVal
  have hemb : Topology.IsEmbedding
      (Units.map (v.adicCompletionIntegers L).subtype.toMonoidHom) :=
    hval.toIsEmbedding.units_map
  have hlocal :
      chapter15FiniteUnitIntegralSubgroup (R := 𝓞 L) (K := L) v =
        (Submonoid.ofClass (v.adicCompletionIntegers L)).units := by
    apply Subgroup.ext
    intro u
    constructor
    · rintro ⟨x, rfl⟩
      exact Submonoid.mem_units_of_val_mem_inv_val_mem _ x.1.2 x.2.2
    · intro hu
      rcases hu with ⟨hu, huinv⟩
      let x : (v.adicCompletionIntegers L)ˣ :=
        { val := ⟨(u : v.adicCompletion L), hu⟩
          inv := ⟨((u⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L), huinv⟩
          val_inv := by apply Subtype.ext; exact u.val_inv
          inv_val := by apply Subtype.ext; exact u.inv_val }
      exact ⟨x, by apply Units.ext; rfl⟩
  have hrange : Set.range
      (Units.map (v.adicCompletionIntegers L).subtype.toMonoidHom) =
      (chapter15FiniteUnitIntegralSubgroup (R := 𝓞 L) (K := L) v :
        Set ((v.adicCompletion L)ˣ)) := by
    rfl
  have hopenEmbedding : Topology.IsOpenEmbedding
      (Units.map (v.adicCompletionIntegers L).subtype.toMonoidHom) :=
    { toIsEmbedding := hemb
      isOpen_range := by
        rw [hrange, hlocal]
        exact (Valued.isOpen_valuationSubring _).preimage Units.continuous_val |>.inter
          ((Valued.isOpen_valuationSubring _).preimage Units.continuous_coe_inv) }
  constructor
  · rw [chapter15LocalFieldUnitCongruenceSubgroup, Subgroup.coe_map]
    exact hker_compact.image hmap
  · have hker_open : IsOpen
        (chapter15LocalUnitCongruenceKernel (R := 𝓞 L) (K := L) v m :
          Set (v.adicCompletionIntegers L)ˣ) := by
      rw [hker]
      exact hred.isOpen_preimage {1}
        ((discreteTopology_iff_isOpen_singleton.mp inferInstance) 1)
    rw [chapter15LocalFieldUnitCongruenceSubgroup, Subgroup.coe_map]
    exact hopenEmbedding.isOpenMap _ hker_open

private def chapter15FiniteMatrixLevelSubgroup
    (n : ℕ) (B : ∀ v : Chapter15FinitePlace R,
      Subgroup (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))) :
    Subgroup (Chapter15FiniteMatrixGroup n R K) where
  carrier := {g | ∀ v, g v ∈ B v}
  one_mem' := by
    intro v
    exact (B v).one_mem
  mul_mem' := by
    intro g h hg hh v
    exact (B v).mul_mem (hg v) (hh v)
  inv_mem' := by
    intro g hg v
    exact (B v).inv_mem (hg v)

private theorem chapter15_finite_matrix_level_compact_open_of_local
    (n : ℕ) {L : Type*} [Field L] [NumberField L]
    (B : ∀ v : Chapter15FinitePlace (𝓞 L),
      Subgroup (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L)))
    (S : Finset (Chapter15FinitePlace (𝓞 L)))
    (hsub : ∀ v, B v ≤ chapter15FiniteMatrixIntegralSubgroup
      (R := 𝓞 L) (K := L) n v)
    (hcompact : ∀ v, IsCompact (B v : Set
      (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L))))
    (hopen : ∀ v, IsOpen (B v : Set
      (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L))))
    (houtside : ∀ v ∉ S, B v =
      chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 L) (K := L) n v) :
    IsCompact (chapter15FiniteMatrixLevelSubgroup
      (R := 𝓞 L) (K := L) n B : Set (Chapter15FiniteMatrixGroup n (𝓞 L) L)) ∧
      IsOpen (chapter15FiniteMatrixLevelSubgroup
        (R := 𝓞 L) (K := L) n B : Set (Chapter15FiniteMatrixGroup n (𝓞 L) L)) := by
  let C : Set (Chapter15FiniteMatrixGroup n (𝓞 L) L) :=
    ⋂ v : {v // v ∈ S},
      (fun g : Chapter15FiniteMatrixGroup n (𝓞 L) L => g v.1) ⁻¹'
        (B v.1 : Set (Matrix.GeneralLinearGroup (Fin n) (v.1.adicCompletion L)))
  have hTC :
      (chapter15FiniteMatrixLevelSubgroup
        (R := 𝓞 L) (K := L) n B : Set (Chapter15FiniteMatrixGroup n (𝓞 L) L)) =
        (chapter15StandardFiniteMatrixLevel (R := 𝓞 L) (K := L) n :
          Set (Chapter15FiniteMatrixGroup n (𝓞 L) L)) ∩ C := by
    ext g
    constructor
    · intro hg
      change ∀ v, g v ∈ B v at hg
      refine ⟨?_, ?_⟩
      · change ∀ v, g v ∈
          chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 L) (K := L) n v
        intro v
        exact hsub v (hg v)
      · change g ∈ ⋂ v : {v // v ∈ S},
          (fun g : Chapter15FiniteMatrixGroup n (𝓞 L) L => g v.1) ⁻¹'
            (B v.1 : Set (Matrix.GeneralLinearGroup (Fin n)
              (v.1.adicCompletion L)))
        exact Set.mem_iInter.mpr (fun v => hg v.1)
    · rintro ⟨hg, hc⟩
      change ∀ v, g v ∈ B v
      change ∀ v, g v ∈
        chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 L) (K := L) n v at hg
      change g ∈ ⋂ v : {v // v ∈ S},
        (fun g : Chapter15FiniteMatrixGroup n (𝓞 L) L => g v.1) ⁻¹'
          (B v.1 : Set (Matrix.GeneralLinearGroup (Fin n)
            (v.1.adicCompletion L))) at hc
      intro v
      by_cases hv : v ∈ S
      · exact Set.mem_iInter.mp hc ⟨v, hv⟩
      · rw [houtside v hv]
        exact hg v
  have hev : ∀ v : Chapter15FinitePlace (𝓞 L),
      Continuous (fun g : Chapter15FiniteMatrixGroup n (𝓞 L) L => g v) := by
    intro v
    exact RestrictedProduct.continuous_eval
      (R := fun v : Chapter15FinitePlace (𝓞 L) =>
        Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L))
      (A := fun v =>
        (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 L) (K := L) n v :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L))))
      (𝓕 := Filter.cofinite) v
  have hCclosed : IsClosed C := by
    dsimp [C]
    apply isClosed_iInter
    intro v
    exact (hcompact v.1).isClosed.preimage (hev v.1)
  have hCopen : IsOpen C := by
    dsimp [C]
    apply isOpen_iInter_of_finite
    intro v
    exact (hopen v.1).preimage (hev v.1)
  have hstdcompact : IsCompact
      (chapter15StandardFiniteMatrixLevel (R := 𝓞 L) (K := L) n :
        Set (Chapter15FiniteMatrixGroup n (𝓞 L) L)) :=
    chapter15_standard_finite_matrix_level_is_compact n
  have hstdopen : IsOpen
      (chapter15StandardFiniteMatrixLevel (R := 𝓞 L) (K := L) n :
        Set (Chapter15FiniteMatrixGroup n (𝓞 L) L)) :=
    chapter15_standard_finite_matrix_level_is_open n
  constructor
  · rw [hTC]
    exact hstdcompact.of_isClosed_subset (hstdcompact.isClosed.inter hCclosed)
      inter_subset_left
  · rw [hTC]
    exact hstdopen.inter hCopen

/-! ### A principal congruence level at finitely many places -/

def chapter15PrincipalCongruenceLocalMatrixLevel
    (n : ℕ) (S : Finset (Chapter15FinitePlace R))
    (m : Chapter15FinitePlace R → ℕ) (v : Chapter15FinitePlace R) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) := by
  classical
  by_cases hv : v ∈ S
  · exact chapter15LocalMatrixCongruenceSubgroup n v (m v)
  · exact chapter15FiniteMatrixIntegralSubgroup n v

def chapter15PrincipalCongruenceLocalUnitLevel
    (S : Finset (Chapter15FinitePlace R))
    (m : Chapter15FinitePlace R → ℕ) (v : Chapter15FinitePlace R) :
    Subgroup ((v.adicCompletion K)ˣ) := by
  classical
  by_cases hv : v ∈ S
  · exact chapter15LocalFieldUnitCongruenceSubgroup v (m v)
  · exact chapter15FiniteUnitIntegralSubgroup v

/- The exponent-zero and one-prime specializations are useful API bridges. -/
theorem chapter15_principal_congruence_local_matrix_level_outside_support
    (n : ℕ) (S : Finset (Chapter15FinitePlace R))
    (m : Chapter15FinitePlace R → ℕ) {v : Chapter15FinitePlace R} (hv : v ∉ S) :
    chapter15PrincipalCongruenceLocalMatrixLevel (R := R) (K := K) n S m v =
      chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v := by
  classical
  simp [chapter15PrincipalCongruenceLocalMatrixLevel, hv]

theorem chapter15_principal_congruence_local_unit_level_outside_support
    (S : Finset (Chapter15FinitePlace R))
    (m : Chapter15FinitePlace R → ℕ) {v : Chapter15FinitePlace R} (hv : v ∉ S) :
    chapter15PrincipalCongruenceLocalUnitLevel (R := R) (K := K) S m v =
      chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v := by
  classical
  simp [chapter15PrincipalCongruenceLocalUnitLevel, hv]

def chapter15PrincipalCongruenceMatrixLevelData
    (n : ℕ) [NumberField K] (S : Finset (Chapter15FinitePlace (𝓞 K)))
    (m : Chapter15FinitePlace (𝓞 K) → ℕ) :
    Chapter15FiniteMatrixLevel (R := 𝓞 K) (K := K) n where
  localSubgroup := chapter15PrincipalCongruenceLocalMatrixLevel
    (R := 𝓞 K) (K := K) n S m
  subgroup := chapter15FiniteMatrixLevelSubgroup
    (R := 𝓞 K) (K := K) n
    (chapter15PrincipalCongruenceLocalMatrixLevel
      (R := 𝓞 K) (K := K) n S m)
  mem_iff := by
    intro g
    rfl
  isCompact := by
    have hlevels := chapter15_finite_matrix_level_compact_open_of_local
      (L := K) n
      (chapter15PrincipalCongruenceLocalMatrixLevel
        (R := 𝓞 K) (K := K) n S m) S
      (by
        intro v
        classical
        by_cases hv : v ∈ S
        · intro g hg
          have hg' : g ∈ chapter15LocalMatrixCongruenceSubgroup
              (R := 𝓞 K) (K := K) n v (m v) := by
            simpa [chapter15PrincipalCongruenceLocalMatrixLevel, hv] using hg
          rcases (chapter15_local_matrix_congruence_subgroup_mem_iff
            (R := 𝓞 K) (K := K) n v (m v) g).1 hg' with ⟨h, hh, heq⟩
          exact ⟨h, heq⟩
        · rw [chapter15_principal_congruence_local_matrix_level_outside_support
            n S m hv])
      (by
        intro v
        classical
        by_cases hv : v ∈ S
        · simpa [chapter15PrincipalCongruenceLocalMatrixLevel, hv] using
            (chapter15_local_matrix_congruence_is_compact_open
              (L := K) n v (m v)).1
        · rw [chapter15_principal_congruence_local_matrix_level_outside_support
            n S m hv]
          exact chapter15_finite_integral_matrix_group_is_compact n v)
      (by
        intro v
        classical
        by_cases hv : v ∈ S
        · simpa [chapter15PrincipalCongruenceLocalMatrixLevel, hv] using
            (chapter15_local_matrix_congruence_is_compact_open
              (L := K) n v (m v)).2
        · rw [chapter15_principal_congruence_local_matrix_level_outside_support
            n S m hv]
          exact chapter15_finite_integral_matrix_group_is_open n v)
      (by
        intro v hv
        exact chapter15_principal_congruence_local_matrix_level_outside_support
          n S m hv)
    exact hlevels.1
  isOpen := by
    have hlevels := chapter15_finite_matrix_level_compact_open_of_local
      (L := K) n
      (chapter15PrincipalCongruenceLocalMatrixLevel
        (R := 𝓞 K) (K := K) n S m) S
      (by
        intro v
        classical
        by_cases hv : v ∈ S
        · intro g hg
          have hg' : g ∈ chapter15LocalMatrixCongruenceSubgroup
              (R := 𝓞 K) (K := K) n v (m v) := by
            simpa [chapter15PrincipalCongruenceLocalMatrixLevel, hv] using hg
          rcases (chapter15_local_matrix_congruence_subgroup_mem_iff
            (R := 𝓞 K) (K := K) n v (m v) g).1 hg' with ⟨h, hh, heq⟩
          exact ⟨h, heq⟩
        · rw [chapter15_principal_congruence_local_matrix_level_outside_support
            n S m hv])
      (by
        intro v
        classical
        by_cases hv : v ∈ S
        · simpa [chapter15PrincipalCongruenceLocalMatrixLevel, hv] using
            (chapter15_local_matrix_congruence_is_compact_open
              (L := K) n v (m v)).1
        · rw [chapter15_principal_congruence_local_matrix_level_outside_support
            n S m hv]
          exact chapter15_finite_integral_matrix_group_is_compact n v)
      (by
        intro v
        classical
        by_cases hv : v ∈ S
        · simpa [chapter15PrincipalCongruenceLocalMatrixLevel, hv] using
            (chapter15_local_matrix_congruence_is_compact_open
              (L := K) n v (m v)).2
        · rw [chapter15_principal_congruence_local_matrix_level_outside_support
            n S m hv]
          exact chapter15_finite_integral_matrix_group_is_open n v)
      (by
        intro v hv
        exact chapter15_principal_congruence_local_matrix_level_outside_support
          n S m hv)
    exact hlevels.2
  standard_outside_finite := by
    refine ⟨S, ?_⟩
    intro v hv
    exact chapter15_principal_congruence_local_matrix_level_outside_support
      n S m hv

/-! ### Upper-triangular reduction levels -/

def chapter15UpperTriangularSubgroup (n : ℕ) (S : Type*) [Ring S] :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) S) :=
  Subgroup.closure {g : Matrix.GeneralLinearGroup (Fin n) S |
    ∀ i j : Fin n, j < i → g i j = 0}

theorem chapter15UpperTriangularSubgroup_mem_iff
    (n : ℕ) (S : Type*) [Ring S]
    (g : Matrix.GeneralLinearGroup (Fin n) S) :
    g ∈ chapter15UpperTriangularSubgroup n S ↔
      ∀ i j : Fin n, j < i → g i j = 0 := by
  sorry

def chapter15LocalUpperTriangularMatrixLevel
    (n : ℕ) (v : Chapter15FinitePlace R) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :=
  Subgroup.map
    (Matrix.GeneralLinearGroup.map (v.adicCompletionIntegers K).subtype)
      ((chapter15UpperTriangularSubgroup n
      ((v.adicCompletionIntegers K) ⧸ (IsLocalRing.maximalIdeal
        (v.adicCompletionIntegers K)) ^ 1)).comap
      (chapter15LocalMatrixReduction (R := R) (K := K) n v 1))

private theorem chapter15_local_upper_triangular_matrix_level_is_compact_open
    (n : ℕ) {L : Type*} [Field L] [NumberField L]
    (v : Chapter15FinitePlace (𝓞 L)) :
    IsCompact
        (chapter15LocalUpperTriangularMatrixLevel (R := 𝓞 L) (K := L) n v :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L))) ∧
      IsOpen
        (chapter15LocalUpperTriangularMatrixLevel (R := 𝓞 L) (K := L) n v :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L))) := by
  classical
  let : IsDiscreteValuationRing (v.adicCompletionIntegers L) :=
    LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_completion_integers_is_dvr L v
  let : CompactSpace (v.adicCompletionIntegers L) :=
    chapter15_local_integer_compactSpace v
  let : Finite ((v.adicCompletionIntegers L) ⧸
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ 1) :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.chapter06_dvr_power_quotient_finite 1
  let : Finite (Matrix.GeneralLinearGroup (Fin n)
      ((v.adicCompletionIntegers L) ⧸
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ 1)) :=
    chapter15_local_matrix_reduction_target_finite n v 1
  let : DiscreteTopology ((v.adicCompletionIntegers L) ⧸
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ 1) :=
    chapter15_local_reduction_quotient_discrete v 1
  let : DiscreteTopology (Matrix.GeneralLinearGroup (Fin n)
      ((v.adicCompletionIntegers L) ⧸
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ 1)) :=
    Finite.instDiscreteTopology
  have hred : Continuous
      (chapter15LocalMatrixReduction (R := 𝓞 L) (K := L) n v 1) := by
    change Continuous (Matrix.GeneralLinearGroup.map
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal
        (v.adicCompletionIntegers L)) ^ 1)))
    exact continuous_quot_mk.generalLinearGroup_map
  have hupper_compact : IsCompact
      (chapter15UpperTriangularSubgroup n
        ((v.adicCompletionIntegers L) ⧸
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ 1) :
        Set (Matrix.GeneralLinearGroup (Fin n)
          ((v.adicCompletionIntegers L) ⧸
            (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ 1))) :=
    (Set.toFinite _).isCompact
  have hupper_open : IsOpen
      (chapter15UpperTriangularSubgroup n
        ((v.adicCompletionIntegers L) ⧸
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ 1) :
        Set (Matrix.GeneralLinearGroup (Fin n)
          ((v.adicCompletionIntegers L) ⧸
            (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ 1))) :=
    isOpen_discrete _
  have hupper_closed : IsClosed
      (chapter15UpperTriangularSubgroup n
        ((v.adicCompletionIntegers L) ⧸
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ 1) :
        Set (Matrix.GeneralLinearGroup (Fin n)
          ((v.adicCompletionIntegers L) ⧸
            (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ 1))) :=
    isClosed_discrete _
  have hpre_closed : IsClosed
      (((chapter15UpperTriangularSubgroup n
        ((v.adicCompletionIntegers L) ⧸
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ 1)).comap
        (chapter15LocalMatrixReduction (R := 𝓞 L) (K := L) n v 1) :
        Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers L)))) := by
    exact hupper_closed.preimage hred
  have hA : IsCompact
      (Set.univ : Set (v.adicCompletionIntegers L)) :=
    isCompact_univ_iff.mpr inferInstance
  have hmatrix_eq :
      (Set.matrix (Set.univ : Set (v.adicCompletionIntegers L)) :
        Set (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L))) = Set.univ := by
    ext M
    simp [Set.mem_matrix]
  have hmatrix : IsCompact
      (Set.univ : Set (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L))) := by
    rw [← hmatrix_eq]
    exact hA.matrix
  have hunit_eq :
      ((⊤ : Submonoid (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L))).units :
        Set (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L))ˣ) = Set.univ := by
    ext u
    simp
  have hunit : IsCompact
      (Set.univ : Set (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L))ˣ) := by
    rw [← hunit_eq]
    exact Submonoid.units_isCompact hmatrix
  have hgl : IsCompact
      (Set.univ : Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers L))) := by
    change IsCompact
      (Set.univ : Set (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L))ˣ)
    exact hunit
  have hpre_compact : IsCompact
      (((chapter15UpperTriangularSubgroup n
        ((v.adicCompletionIntegers L) ⧸
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ 1)).comap
        (chapter15LocalMatrixReduction (R := 𝓞 L) (K := L) n v 1) :
        Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers L)))) :=
    hgl.of_isClosed_subset hpre_closed (Set.subset_univ _)
  have hpre_open : IsOpen
      (((chapter15UpperTriangularSubgroup n
        ((v.adicCompletionIntegers L) ⧸
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers L)) ^ 1)).comap
        (chapter15LocalMatrixReduction (R := 𝓞 L) (K := L) n v 1) :
        Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletionIntegers L)))) := by
    exact hred.isOpen_preimage _ hupper_open
  have hmap : Continuous
      (Matrix.GeneralLinearGroup.map (n := Fin n) (v.adicCompletionIntegers L).subtype) :=
    (continuous_subtype_val :
      Continuous ((↑) : v.adicCompletionIntegers L → v.adicCompletion L)).generalLinearGroup_map
  have hval : Topology.IsOpenEmbedding
      ((↑) : v.adicCompletionIntegers L → v.adicCompletion L) :=
    (Valued.isOpen_valuationSubring _).isOpenEmbedding_subtypeVal
  have hemb : Topology.IsEmbedding
      (Matrix.GeneralLinearGroup.map (n := Fin n) (v.adicCompletionIntegers L).subtype) :=
    hval.toIsEmbedding.generalLinearGroup_map
  have hrange : Set.range
      (Matrix.GeneralLinearGroup.map (n := Fin n) (v.adicCompletionIntegers L).subtype) =
      (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 L) (K := L) n v :
        Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L))) := by
    rfl
  have hopenEmbedding : Topology.IsOpenEmbedding
      (Matrix.GeneralLinearGroup.map (n := Fin n) (v.adicCompletionIntegers L).subtype) :=
    { toIsEmbedding := hemb
      isOpen_range := by
        rw [hrange]
        exact chapter15_finite_integral_matrix_group_is_open n v }
  constructor
  · rw [chapter15LocalUpperTriangularMatrixLevel, Subgroup.coe_map]
    exact hpre_compact.image hmap
  · rw [chapter15LocalUpperTriangularMatrixLevel, Subgroup.coe_map]
    exact hopenEmbedding.isOpenMap _ hpre_open

private def chapter15UpperTriangularFiniteLocalLevel
    (n : ℕ) {L : Type*} [Field L] [NumberField L]
    (S : Finset (Chapter15FinitePlace (𝓞 L)))
    (v : Chapter15FinitePlace (𝓞 L)) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L)) := by
  classical
  by_cases hv : v ∈ S
  · exact chapter15LocalUpperTriangularMatrixLevel (R := 𝓞 L) (K := L) n v
  · exact chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 L) (K := L) n v

def chapter15UpperTriangularFiniteMatrixLevelData
    (n : ℕ) [NumberField K] (S : Finset (Chapter15FinitePlace (𝓞 K))) :
    Chapter15FiniteMatrixLevel (R := 𝓞 K) (K := K) n where
  localSubgroup := chapter15UpperTriangularFiniteLocalLevel n S
  subgroup := chapter15FiniteMatrixLevelSubgroup
    (R := 𝓞 K) (K := K) n (chapter15UpperTriangularFiniteLocalLevel n S)
  mem_iff := by
    intro g
    rfl
  isCompact := by
    have hlevels := chapter15_finite_matrix_level_compact_open_of_local
      (L := K) n (chapter15UpperTriangularFiniteLocalLevel n S) S
      (by
        intro v
        classical
        by_cases hv : v ∈ S
        · intro g hg
          have hg' : g ∈ chapter15LocalUpperTriangularMatrixLevel
              (R := 𝓞 K) (K := K) n v := by
            simpa [chapter15UpperTriangularFiniteLocalLevel, hv] using hg
          rcases hg' with ⟨h, hh, rfl⟩
          exact ⟨h, rfl⟩
        · simp [chapter15UpperTriangularFiniteLocalLevel, hv])
      (by
        intro v
        classical
        by_cases hv : v ∈ S
        · simpa [chapter15UpperTriangularFiniteLocalLevel, hv] using
            (chapter15_local_upper_triangular_matrix_level_is_compact_open
              (L := K) n v).1
        · simpa [chapter15UpperTriangularFiniteLocalLevel, hv] using
            chapter15_finite_integral_matrix_group_is_compact n v)
      (by
        intro v
        classical
        by_cases hv : v ∈ S
        · simpa [chapter15UpperTriangularFiniteLocalLevel, hv] using
            (chapter15_local_upper_triangular_matrix_level_is_compact_open
              (L := K) n v).2
        · simpa [chapter15UpperTriangularFiniteLocalLevel, hv] using
            chapter15_finite_integral_matrix_group_is_open n v)
      (by
        intro v hv
        simp [chapter15UpperTriangularFiniteLocalLevel, hv])
    exact hlevels.1
  isOpen := by
    have hlevels := chapter15_finite_matrix_level_compact_open_of_local
      (L := K) n (chapter15UpperTriangularFiniteLocalLevel n S) S
      (by
        intro v
        classical
        by_cases hv : v ∈ S
        · intro g hg
          have hg' : g ∈ chapter15LocalUpperTriangularMatrixLevel
              (R := 𝓞 K) (K := K) n v := by
            simpa [chapter15UpperTriangularFiniteLocalLevel, hv] using hg
          rcases hg' with ⟨h, hh, rfl⟩
          exact ⟨h, rfl⟩
        · simp [chapter15UpperTriangularFiniteLocalLevel, hv])
      (by
        intro v
        classical
        by_cases hv : v ∈ S
        · simpa [chapter15UpperTriangularFiniteLocalLevel, hv] using
            (chapter15_local_upper_triangular_matrix_level_is_compact_open
              (L := K) n v).1
        · simpa [chapter15UpperTriangularFiniteLocalLevel, hv] using
            chapter15_finite_integral_matrix_group_is_compact n v)
      (by
        intro v
        classical
        by_cases hv : v ∈ S
        · simpa [chapter15UpperTriangularFiniteLocalLevel, hv] using
            (chapter15_local_upper_triangular_matrix_level_is_compact_open
              (L := K) n v).2
        · simpa [chapter15UpperTriangularFiniteLocalLevel, hv] using
            chapter15_finite_integral_matrix_group_is_open n v)
      (by
        intro v hv
        simp [chapter15UpperTriangularFiniteLocalLevel, hv])
    exact hlevels.2
  standard_outside_finite := by
    refine ⟨S, ?_⟩
    intro v hv
    simp [chapter15UpperTriangularFiniteLocalLevel, hv]

/-! ### Level refinement -/

def chapter15LevelRefines {n : ℕ}
    (L₁ L₂ : Chapter15FiniteMatrixLevel (R := R) (K := K) n) : Prop :=
  L₁.subgroup ≤ L₂.subgroup

theorem chapter15_level_refines_iff_forgets_local_information
    {n : ℕ} (L₁ L₂ : Chapter15FiniteMatrixLevel (R := R) (K := K) n)
    : chapter15LevelRefines L₁ L₂ ↔
      ∀ g, g ∈ L₁.subgroup → g ∈ L₂.subgroup := by
  constructor
  · intro h g hg
    exact h hg
  · intro h g hg
    exact h g hg

/- The right quotient at a larger level is therefore a coarser quotient; the
actual quotient map is constructed after the double-coset type in §15.4. -/

end

end LastLib.Book04AdelesAndIdeles.Chapter15
