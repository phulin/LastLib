import LastLib.Book03RamificationTheory.Chapter04.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter04

noncomputable section

open scoped BigOperators Pointwise

/-! ## 4.1. Passing to an intermediate base -/

/-- The standing finite-Galois/separable-residue hypotheses for Chapters 4 and
5, recorded independently of any chosen valuation branch. -/
structure Chapter04StandingGaloisResidueData
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] : Prop where
  finite_galois_extension : FiniteDimensional K L
  galois_extension : IsGalois K L
  finite_residue_extension : FiniteDimensional k l
  separable_residue_extension : Algebra.IsSeparable k l

/-- The fixed field used for the subgroup `H ≤ Gal(L / K)`. -/
abbrev chapter04FixedField
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (H : Subgroup Gal(L / K)) : IntermediateField K L :=
  IntermediateField.fixedField H

/-- Membership in the fixed field is pointwise fixedness by the subgroup. -/
theorem chapter04_mem_fixedField_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (H : Subgroup Gal(L / K)) (x : L) :
    x ∈ chapter04FixedField H ↔ ∀ σ ∈ H, σ x = x := by
  exact IntermediateField.mem_fixedField_iff H x

/-- `L / Lᴴ` is Galois for every subgroup `H`; no normality of `H` is
needed for this upper extension. -/
theorem chapter04_top_over_fixed_field_is_galois
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L / K)) :
    IsGalois (chapter04FixedField H) L := by
  infer_instance

/-- The subgroup and the Galois group of the upper extension are canonically
isomorphic. -/
def chapter04_subgroup_equiv_upper_galois_group
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L / K)) :
    H ≃* Gal(L / chapter04FixedField H) := by
  exact IntermediateField.subgroupEquivAlgEquiv H

/-- Normality is exactly the condition that the fixed field is Galois over the
original base. -/
theorem chapter04_fixed_field_is_galois_over_base_iff_normal
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L / K)) :
    IsGalois K (chapter04FixedField H) ↔ H.Normal := by
  constructor
  · intro h
    have hnormal : (chapter04FixedField H).fixingSubgroup.Normal :=
      @IsGalois.fixingSubgroup_normal_of_isGalois K L _ _ _
        (chapter04FixedField H) inferInstance h
    rw [IntermediateField.fixingSubgroup_fixedField H] at hnormal
    exact hnormal
  · intro h
    exact @IsGalois.of_fixedField_normal_subgroup K L _ _ _ inferInstance H h

/-- Perfect residue/base fields make the finite residue extension separable,
which is the standing separability interface for the later quotient results. -/
theorem chapter04_perfect_base_finite_extension_is_separable
    {k l : Type*} [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [PerfectField k] :
    Algebra.IsSeparable k l := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.perfect_residue_field_has_separable_finite_extensions
      (k := k) (l := l)

/-- A finite residue field is perfect, so the separability hypothesis is
automatic in the finite-residue-field case. -/
theorem chapter04_finite_base_field_is_perfect
    (k : Type*) [Field k] [Finite k] : PerfectField k := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.finite_residue_field_is_perfect k

/-- The subgroup formula in source order: the lower filtration of `L / Lᴴ`
is the restriction of the lower filtration of `L / K`. -/
theorem chapter04_lower_subgroup_formula
    {G : Type*} [Group G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) (i : ℤ) :
    (chapter04LowerGroup (chapter04SubgroupLowerFiltration F H) i).map H.subtype =
      H ⊓ chapter04LowerGroup F i := by
  exact chapter04SubgroupLowerGroup_map_eq_inf F H i

/-- Membership form of the subgroup formula, expressing equality of the two
displacement tests on the common top field. -/
theorem chapter04_lower_subgroup_displacement_test
    {G : Type*} [Group G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) (i : ℤ) (σ : H) :
    σ ∈ chapter04LowerGroup (chapter04SubgroupLowerFiltration F H) i ↔
      (σ : G) ∈ chapter04LowerGroup F i := by
  exact chapter04SubgroupLowerGroup_mem_iff F H i σ

/-- Lower breaks of the intermediate extension are inherited from the ambient
extension; they may disappear when the subgroup misses a graded quotient. -/
theorem chapter04_lower_breaks_restrict_to_ambient_breaks
    {G : Type*} [Group G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) (i : ℤ)
    (hbreak : chapter04LowerBreak (chapter04SubgroupLowerFiltration F H) i) :
    chapter04LowerBreak F i := by
  exact chapter04SubgroupLowerBreak_implies_lowerBreak F H i hbreak

/-- In the valuation-ring realization, the preceding formula specializes to
the intersection `H ∩ Gᵢ` inside the decomposition group. -/
theorem chapter04_valuation_lower_subgroup_formula
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L)
    (H : Subgroup
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup K A))
    (i : ℤ) :
    (chapter04LowerGroup
      (chapter04SubgroupLowerFiltration (chapter04ValuationLowerFiltration K A) H) i).map
        H.subtype =
      H ⊓ chapter04LowerGroup (chapter04ValuationLowerFiltration K A) i := by
  exact chapter04_lower_subgroup_formula _ H i

/-- Conjugate subgroups determine conjugate intermediate fields. -/
theorem chapter04_conjugate_fixed_fields_have_conjugate_fixing_subgroups
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L / K)) (σ : Gal(L / K)) :
    ((chapter04FixedField H).map σ).fixingSubgroup =
      (MulAut.conj σ) • H := by
  simp [IntermediateField.fixingSubgroup_fixedField H]

/-- Equivalently, conjugating the field and then taking its fixed field gives
the conjugate subgroup field. -/
theorem chapter04_conjugate_fixed_fields_eq
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L / K)) (σ : Gal(L / K)) :
    (chapter04FixedField H).map σ =
      chapter04FixedField ((MulAut.conj σ) • H) := by
  exact
    ((IsGalois.fixedField_eq_iff_fixingSubgroup_eq).mpr
      (chapter04_conjugate_fixed_fields_have_conjugate_fixing_subgroups H σ)).symm

/-- Conjugate intermediate fields have the same lower cardinality profile. -/
theorem chapter04_conjugate_subgroups_have_identical_ramification_profile
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) (g : G)
    (hconj : ∀ n : ℕ,
      (F.lower n).map (MulAut.conj g).toMonoidHom = F.lower n) :
    chapter04SubgroupLowerCardinalityProfile F
        (chapter04ConjugateSubgroup H g) =
      chapter04SubgroupLowerCardinalityProfile F H := by
  exact chapter04_conjugate_subgroups_have_identical_lower_cardinality_profile F H g hconj

end
end LastLib.Book03RamificationTheory.Chapter04
