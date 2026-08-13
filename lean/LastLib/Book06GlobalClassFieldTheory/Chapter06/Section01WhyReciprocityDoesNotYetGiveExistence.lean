import LastLib.Book06GlobalClassFieldTheory.Chapter06.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter06

open scoped BigOperators

noncomputable section

/-! # 6.1. Why reciprocity does not yet give existence

The section isolates the finite-character separation argument.  The actual
construction of each character field is deferred to Section 6.3; this file
records the logical reduction that the global existence theorem uses.
-/

/- The quotient by an open finite-index subgroup is a finite abelian group. -/
theorem chapter06_idele_class_quotient_finite
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (H : Chapter06OpenFiniteIndexSubgroup C) :
    Finite (C ⧸ H.subgroup) := by
  exact Subgroup.finiteIndex_iff_finite_quotient.mp H.finiteIndex'

/- Characters of the finite quotient separate a point outside the subgroup. -/
theorem chapter06_finite_quotient_characters_separate
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (H : Chapter06OpenFiniteIndexSubgroup C) {x : C}
    (hx : x ∉ H.subgroup) :
    ∃ χ : Chapter06QuotientCharacter H,
      chapter06LiftQuotientCharacter H χ x ≠ 1 := by
  sorry

/- The lifted character kernel is the pullback of the quotient kernel. -/
theorem chapter06_lifted_character_mem_kernel_iff
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (H : Chapter06OpenFiniteIndexSubgroup C)
    (χ : Chapter06QuotientCharacter H) (x : C) :
    x ∈ (chapter06LiftQuotientCharacter H χ).ker ↔
      QuotientGroup.mk' H.subgroup x ∈ χ.ker := by
  rfl

/- Finite character duality recovers H as the intersection of all lifted
character kernels. -/
theorem chapter06_open_subgroup_is_character_kernel_intersection
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (H : Chapter06OpenFiniteIndexSubgroup C) :
    H.subgroup = ⨅ χ ∈ chapter06LiftedQuotientCharacters H, χ.ker := by
  symm
  exact chapter06_lifted_quotient_character_kernels_inf H

/- A single finite character realization, including its faithful cyclic
Galois character and the finite reciprocity witness for its field. -/
structure Chapter06FiniteCharacterRealization
    (K Ks C : Type*) [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] [TopologicalSpace C] (χ : C →* ℂˣ) where
  reciprocity : Chapter06FiniteReciprocityWitness K Ks C
  cyclic : IsCyclic (Gal(reciprocity.extension.field / K))
  galoisCharacter : Gal(reciprocity.extension.field / K) →* ℂˣ
  faithful : Function.Injective galoisCharacter
  factorization : χ = galoisCharacter.comp reciprocity.artin
  continuous_character : Continuous χ

/- A faithful character does not enlarge the kernel of the reciprocity map. -/
theorem chapter06_finite_character_realization_kernel
    {K Ks C : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] [TopologicalSpace C] {χ : C →* ℂˣ}
    (R : Chapter06FiniteCharacterRealization K Ks C χ) :
    χ.ker = R.reciprocity.artin.ker := by
  sorry

/- Finite character duality already identifies the intersection of all lifted
   quotient-character kernels with H.  Character realizations are used later
   to construct the corresponding compositum, not to prove this group lemma. -/
theorem chapter06_character_realizations_recover_open_subgroup
    {C : Type*}
    [CommGroup C] [TopologicalSpace C]
    (H : Chapter06OpenFiniteIndexSubgroup C) :
    ⨅ χ ∈ chapter06LiftedQuotientCharacters H, χ.ker = H.subgroup := by
  rw [← chapter06_open_subgroup_is_character_kernel_intersection H]

/- The compositum argument only needs the finite reciprocity witness for the
compositum and the equality of its Artin kernel with the character
intersection. -/
theorem chapter06_compositum_norm_subgroup_is_the_starting_subgroup
    {K Ks C : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [CommGroup C] [TopologicalSpace C]
    (H : Chapter06OpenFiniteIndexSubgroup C)
    (R :
      Chapter06FiniteReciprocityWitness K Ks C)
    (hkernel :
      R.artin.ker =
        ⨅ χ ∈ chapter06LiftedQuotientCharacters H, χ.ker) :
    chapter06NormSubgroup R.extension.normMap = H.subgroup := by
  rw [← R.kernel_eq_norm, hkernel]
  exact chapter06_lifted_quotient_character_kernels_inf H

end

end LastLib.Book06GlobalClassFieldTheory.Chapter06
