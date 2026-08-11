import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section01WhyUnitsNeedTheirOwnFiltration

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing

/-! ## 10.2. The first quotient -/

/-- Reduction on the ring-of-integers unit group is surjective. -/
theorem chapter10_unit_reduction_surjective
    {L : Type*} [Field L] (A : ValuationSubring L) :
    Function.Surjective (chapter10UnitReduction A) := by
  exact IsLocalRing.surjective_units_map_of_local_ringHom
    (IsLocalRing.residue A) IsLocalRing.residue_surjective
    (inferInstanceAs (IsLocalHom (IsLocalRing.residue A)))

/-- The kernel of unit reduction is exactly the first principal-unit group. -/
theorem chapter10_unit_reduction_kernel
    {L : Type*} [Field L] (A : ValuationSubring L) :
    (chapter10UnitReduction A).ker = chapter10UnitFiltration A 1 := by
  classical
  ext u
  constructor
  · intro hu
    change chapter10UnitReduction A u = 1 at hu
    have hval : IsLocalRing.residue A (u : A) = 1 := by
      have h := congrArg Units.val hu
      simpa [chapter10UnitReduction] using h
    change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ 1
    rw [pow_one]
    rw [← IsLocalRing.residue_eq_zero_iff]
    simpa [map_sub] using sub_eq_zero.mpr hval
  · intro hu
    change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ 1 at hu
    rw [pow_one] at hu
    have hzero : IsLocalRing.residue A (u : A) - 1 = 0 := by
      have hz : IsLocalRing.residue A ((u : A) - 1) = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).2 hu
      simpa [map_sub] using hz
    have hval : IsLocalRing.residue A (u : A) = 1 := sub_eq_zero.mp hzero
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    change IsLocalRing.residue A (u : A) = 1
    exact hval

/-- The first unit quotient is the multiplicative group of the residue field. -/
theorem chapter10_first_unit_quotient_equiv_residue_units
    {L : Type*} [Field L] (A : ValuationSubring L) :
    Nonempty
      ((Chapter10UnitRingQuotient A 1) ≃*
        (Chapter10ResidueField A)ˣ) := by
  change Nonempty
    ((Aˣ ⧸ chapter10UnitFiltration A 1) ≃* (Chapter10ResidueField A)ˣ)
  rw [← chapter10_unit_reduction_kernel A]
  exact ⟨QuotientGroup.quotientKerEquivOfSurjective
    (chapter10UnitReduction A) (chapter10_unit_reduction_surjective A)⟩

/-- Units whose order divides a specified exponent. -/
def chapter10RootOfUnitySubgroup
    {L : Type*} [Field L] (A : ValuationSubring L) (m : ℕ) : Subgroup Aˣ where
  carrier := {u | u ^ m = 1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change (u * v) ^ m = 1 at *
    rw [mul_pow, hu, hv, one_mul]
  inv_mem' := by
    intro u hu
    change (u⁻¹) ^ m = 1 at *
    rw [inv_pow, hu]
    simp

/-- In a finite residue field, every nonzero root of the Teichmüller
polynomial is simple. -/
theorem chapter10_teichmuller_residue_roots_are_simple
    {L : Type*} [Field L] (A : ValuationSubring L)
    [Fintype (Chapter10ResidueField A)]
    (a : Chapter10ResidueField A)
    (ha : a ≠ 0)
    (_hroot : a ^ (Fintype.card (Chapter10ResidueField A) - 1) = 1) :
    (Polynomial.derivative
      (Polynomial.X ^ (Fintype.card (Chapter10ResidueField A) - 1) -
        Polynomial.C 1)).eval a ≠ 0 := by
  have hcard : 1 ≤ Fintype.card (Chapter10ResidueField A) :=
    Fintype.card_pos
  have hcoef :
      ((Fintype.card (Chapter10ResidueField A) - 1 : ℕ) :
        Chapter10ResidueField A) = -1 := by
    rw [Nat.cast_sub hcard, FiniteField.cast_card_eq_zero]
    simp
  simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
    Polynomial.derivative_C, sub_zero, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, hcoef]
  exact mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero _ ha)

/-- A multiplicative residue section with the simple-root lifting property. -/
def Chapter10TeichmullerSectionSpec
    {L : Type*} [Field L] (A : ValuationSubring L) (q : ℕ) : Prop :=
  ∃ s : (Chapter10ResidueField A)ˣ →* Aˣ,
    (∀ a, chapter10UnitReduction A (s a) = a) ∧
      (∀ a, (s a) ^ (q - 1) = 1) ∧
      (∀ a u, chapter10UnitReduction A u = a →
        u ^ (q - 1) = 1 → u = s a)

/-- Existence and uniqueness of Teichmüller lifts over a finite residue field. -/
theorem chapter10_teichmuller_section_exists_unique
    {L : Type*} [Field L] (A : ValuationSubring L)
    [Fintype (Chapter10ResidueField A)]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    ∃! s : (Chapter10ResidueField A)ˣ →* Aˣ,
      (∀ a, chapter10UnitReduction A (s a) = a) ∧
        (∀ a, (s a) ^ (Fintype.card (Chapter10ResidueField A) - 1) = 1) ∧
        (∀ a u, chapter10UnitReduction A u = a →
          u ^ (Fintype.card (Chapter10ResidueField A) - 1) = 1 → u = s a) := by
  sorry

/-- The Teichmüller lift extends by the convention `[0] = 0`. -/
theorem chapter10_teichmuller_zero_extension
    {L : Type*} [Field L] (A : ValuationSubring L) (_q : ℕ)
    (s : (Chapter10ResidueField A)ˣ →* Aˣ)
    (_hs : ∀ a, chapter10UnitReduction A (s a) = a) :
    ∃ t : Chapter10ResidueField A → A,
      t 0 = 0 ∧
        ∀ a : (Chapter10ResidueField A)ˣ, t a = (s a : A) := by
  classical
  let t : Chapter10ResidueField A → A := fun a =>
    if h : a = 0 then 0 else (s (Units.mk0 a h) : A)
  refine ⟨t, ?_, ?_⟩
  · simp [t]
  · intro a
    simp [t, Units.ne_zero a]

/-- The finite-residue-field splitting of the unit group. -/
theorem chapter10_teichmuller_unit_splitting
    {L : Type*} [Field L] (A : ValuationSubring L)
    [Fintype (Chapter10ResidueField A)]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    Nonempty
      (Aˣ ≃*
        (chapter10RootOfUnitySubgroup A
            (Fintype.card (Chapter10ResidueField A) - 1) ×
          chapter10UnitFiltration A 1)) := by
  sorry

/-- A canonical multiplicative residue section is an additional structure. -/
def Chapter10ResidueUnitSection
    {L : Type*} [Field L] (A : ValuationSubring L) : Prop :=
  ∃ s : (Chapter10ResidueField A)ˣ →* Aˣ,
    ∀ a, chapter10UnitReduction A (s a) = a

/-- Not every residue-unit surjection is supplied with a multiplicative section. -/
theorem chapter10_arbitrary_residue_fields_need_not_split_canonically :
    ¬ (∀ (L : Type) [Field L] (A : ValuationSubring L),
      Chapter10ResidueUnitSection A) := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
