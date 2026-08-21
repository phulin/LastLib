import LastLib.Book03RamificationTheory.Chapter01.Section02InertiaRevisited
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section05MonogenicityAndResidueGenerators

namespace LastLib.Book03RamificationTheory.Chapter01

noncomputable section

open scoped BigOperators WithZero

/-! ## 1.3. The first infinitesimal action -/

/-- A ratio witness for the action on a chosen uniformizer. -/
structure Chapter01UniformizerRatioWitness
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (π : A)
    (I : Subgroup (chapter01DecompositionGroup K A)) where
  ratio : I → Aˣ
  relation : ∀ σ : I,
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ValuationRingAction
        K A (σ : chapter01DecompositionGroup K A) π =
      (ratio σ : A) * π

/-- The explicit uniformizer-ratio existence interface. -/
theorem chapter01_uniformizer_ratio_exists_for_valuation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π)
    (σ : chapter01InertiaGroup K vL.valuationSubring) :
    ∃ c : vL.valuationSubringˣ,
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ValuationRingAction
          K vL.valuationSubring
          (σ : chapter01DecompositionGroup K vL.valuationSubring) π =
        (c : vL.valuationSubring) * π := by
  sorry

/-- A chosen unit ratio `σ(π)/π` for an inertial automorphism. -/
noncomputable def chapter01UniformizerRatio
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π)
    (σ : chapter01InertiaGroup K vL.valuationSubring) :
    vL.valuationSubringˣ :=
  Classical.choose (chapter01_uniformizer_ratio_exists_for_valuation vL π hπ σ)

@[simp] theorem chapter01UniformizerRatio_relation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π)
    (σ : chapter01InertiaGroup K vL.valuationSubring) :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ValuationRingAction
        K vL.valuationSubring
        (σ : chapter01DecompositionGroup K vL.valuationSubring) π =
      (chapter01UniformizerRatio vL π hπ σ : vL.valuationSubring) * π := by
  exact Classical.choose_spec
    (chapter01_uniformizer_ratio_exists_for_valuation vL π hπ σ)

/-- The residue of the uniformizer ratio. -/
def chapter01UniformizerRatioResidue
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π) :
    chapter01InertiaGroup K vL.valuationSubring →
      (chapter01ResidueField vL)ˣ :=
  fun σ => Units.map (IsLocalRing.residue vL.valuationSubring).toMonoidHom
    (chapter01UniformizerRatio vL π hπ σ)

/-- The tame character on the first infinitesimal layer. -/
noncomputable def chapter01TameCharacter
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π) :
    chapter01InertiaGroup K vL.valuationSubring →*
      (chapter01ResidueField vL)ˣ := by
  refine
    { toFun := chapter01UniformizerRatioResidue vL π hπ
      map_one' := ?_
      map_mul' := ?_ }
  · sorry
  · sorry

@[simp] theorem chapter01TameCharacter_apply
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π)
    (σ : chapter01InertiaGroup K vL.valuationSubring) :
    chapter01TameCharacter vL π hπ σ =
      Units.map (IsLocalRing.residue vL.valuationSubring).toMonoidHom
        (chapter01UniformizerRatio vL π hπ σ) := by
  rfl

/-- Changing a uniformizer changes its ratio by `σ(u)/u`; its residue is one. -/
theorem chapter01_uniformizer_change_ratio_residue
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π π' : vL.valuationSubring)
    (hπ : chapter01IsUniformizer vL π)
    (hπ' : chapter01IsUniformizer vL π')
    (u : vL.valuationSubringˣ)
    (hchange : π' = (u : vL.valuationSubring) * π)
    (σ : chapter01InertiaGroup K vL.valuationSubring) :
    chapter01TameCharacter vL π' hπ' σ =
      chapter01TameCharacter vL π hπ σ := by
  sorry

/-- The tame character is intrinsic to the extension, not to the chosen
uniformizer. -/
theorem chapter01_tame_character_is_intrinsic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π π' : vL.valuationSubring)
    (hπ : chapter01IsUniformizer vL π)
    (hπ' : chapter01IsUniformizer vL π') :
    chapter01TameCharacter (K := K) vL π hπ =
      chapter01TameCharacter (K := K) vL π' hπ' := by
  sorry

/-
The next structure records the integral-model part of the source's maximal
unramified-stage argument.  `A₀` is the chosen integral model of the
unramified field, while `k` and `l` are its displayed residue fields.
-/
-- SOURCE_ISSUE: The source says residue separability alone gives the
-- monogenic presentation `B = 𝓞_{K₀}[π_L]`.  Immediate/separable defect
-- extensions over imperfect residue fields show that a defectless (for
-- example perfect-residue) hypothesis is also needed for this conclusion.
-- LOCAL_DEPENDENCY_GUESS: the preceding chapter's maximal-unramified package
-- supplies the identification of `A₀` with `𝓞_{K₀}` and of `B` with the
-- integral closure in `L`; this chapter only needs the monogenic interface.
structure Chapter01MaximalUnramifiedMonogenicPresentation
    (A₀ B k l : Type*) [CommRing A₀] [CommRing B]
    [Field k] [Field l] [Algebra A₀ B] [Algebra k l]
    (π : B) where
  residue_separable : Algebra.IsSeparable k l
  integral_generator :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08MonogenicBy A₀ B π

@[simp] theorem chapter01_maximal_unramified_monogenic_ring_eq_adjoin
    {A₀ B k l : Type*} [CommRing A₀] [CommRing B]
    [Field k] [Field l] [Algebra A₀ B] [Algebra k l]
    (π : B)
    (_P : Chapter01MaximalUnramifiedMonogenicPresentation A₀ B k l π) :
    Algebra.adjoin A₀ ({π} : Set B) = ⊤ := by
  exact _P.integral_generator.2

/-- The canonical maximal-unramified stage package, specialized to the
defectless perfect-residue interface used by the preceding book. -/
theorem chapter01_separable_residue_has_clean_unramified_stage
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B]
    [Module.IsTorsionFree A B] [FaithfulSMul A B]
    [IsIntegralClosure B A L]
    [Module.Finite
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09BaseResidueField A)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09ExtensionResidueField B)]
    [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Chapter09FiniteLocalExtension
      A B K L]
    [PerfectField
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09BaseResidueField A)]
    (hresidue_separable : Algebra.IsSeparable
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09BaseResidueField A)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09ExtensionResidueField B)) :
    Nonempty
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Chapter09Corollary92Data A B K L) := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09_corollary_92
      A B K L hresidue_separable

/-- The congruence modulo `𝔪²` which defines the first positive lower group. -/
def chapter01FirstInfinitesimalCongruence
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) (π : vL.valuationSubring)
    (σ : chapter01InertiaGroup K vL.valuationSubring) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ValuationRingAction
      K vL.valuationSubring
      (σ : chapter01DecompositionGroup K vL.valuationSubring) π - π ∈
    (IsLocalRing.maximalIdeal vL.valuationSubring) ^ 2

/-- The character kernel is the first infinitesimal congruence kernel. -/
theorem chapter01_tame_character_mem_kernel_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π)
    (σ : chapter01InertiaGroup K vL.valuationSubring) :
    σ ∈ (chapter01TameCharacter vL π hπ).ker ↔
      chapter01FirstInfinitesimalCongruence vL π σ := by
  sorry

/-- The zero lower group is inertia. -/
theorem chapter01_lower_ramification_group_zero_eq_inertia
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    chapter01LowerRamificationGroup K A 0 = chapter01InertiaGroup K A := by
  change
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup K A 1 = _
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FirstRamificationGroup_eq_inertia A

/-- Lower ramification groups descend with the index. -/
theorem chapter01_lower_ramification_group_succ_le
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (i : ℕ) :
    chapter01LowerRamificationGroup K A (i + 1) ≤
      chapter01LowerRamificationGroup K A i := by
  change
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
        K A (i + 1 + 1) ≤
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
        K A (i + 1)
  simpa [Nat.add_assoc] using
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup_succ_le
      A (i + 1))

/-- Under residue separability, the character kernel is wild inertia. -/
theorem chapter01_tame_character_kernel_eq_wild_inertia
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (k : Type*) [Field k]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    [Algebra k (chapter01ResidueField vL)]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π)
    (hresidue_separable : Algebra.IsSeparable k (chapter01ResidueField vL)) :
    (chapter01TameCharacter vL π hπ).ker =
      (chapter01WildInertiaGroup K vL.valuationSubring).comap
        (chapter01InertiaGroup K vL.valuationSubring).subtype := by
  sorry

/-- The cotangent line is the finite-precision object on which the first
infinitesimal scalar action is read. -/
def chapter01FirstInfinitesimalScalarAction
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π) :
    chapter01InertiaGroup K vL.valuationSubring →
      (chapter01ResidueField vL →+ chapter01ResidueField vL) :=
  fun σ =>
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10ResiduePowerScaling
      vL.valuationSubring
      (chapter01UniformizerRatio vL π hπ σ) 1

/-- In uniformizer coordinates, the first infinitesimal action is multiplication
by the residue of the ratio. -/
theorem chapter01_first_infinitesimal_scalar_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : Valuation L ℤᵐ⁰) [IsDiscreteValuationRing vL.valuationSubring]
    (π : vL.valuationSubring) (hπ : chapter01IsUniformizer vL π)
    (σ : chapter01InertiaGroup K vL.valuationSubring)
    (a : chapter01ResidueField vL) :
    chapter01FirstInfinitesimalScalarAction vL π hπ σ a =
      (chapter01TameCharacter vL π hπ σ : chapter01ResidueField vL) * a := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter01
