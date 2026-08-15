import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Section02ConstructionAndMaximality
import Mathlib.FieldTheory.Galois.Basic

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09

open scoped BigOperators Polynomial
open Ideal IsLocalRing Polynomial

noncomputable section

/-! ## Book 2, Chapter 9.3: the clean decomposition theorem -/

/-- The full data asserted by Corollary 9.2.  The first and second degree
factors are kept as `finrank`s so that the displayed equalities remain
meaningful at the interface level, while the two finite-dimensional fields
record the finiteness used by the degree interpretation. -/
structure Chapter09Corollary92Data
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Chapter09FiniteLocalExtension A B K L] where
  K₀ : IntermediateField K L
  finite_base : FiniteDimensional K K₀
  finite_remainder : FiniteDimensional K₀ L
  maximal : chapter09MaximalUnramifiedSubextension A B K L K₀
  unramified : chapter09UnramifiedIntermediate A B K L K₀
  remainder : Chapter09RemainderInvariantData A B K L K₀
  remainder_totally_ramified : remainder.residue_degree = 1
  base_degree : Module.finrank K K₀ =
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree A B
      (IsLocalRing.maximalIdeal B)
  remainder_degree : Module.finrank K₀ L =
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex A B
      (IsLocalRing.maximalIdeal B)

/- Corollary 9.2: separable residue extensions allocate all residue degree to
the unramified stage and all ramification index to the remainder. -/
theorem chapter09_corollary_92
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Chapter09FiniteLocalExtension A B K L]
    (hseparable : Algebra.IsSeparable (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)) :
    Nonempty (Chapter09Corollary92Data A B K L) := by
  sorry

/-- The two displayed degree identities of Corollary 9.2. -/
theorem chapter09_corollary_92_degree_formulas
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Chapter09FiniteLocalExtension A B K L]
    (d : Chapter09Corollary92Data A B K L) :
    Module.finrank K d.K₀ =
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree A B
          (IsLocalRing.maximalIdeal B) ∧
      Module.finrank d.K₀ L =
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex A B
          (IsLocalRing.maximalIdeal B) := by
  exact ⟨d.base_degree, d.remainder_degree⟩

/-- A finite field is perfect, giving the perfect-residue-field case of the
corollary without adding a characteristic-zero assumption. -/
theorem chapter09_finite_field_is_perfect (k : Type*) [Field k] [Finite k] :
    PerfectField k := by
  infer_instance

/-- Finite residue fields force the clean decomposition.  This covers the
usual finite-residue local fields, including the standard `p`-adic examples. -/
theorem chapter09_finite_residue_field_clean_decomposition
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Finite (chapter09BaseResidueField A)]
    [Chapter09FiniteLocalExtension A B K L] :
    Nonempty (Chapter09Corollary92Data A B K L) := by
  sorry

/-- A clean unramified-then-totally-ramified decomposition exists exactly for
separable residue extensions. -/
def chapter09CleanTwoStageDecomposition
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Chapter09FiniteLocalExtension A B K L] : Prop :=
  Nonempty (Chapter09Corollary92Data A B K L)

theorem chapter09_clean_two_stage_decomposition_iff_residue_separable
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Chapter09FiniteLocalExtension A B K L] :
    chapter09CleanTwoStageDecomposition A B K L ↔
      Algebra.IsSeparable (chapter09BaseResidueField A)
        (chapter09ExtensionResidueField B) := by
  sorry


/-! ### Galois and nongalois interpretations -/

/-- The fixed field of a subgroup of the finite Galois group, using Mathlib's
canonical `IntermediateField.fixedField`. -/
noncomputable def chapter09InertiaFixedField
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (I : Subgroup (L ≃ₐ[K] L)) : IntermediateField K L :=
  IntermediateField.fixedField I

/-- The residue action attached to a Galois local extension.  The action is
kept as explicit data because the abstract `A`/`B` package does not itself
choose a valuation-subring presentation for the reduction map. -/
structure Chapter09ResidueActionData
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Chapter09FiniteLocalExtension A B K L] [IsGalois K L] where
  /-- The residue action is the separable-residue case of the inertia
  exact sequence; this hypothesis is part of the data rather than an
  implicit premise of the action fields below. -/
  residue_separable : Algebra.IsSeparable (chapter09BaseResidueField A)
    (chapter09ExtensionResidueField B)
  action : (L ≃ₐ[K] L) →* RingAut (chapter09ExtensionResidueField B)
  fixes_base : ∀ σ : L ≃ₐ[K] L, ∀ x : chapter09BaseResidueField A,
    action σ (algebraMap (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B) x) =
      algebraMap (chapter09BaseResidueField A)
        (chapter09ExtensionResidueField B) x
  action_surjective_over_base :
    ∀ φ : RingAut (chapter09ExtensionResidueField B),
      (∀ x : chapter09BaseResidueField A,
        φ (algebraMap (chapter09BaseResidueField A)
          (chapter09ExtensionResidueField B) x) =
          algebraMap (chapter09BaseResidueField A)
            (chapter09ExtensionResidueField B) x) →
      ∃ σ : L ≃ₐ[K] L, action σ = φ
  /-- The residue action is induced by the action on the integral closure,
  rather than being an unrelated abstract monoid hom. -/
  action_compatibility :
    ∀ σ : L ≃ₐ[K] L, ∀ x : B,
      ∃ y : B,
        algebraMap B L y = σ (algebraMap B L x) ∧
          action σ (IsLocalRing.residue B x) = IsLocalRing.residue B y

/-- Data expressing the Galois identification `K₀ = L^I`.  The subgroup is
named as inertia by the field `inertia_order`; its fixed-field equality is the
precise part of the assertion used by this chapter. -/
structure Chapter09GaloisInertiaIdentification
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Chapter09FiniteLocalExtension A B K L]
    [IsGalois K L] (I : Subgroup (L ≃ₐ[K] L)) where
  K₀ : IntermediateField K L
  maximal : chapter09MaximalUnramifiedSubextension A B K L K₀
  fixed_field_eq : chapter09InertiaFixedField K L I = K₀
  residue_action : Chapter09ResidueActionData A B K L
  inertia_eq_kernel : I = MonoidHom.ker residue_action.action
  inertia_order : Nat.card I =
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex A B
      (IsLocalRing.maximalIdeal B)

/- The Galois case of the canonical subextension. -/
theorem chapter09_galois_inertia_fixed_field
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Chapter09FiniteLocalExtension A B K L] [IsGalois K L]
    (hseparable : Algebra.IsSeparable (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)) :
    ∃ I : Subgroup (L ≃ₐ[K] L),
      Nonempty (Chapter09GaloisInertiaIdentification A B K L I) := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09
