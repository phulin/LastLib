import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03.Dependencies

/-!
# 3.4 Examples and failures
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03

open scoped TensorProduct

theorem chapter03_field_extension_flat
    (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Module.Flat K L := by
  sorry

theorem chapter03_field_extension_faithfullyFlat
    (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Module.FaithfullyFlat K L := by
  sorry

theorem chapter03_field_tensor_zero_iff
    {K L M : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] :
    Subsingleton (L ⊗[K] M) ↔ Subsingleton M := by
  letI : Module.FaithfullyFlat K L := chapter03_field_extension_faithfullyFlat K L
  exact Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right K L

theorem chapter03_galois_equalizer_eq_fixedPoints
    (G K L : Type*) [Field K] [Field L] [Algebra K L] [Group G]
    [MulSemiringAction G L] [IsGaloisGroup G K L] :
    chapter03AmitsurEqualizer K L = MulAction.fixedPoints G L := by
  sorry

theorem chapter03_galois_fixedPoints_eq_range_algebraMap
    (G K L : Type*) [Field K] [Field L] [Algebra K L] [Group G]
    [MulSemiringAction G L] [IsGaloisGroup G K L] :
    MulAction.fixedPoints G L = Set.range (algebraMap K L) := by
  sorry

theorem chapter03_complex_solution_of_x_squared_add_one :
    (Complex.I : ℂ) ^ 2 + 1 = 0 := by
  sorry

theorem chapter03_real_no_solution_of_x_squared_add_one :
    ¬ ∃ x : ℝ, x ^ 2 + 1 = 0 := by
  sorry

theorem chapter03_complex_solution_not_conjugation_invariant :
    Complex.conj Complex.I ≠ Complex.I := by
  sorry

theorem chapter03_localization_flat
    (A : Type*) [CommRing A] (f : A) :
    Module.Flat A (Localization.Away f) := by
  exact IsLocalization.flat (Localization.Away f) (Submonoid.powers f)

theorem chapter03_localization_amitsur_equalizer_eq_univ
    (A : Type*) [CommRing A] (f : A) :
    chapter03AmitsurEqualizer A (Localization.Away f) = Set.univ := by
  sorry

abbrev chapter03NilpotentLocalization : Type := Localization.Away (0 : ZMod 2)

theorem chapter03_nilpotent_localization_subsingleton :
    Subsingleton chapter03NilpotentLocalization := by
  sorry

theorem chapter03_nilpotent_localization_flat :
    Module.Flat (ZMod 2) chapter03NilpotentLocalization := by
  exact chapter03_localization_flat (ZMod 2) 0

theorem chapter03_nilpotent_localization_map_not_injective :
    ¬ Function.Injective (algebraMap (ZMod 2) chapter03NilpotentLocalization) := by
  sorry

theorem chapter03_nilpotent_localization_not_faithfullyFlat :
    ¬ Module.FaithfullyFlat (ZMod 2) chapter03NilpotentLocalization := by
  sorry

def chapter03QuotientTestMap : ℤ →ₗ[ℤ] ℤ :=
  (LinearMap.lsmul ℤ ℤ) 2

theorem chapter03_quotient_test_map_injective :
    Function.Injective chapter03QuotientTestMap := by
  sorry

theorem chapter03_quotient_baseChange_test_map_not_injective :
    ¬ Function.Injective (chapter03QuotientTestMap.lTensor (ZMod 2)) := by
  sorry

def chapter03InjectiveNonflatRingHom : ℤ →+* TrivSqZeroExt ℤ (ZMod 2) :=
  TrivSqZeroExt.inlHom ℤ (ZMod 2)

theorem chapter03_injective_nonflat_ringHom_injective :
    Function.Injective chapter03InjectiveNonflatRingHom := by
  sorry

theorem chapter03_injective_nonflat_ringHom_target_not_flat :
    ¬ Module.Flat ℤ (TrivSqZeroExt ℤ (ZMod 2)) := by
  sorry

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03
