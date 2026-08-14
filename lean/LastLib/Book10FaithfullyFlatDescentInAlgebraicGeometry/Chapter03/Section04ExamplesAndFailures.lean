import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.Flat.TorsionFree
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03.Dependencies
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03.Section02TheAmitsurEqualizer

/-!
# 3.4 Examples and failures
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03

open scoped TensorProduct

theorem chapter03_field_extension_flat
    (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Module.Flat K L := by
  infer_instance

theorem chapter03_field_extension_faithfullyFlat
    (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Module.FaithfullyFlat K L := by
  infer_instance

theorem chapter03_field_tensor_zero_iff
    {K L M : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] :
    Subsingleton (L ⊗[K] M) ↔ Subsingleton M := by
  have hflat : Module.FaithfullyFlat K L := chapter03_field_extension_faithfullyFlat K L
  exact @Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right K L
    inferInstance inferInstance inferInstance M inferInstance inferInstance hflat

theorem chapter03_galois_equalizer_eq_fixedPoints
    (G K L : Type*) [Field K] [Field L] [Algebra K L] [Group G]
    [MulSemiringAction G L] [IsGaloisGroup G K L] :
    chapter03AmitsurEqualizer K L = MulAction.fixedPoints G L := by
  rw [chapter03_amitsur_equalizer_eq_range]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    rw [MulAction.mem_fixedPoints]
    intro g
    simp
  · intro hx
    exact IsGaloisGroup.isInvariant.isInvariant x hx

theorem chapter03_galois_fixedPoints_eq_range_algebraMap
    (G K L : Type*) [Field K] [Field L] [Algebra K L] [Group G]
    [MulSemiringAction G L] [IsGaloisGroup G K L] :
    MulAction.fixedPoints G L = Set.range (algebraMap K L) := by
  rw [← chapter03_galois_equalizer_eq_fixedPoints G K L]
  exact chapter03_amitsur_equalizer_eq_range

theorem chapter03_complex_solution_of_x_squared_add_one :
    (Complex.I : ℂ) ^ 2 + 1 = 0 := by
  rw [Complex.I_sq]
  norm_num

theorem chapter03_real_no_solution_of_x_squared_add_one :
    ¬ ∃ x : ℝ, x ^ 2 + 1 = 0 := by
  rintro ⟨x, hx⟩
  nlinarith [sq_nonneg x]

theorem chapter03_complex_solution_not_conjugation_invariant :
    (starRingEnd ℂ) Complex.I ≠ Complex.I := by
  rw [Complex.conj_I]
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

theorem chapter03_localization_flat
    (A : Type*) [CommRing A] (f : A) :
    Module.Flat A (Localization.Away f) := by
  exact IsLocalization.flat (Localization.Away f) (Submonoid.powers f)

theorem chapter03_localization_amitsur_equalizer_eq_univ
    (A : Type*) [CommRing A] (f : A) :
    chapter03AmitsurEqualizer A (Localization.Away f) = Set.univ := by
  ext b
  constructor
  · intro hb
    trivial
  · intro hb
    change (1 : Localization.Away f) ⊗ₜ[A] b = b ⊗ₜ[A] (1 : Localization.Away f)
    calc
      (1 : Localization.Away f) ⊗ₜ[A] b =
          (1 : Localization.Away f) ⊗ₜ[A]
            (b • (1 : Localization.Away f)) := by simp
      _ = b • ((1 : Localization.Away f) ⊗ₜ[A] (1 : Localization.Away f)) := by
        rw [TensorProduct.tmul_smul]
      _ = b ⊗ₜ[A] (1 : Localization.Away f) := by
        exact (TensorProduct.tmul_eq_smul_one_tmul b (1 : Localization.Away f)).symm

abbrev chapter03NilpotentLocalization : Type := Localization.Away (0 : ZMod 2)

theorem chapter03_nilpotent_localization_subsingleton :
    Subsingleton chapter03NilpotentLocalization := by
  apply IsLocalization.subsingleton (M := Submonoid.powers (0 : ZMod 2))
  exact ⟨1, by simp⟩

theorem chapter03_nilpotent_localization_flat :
    Module.Flat (ZMod 2) chapter03NilpotentLocalization := by
  exact chapter03_localization_flat (ZMod 2) 0

theorem chapter03_nilpotent_localization_map_not_injective :
    ¬ Function.Injective (algebraMap (ZMod 2) chapter03NilpotentLocalization) := by
  intro hinj
  apply (show (0 : ZMod 2) ≠ 1 by decide)
  apply hinj
  exact @Subsingleton.elim chapter03NilpotentLocalization
    chapter03_nilpotent_localization_subsingleton _ _

theorem chapter03_nilpotent_localization_not_faithfullyFlat :
    ¬ Module.FaithfullyFlat (ZMod 2) chapter03NilpotentLocalization := by
  intro hff
  have hfaithful : FaithfulSMul (ZMod 2) chapter03NilpotentLocalization :=
    @Module.FaithfullyFlat.faithfulSMul (ZMod 2) chapter03NilpotentLocalization
      _ _ _ hff
  exact chapter03_nilpotent_localization_map_not_injective
    (@FaithfulSMul.algebraMap_injective (ZMod 2) chapter03NilpotentLocalization
      _ _ _ hfaithful)

def chapter03QuotientTestMap : ℤ →ₗ[ℤ] ℤ :=
  (LinearMap.lsmul ℤ ℤ) 2

theorem chapter03_quotient_test_map_injective :
    Function.Injective chapter03QuotientTestMap := by
  simpa [chapter03QuotientTestMap] using
    (LinearMap.lsmul_injective (R := ℤ) (M := ℤ) (x := (2 : ℤ)) (by norm_num))

theorem chapter03_quotient_baseChange_test_map_not_injective :
    ¬ Function.Injective (chapter03QuotientTestMap.lTensor (ZMod 2)) := by
  intro hinj
  have hxzero : (1 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ) = 0 := by
    apply hinj
    simp [chapter03QuotientTestMap]
    rw [show (2 : ℤ) = (2 : ℤ) • (1 : ℤ) by norm_num]
    rw [TensorProduct.tmul_smul]
    change (0 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ) = 0
    simp
  have hone : (1 : ZMod 2) = 0 := by
    have h := congrArg (TensorProduct.rid ℤ (ZMod 2)) hxzero
    simp at h
  exact one_ne_zero hone

def chapter03InjectiveNonflatRingHom : ℤ →+* TrivSqZeroExt ℤ (ZMod 2) :=
  TrivSqZeroExt.inlHom ℤ (ZMod 2)

theorem chapter03_injective_nonflat_ringHom_injective :
    Function.Injective chapter03InjectiveNonflatRingHom := by
  intro x y h
  change (TrivSqZeroExt.inl x : TrivSqZeroExt ℤ (ZMod 2)) = TrivSqZeroExt.inl y at h
  exact TrivSqZeroExt.inl_injective h

theorem chapter03_injective_nonflat_ringHom_target_not_flat :
    ¬ Module.Flat ℤ (TrivSqZeroExt ℤ (ZMod 2)) := by
  intro hflat
  have hzero : (2 : ℤ) • (TrivSqZeroExt.inr (1 : ZMod 2) : TrivSqZeroExt ℤ (ZMod 2)) = 0 := by
    rw [← TrivSqZeroExt.inr_smul]
    have htwo : (2 : ZMod 2) = 0 := by rfl
    simp [htwo]
  have htf : Module.IsTorsionFree ℤ (TrivSqZeroExt ℤ (ZMod 2)) :=
    @Module.Flat.isTorsionFree ℤ (TrivSqZeroExt ℤ (ZMod 2)) _ _ _ hflat
  rcases (Module.isTorsionFree_iff_smul_eq_zero.mp htf) 2
      (TrivSqZeroExt.inr (1 : ZMod 2)) hzero with h2 | hmem
  · norm_num at h2
  · exact one_ne_zero (TrivSqZeroExt.inr_injective hmem)

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03
