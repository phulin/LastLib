import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03.Dependencies

/-!
# 3.2 The Amitsur equalizer
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03

open scoped TensorProduct

theorem chapter03_amitsur_unit_injective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
    Function.Injective (Algebra.linearMap A B) := by
  sorry

theorem chapter03_amitsur_exact
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
    Function.Exact (Algebra.linearMap A B) (chapter03AmitsurDifference A B) := by
  sorry

theorem chapter03_amitsur_equalizer_eq_range
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
    chapter03AmitsurEqualizer A B = Set.range (algebraMap A B) := by
  sorry

theorem chapter03_amitsur_equalizer_iff
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (b : B) :
    b ∈ chapter03AmitsurEqualizer A B ↔ ∃ a : A, algebraMap A B a = b := by
  rw [chapter03_amitsur_equalizer_eq_range]
  rfl

theorem chapter03_module_amitsur_augmentation_injective
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B] :
    Function.Injective (chapter03ModuleAmitsurAugmentation A B M) := by
  exact Module.FaithfullyFlat.tensorProduct_mk_injective M

theorem chapter03_module_amitsur_exact
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B] :
    Function.Exact (chapter03ModuleAmitsurAugmentation A B M)
      (chapter03ModuleAmitsurDifference A B M) := by
  sorry

theorem chapter03_module_amitsur_equalizer_eq_range
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B] :
    {x : B ⊗[A] M | chapter03AmitsurInvariant A B M x} =
      Set.range (chapter03ModuleAmitsurAugmentation A B M) := by
  sorry

theorem chapter03_amitsur_higher_complex_exact
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
    Chapter03AmitsurFaceFamilyMatchesLowDegree A B (chapter03AmitsurFace A B) ∧
      Chapter03AmitsurDifferentialSquaresToZero A B (chapter03AmitsurFace A B) ∧
      Chapter03AmitsurPositiveExact A B (chapter03AmitsurFace A B) := by
  sorry

theorem chapter03_module_amitsur_higher_complex_exact
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B] :
    Chapter03ModuleAmitsurDifferentialSquaresToZero A B M
        (chapter03ModuleAmitsurFace A B M) ∧
      Chapter03ModuleAmitsurPositiveExact A B M
        (chapter03ModuleAmitsurFace A B M) := by
  sorry

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03
