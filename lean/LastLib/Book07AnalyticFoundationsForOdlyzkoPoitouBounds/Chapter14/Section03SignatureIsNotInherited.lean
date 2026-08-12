import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter14.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter14

noncomputable section

universe u

open NumberField

/-! ## 14.3. Signature is not inherited automatically -/

def chapter14AdjoinsImaginaryUnit
    (K L : Type*) [Field K] [Field L] [Algebra K L] (ι : L) : Prop :=
  ι ^ 2 = -1 ∧ Algebra.adjoin K ({ι} : Set L) = ⊤

theorem chapter14_adjoining_imaginary_unit_is_totally_complex
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (hK : IsTotallyReal K) (ι : L)
    (hι : chapter14AdjoinsImaginaryUnit K L ι) :
    IsTotallyComplex L := by
  sorry

theorem chapter14_adjoining_imaginary_unit_has_no_real_places
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (hK : IsTotallyReal K) (ι : L)
    (hι : chapter14AdjoinsImaginaryUnit K L ι) :
    chapter14RealPlaces L = 0 := by
  sorry

theorem chapter14_gaussian_field_is_totally_complex :
    IsTotallyComplex chapter14GaussianField := by
  sorry

theorem chapter14_gaussian_field_real_places :
    chapter14RealPlaces chapter14GaussianField = 0 := by
  sorry

theorem chapter14_gaussian_field_degree :
    chapter14Degree chapter14GaussianField = 2 := by
  sorry

theorem chapter14_gaussian_field_rootDiscriminant :
    chapter14RootDiscriminant chapter14GaussianField = 2 := by
  sorry

theorem chapter14_real_proportion_decreases_in_gaussian_extension :
    chapter14RealProportion ℚ = 1 ∧
      chapter14RealProportion chapter14GaussianField = 0 ∧
      chapter14RealProportion chapter14GaussianField <
        chapter14RealProportion ℚ := by
  sorry

theorem chapter14_uniform_signature_cap_of_modelwise_cap
    (S : Chapter14NumberFieldSequence.{u}) (U α : ℝ) (N : ℕ)
    (hcap : chapter14ModelwiseDegreeCap.{u} U α N)
    (hceil : chapter14UniformRootDiscriminantCeiling S U)
    (hα : chapter14UniformRealProportionLowerBound S α) :
    chapter14UniformDegreeCap S N := by
  intro m
  simpa [chapter14SequenceDegree, chapter14SequenceRootDiscriminant,
    chapter14SequenceRealProportion] using
    hcap (S.field m) (hceil m) (hα m)

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter14
