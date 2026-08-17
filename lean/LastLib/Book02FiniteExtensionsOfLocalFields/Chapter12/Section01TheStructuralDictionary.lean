import Mathlib.Analysis.Normed.Field.Krasner
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section06FiniteExtensionsOfCompleteFields

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12

noncomputable section

/-! ## 12.1. Why proximity can force field containment -/

/-- A normed algebra over a normed field supplies the chosen normalization on
the base field. -/
theorem chapter12_norm_extension_agreement
    {K L : Type*} [NormedField K] [NormedField L] [NormedAlgebra K L] :
    ∀ x : K, ‖algebraMap K L x‖ = ‖x‖ := by
  intro x
  exact norm_algebraMap' L x

/--
Mathlib's `IsKrasner` is the established interface for the fixed norm on an
algebraic extension.  Completeness of the base and the ultrametric hypothesis
give this interface without requiring completeness of the algebraic
extension itself.
-/
theorem chapter12_complete_base_has_krasner_property
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [NormedField L] [NormedAlgebra K L]
    [Algebra.IsAlgebraic K L] : IsKrasner K L := by
  infer_instance

/-- A finite extension of a complete normed field is complete in its induced
normed-algebra topology.  This is the completeness input used when Hensel's
lemma is applied in a finite splitting field. -/
theorem chapter12_finite_extension_is_complete
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedField L] [NormedAlgebra K L] [FiniteDimensional K L] :
    CompleteSpace L := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_finite_extension_is_complete
    (K := K) (L := L)

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12
