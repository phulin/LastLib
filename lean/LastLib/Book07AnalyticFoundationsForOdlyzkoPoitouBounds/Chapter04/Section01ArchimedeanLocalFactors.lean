import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04

noncomputable section

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03

/-! ### 4.1. Archimedean local factors -/

/-
The source states these Mellin identities in the convergence half-plane
`0 < Re(s)`.  The definitions in `Dependencies` use the standard
zero-measure convention at the singular point, while the theorem hypotheses
retain the required domain explicitly.
-/
theorem chapter04_real_gaussian_mellin_eq_gamma
    {s : ℂ} (hs : 0 < s.re) :
    chapter04RealGaussianMellin s = chapter04GammaReal s := by
  sorry

theorem chapter04_complex_gaussian_mellin_eq_gamma
    {s : ℂ} (hs : 0 < s.re) :
    chapter04ComplexGaussianMellin s = chapter04GammaComplex s := by
  sorry

theorem chapter04_gamma_real_eq_mathlib
    (s : ℂ) :
    chapter04GammaReal s = Complex.Gammaℝ s := by
  sorry

/-!
Mathlib's Deligne normalization is `Gammaℂ s = 2 * (2π)^(-s) Γ(s)`,
whereas the book fixes `Gamma_C(s) = (2π)^(-s) Γ(s)`.  The factor-two
compatibility is exposed rather than silently identifying the two symbols.
-/
theorem chapter04_gamma_complex_eq_half_mathlib
    (s : ℂ) :
    chapter04GammaComplex s = (2 : ℂ)⁻¹ * Complex.Gammaℂ s := by
  sorry

theorem chapter04_euler_completed_dedekind_zeta_eq_displayed
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter04EulerCompletedDedekindZeta K s =
      (chapter04AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
        chapter04GammaReal s ^ chapter04RealPlaces K *
          chapter04GammaComplex s ^ chapter04ComplexPlaces K *
            chapter03DedekindZeta K s := by
  simp [chapter04EulerCompletedDedekindZeta, chapter04ArchimedeanFactor, mul_assoc]

theorem chapter04_euler_completed_dedekind_zeta_uses_absolute_discriminant
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter04EulerCompletedDedekindZeta K s =
      (chapter02AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
        chapter04ArchimedeanFactor K s * chapter03DedekindZeta K s := by
  rfl

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04
