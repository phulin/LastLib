import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04

noncomputable section

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03

/-! ### 4.1. Archimedean local factors -/

/-
SOURCE_ISSUE: The displayed real and complex Mellin integrals are written
without a convergence domain, although their literal `dx / |x|` and
`dx dy / (π |z|²)` integrands are singular at the origin.  The minimal
correction is to state the identities for `0 < Re(s)`; the definitions in
`Dependencies` use the standard zero-measure convention at the singular
point.
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

theorem chapter04_completed_dedekind_zeta_eq_displayed
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter04CompletedDedekindZeta K s =
      (chapter04AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
        chapter04GammaReal s ^ chapter04RealPlaces K *
          chapter04GammaComplex s ^ chapter04ComplexPlaces K *
            chapter03DedekindZeta K s := by
  simp [chapter04CompletedDedekindZeta, chapter04ArchimedeanFactor, mul_assoc]

theorem chapter04_completed_dedekind_zeta_uses_absolute_discriminant
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter04CompletedDedekindZeta K s =
      (chapter02AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
        chapter04ArchimedeanFactor K s * chapter03DedekindZeta K s := by
  rfl

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04
