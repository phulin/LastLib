import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Section03PrimeAndDiscriminantTerms

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06

noncomputable section

open MeasureTheory Set
open scoped BigOperators

/-! ### 6.4. Gamma and pole terms -/

theorem chapter06_gamma_arguments_positive_on_right_line
    {c t : ℝ} (hc : 1 < c) :
    0 < (chapter06VerticalLinePoint c t).re ∧
      0 < (chapter06VerticalLinePoint c t / 2).re := by
  sorry

theorem chapter06_digamma_integral_applicable_on_right_line
    {c t : ℝ} (hc : 1 < c) :
    0 < (chapter06VerticalLinePoint c t).re ∧
      0 < (chapter06VerticalLinePoint c t / 2).re := by
  exact chapter06_gamma_arguments_positive_on_right_line hc

def chapter06DigammaIntegralIntegrand (z : ℂ) (x : ℝ) : ℂ :=
  (((Real.exp (-x) : ℝ) : ℂ) - Complex.exp (-(z * (x : ℂ)))) /
    (1 - (Real.exp (-x) : ℂ))

def chapter06DigammaSeriesTerm (z : ℂ) (k : ℕ) : ℂ :=
  (1 / ((k + 1 : ℕ) : ℂ)) - 1 / ((k : ℂ) + z)

theorem chapter06_digamma_eq_gamma_log_derivative (z : ℂ) :
    Complex.digamma z = chapter06LogDerivative Complex.Gamma z := by
  rfl

theorem chapter06_digamma_series_representation
    {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z =
      (-Real.eulerMascheroniConstant : ℂ) +
        ∑' k : ℕ, chapter06DigammaSeriesTerm z k := by
  sorry

theorem chapter06_digamma_series_absolutely_summable
    {z : ℂ} (hz : 0 < z.re) :
    Summable (fun k : ℕ => ‖chapter06DigammaSeriesTerm z k‖) := by
  sorry

theorem chapter06_digamma_integral_representation
    {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z =
      (-Real.eulerMascheroniConstant : ℂ) +
        ∫ x : ℝ in Ioi 0, chapter06DigammaIntegralIntegrand z x := by
  sorry

theorem chapter06_digamma_integrand_integrable
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (chapter06DigammaIntegralIntegrand z) (Ioi 0) := by
  sorry

theorem chapter06_real_place_contribution_formula
    (F : ℝ → ℝ) :
    chapter06RealPlaceContribution F =
      Real.eulerMascheroniConstant + Real.log (8 * Real.pi) + Real.pi / 2 -
        (∫ x : ℝ in Ioi 0, (1 - F x) / (2 * Real.sinh (x / 2))) -
        (∫ x : ℝ in Ioi 0, (1 - F x) / (2 * Real.cosh (x / 2))) := by
  rfl

theorem chapter06_complex_place_contribution_formula
    (F : ℝ → ℝ) :
    chapter06ComplexPlaceContribution F =
      2 * (Real.eulerMascheroniConstant + Real.log (8 * Real.pi)) -
        2 * ∫ x : ℝ in Ioi 0, (1 - F x) / (2 * Real.sinh (x / 2)) := by
  rfl

theorem chapter06_gamma_place_contributions_sum
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) :
    (chapter06RealPlaces K : ℝ) * chapter06RealPlaceContribution F +
        (chapter06ComplexPlaces K : ℝ) * chapter06ComplexPlaceContribution F =
      (chapter06Degree K : ℝ) * (Real.eulerMascheroniConstant + Real.log (8 * Real.pi)) +
        (chapter06RealPlaces K : ℝ) * (Real.pi / 2) -
        (chapter06Degree K : ℝ) * chapter06B F -
        (chapter06RealPlaces K : ℝ) * chapter06C F := by
  sorry

theorem chapter06_integral_two_cosh_half :
    (∫ x : ℝ in Ioi 0, 1 / (2 * Real.cosh (x / 2))) = Real.pi / 2 := by
  sorry

theorem chapter06_phi_at_zero_and_one
    {F : ℝ → ℝ} (hF : Chapter06BasicallyAdmissible F) :
    chapter06Phi F 0 =
        (2 * chapter06A F : ℂ) ∧
      chapter06Phi F 1 = (2 * chapter06A F : ℂ) := by
  sorry

def chapter06PoleFactorTransformContribution (F : ℝ → ℝ) : ℝ :=
  -(chapter06Phi F 0 + chapter06Phi F 1).re

theorem chapter06_pole_factor_transform_contribution
    {F : ℝ → ℝ} (hF : Chapter06BasicallyAdmissible F) :
    chapter06PoleFactorTransformContribution F = -4 * chapter06A F := by
  sorry

theorem chapter06_pole_terms_enter_with_negative_sign
    {F : ℝ → ℝ} (hF : Chapter06BasicallyAdmissible F) :
    chapter06PoleFactorTransformContribution F ≤ 0 := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06
