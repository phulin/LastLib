import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07.Section02TheStripPositiveKernel

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07

noncomputable section

open MeasureTheory

def chapter07FOfG (G : Chapter07TestFunction) : Chapter07TestFunction :=
  fun x => G x * chapter07SechHalf x

theorem chapter07FOfG_eq_div_cosh (G : Chapter07TestFunction) :
    chapter07FOfG G = fun x => G x / Real.cosh (x / 2) := by
  sorry

def chapter07UnconditionalAdmissible (F : Chapter07TestFunction) : Prop :=
  ∃ G : Chapter07TestFunction,
    F = chapter07FOfG G ∧ Integrable G ∧ chapter07Even G ∧
      chapter07PositiveType G

def chapter07PairedZeroContribution
    (G : Chapter07TestFunction) (β γ : ℝ) : ℝ :=
  2 * ∫ x : ℝ,
    G x * chapter07StripKernel (β - 1 / 2) x * Real.cos (γ * x)

theorem chapter07_paired_zero_contribution_formula
    (G : Chapter07TestFunction) (β γ : ℝ)
    (hG : Integrable G) (heven : chapter07Even G)
    (hβ : |β - 1 / 2| ≤ 1 / 2) :
    (chapter07ZeroTransform (chapter07FOfG G)
        ((β : ℂ) + Complex.I * (γ : ℂ)) +
      chapter07ZeroTransform (chapter07FOfG G)
        (chapter07ZeroPartner ((β : ℂ) + Complex.I * (γ : ℂ)))).re =
      chapter07PairedZeroContribution G β γ := by
  sorry

theorem chapter07_pair_kernel_positiveType_strict
    (G : Chapter07TestFunction) (a : ℝ)
    (hG : chapter07PositiveType G) (ha : |a| < 1 / 2) :
    chapter07PositiveType (fun x => G x * chapter07StripKernel a x) := by
  exact chapter07_positiveType_mul G (chapter07StripKernel a) hG
    (chapter07_stripKernel_positiveType a ha)

theorem chapter07_pair_kernel_positiveType_endpoint
    (G : Chapter07TestFunction) (a : ℝ)
    (hG : chapter07PositiveType G)
    (ha : a = (1 / 2 : ℝ) ∨ a = -(1 / 2 : ℝ)) :
    chapter07PositiveType (fun x => G x * chapter07StripKernel a x) := by
  sorry

theorem chapter07_paired_zero_contribution_nonnegative
    (G : Chapter07TestFunction) (β γ : ℝ)
    (hG_integrable : Integrable G) (hG_even : chapter07Even G)
    (hG_positive : chapter07PositiveType G)
    (hβ : |β - 1 / 2| ≤ 1 / 2) :
    0 ≤ chapter07PairedZeroContribution G β γ := by
  sorry

theorem chapter07_fixed_pair_central_line
    {ρ : ℂ} (hρ : ρ = chapter07ZeroPartner ρ) :
    ρ.re = 1 / 2 := by
  sorry

theorem chapter07_fixed_zero_contribution_nonnegative
    (G : Chapter07TestFunction) (γ : ℝ)
    (hG_integrable : Integrable G) (hG_even : chapter07Even G)
    (hG_positive : chapter07PositiveType G) :
    0 ≤
      (chapter07ZeroTransform (chapter07FOfG G)
        ((1 / 2 : ℂ) + Complex.I * (γ : ℂ))).re := by
  sorry

theorem chapter07_fixed_zero_contribution_is_half_paired
    (G : Chapter07TestFunction) (γ : ℝ)
    (hG_integrable : Integrable G) (hG_even : chapter07Even G) :
    (chapter07ZeroTransform (chapter07FOfG G)
        ((1 / 2 : ℂ) + Complex.I * (γ : ℂ))).re =
      chapter07PairedZeroContribution G (1 / 2 : ℝ) γ / 2 := by
  sorry

theorem chapter07_unconditional_zero_term_nonnegative
    (Z : Chapter07ZeroSpectrum) (G : Chapter07TestFunction)
    (hG_integrable : Integrable G) (hG_even : chapter07Even G)
    (hG_positive : chapter07PositiveType G)
    (hsum : chapter07ZeroTermConvergent Z (chapter07FOfG G)) :
    0 ≤ chapter07ZeroTerm Z (chapter07FOfG G) := by
  sorry

theorem chapter07_unconditional_zero_term_nonnegative_of_admissible
    (Z : Chapter07ZeroSpectrum) (F : Chapter07TestFunction)
    (hF : chapter07UnconditionalAdmissible F)
    (hsum : chapter07ZeroTermConvergent Z F) :
    0 ≤ chapter07ZeroTerm Z F := by
  sorry

end
end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07
