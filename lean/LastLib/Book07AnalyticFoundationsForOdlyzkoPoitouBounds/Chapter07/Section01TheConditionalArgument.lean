import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07

noncomputable section

open MeasureTheory

/- Reuse Chapter 5's source-facing GRH predicate and add the origin
   integrability condition (5.1), which is part of basic admissibility in the
   book even though Chapter 5 exposes it as a separate predicate. -/
abbrev chapter07GRHAdmissible (f : Chapter07TestFunction) : Prop :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Chapter05GRHAdmissible f ∧
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05OriginCondition f

theorem chapter07_zeroTransform_on_critical_line
    (f : Chapter07TestFunction) (hf : Integrable f)
    (heven : chapter07Even f) (γ : ℝ) :
    chapter07ZeroTransform f ((1 / 2 : ℂ) + Complex.I * (γ : ℂ)) =
      chapter07FourierTransform f γ := by
  sorry

theorem chapter07_grh_zero_representation
    (Z : Chapter07ZeroSpectrum) (hgrh : chapter07GRH Z)
    {ρ : ℂ} (hρ : ρ ∈ Z.support) :
    ∃ γ : ℝ, ρ = (1 / 2 : ℂ) + Complex.I * (γ : ℂ) := by
  exact hgrh ρ hρ

theorem chapter07_grh_zero_summand_nonnegative
    (Z : Chapter07ZeroSpectrum) (f : Chapter07TestFunction)
    (hgrh : chapter07GRH Z) (hf : chapter07GRHAdmissible f)
    {ρ : ℂ} (hρ : ρ ∈ Z.support) :
    0 ≤ (chapter07ZeroTermSummand Z f ρ).re := by
  sorry

theorem chapter07_grh_zero_term_nonnegative
    (Z : Chapter07ZeroSpectrum) (f : Chapter07TestFunction)
    (hgrh : chapter07GRH Z) (hf : chapter07GRHAdmissible f)
    (hsum : chapter07ZeroTermConvergent Z f) :
    0 ≤ chapter07ZeroTerm Z f := by
  sorry

end
end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07
