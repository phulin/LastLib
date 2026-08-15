import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07

noncomputable section

open MeasureTheory

/- Reuse Chapter 5's source-facing GRH predicate.  Its `basic` field already
   carries the origin integrability condition (5.1). -/
abbrev chapter07GRHAdmissible (f : Chapter07TestFunction) : Prop :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Chapter05GRHAdmissible f

theorem chapter07_zeroTransform_on_critical_line
    (f : Chapter07TestFunction) (hf : Integrable f)
    (heven : chapter07Even f) (γ : ℝ) :
    chapter07ZeroTransform f ((1 / 2 : ℂ) + Complex.I * (γ : ℂ)) =
      chapter07FourierTransform f γ := by
  simpa [chapter07ZeroTransform, chapter07FourierTransform,
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05BilateralLaplaceTransform,
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05LaplaceKernel,
    mul_comm, mul_left_comm, mul_assoc] using
    (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05_laplace_on_critical_line
      hf heven γ)

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
  obtain ⟨γ, rfl⟩ := chapter07_grh_zero_representation Z hgrh hρ
  have htransform :
    chapter07ZeroTransform f ((1 / 2 : ℂ) + Complex.I * (γ : ℂ)) =
        chapter07FourierTransform f γ :=
    chapter07_zeroTransform_on_critical_line f
      (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05_basically_admissible_integrable
        hf.basic)
      hf.basic.even γ
  have hnonnegative : 0 ≤ (chapter07FourierTransform f γ).re :=
    (hf.transformNonnegative γ).2
  dsimp [chapter07ZeroTermSummand]
  rw [htransform]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero]
  exact mul_nonneg (by positivity) hnonnegative

theorem chapter07_grh_zero_term_nonnegative
    (Z : Chapter07ZeroSpectrum) (f : Chapter07TestFunction)
    (hgrh : chapter07GRH Z) (hf : chapter07GRHAdmissible f)
    (hsum : chapter07ZeroTermConvergent Z f) :
    0 ≤ chapter07ZeroTerm Z f := by
  have hnonnegative : ∀ ρ : ℂ, 0 ≤ (chapter07ZeroTermSummand Z f ρ).re := by
    intro ρ
    by_cases hρ : ρ ∈ Z.support
    · exact chapter07_grh_zero_summand_nonnegative Z f hgrh hf hρ
    · have hm : Z.multiplicity ρ = 0 := by
        by_contra hm
        exact hρ ((Z.support_iff_multiplicity_ne_zero ρ).2 hm)
      simp [chapter07ZeroTermSummand, hm]
  rw [chapter07ZeroTerm, Complex.re_tsum hsum]
  exact tsum_nonneg hnonnegative

theorem chapter07_grh_canonical_zero_summand_nonnegative
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter07CanonicalZeroSpectrum K) (f : Chapter07TestFunction)
    (hgrh : chapter07CanonicalGRH K Z)
    (hf : LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Chapter05GRHAdmissible f)
    {ρ : ℂ} (hρ : ρ ∈ Z.support) :
    0 ≤
      (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06ZeroSummand
        Z f ρ).re := by
  obtain ⟨γ, hγ⟩ := hgrh ρ hρ
  have htransform :
      chapter07ZeroTransform f ((1 / 2 : ℂ) + Complex.I * (γ : ℂ)) =
        chapter07FourierTransform f γ :=
    chapter07_zeroTransform_on_critical_line f
      (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05_basically_admissible_integrable
        hf.basic)
      hf.basic.even γ
  rw [← chapter07_zeroTermSummand_of_chapter06 K Z f ρ]
  dsimp [chapter07ZeroTermSummand]
  rw [hγ, htransform]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero]
  exact mul_nonneg (by positivity) (hf.transformNonnegative γ).2

theorem chapter07_grh_canonical_zero_contribution_nonnegative
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter07CanonicalZeroSpectrum K) (f : Chapter07TestFunction)
    (hgrh : chapter07CanonicalGRH K Z)
    (hf : LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Chapter05GRHAdmissible f)
    (hsum : Summable (fun ρ : ℂ =>
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06ZeroSummand
        Z f ρ)) :
    0 ≤ LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06ZeroContribution
      Z f := by
  have hnonnegative : ∀ ρ : ℂ, 0 ≤
      (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06ZeroSummand
        Z f ρ).re := by
    intro ρ
    by_cases hρ : ρ ∈ Z.support
    · exact chapter07_grh_canonical_zero_summand_nonnegative K Z f hgrh hf hρ
    · have hm : Z.multiplicity ρ = 0 := by
        by_contra hm
        exact hρ ((Z.support_iff_multiplicity_ne_zero ρ).2 hm)
      simp [LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06ZeroSummand,
        hm]
  rw [LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06ZeroContribution,
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06SymmetricZeroSum,
    Complex.re_tsum hsum]
  exact tsum_nonneg hnonnegative

end
end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07
