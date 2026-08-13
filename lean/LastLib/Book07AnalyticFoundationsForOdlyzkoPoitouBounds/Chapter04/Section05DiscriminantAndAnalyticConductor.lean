import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.Section04PolesZerosAndGrowth

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04

noncomputable section

open NumberField

/-! ### 4.5. Discriminant and analytic conductor -/

/-- The finite conductor in the completed Dedekind-zeta expression. -/
noncomputable abbrev chapter04FiniteConductor
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  chapter04AbsoluteDiscriminant K

/-- Analytic conductor with an arbitrary positive fixed height offset. -/
noncomputable def chapter04AnalyticConductorWithOffset
    (K : Type*) [Field K] [NumberField K]
    (c t : ℝ) : ℝ :=
  chapter04FiniteConductor K * Real.rpow (|t| + c) (chapter04Degree K : ℝ)

/-- The convenient offset-three analytic conductor used in the source. -/
noncomputable def chapter04AnalyticConductor
    (K : Type*) [Field K] [NumberField K] (t : ℝ) : ℝ :=
  chapter04AnalyticConductorWithOffset K 3 t

theorem chapter04_finite_conductor_eq_discriminant
    (K : Type*) [Field K] [NumberField K] :
    chapter04FiniteConductor K = chapter04AbsoluteDiscriminant K := by
  rfl

theorem chapter04_analytic_conductor_eq_displayed
    (K : Type*) [Field K] [NumberField K] (t : ℝ) :
    chapter04AnalyticConductor K t =
      chapter04AbsoluteDiscriminant K *
        Real.rpow (|t| + 3) (chapter04Degree K : ℝ) := by
  rfl

theorem chapter04_analytic_conductor_pos
    (K : Type*) [Field K] [NumberField K] (t : ℝ) :
    0 < chapter04AnalyticConductor K t := by
  sorry

theorem chapter04_analytic_conductor_with_offset_pos
    (K : Type*) [Field K] [NumberField K]
    {c t : ℝ} (hc : 0 < c) :
    0 < chapter04AnalyticConductorWithOffset K c t := by
  sorry

theorem chapter04_log_analytic_conductor_eq
    (K : Type*) [Field K] [NumberField K] (t : ℝ) :
    Real.log (chapter04AnalyticConductor K t) =
      Real.log (chapter04AbsoluteDiscriminant K) +
        (chapter04Degree K : ℝ) * Real.log (|t| + 3) := by
  sorry

theorem chapter04_log_analytic_conductor_with_offset_eq
    (K : Type*) [Field K] [NumberField K]
    {c t : ℝ} (hc : 0 < c) :
    Real.log (chapter04AnalyticConductorWithOffset K c t) =
      Real.log (chapter04AbsoluteDiscriminant K) +
        (chapter04Degree K : ℝ) * Real.log (|t| + c) := by
  sorry

theorem chapter04_zero_counting_unit_band_bound_log_analytic_conductor
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ((chapter04ZeroCounting K (T + 1) - chapter04ZeroCounting K T : ℕ) : ℝ) ≤
        C * Real.log (chapter04AnalyticConductor K T) := by
  sorry

theorem chapter04_analytic_conductor_keeps_degree_and_discriminant_exponents
    (K : Type*) [Field K] [NumberField K] {c t : ℝ} :
    chapter04AnalyticConductorWithOffset K c t =
      chapter04AbsoluteDiscriminant K *
        Real.rpow (|t| + c) (chapter04Degree K : ℝ) := by
  rfl

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04
