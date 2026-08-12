import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-! ## 8.1 The three governing integrals -/

variable {K : Type*} [Field K] [NumberField K]

theorem chapter08_signature_formula :
    Chapter08RealPlaceCount K + 2 * Chapter08ComplexPlaceCount K = Chapter08Degree K := by
  sorry

theorem chapter08_signature_proportion_nonnegative (hK : 0 < Chapter08Degree K) :
    0 ≤ chapter08SignatureProportion K := by
  sorry

theorem chapter08_signature_proportion_le_one (hK : 0 < Chapter08Degree K) :
    chapter08SignatureProportion K ≤ 1 := by
  sorry

theorem chapter08_absolute_discriminant_pos (hK : 0 < Chapter08Degree K) :
    0 < Chapter08AbsoluteDiscriminant K := by
  sorry

theorem chapter08_archimedean_integrals_convergent
    {F : ℝ → ℝ} (hF : Chapter08BasicallyAdmissible F) :
    IntegrableOn (fun x : ℝ => F x * Real.cosh (x / 2)) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => (1 - F x) / (2 * Real.sinh (x / 2))) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => (1 - F x) / (2 * Real.cosh (x / 2))) (Ioi 0) := by
  sorry

theorem chapter08_root_discriminant_log_eq_div
    (hK : 0 < Chapter08Degree K) :
    Real.log (Chapter08RootDiscriminant K) =
      Real.log (Chapter08AbsoluteDiscriminant K) / (Chapter08Degree K : ℝ) := by
  sorry

/-!
Dropping the nonnegative zero and prime contributions in the earlier explicit formula gives the
book's equation (8.2).
-/
theorem chapter08_root_discriminant_lower_bound
    {F : ℝ → ℝ} (hK : 0 < Chapter08Degree K)
    (hformula : Chapter08ExplicitFormulaData K F)
    (hzero : 0 ≤ hformula.zeroContribution)
    (hprime : 0 ≤ hformula.primeContribution) :
    Real.log (Chapter08RootDiscriminant K) ≥
      Real.eulerMascheroniConstant + Real.log (8 * Real.pi) +
        chapter08SignatureProportion K * (Real.pi / 2) -
        4 * chapter08A F / (Chapter08Degree K : ℝ) -
        chapter08B F -
        chapter08SignatureProportion K * chapter08C F := by
  sorry

theorem chapter08_pole_cost_tends_to_zero (F : ℝ → ℝ) :
    Tendsto (fun n : ℕ => 4 * chapter08A F / (n : ℝ)) atTop (𝓝 0) := by
  sorry

theorem chapter08_signature_correction_nonnegative
    {F : ℝ → ℝ}
    (hα : 0 ≤ chapter08SignatureProportion K)
    (hC : chapter08C F ≤ Real.pi / 2) :
    0 ≤ chapter08SignatureProportion K * (Real.pi / 2 - chapter08C F) := by
  sorry

theorem chapter08_signature_correction_strictly_favorable
    (hα : 0 < chapter08SignatureProportion K) {F : ℝ → ℝ}
    (hC : chapter08C F < Real.pi / 2) :
    0 < chapter08SignatureProportion K * (Real.pi / 2 - chapter08C F) := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08
