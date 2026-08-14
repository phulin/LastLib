import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

/-! ### 6.6. Normalization diagnostics -/

structure Chapter06NormalizationDiagnostics where
  primeTermSign : ℝ
  zeroTermSign : ℝ
  poleTermSign : ℝ
  extraRealPlaceConstant : ℝ

def chapter06NormalizationLedger : Chapter06NormalizationDiagnostics where
  primeTermSign := 1
  zeroTermSign := 1
  poleTermSign := -1
  extraRealPlaceConstant := Real.pi / 2

theorem chapter06_normalization_diagnostics :
    chapter06NormalizationLedger.primeTermSign = 1 ∧
      chapter06NormalizationLedger.zeroTermSign = 1 ∧
      chapter06NormalizationLedger.poleTermSign = -1 ∧
      chapter06NormalizationLedger.extraRealPlaceConstant = Real.pi / 2 := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

theorem chapter06_completion_constant_diagnostic :
    chapter06GammaConstant =
      Real.eulerMascheroniConstant + Real.log (8 * Real.pi) := by
  rfl

theorem chapter06_universal_expression_coefficient_diagnostic
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) :
    chapter06UniversalLowerBoundExpression K F =
      (chapter06Degree K : ℝ) * chapter06GammaConstant +
        (chapter06RealPlaces K : ℝ) * (Real.pi / 2) -
        4 * chapter06A F - (chapter06Degree K : ℝ) * chapter06B F -
        (chapter06RealPlaces K : ℝ) * chapter06C F := by
  rfl

structure Chapter06TriangularAsymptoticData where
  degree : ℕ → ℕ
  alpha : ℝ
  B : ℕ → ℝ
  C : ℕ → ℝ
  pole : ℕ → ℝ
  degree_tendsToInfinity : Tendsto (fun n => (degree n : ℝ)) atTop atTop
  B_tendsto : Tendsto B atTop (𝓝 (Real.log 2))
  C_tendsto : Tendsto C atTop (𝓝 (Real.pi / 2 - 1))
  pole_tendsto : Tendsto pole atTop (𝓝 0)

theorem chapter06_triangular_limiting_diagnostic
    (A : Chapter06TriangularAsymptoticData) :
    Tendsto (fun n =>
      chapter06AsymptoticExpression A.alpha (A.B n) (A.C n) (A.pole n)) atTop
      (𝓝 (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) + A.alpha)) := by
  have hconst : Tendsto (fun _ : ℕ =>
      chapter06GammaConstant + A.alpha * (Real.pi / 2)) atTop
      (𝓝 (chapter06GammaConstant + A.alpha * (Real.pi / 2))) :=
    tendsto_const_nhds
  have hpole : Tendsto (fun n => -A.pole n) atTop (𝓝 0) := by
    simpa using A.pole_tendsto.neg
  have hB : Tendsto (fun n => -A.B n) atTop
      (𝓝 (-Real.log 2)) := by
    simpa using A.B_tendsto.neg
  have hC : Tendsto (fun n => -A.alpha * A.C n) atTop
      (𝓝 (-A.alpha * (Real.pi / 2 - 1))) := by
    simpa using (A.C_tendsto.const_mul (-A.alpha))
  have hsum := hconst.add hpole |>.add hB |>.add hC
  have hlog : Real.log (8 * Real.pi) - Real.log 2 =
      Real.log (4 * Real.pi) := by
    rw [← Real.log_div (by positivity) (by norm_num)]
    congr 1
    ring
  convert hsum using 1
  · funext n
    simp [chapter06AsymptoticExpression]
    ring
  · congr 1
    rw [chapter06_completion_constant_diagnostic, ← hlog]
    ring

def chapter06AsymptoticExpressionWithoutB (alpha C pole : ℝ) : ℝ :=
  chapter06AsymptoticExpression alpha 0 C pole

def chapter06AsymptoticExpressionWithoutC (alpha B pole : ℝ) : ℝ :=
  chapter06AsymptoticExpression alpha B 0 pole

theorem chapter06_missing_B_loss_diagnostic
    (A : Chapter06TriangularAsymptoticData) :
    Tendsto (fun n =>
      chapter06AsymptoticExpressionWithoutB A.alpha (A.C n) (A.pole n)) atTop
      (𝓝 (Real.eulerMascheroniConstant + Real.log (8 * Real.pi) + A.alpha)) := by
  have hconst : Tendsto (fun _ : ℕ =>
      chapter06GammaConstant + A.alpha * (Real.pi / 2)) atTop
      (𝓝 (chapter06GammaConstant + A.alpha * (Real.pi / 2))) :=
    tendsto_const_nhds
  have hpole : Tendsto (fun n => -A.pole n) atTop (𝓝 0) := by
    simpa using A.pole_tendsto.neg
  have hC : Tendsto (fun n => -A.alpha * A.C n) atTop
      (𝓝 (-A.alpha * (Real.pi / 2 - 1))) := by
    simpa using (A.C_tendsto.const_mul (-A.alpha))
  have hsum := hconst.add hpole |>.add hC
  convert hsum using 1
  · funext n
    simp [chapter06AsymptoticExpressionWithoutB, chapter06AsymptoticExpression]
    ring
  · congr 1
    rw [chapter06_completion_constant_diagnostic]
    ring

theorem chapter06_missing_C_loss_diagnostic
    (A : Chapter06TriangularAsymptoticData) :
    Tendsto (fun n =>
      chapter06AsymptoticExpressionWithoutC A.alpha (A.B n) (A.pole n)) atTop
      (𝓝 (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) +
        A.alpha * (Real.pi / 2))) := by
  have hconst : Tendsto (fun _ : ℕ =>
      chapter06GammaConstant + A.alpha * (Real.pi / 2)) atTop
      (𝓝 (chapter06GammaConstant + A.alpha * (Real.pi / 2))) :=
    tendsto_const_nhds
  have hpole : Tendsto (fun n => -A.pole n) atTop (𝓝 0) := by
    simpa using A.pole_tendsto.neg
  have hB : Tendsto (fun n => -A.B n) atTop
      (𝓝 (-Real.log 2)) := by
    simpa using A.B_tendsto.neg
  have hsum := hconst.add hpole |>.add hB
  have hlog : Real.log (8 * Real.pi) - Real.log 2 =
      Real.log (4 * Real.pi) := by
    rw [← Real.log_div (by positivity) (by norm_num)]
    congr 1
    ring
  convert hsum using 1
  · funext n
    simp [chapter06AsymptoticExpressionWithoutC, chapter06AsymptoticExpression]
    ring
  · congr 1
    rw [chapter06_completion_constant_diagnostic, ← hlog]
    ring

def chapter06TrivialZeroSet
    (K : Type*) [Field K] [NumberField K] : Set ℂ :=
  {s | LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.chapter03DedekindZeta
      K s = 0 ∧ s.re ≤ 0}

def chapter06NaiveContourCrossingSet
    (K : Type*) [Field K] [NumberField K] : Set ℂ :=
  ({(1 : ℂ)} : Set ℂ) ∪ chapter06TrivialZeroSet K

def chapter06NaivePoleResidue (F : ℝ → ℝ) : ℂ :=
  chapter06Phi F 1

/-
SOURCE_WARNING (books/007-analytic-foundations-for-odlyzko-poitou-bounds.md:§6.6):
shifting `-ζ'_K/ζ_K` alone crosses the pole at `1` and the individual
trivial zeros, whereas the completed function packages the latter into its
Gamma factors and retains the `s(s-1)` pole contribution.  The crossing set
and the nonzero pole residue are exposed above; deleting the pole term is not
part of the Chapter 6 API.
-/
end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06
