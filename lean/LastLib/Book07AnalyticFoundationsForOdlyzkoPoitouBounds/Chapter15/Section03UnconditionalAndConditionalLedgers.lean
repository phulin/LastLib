import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter15.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter15

noncomputable section

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09

open Filter
open scoped Topology

/-! ## 15.3. Unconditional and conditional ledgers -/

def chapter15UnconditionalAsymptoticExponent (α₀ : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + α₀

def chapter15GRHAsymptoticExponent (α₀ : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + α₀ * (Real.pi / 2)

def chapter15UnconditionalThreshold (α₀ : ℝ) : ℝ :=
  4 * Real.pi * Real.exp (chapter15UnconditionalAsymptoticExponent α₀)

def chapter15GRHThreshold (α₀ : ℝ) : ℝ :=
  8 * Real.pi * Real.exp (chapter15GRHAsymptoticExponent α₀)

theorem chapter15_intermediate_signature_thresholds (α₀ : ℝ) :
    chapter15UnconditionalThreshold α₀ =
        4 * Real.pi * Real.exp
          (Real.eulerMascheroniConstant + α₀) ∧
      chapter15GRHThreshold α₀ =
        8 * Real.pi * Real.exp
          (Real.eulerMascheroniConstant + α₀ * (Real.pi / 2)) := by
  constructor <;> rfl

theorem chapter15_asymptotic_threshold_ledger :
    chapter15UnconditionalThreshold 0 =
        4 * Real.pi * Real.exp Real.eulerMascheroniConstant ∧
      chapter15UnconditionalThreshold 1 =
        4 * Real.pi * Real.exp (1 + Real.eulerMascheroniConstant) ∧
      chapter15GRHThreshold 0 =
        8 * Real.pi * Real.exp Real.eulerMascheroniConstant ∧
      chapter15GRHThreshold 1 =
        8 * Real.pi * Real.exp
          (Real.eulerMascheroniConstant + Real.pi / 2) := by
  norm_num [chapter15UnconditionalThreshold, chapter15GRHThreshold,
    chapter15UnconditionalAsymptoticExponent,
    chapter15GRHAsymptoticExponent]; ring

def chapter15UnconditionalInfiniteDegreeExponent
    (T α₀ : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) +
      α₀ * (Real.pi / 2) - chapter15BT T - α₀ * chapter15CT T

def chapter15GRHInfiniteDegreeExponent
    (T α₀ : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) +
      α₀ * (Real.pi / 2) - chapter15GRHBT T - α₀ * chapter15GRHCT T

def chapter15HasUnconditionalDegreeCap (U α₀ : ℝ) : Prop :=
  ∃ N : ℕ, ∀ (K : Type*) [Field K] [NumberField K],
    chapter15RootDiscriminant K ≤ U →
      α₀ ≤ chapter15RealProportion K →
        chapter15Degree K < N

def chapter15HasGRHDegreeCap (U α₀ : ℝ) : Prop :=
  ∃ N : ℕ,
    ∀ (K : Type*) [Field K] [NumberField K]
      [Chapter09ZetaZeroInterface K],
      chapter15GRHFor K →
        chapter15RootDiscriminant K ≤ U →
          α₀ ≤ chapter15RealProportion K →
            chapter15Degree K < N

theorem chapter15_unconditional_strict_threshold_gives_effective_cap
    {U α₀ : ℝ}
    (hU : U < chapter15UnconditionalThreshold α₀)
    (hα₀ : 0 ≤ α₀) (hα₀' : α₀ ≤ 1) :
    chapter15HasUnconditionalDegreeCap U α₀ := by
  have hU' : U < chapter09UnconditionalAsymptoticConstant α₀ := hU
  by_cases hUpos : 0 < U
  · refine ⟨chapter09Threshold U α₀, ?_⟩
    intro K _ _ hroot hα
    have hroot' : chapter09RootDiscriminant K ≤ U := by
      rw [← chapter15_rootDiscriminant_eq_chapter09 K]
      exact hroot
    have hα' : α₀ ≤ chapter09RealProportion K := by
      by_cases ha : 0 ≤ α₀
      · by_cases ha' : α₀ ≤ 1
        · exact hα
        · exact (False.elim (ha' hα₀'))
      · exact (False.elim (ha hα₀))
    exact chapter09_threshold_principle hUpos hU' K hroot' hα'
  · refine ⟨1, ?_⟩
    intro K _ _ hroot hα
    have hUle : U ≤ 0 := le_of_not_gt hUpos
    have hrootpos := chapter15_rootDiscriminant_pos K
    exfalso
    linarith

theorem chapter15_grh_strict_threshold_gives_effective_cap
    {U α₀ : ℝ}
    (hU : U < chapter15GRHThreshold α₀)
    (hα₀ : 0 ≤ α₀) (hα₀' : α₀ ≤ 1) :
    chapter15HasGRHDegreeCap U α₀ := by
  have hU' : U < chapter09GRHAsymptoticConstant α₀ := hU
  by_cases hUpos : 0 < U
  · refine ⟨chapter09GRHThreshold U α₀, ?_⟩
    intro K _ _ _ hgrh hroot hα
    have hroot' : chapter09RootDiscriminant K ≤ U := by
      rw [← chapter15_rootDiscriminant_eq_chapter09 K]
      exact hroot
    have hα' : α₀ ≤ chapter09RealProportion K := by
      by_cases ha : 0 ≤ α₀
      · by_cases ha' : α₀ ≤ 1
        · exact hα
        · exact (False.elim (ha' hα₀'))
      · exact (False.elim (ha hα₀))
    exact chapter09_grh_threshold_principle hUpos hU' K hgrh hroot' hα'
  · refine ⟨1, ?_⟩
    intro K _ _ _ hgrh hroot hα
    have hUle : U ≤ 0 := le_of_not_gt hUpos
    have hrootpos := chapter15_rootDiscriminant_pos K
    exfalso
    linarith

/-!
The asymptotic constants alone do not record a finite support or a finite
degree margin.  These certificate records make the finite data required by a
cutoff explicit: a rational support, its archimedean endpoint, and a positive
pole gap.
-/

structure Chapter15UnconditionalFiniteCertificate
    (U α₀ : ℝ) where
  T : ℚ
  T_pos : 0 < (T : ℝ)
  infinite_degree_gap :
    Real.log U < chapter15UnconditionalInfiniteDegreeExponent (T : ℝ) α₀
  N : ℕ
  N_pos : 0 < N
  pole_gap :
    2 * (T : ℝ) / (N : ℝ) <
      chapter15UnconditionalInfiniteDegreeExponent (T : ℝ) α₀ - Real.log U

structure Chapter15GRHFiniteCertificate
    (U α₀ : ℝ) where
  T : ℚ
  T_pos : 0 < (T : ℝ)
  infinite_degree_gap :
    Real.log U < chapter15GRHInfiniteDegreeExponent (T : ℝ) α₀
  N : ℕ
  N_pos : 0 < N
  pole_gap :
    chapter15GRHPoleCost N (T : ℝ) <
      chapter15GRHInfiniteDegreeExponent (T : ℝ) α₀ - Real.log U

theorem chapter15_unconditional_finite_certificate_exists
    {U α₀ : ℝ} (hUpos : 0 < U)
    (hU : U < chapter15UnconditionalThreshold α₀) :
    Nonempty (Chapter15UnconditionalFiniteCertificate U α₀) := by
  have hU' : U < chapter09UnconditionalAsymptoticConstant α₀ := hU
  rcases chapter09_threshold_certificate_exists hUpos hU' with ⟨C⟩
  refine ⟨⟨C.T, C.T_pos, ?_, C.N, C.N_pos, ?_⟩⟩
  · exact C.infinite_degree_gap
  · exact C.pole_gap

theorem chapter15_grh_finite_certificate_exists
    {U α₀ : ℝ} (hUpos : 0 < U)
    (hU : U < chapter15GRHThreshold α₀) :
    Nonempty (Chapter15GRHFiniteCertificate U α₀) := by
  have hU' : U < chapter09GRHAsymptoticConstant α₀ := hU
  rcases chapter09_grh_threshold_certificate_exists hUpos hU' with ⟨C⟩
  refine ⟨⟨C.T, C.T_pos, ?_, C.N, C.N_pos, ?_⟩⟩
  · exact C.infinite_degree_gap
  · exact C.pole_gap

theorem chapter15_unconditional_finite_certificate_gives_cap
    {U α₀ : ℝ}
    (C : Chapter15UnconditionalFiniteCertificate U α₀) :
    chapter15HasUnconditionalDegreeCap U α₀ := by
  refine ⟨C.N, ?_⟩
  intro K _ _ hroot hα
  have hUpos : 0 < U :=
    lt_of_lt_of_le (chapter15_rootDiscriminant_pos K) hroot
  have hroot' : chapter09RootDiscriminant K ≤ U := by
    rw [← chapter15_rootDiscriminant_eq_chapter09 K]
    exact hroot
  have hlogceil : Real.log (chapter09RootDiscriminant K) ≤ Real.log U := by
    exact Real.strictMonoOn_log.monotoneOn
      (show chapter09RootDiscriminant K ∈ Set.Ioi 0 from
        chapter09_root_discriminant_pos K)
      (show U ∈ Set.Ioi 0 from hUpos) hroot'
  have hloglower := chapter09_universal_odlyzko_poitou_log_bound
    K C.T_pos
  let F : Chapter09TestFunction := chapter09UnconditionalTestFunction (C.T : ℝ)
  have hAeq : chapter09A F = (C.T : ℝ) / 2 := by
    change chapter09UnconditionalPoleIntegral (C.T : ℝ) = (C.T : ℝ) / 2
    exact chapter09_unconditional_pole_integral C.T_pos
  have hA : 0 ≤ chapter09A F := by
    rw [hAeq]
    exact div_nonneg (le_of_lt C.T_pos) (by norm_num)
  have hC : chapter09C F < Real.pi / 2 := by
    simpa [F, chapter09CT] using
      (chapter09_unconditional_archimedean_C_lt_pi_div_two C.T_pos)
  by_contra hnot
  have hNle : C.N ≤ chapter09Degree K := Nat.le_of_not_gt hnot
  have hmono := chapter09_fixed_certificate_covers_larger_degree_and_signature
    F hA hC C.N_pos hNle hα
  have hfixed :
      chapter09FixedTestFunctionLogBound F C.N α₀ =
        chapter15UnconditionalInfiniteDegreeExponent (C.T : ℝ) α₀ -
          2 * (C.T : ℝ) / (C.N : ℝ) := by
    unfold chapter09FixedTestFunctionLogBound chapter09FixedTestFunctionConstant
      chapter15UnconditionalInfiniteDegreeExponent
    rw [hAeq]
    rw [chapter15_BT_eq_chapter09, chapter15_CT_eq_chapter09]
    simp [chapter09BT, chapter09CT, F]
    ring
  have hexponent :
      chapter09UnconditionalExponent K (C.T : ℝ) =
        chapter09FixedTestFunctionLogBound F
          (chapter09Degree K) (chapter09RealProportion K) := by
    simpa [F] using
      (chapter09_unconditional_exponent_eq_fixed_test_function_log_bound
        K C.T_pos)
  have hfixedlower :
      chapter15UnconditionalInfiniteDegreeExponent (C.T : ℝ) α₀ -
          2 * (C.T : ℝ) / (C.N : ℝ) ≤
        chapter09UnconditionalExponent K (C.T : ℝ) := by
    calc
      chapter15UnconditionalInfiniteDegreeExponent (C.T : ℝ) α₀ -
          2 * (C.T : ℝ) / (C.N : ℝ) =
          chapter09FixedTestFunctionLogBound F C.N α₀ := hfixed.symm
      _ ≤ chapter09FixedTestFunctionLogBound F
          (chapter09Degree K) (chapter09RealProportion K) := hmono
      _ = chapter09UnconditionalExponent K (C.T : ℝ) := hexponent.symm
  have hstrict : Real.log U <
      chapter15UnconditionalInfiniteDegreeExponent (C.T : ℝ) α₀ -
        2 * (C.T : ℝ) / (C.N : ℝ) := by
    linarith [C.pole_gap]
  linarith [hloglower, hlogceil, hfixedlower, hstrict]

theorem chapter15_grh_finite_certificate_gives_cap
    {U α₀ : ℝ}
    (C : Chapter15GRHFiniteCertificate U α₀) :
    chapter15HasGRHDegreeCap U α₀ := by
  refine ⟨C.N, ?_⟩
  intro K _ _ _ hgrh hroot hα
  have hUpos : 0 < U :=
    lt_of_lt_of_le (chapter15_rootDiscriminant_pos K) hroot
  have hroot' : chapter09RootDiscriminant K ≤ U := by
    rw [← chapter15_rootDiscriminant_eq_chapter09 K]
    exact hroot
  have hlogceil : Real.log (chapter09RootDiscriminant K) ≤ Real.log U := by
    exact Real.strictMonoOn_log.monotoneOn
      (show chapter09RootDiscriminant K ∈ Set.Ioi 0 from
        chapter09_root_discriminant_pos K)
      (show U ∈ Set.Ioi 0 from hUpos) hroot'
  have hexpbound := chapter09_grh_universal_odlyzko_poitou_bound
    K C.T_pos hgrh
  have hloglower : chapter09GRHExponent K (C.T : ℝ) ≤
      Real.log (chapter09RootDiscriminant K) := by
    rw [← Real.exp_le_exp]
    simpa [Real.exp_log (chapter09_root_discriminant_pos K)] using hexpbound
  let F : Chapter09TestFunction := chapter09GRHTestFunction (C.T : ℝ)
  have hAeq : chapter09A F = chapter09GRHPoleIntegral (C.T : ℝ) := by
    rfl
  have hA : 0 ≤ chapter09A F := by
    rw [hAeq, chapter09_grh_pole_integral C.T_pos]
    exact mul_nonneg
      (div_nonneg (by norm_num) (le_of_lt C.T_pos))
      (sub_nonneg.mpr (Real.one_le_cosh _))
  have hC : chapter09C F < Real.pi / 2 := by
    simpa [F, chapter09GRHCT] using
      (chapter09_grh_archimedean_C_lt_pi_div_two C.T_pos)
  by_contra hnot
  have hNle : C.N ≤ chapter09Degree K := Nat.le_of_not_gt hnot
  have hmono := chapter09_fixed_certificate_covers_larger_degree_and_signature
    F hA hC C.N_pos hNle hα
  have hpole_eq :
      chapter15GRHPoleCost C.N (C.T : ℝ) =
        4 * chapter09A F / (C.N : ℝ) := by
    unfold chapter15GRHPoleCost
    rw [chapter15_GT_eq_chapter09, chapter15_A_eq_chapter09]
  have hfixed :
      chapter09FixedTestFunctionLogBound F C.N α₀ =
        chapter15GRHInfiniteDegreeExponent (C.T : ℝ) α₀ -
          chapter15GRHPoleCost C.N (C.T : ℝ) := by
    rw [hpole_eq]
    unfold chapter09FixedTestFunctionLogBound chapter09FixedTestFunctionConstant
      chapter15GRHInfiniteDegreeExponent
    rw [hAeq, chapter15_GRHBT_eq_chapter09, chapter15_GRHCT_eq_chapter09]
    simp [chapter09GRHBT, chapter09GRHCT, F]
    ring
  have hexponent :
      chapter09GRHExponent K (C.T : ℝ) =
        chapter09FixedTestFunctionLogBound F
          (chapter09Degree K) (chapter09RealProportion K) := by
    unfold chapter09GRHExponent chapter09FixedTestFunctionLogBound
      chapter09FixedTestFunctionConstant
    rw [hAeq]
    simp [chapter09GRHBT, chapter09GRHCT, F]
    ring
  have hfixedlower :
      chapter15GRHInfiniteDegreeExponent (C.T : ℝ) α₀ -
          chapter15GRHPoleCost C.N (C.T : ℝ) ≤
        chapter09GRHExponent K (C.T : ℝ) := by
    calc
      chapter15GRHInfiniteDegreeExponent (C.T : ℝ) α₀ -
          chapter15GRHPoleCost C.N (C.T : ℝ) =
          chapter09FixedTestFunctionLogBound F C.N α₀ := hfixed.symm
      _ ≤ chapter09FixedTestFunctionLogBound F
          (chapter09Degree K) (chapter09RealProportion K) := hmono
      _ = chapter09GRHExponent K (C.T : ℝ) := hexponent.symm
  have hstrict : Real.log U <
      chapter15GRHInfiniteDegreeExponent (C.T : ℝ) α₀ -
        chapter15GRHPoleCost C.N (C.T : ℝ) := by
    linarith [C.pole_gap]
  linarith [hloglower, hlogceil, hfixedlower, hstrict]

theorem chapter15_unconditional_asymptotic_lower_bound
    (S : Chapter09NumberFieldSequence) (α₀ : ℝ) (T : ℕ → ℝ)
    (hTpos : ∀ j, 0 < T j)
    (hT : Tendsto T atTop atTop)
    (hdegree : Tendsto
      (fun j => (chapter09SequenceDegree S j : ℝ)) atTop atTop)
    (hroot : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (chapter09SequenceRootDiscriminant S))
    (halpha : α₀ ≤ Filter.liminf
      (chapter09SequenceRealProportion S) atTop)
    (hTdegree : Tendsto
      (fun j => T j / (chapter09SequenceDegree S j : ℝ))
      atTop (𝓝 0)) :
    Filter.liminf (chapter09SequenceRootDiscriminant S) atTop ≥
      chapter15UnconditionalThreshold α₀ := by
  exact chapter09_unconditional_asymptotic_lower_bound S α₀ T hTpos hT
    hdegree hroot halpha hTdegree

theorem chapter15_grh_asymptotic_lower_bound
    (S : Chapter09NumberFieldSequence) (α₀ : ℝ) (T : ℕ → ℝ)
    (hGRH : ∀ j, chapter09SequenceGRH S j)
    (hTpos : ∀ j, 0 < T j)
    (hT : Tendsto T atTop atTop)
    (hdegree : Tendsto
      (fun j => (chapter09SequenceDegree S j : ℝ)) atTop atTop)
    (hroot : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (chapter09SequenceRootDiscriminant S))
    (halpha : α₀ ≤ Filter.liminf
      (chapter09SequenceRealProportion S) atTop)
    (hpole : Tendsto
      (fun j =>
        Real.exp (T j / 2) /
          ((chapter09SequenceDegree S j : ℝ) * T j))
      atTop (𝓝 0)) :
    Filter.liminf (chapter09SequenceRootDiscriminant S) atTop ≥
      chapter15GRHThreshold α₀ := by
  exact chapter09_grh_asymptotic_lower_bound S α₀ T hGRH hTpos hT
    hdegree hroot halpha hpole

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter15
