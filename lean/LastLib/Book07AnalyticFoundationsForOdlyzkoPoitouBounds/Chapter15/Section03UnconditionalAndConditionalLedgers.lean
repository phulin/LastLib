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
  sorry

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
  sorry

theorem chapter15_grh_strict_threshold_gives_effective_cap
    {U α₀ : ℝ}
    (hU : U < chapter15GRHThreshold α₀)
    (hα₀ : 0 ≤ α₀) (hα₀' : α₀ ≤ 1) :
    chapter15HasGRHDegreeCap U α₀ := by
  sorry

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
  sorry

theorem chapter15_grh_finite_certificate_exists
    {U α₀ : ℝ} (hUpos : 0 < U)
    (hU : U < chapter15GRHThreshold α₀) :
    Nonempty (Chapter15GRHFiniteCertificate U α₀) := by
  sorry

theorem chapter15_unconditional_finite_certificate_gives_cap
    {U α₀ : ℝ}
    (C : Chapter15UnconditionalFiniteCertificate U α₀) :
    chapter15HasUnconditionalDegreeCap U α₀ := by
  sorry

theorem chapter15_grh_finite_certificate_gives_cap
    {U α₀ : ℝ}
    (C : Chapter15GRHFiniteCertificate U α₀) :
    chapter15HasGRHDegreeCap U α₀ := by
  sorry

theorem chapter15_unconditional_asymptotic_lower_bound
    (S : Chapter09NumberFieldSequence) (α₀ : ℝ) (T : ℕ → ℝ)
    (hTpos : ∀ j, 0 < T j)
    (hT : Tendsto T atTop atTop)
    (hdegree : Tendsto
      (fun j => (chapter09SequenceDegree S j : ℝ)) atTop atTop)
    (halpha : α₀ ≤ Filter.liminf
      (chapter09SequenceRealProportion S) atTop)
    (hTdegree : Tendsto
      (fun j => T j / (chapter09SequenceDegree S j : ℝ))
      atTop (𝓝 0)) :
    Filter.liminf (chapter09SequenceRootDiscriminant S) atTop ≥
      chapter15UnconditionalThreshold α₀ := by
  sorry

theorem chapter15_grh_asymptotic_lower_bound
    (S : Chapter09NumberFieldSequence) (α₀ : ℝ) (T : ℕ → ℝ)
    (hGRH : ∀ j, chapter09SequenceGRH S j)
    (hTpos : ∀ j, 0 < T j)
    (hT : Tendsto T atTop atTop)
    (hdegree : Tendsto
      (fun j => (chapter09SequenceDegree S j : ℝ)) atTop atTop)
    (halpha : α₀ ≤ Filter.liminf
      (chapter09SequenceRealProportion S) atTop)
    (hpole : Tendsto
      (fun j =>
        Real.exp (T j / 2) /
          ((chapter09SequenceDegree S j : ℝ) * T j))
      atTop (𝓝 0)) :
    Filter.liminf (chapter09SequenceRootDiscriminant S) atTop ≥
      chapter15GRHThreshold α₀ := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter15
