import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01

noncomputable section

open MeasureTheory
open Filter
open scoped BigOperators Topology

/-! ## 1.4. Scope and standing conventions -/

/- The angular-frequency convention has no `2 * π` in its exponential. -/
def chapter01FourierTransform (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => ∫ x : ℝ,
    f x * Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))

@[simp]
theorem chapter01FourierTransform_apply (f : ℝ → ℂ) (t : ℝ) :
    chapter01FourierTransform f t =
      ∫ x : ℝ, f x * Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) :=
  rfl

noncomputable def chapter01EulerConstant : ℝ :=
  Real.eulerMascheroniConstant

theorem chapter01EulerConstant_eq_canonical :
    chapter01EulerConstant = Real.eulerMascheroniConstant :=
  rfl

def chapter01NaturalLog : ℝ → ℝ := Real.log

@[simp]
theorem chapter01NaturalLog_apply (x : ℝ) :
    chapter01NaturalLog x = Real.log x :=
  rfl

/- A zero family records multiplicity, conjugation symmetry, and local
   finiteness in symmetric vertical windows.  This is the book-facing
   summation convention for zeros. -/
structure Chapter01ZeroMultiplicity where
  multiplicity : ℂ → ℕ
  multiplicity_conjugation : ∀ z : ℂ, multiplicity (star z) = multiplicity z
  locally_finite : ∀ T : ℝ,
    {z : ℂ | multiplicity z ≠ 0 ∧ |z.im| ≤ T}.Finite

noncomputable def chapter01ZeroWindow
    (Z : Chapter01ZeroMultiplicity) (T : ℝ) : Finset ℂ :=
  (Z.locally_finite T).toFinset

theorem chapter01ZeroWindow_mem_iff
    (Z : Chapter01ZeroMultiplicity) (T : ℝ) (z : ℂ) :
    z ∈ chapter01ZeroWindow Z T ↔ Z.multiplicity z ≠ 0 ∧ |z.im| ≤ T := by
  simp [chapter01ZeroWindow]

theorem chapter01ZeroWindow_conjugation_mem_iff
    (Z : Chapter01ZeroMultiplicity) (T : ℝ) (z : ℂ) :
    star z ∈ chapter01ZeroWindow Z T ↔
      z ∈ chapter01ZeroWindow Z T := by
  rw [chapter01ZeroWindow_mem_iff, chapter01ZeroWindow_mem_iff]
  have hm := Z.multiplicity_conjugation z
  constructor
  · rintro ⟨hm', hT⟩
    refine ⟨?_, ?_⟩
    · rw [hm] at hm'
      exact hm'
    · simpa using hT
  · rintro ⟨hm', hT⟩
    refine ⟨?_, ?_⟩
    · rw [hm]
      exact hm'
    · simpa using hT

noncomputable def chapter01SymmetricZeroPartialSum
    (Z : Chapter01ZeroMultiplicity) (F : ℂ → ℂ) (T : ℝ) : ℂ :=
  Finset.sum (chapter01ZeroWindow Z T)
    (fun z => (Z.multiplicity z : ℕ) • F z)

def chapter01SymmetricZeroSum
    (Z : Chapter01ZeroMultiplicity) (F : ℂ → ℂ) (s : ℂ) : Prop :=
  Tendsto (chapter01SymmetricZeroPartialSum Z F) atTop (𝓝 s)

theorem chapter01SymmetricZeroSum_uses_multiplicity
    (Z : Chapter01ZeroMultiplicity) (F : ℂ → ℂ) (T : ℝ) :
    chapter01SymmetricZeroPartialSum Z F T =
      Finset.sum (chapter01ZeroWindow Z T)
        (fun z => (Z.multiplicity z : ℕ) • F z) :=
  rfl

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01
