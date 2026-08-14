import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Order.LiminfLimsup

import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Dependencies
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08.Section02TheTriangularAutocorrelation

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

/-!
Shared interfaces for Chapter 9.

The preceding Book 07 chapters are otherwise developed in parallel.  The
focused Chapter 6 dependency is imported only for the completed-zeta zero
predicate; the declarations below remain the minimal book-facing surface
needed by this chapter and are thin over canonical number-field objects.
-/

abbrev chapter09Degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank ℚ K

abbrev chapter09RealPlaceCount (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrRealPlaces K

abbrev chapter09ComplexPlaceCount (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrComplexPlaces K

def chapter09AbsoluteDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  |(NumberField.discr K : ℝ)|

def chapter09RootDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.rpow (chapter09AbsoluteDiscriminant K)
    (1 / (chapter09Degree K : ℝ))

abbrev chapter09EulerMascheroni : ℝ := Real.eulerMascheroniConstant

def chapter09RealProportion (K : Type*) [Field K] [NumberField K] : ℝ :=
  (chapter09RealPlaceCount K : ℝ) / (chapter09Degree K : ℝ)

theorem chapter09_signature_formula
    (K : Type*) [Field K] [NumberField K] :
    chapter09RealPlaceCount K + 2 * chapter09ComplexPlaceCount K =
      chapter09Degree K := by
  simpa [chapter09RealPlaceCount, chapter09ComplexPlaceCount, chapter09Degree] using
    (NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K)

theorem chapter09_degree_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter09Degree K := by
  exact Module.finrank_pos

theorem chapter09_absolute_discriminant_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter09AbsoluteDiscriminant K := by
  rw [chapter09AbsoluteDiscriminant, abs_pos]
  exact_mod_cast NumberField.discr_ne_zero K

theorem chapter09_root_discriminant_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter09RootDiscriminant K := by
  rw [chapter09RootDiscriminant]
  exact Real.rpow_pos_of_pos (chapter09_absolute_discriminant_pos K) _

theorem chapter09_root_discriminant_eq_canonical
    (K : Type*) [Field K] [NumberField K] :
    chapter09RootDiscriminant K = NumberField.rootDiscr K := by
  rw [chapter09RootDiscriminant, NumberField.rootDiscr_def]
  simp [chapter09AbsoluteDiscriminant, chapter09Degree, Int.cast_abs]

theorem chapter09_real_proportion_mem_Icc
    (K : Type*) [Field K] [NumberField K] :
    chapter09RealProportion K ∈ Set.Icc (0 : ℝ) 1 := by
  have hdeg : 0 < chapter09Degree K := Module.finrank_pos
  have hreal : chapter09RealPlaceCount K ≤ chapter09Degree K := by
    have hsig := chapter09_signature_formula K
    omega
  constructor
  · unfold chapter09RealProportion
    positivity
  · unfold chapter09RealProportion
    have hdegR : 0 < (chapter09Degree K : ℝ) := by exact_mod_cast hdeg
    exact (div_le_one hdegR).2 (by exact_mod_cast hreal)

/- The nontrivial-zero support is tied to the completed-zeta function used by
   the preceding analytic package.  This keeps possible boundary zeros in the
   support; the source's unconditional strip-positivity argument explicitly
   includes those endpoints.  Multiplicities and the functional-equation
   package remain upstream data; this interface only supplies support. -/
def chapter09NontrivialCompletedDedekindZetaZero
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) : Prop :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06Xi K ρ = 0

class Chapter09ZetaZeroInterface
    (K : Type*) [Field K] [NumberField K] where
  nontrivialZeros : Set ℂ
  nontrivialZeros_spec :
    ∀ ρ, ρ ∈ nontrivialZeros ↔
      chapter09NontrivialCompletedDedekindZetaZero K ρ

def chapter09GRHOnZeros (zeros : Set ℂ) : Prop :=
  ∀ ρ ∈ zeros, ρ.re = 1 / 2

def chapter09GRH
    (K : Type*) [Field K] [NumberField K]
    [Chapter09ZetaZeroInterface K] : Prop :=
  chapter09GRHOnZeros
    (Chapter09ZetaZeroInterface.nontrivialZeros (K := K))

abbrev Chapter09TestFunction := ℝ → ℝ

def chapter09TriangularAutocorrelation (T : ℝ) : Chapter09TestFunction :=
  fun x => max (1 - |x| / T) 0

def chapter09UnconditionalTestFunction (T : ℝ) : Chapter09TestFunction :=
  fun x => chapter09TriangularAutocorrelation T x / Real.cosh (x / 2)

def chapter09GRHTestFunction (T : ℝ) : Chapter09TestFunction :=
  chapter09TriangularAutocorrelation T

def chapter09A (F : Chapter09TestFunction) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), F x * Real.cosh (x / 2)

def chapter09B (F : Chapter09TestFunction) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), (1 - F x) / (2 * Real.sinh (x / 2))

def chapter09C (F : Chapter09TestFunction) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), (1 - F x) / (2 * Real.cosh (x / 2))

def chapter09BT (T : ℝ) : ℝ :=
  chapter09B (chapter09UnconditionalTestFunction T)

def chapter09CT (T : ℝ) : ℝ :=
  chapter09C (chapter09UnconditionalTestFunction T)

def chapter09GRHBT (T : ℝ) : ℝ :=
  chapter09B (chapter09GRHTestFunction T)

def chapter09GRHCT (T : ℝ) : ℝ :=
  chapter09C (chapter09GRHTestFunction T)

def chapter09UnconditionalPoleIntegral (T : ℝ) : ℝ :=
  chapter09A (chapter09UnconditionalTestFunction T)

def chapter09GRHPoleIntegral (T : ℝ) : ℝ :=
  chapter09A (chapter09GRHTestFunction T)

theorem chapter09_triangular_at_zero (T : ℝ) :
    chapter09TriangularAutocorrelation T 0 = 1 := by
  simp [chapter09TriangularAutocorrelation]

theorem chapter09_unconditional_test_function_at_zero (T : ℝ) :
    chapter09UnconditionalTestFunction T 0 = 1 := by
  simp [chapter09UnconditionalTestFunction, chapter09_triangular_at_zero]

theorem chapter09_grh_test_function_at_zero (T : ℝ) :
    chapter09GRHTestFunction T 0 = 1 := by
  exact chapter09_triangular_at_zero T

theorem chapter09_unconditional_pole_integral
    {T : ℝ} (hT : 0 < T) :
    chapter09UnconditionalPoleIntegral T = T / 2 := by
  simpa [chapter09UnconditionalPoleIntegral, chapter09A,
    chapter09UnconditionalTestFunction, chapter09TriangularAutocorrelation,
    Chapter08.chapter08A, Chapter08.chapter08FUnconditionalTriangle,
    Chapter08.chapter08TriangularAutocorrelation] using
    (Chapter08.chapter08_unconditional_triangle_A hT)

theorem chapter09_grh_pole_integral
    {T : ℝ} (hT : 0 < T) :
    chapter09GRHPoleIntegral T = 4 / T * (Real.cosh (T / 2) - 1) := by
  simpa [chapter09GRHPoleIntegral, chapter09A,
    chapter09GRHTestFunction, chapter09TriangularAutocorrelation,
    Chapter08.chapter08A, Chapter08.chapter08FGRHTriangle,
    Chapter08.chapter08TriangularAutocorrelation] using
    (Chapter08.chapter08_grh_triangle_A hT)

def chapter09UnconditionalExponent
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : ℝ :=
  chapter09EulerMascheroni + Real.log (8 * Real.pi) +
      chapter09RealProportion K * (Real.pi / 2) -
    2 * T / (chapter09Degree K : ℝ) - chapter09BT T -
      chapter09RealProportion K * chapter09CT T

def chapter09GRHExponent
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : ℝ :=
  chapter09EulerMascheroni + Real.log (8 * Real.pi) +
      chapter09RealProportion K * (Real.pi / 2) -
    4 * chapter09GRHPoleIntegral T / (chapter09Degree K : ℝ) -
      chapter09GRHBT T - chapter09RealProportion K * chapter09GRHCT T

/- A wrapper for varying number fields.  The zero set is carried as a field of
the model because the canonical completed-zeta object is supplied upstream. -/
structure Chapter09NumberFieldModel where
  K : Type*
  [field : Field K]
  [numberField : NumberField K]
  nontrivialZeros : Set ℂ
  nontrivialZeros_spec :
    ∀ ρ, ρ ∈ nontrivialZeros ↔
      chapter09NontrivialCompletedDedekindZetaZero K ρ

namespace Chapter09NumberFieldModel

def degree (M : Chapter09NumberFieldModel) : ℕ := by
  letI := M.field
  letI := M.numberField
  exact chapter09Degree M.K

def realProportion (M : Chapter09NumberFieldModel) : ℝ := by
  letI := M.field
  letI := M.numberField
  exact chapter09RealProportion M.K

def rootDiscriminant (M : Chapter09NumberFieldModel) : ℝ := by
  letI := M.field
  letI := M.numberField
  exact chapter09RootDiscriminant M.K

def satisfiesGRH (M : Chapter09NumberFieldModel) : Prop :=
  chapter09GRHOnZeros M.nontrivialZeros

/- A model carries its zero set as data, whereas the fieldwise GRH theorem
   consumes the chapter's zero-interface typeclass.  This constructor is the
   non-circular bridge needed when applying that theorem to a model member. -/
@[instance_reducible]
def zetaZeroInterface (M : Chapter09NumberFieldModel) :
    @Chapter09ZetaZeroInterface M.K M.field M.numberField := by
  letI := M.field
  letI := M.numberField
  exact
    { nontrivialZeros := M.nontrivialZeros
      nontrivialZeros_spec := M.nontrivialZeros_spec }

theorem degree_pos (M : Chapter09NumberFieldModel) : 0 < M.degree := by
  exact @chapter09_degree_pos M.K M.field M.numberField

theorem real_proportion_mem_Icc (M : Chapter09NumberFieldModel) :
    M.realProportion ∈ Set.Icc (0 : ℝ) 1 := by
  exact @chapter09_real_proportion_mem_Icc M.K M.field M.numberField

theorem root_discriminant_pos (M : Chapter09NumberFieldModel) :
    0 < M.rootDiscriminant := by
  exact @chapter09_root_discriminant_pos M.K M.field M.numberField

end Chapter09NumberFieldModel

structure Chapter09NumberFieldSequence where
  field : ℕ → Chapter09NumberFieldModel

def chapter09SequenceDegree (S : Chapter09NumberFieldSequence) : ℕ → ℕ :=
  fun j => (S.field j).degree

def chapter09SequenceRealProportion
    (S : Chapter09NumberFieldSequence) : ℕ → ℝ :=
  fun j => (S.field j).realProportion

def chapter09SequenceRootDiscriminant
    (S : Chapter09NumberFieldSequence) : ℕ → ℝ :=
  fun j => (S.field j).rootDiscriminant

def chapter09SequenceGRH (S : Chapter09NumberFieldSequence) (j : ℕ) : Prop :=
  chapter09GRHOnZeros (S.field j).nontrivialZeros

theorem chapter09_sequence_degree_pos
    (S : Chapter09NumberFieldSequence) (j : ℕ) :
    0 < chapter09SequenceDegree S j := by
  exact Chapter09NumberFieldModel.degree_pos (S.field j)

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09
