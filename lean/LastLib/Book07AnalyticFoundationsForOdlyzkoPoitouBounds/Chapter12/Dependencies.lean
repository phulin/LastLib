import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08.Section03ExactEvaluationOfTheArchimedeanTerms
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09.Section01UniversalOdlyzkoPoitouInequalities
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12

open Filter Set
open NumberField NumberField.InfinitePlace
open scoped BigOperators

noncomputable section

/-!
Shared interfaces for Chapter 12.  Chapter 11 supplies the geometric and
explicit-formula expressions, while Chapter 10 supplies the certified
archimedean ledger used by the finite-search interfaces in §12.2.
-/

abbrev chapter12Degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank ℚ K

abbrev chapter12RealPlaceCount (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrRealPlaces K

abbrev chapter12ComplexPlaceCount (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrComplexPlaces K

def chapter12RealProportion (K : Type*) [Field K] [NumberField K] : ℝ :=
  (chapter12RealPlaceCount K : ℝ) / (chapter12Degree K : ℝ)

theorem chapter12_signature_formula
    (K : Type*) [Field K] [NumberField K] :
    chapter12RealPlaceCount K + 2 * chapter12ComplexPlaceCount K =
      chapter12Degree K := by
  simpa [chapter12RealPlaceCount, chapter12ComplexPlaceCount, chapter12Degree] using
    (NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K)

theorem chapter12_degree_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter12Degree K := by
  exact Module.finrank_pos

structure Chapter12Signature where
  degree : ℕ
  realPlaces : ℕ
  complexPlaces : ℕ
  degree_eq : realPlaces + 2 * complexPlaces = degree

def chapter12FieldSignature
    (K : Type*) [Field K] [NumberField K] : Chapter12Signature :=
  { degree := chapter12Degree K
    realPlaces := chapter12RealPlaceCount K
    complexPlaces := chapter12ComplexPlaceCount K
    degree_eq := chapter12_signature_formula K }

def chapter12SignatureRatio (s : Chapter12Signature) : ℝ :=
  (s.realPlaces : ℝ) / (s.degree : ℝ)

theorem chapter12_field_signature_ratio
    (K : Type*) [Field K] [NumberField K] :
    chapter12SignatureRatio (chapter12FieldSignature K) =
      chapter12RealProportion K :=
  rfl

def chapter12AdmissibleSignature (n r₁ : ℕ) : Prop :=
  ∃ r₂ : ℕ, r₁ + 2 * r₂ = n

theorem chapter12_field_signature_admissible
    (K : Type*) [Field K] [NumberField K] :
    chapter12AdmissibleSignature (chapter12Degree K) (chapter12RealPlaceCount K) := by
  exact ⟨chapter12ComplexPlaceCount K, chapter12_signature_formula K⟩

theorem chapter12_signature_ratio_eq_one_iff
    (s : Chapter12Signature) (hdegree : 0 < s.degree) :
    chapter12SignatureRatio s = 1 ↔ s.realPlaces = s.degree := by
  constructor
  · intro h
    change (s.realPlaces : ℝ) / (s.degree : ℝ) = 1 at h
    have hdeg : (s.degree : ℝ) ≠ 0 := by
      positivity
    have h' : (s.realPlaces : ℝ) = (s.degree : ℝ) := by
      simpa using (div_eq_iff hdeg).mp h
    exact_mod_cast h'
  · intro h
    change (s.realPlaces : ℝ) / (s.degree : ℝ) = 1
    have hdeg : (s.degree : ℝ) ≠ 0 := by
      positivity
    rw [h]
    exact div_self hdeg

def chapter12FullRealSignature (K : Type*) [Field K] [NumberField K] : Prop :=
  chapter12RealPlaceCount K = chapter12Degree K

theorem chapter12_full_real_signature_of_isTotallyReal
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] :
    chapter12FullRealSignature K := by
  simpa [chapter12FullRealSignature, chapter12RealPlaceCount, chapter12Degree] using
    (NumberField.IsTotallyReal.finrank K).symm

theorem chapter12_real_proportion_eq_one_of_isTotallyReal
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] :
    chapter12RealProportion K = 1 := by
  rw [chapter12RealProportion,
    chapter12_full_real_signature_of_isTotallyReal K]
  have hdegree : (0 : ℝ) < (chapter12Degree K : ℝ) := by
    exact_mod_cast chapter12_degree_pos K
  exact div_self (ne_of_gt hdegree)

theorem chapter12_real_proportion_eq_one_iff_full_real_signature
    (K : Type*) [Field K] [NumberField K] :
    chapter12RealProportion K = 1 ↔ chapter12FullRealSignature K := by
  simpa [chapter12FieldSignature, chapter12SignatureRatio, chapter12RealProportion,
    chapter12FullRealSignature] using
    (chapter12_signature_ratio_eq_one_iff (chapter12FieldSignature K)
      (chapter12_degree_pos K))

theorem chapter12_real_proportion_mem_Icc
    (K : Type*) [Field K] [NumberField K] :
    chapter12RealProportion K ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]
  constructor
  · rw [chapter12RealProportion]
    exact div_nonneg (by positivity) (by positivity)
  · rw [chapter12RealProportion]
    have hsign := chapter12_signature_formula K
    have hreal : chapter12RealPlaceCount K ≤ chapter12Degree K := by
      omega
    have hdegree : (0 : ℝ) < (chapter12Degree K : ℝ) := by
      exact_mod_cast chapter12_degree_pos K
    apply (div_le_iff₀ hdegree).2
    simpa using (show (chapter12RealPlaceCount K : ℝ) ≤ (chapter12Degree K : ℝ) by
      exact_mod_cast hreal)

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12
