import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.Section03TheShapeOfAUsefulLowerBound
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13.Dependencies
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter14

noncomputable section

universe u

open NumberField
open scoped NumberField Polynomial

/-!
## Shared interfaces for the failure diagnostics

The diagnostics in this chapter are about the distinction between numerical
analytic output and the arithmetic structure that produced it.  The numerical
fields below are thin wrappers around the canonical Mathlib number-field
quantities.  The sequence and profile records keep the quantifiers in the
warnings explicit without pretending that an arbitrary sequence is a tower.
-/

/-- The absolute degree used by the analytic ledger. -/
abbrev chapter14Degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank ℚ K

/-- The canonical root discriminant used by Mathlib. -/
noncomputable abbrev chapter14RootDiscriminant
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  NumberField.rootDiscr K

/-- The real and complex place counts in the signature. -/
noncomputable abbrev chapter14RealPlaces
    (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrRealPlaces K

noncomputable abbrev chapter14ComplexPlaces
    (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrComplexPlaces K

/-- The signature proportion seen by the signature-sensitive thresholds. -/
noncomputable def chapter14RealProportion
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  (chapter14RealPlaces K : ℝ) / (chapter14Degree K : ℝ)

theorem chapter14_degree_pos
    (K : Type*) [Field K] [NumberField K] : 0 < chapter14Degree K := by
  sorry

theorem chapter14_signature_identity
    (K : Type*) [Field K] [NumberField K] :
    chapter14RealPlaces K + 2 * chapter14ComplexPlaces K = chapter14Degree K := by
  sorry

theorem chapter14_realProportion_mem_Icc
    (K : Type*) [Field K] [NumberField K] :
    chapter14RealProportion K ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

theorem chapter14_rootDiscriminant_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter14RootDiscriminant K := by
  sorry

@[simp]
theorem chapter14_rootDiscriminant_eq_canonical
    (K : Type*) [Field K] [NumberField K] :
    chapter14RootDiscriminant K = NumberField.rootDiscr K :=
  rfl

/-! ### Number-field models and sequences -/

/- A model packages the typeclass instances needed to quantify over a field in
  a sequence.  It is the same device used by the earlier universal-inequality
  interfaces, but carries no zero-set or analytic hypothesis. -/
structure Chapter14NumberFieldModel where
  K : Type u
  [field : Field K]
  [numberField : NumberField K]

namespace Chapter14NumberFieldModel

noncomputable def degree (M : Chapter14NumberFieldModel.{u}) : ℕ := by
  letI := M.field
  letI := M.numberField
  exact chapter14Degree M.K

noncomputable def realProportion (M : Chapter14NumberFieldModel.{u}) : ℝ := by
  letI := M.field
  letI := M.numberField
  exact chapter14RealProportion M.K

noncomputable def rootDiscriminant (M : Chapter14NumberFieldModel.{u}) : ℝ := by
  letI := M.field
  letI := M.numberField
  exact chapter14RootDiscriminant M.K

theorem degree_pos (M : Chapter14NumberFieldModel.{u}) : 0 < M.degree := by
  sorry

theorem realProportion_mem_Icc (M : Chapter14NumberFieldModel.{u}) :
    M.realProportion ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

theorem rootDiscriminant_pos (M : Chapter14NumberFieldModel.{u}) :
    0 < M.rootDiscriminant := by
  sorry

end Chapter14NumberFieldModel

structure Chapter14NumberFieldSequence where
  field : ℕ → Chapter14NumberFieldModel.{u}

def chapter14SequenceDegree (S : Chapter14NumberFieldSequence.{u}) : ℕ → ℕ :=
  fun m => (S.field m).degree

def chapter14SequenceRealProportion
    (S : Chapter14NumberFieldSequence.{u}) : ℕ → ℝ :=
  fun m => (S.field m).realProportion

def chapter14SequenceRootDiscriminant
    (S : Chapter14NumberFieldSequence.{u}) : ℕ → ℝ :=
  fun m => (S.field m).rootDiscriminant

def chapter14UniformRootDiscriminantCeiling
    (S : Chapter14NumberFieldSequence.{u}) (U : ℝ) : Prop :=
  ∀ m : ℕ, chapter14SequenceRootDiscriminant S m ≤ U

def chapter14HasUniformAbsoluteRootDiscriminantCeiling
    (S : Chapter14NumberFieldSequence.{u}) : Prop :=
  ∃ U : ℝ, chapter14UniformRootDiscriminantCeiling S U

def chapter14GrowingRootDiscriminantEstimate
    (S : Chapter14NumberFieldSequence.{u}) (c ell : ℝ) : Prop :=
  ∀ m : ℕ,
    chapter14SequenceRootDiscriminant S m < c * ell ^ m

def chapter14UniformRealProportionLowerBound
    (S : Chapter14NumberFieldSequence.{u}) (α : ℝ) : Prop :=
  ∀ m : ℕ, α ≤ chapter14SequenceRealProportion S m

def chapter14UniformDegreeCap
    (S : Chapter14NumberFieldSequence.{u}) (N : ℕ) : Prop :=
  ∀ m : ℕ, chapter14SequenceDegree S m < N

def chapter14ModelwiseDegreeCap (U α : ℝ) (N : ℕ) : Prop :=
  ∀ M : Chapter14NumberFieldModel.{u},
    M.rootDiscriminant ≤ U → α ≤ M.realProportion → M.degree < N

/-! ### Numerical tower and ramification profiles -/

/- A degree profile records exactly the information in a bound on successive
  relative degrees.  It does not assert that the profile comes from a field
  tower; the field-theoretic realization is supplied separately when needed. -/
structure Chapter14TowerDegreeProfile (C : ℕ) where
  totalDegree : ℕ → ℕ
  stepDegree : ℕ → ℕ
  totalDegree_zero : totalDegree 0 = 1
  tower_degree : ∀ m : ℕ,
    totalDegree (m + 1) = stepDegree m * totalDegree m
  step_degree_le : ∀ m : ℕ, stepDegree m ≤ C

def chapter14UnboundedDegreeProfile {C : ℕ}
    (P : Chapter14TowerDegreeProfile C) : Prop :=
  ¬ ∃ N : ℕ, ∀ m : ℕ, P.totalDegree m ≤ N

def chapter14ExponentialTowerDegreeProfile (C : ℕ) :
    Chapter14TowerDegreeProfile C where
  totalDegree := fun m => C ^ m
  stepDegree := fun _ => C
  totalDegree_zero := by simp
  tower_degree := by
    intro m
    simp [pow_succ, Nat.mul_comm]
  step_degree_le := by
    intro m
    exact le_rfl

/- LOCAL_DEPENDENCY_GUESS: the local-field chapter supplies the realization of
  a ramification-depth invariant for a tower.  This record keeps only the
  bounded-step and unbounded-depth interface used by the diagnostic. -/
structure Chapter14LocalTowerRamificationProfile (C : ℕ) where
  stepDegree : ℕ → ℕ
  ramificationDepth : ℕ → ℕ
  step_degree_le : ∀ m : ℕ, stepDegree m ≤ C
  ramificationDepth_strictMono : StrictMono ramificationDepth

def chapter14UnboundedRamificationDepth {C : ℕ}
    (P : Chapter14LocalTowerRamificationProfile C) : Prop :=
  ∀ B : ℕ, ∃ m : ℕ, B < P.ramificationDepth m

/-! ### The Gaussian/cyclotomic example and canonical finite-place language -/

abbrev chapter14GaussianField : Type := CyclotomicField 4 ℚ

def chapter14UnramifiedAtFinitePrimes
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : Prop :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.chapter01UnramifiedAtFinitePrimes K L

def chapter14ExtensionEquivalence
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] : Prop :=
  Nonempty (L ≃ₐ[K] M)

/-! ### Common finite-compositum and nonnested-family interfaces -/

def chapter14PairwiseNonnestedFamily
    (Ω : Type*) [Field Ω] [Algebra ℚ Ω]
    (F : ℕ → IntermediateField ℚ Ω) : Prop :=
  ∀ ⦃i j : ℕ⦄, i ≠ j →
    ¬ F i ≤ F j ∧ ¬ F j ≤ F i

def chapter14BoundedDegreeFamily
    (Ω : Type*) [Field Ω] [Algebra ℚ Ω]
    (F : ℕ → IntermediateField ℚ Ω) (N : ℕ) : Prop :=
  ∀ i : ℕ, Module.finrank ℚ (F i) ≤ N

def chapter14FamilyIsNested
    (Ω : Type*) [Field Ω] [Algebra ℚ Ω]
    (F : ℕ → IntermediateField ℚ Ω) : Prop :=
  ∀ i : ℕ, F i ≤ F (i + 1)

def chapter14FamilyEventuallyConstant
    (Ω : Type*) [Field Ω] [Algebra ℚ Ω]
    (F : ℕ → IntermediateField ℚ Ω) : Prop :=
  ∃ i₀ : ℕ, ∀ j : ℕ, i₀ ≤ j → F j = F i₀

def chapter14CommonFiniteCompositumCeiling
    (Ω : Type*) [Field Ω] [NumberField Ω]
    (F : ℕ → IntermediateField ℚ Ω)
    (U : IntermediateField ℚ Ω) : Prop :=
  (∀ i : ℕ, F i ≤ U) ∧ FiniteDimensional ℚ U

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter14
