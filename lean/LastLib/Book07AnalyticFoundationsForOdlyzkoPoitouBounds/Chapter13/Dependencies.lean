import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.Section03TheShapeOfAUsefulLowerBound
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.Section04PolesZerosAndGrowth
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09.Section01UniversalOdlyzkoPoitouInequalities

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13

noncomputable section

universe u

open MeasureTheory
open NumberField
open scoped BigOperators NumberField

/-!
## Interfaces inherited from the analytic chapters

The source chapter only uses the numerical output of the explicit formula.  The
definitions below keep the analytic output an explicit, reusable interface,
while reusing the canonical number-field and nested-chain interfaces from the
earlier chapters.
-/

/-- The absolute degree of a number field, in the convention used in this chapter. -/
abbrev chapter13Degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.chapter01Degree K

/-- The number of real places divided by the absolute degree. -/
noncomputable abbrev chapter13RealProportion
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.chapter01RealProportion K

/-- The canonical root discriminant supplied by Mathlib. -/
noncomputable abbrev chapter13RootDiscriminant
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.chapter01RootDiscriminant K

/-- The positive absolute discriminant in the real normalization used by the
    root-discriminant API. -/
noncomputable abbrev chapter13AbsoluteDiscriminant
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.chapter01AbsoluteDiscriminant K

theorem chapter13_degree_pos
    (K : Type*) [Field K] [NumberField K] : 0 < chapter13Degree K := by
  sorry

theorem chapter13_realProportion_nonneg
    (K : Type*) [Field K] [NumberField K] : 0 ≤ chapter13RealProportion K := by
  sorry

theorem chapter13_realProportion_le_one
    (K : Type*) [Field K] [NumberField K] : chapter13RealProportion K ≤ 1 := by
  sorry

theorem chapter13_rootDiscriminant_pos
    (K : Type*) [Field K] [NumberField K] : 0 < chapter13RootDiscriminant K := by
  sorry

@[simp]
theorem chapter13_rootDiscriminant_eq_canonical
    (K : Type*) [Field K] [NumberField K] :
    chapter13RootDiscriminant K = NumberField.rootDiscr K :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.chapter01RootDiscriminant_eq_canonical K

/-! ### The three archimedean quantities -/

/-- The pole integral `A(F)` from (8.1). -/
def chapter13A (F : ℝ → ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), F x * Real.cosh (x / 2)

/-- The universal archimedean loss `B(F)` from (8.1). -/
def chapter13B (F : ℝ → ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), (1 - F x) / (2 * Real.sinh (x / 2))

/-- The real-place archimedean loss `C(F)` from (8.1). -/
def chapter13C (F : ℝ → ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), (1 - F x) / (2 * Real.cosh (x / 2))

/-- The logarithmic lower-bound expression in (8.2). -/
def chapter13LogLowerBound (F : ℝ → ℝ) (n : ℕ) (α : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) + α * (Real.pi / 2) -
    4 * chapter13A F / (n : ℝ) - chapter13B F - α * chapter13C F

/-- The real cosine transform, equal to the Fourier transform for an even real function. -/
def chapter13CosineTransform (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, F x * Real.cos (t * x)

/-- Positive type in the real-even convention used for test functions. -/
def chapter13PositiveType (G : ℝ → ℝ) : Prop :=
  Function.Even G ∧
    Continuous G ∧
      Integrable G ∧
        ∀ t : ℝ, 0 ≤ chapter13CosineTransform G t

/-- The finite set of possible nonsmooth points of a basically admissible function. -/
def chapter13PiecewiseC2 (F : ℝ → ℝ) : Prop :=
  ∃ s : Finset ℝ, ∀ x : ℝ, x ∉ (s : Set ℝ) → ContDiffAt ℝ 2 F x

/-- One-sided first derivatives of bounded variation. -/
def chapter13OneSidedDerivativeBoundedVariation (F : ℝ → ℝ) : Prop :=
  ∃ dLeft dRight : ℝ → ℝ,
    (∀ x : ℝ,
      HasDerivWithinAt F (dLeft x) (Set.Iic x) x ∧
        HasDerivWithinAt F (dRight x) (Set.Ici x) x) ∧
      LocallyBoundedVariationOn dLeft Set.univ ∧
      LocallyBoundedVariationOn dRight Set.univ

/-- The basic admissibility conditions used before the positivity refinements. -/
def chapter13BasicallyAdmissible (F : ℝ → ℝ) : Prop :=
  Function.Even F ∧
    Continuous F ∧
    HasCompactSupport F ∧
    F 0 = 1 ∧
    chapter13PiecewiseC2 F ∧
    chapter13OneSidedDerivativeBoundedVariation F ∧
    IntegrableOn (fun x : ℝ => |1 - F x| / x) (Set.Ioc 0 1)

/-- GRH-admissibility: pointwise and Fourier positivity in addition to basic admissibility. -/
def chapter13GRHAdmissible (F : ℝ → ℝ) : Prop :=
  chapter13BasicallyAdmissible F ∧
    (∀ x : ℝ, 0 ≤ F x) ∧
    chapter13PositiveType F

/-- Unconditional admissibility via the strip-positive `sech` factor. -/
def chapter13UnconditionallyAdmissible (F : ℝ → ℝ) : Prop :=
  chapter13BasicallyAdmissible F ∧
    ∃ G : ℝ → ℝ,
      Function.Even G ∧
        (∀ x : ℝ, 0 ≤ G x) ∧
        chapter13PositiveType G ∧
        F = fun x => G x / Real.cosh (x / 2)

/-!
The nontrivial zero predicate is the minimum GRH interface needed here.  It is
defined through the completed-zeta zero predicate from Chapter 4, rather than
through Mathlib's raw `LSeries` representation of the Dedekind zeta function:
the latter is defined to be zero away from its convergence region and is not
the analytic continuation used by the explicit formula.  The completed-zeta
predicate includes the closed critical strip, including possible boundary
zeros; the point `s = 0` is excluded as part of the pole/trivial-zero
bookkeeping.
-/
def chapter13NontrivialDedekindZetaZero
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : Prop :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.chapter04NontrivialZero K s ∧
    0 ≤ s.re ∧ s.re ≤ 1 ∧ s ≠ 0

def chapter13GRHFor (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ s : ℂ, chapter13NontrivialDedekindZetaZero K s → s.re = 1 / 2

/-!
The following records package the exact output of the explicit formula.  They
are not analytic axioms of Chapter 13: they are the local dependency seam for
the preceding Chapters 6--9.
-/

/- LOCAL_DEPENDENCY_GUESS: Chapters 6--8 should provide the analytic lower
bound field below from the explicit formula and unconditional zero positivity. -/
structure Chapter13UnconditionalAnalyticBound (F : ℝ → ℝ) : Prop where
  admissible : chapter13UnconditionallyAdmissible F
  lower_bound :
    ∀ (K : Type u) [Field K] [NumberField K],
      Real.log (chapter13RootDiscriminant K) ≥
        chapter13LogLowerBound F (chapter13Degree K) (chapter13RealProportion K)

/- LOCAL_DEPENDENCY_GUESS: Chapters 6--7 should provide the GRH lower bound
below, with `chapter13GRHFor K` supplied by the global GRH assumption. -/
structure Chapter13GRHAnalyticBound (F : ℝ → ℝ) : Prop where
  admissible : chapter13GRHAdmissible F
  lower_bound :
    ∀ (K : Type u) [Field K] [NumberField K],
      chapter13GRHFor K →
        Real.log (chapter13RootDiscriminant K) ≥
          chapter13LogLowerBound F (chapter13Degree K) (chapter13RealProportion K)

def chapter13FieldwiseAnalyticBound (F : ℝ → ℝ)
    (K : Type u) [Field K] [NumberField K] : Prop :=
    Chapter13UnconditionalAnalyticBound.{u} F ∨
    (Chapter13GRHAnalyticBound.{u} F ∧ chapter13GRHFor K)

/- The source derives positivity of the pole integral from admissibility: the
   test function is nonnegative, continuous, and equals one at the origin.
   Keep that derived fact separate from the explicit-formula output record. -/
theorem chapter13A_pos_of_admissible
    (F : ℝ → ℝ)
    (hF : chapter13UnconditionallyAdmissible F ∨ chapter13GRHAdmissible F) :
    0 < chapter13A F := by
  sorry

/- The source theorem makes one global choice: either the unconditional
   estimate is used for every field, or GRH is assumed for every field under
   consideration.  This wrapper keeps that quantifier outside the fieldwise
   lower-bound interface. -/
def chapter13GlobalAnalyticBound (F : ℝ → ℝ) : Prop :=
  Chapter13UnconditionalAnalyticBound.{u} F ∨
    (Chapter13GRHAnalyticBound.{u} F ∧
      ∀ (K : Type u) [Field K] [NumberField K], chapter13GRHFor K)

theorem chapter13_log_rootDiscriminant_lower_bound
    (F : ℝ → ℝ) (K : Type u) [Field K] [NumberField K]
    (hF : chapter13FieldwiseAnalyticBound F K) :
    Real.log (chapter13RootDiscriminant K) ≥
      chapter13LogLowerBound F (chapter13Degree K) (chapter13RealProportion K) := by
  rcases hF with hF | ⟨hF, hGRH⟩
  · exact hF.lower_bound K
  · exact hF.lower_bound K hGRH

theorem chapter13_global_log_rootDiscriminant_lower_bound
    (F : ℝ → ℝ) (hF : chapter13GlobalAnalyticBound.{u} F) :
    ∀ (K : Type u) [Field K] [NumberField K],
      Real.log (chapter13RootDiscriminant K) ≥
        chapter13LogLowerBound F (chapter13Degree K) (chapter13RealProportion K) := by
  intro K _ _
  rcases hF with hF | ⟨hF, hGRH⟩
  · exact hF.lower_bound K
  · exact hF.lower_bound K (hGRH K)

theorem chapter13_fieldwiseAnalyticBound_of_global
    (F : ℝ → ℝ) (hF : chapter13GlobalAnalyticBound.{u} F) :
    ∀ (K : Type u) [Field K] [NumberField K],
      chapter13FieldwiseAnalyticBound F K := by
  sorry

theorem chapter13_logLowerBound_mono
    (F : ℝ → ℝ) {m n : ℕ} {α β : ℝ}
    (hA : 0 < chapter13A F) (hm : 0 < m) (hmn : m ≤ n)
    (hC : chapter13C F ≤ Real.pi / 2) (hα : α ≤ β) :
    chapter13LogLowerBound F m α ≤ chapter13LogLowerBound F n β := by
  sorry

theorem chapter13_log_rootDiscriminant_le_of_ceiling
    (K : Type*) [Field K] [NumberField K] {U : ℝ}
    (hU : 0 < U) (hceil : chapter13RootDiscriminant K ≤ U) :
    Real.log (chapter13RootDiscriminant K) ≤ Real.log U := by
  sorry

/- The focused Chapter 9 threshold theorem is bridged here to the canonical
   Chapter 13 degree, real-proportion, and root-discriminant interfaces.  The
   absence of a positivity hypothesis on `U` is intentional: when `U ≤ 0`,
   the ceiling is vacuous because root discriminants are positive. -/
def chapter13HasUnconditionalDegreeCap (U α₀ : ℝ) : Prop :=
  ∃ N : ℕ, ∀ (K : Type*) [Field K] [NumberField K],
    chapter13RootDiscriminant K ≤ U →
      α₀ ≤ chapter13RealProportion K →
      chapter13Degree K < N

theorem chapter13_threshold_principle
    {U α₀ : ℝ} (hU : U < 4 * Real.pi * Real.exp
      (Real.eulerMascheroniConstant + α₀))
    (hα₀ : 0 ≤ α₀) (hα₀' : α₀ ≤ 1) :
    chapter13HasUnconditionalDegreeCap U α₀ := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: The source's tower statement uses the threshold
   inequality without
   repeating the harmless range assumptions on `α₀`.  If `α₀ > 1` the class
   of fields being bounded is empty, while if `α₀ < 0` the lower signature
   bound can be strengthened to zero. -/
theorem chapter13_threshold_principle_general
    {U α₀ : ℝ} (hU : U < 4 * Real.pi * Real.exp
      (Real.eulerMascheroniConstant + α₀)) :
    chapter13HasUnconditionalDegreeCap U α₀ := by
  sorry

/-! ### Canonical relative discriminant and local-cost interfaces -/

/-- The relative discriminant ideal, obtained as the relative norm of the different. -/
noncomputable def chapter13RelativeDiscriminantIdeal
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [IsScalarTower ℚ F L]
    [Module.Finite (𝓞 F) (𝓞 L)] : Ideal (𝓞 F) :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.chapter01RelativeDiscriminantIdeal F L

/-- The absolute norm of the relative discriminant ideal. -/
noncomputable def chapter13RelativeDiscriminantNorm
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [IsScalarTower ℚ F L]
    [Module.Finite (𝓞 F) (𝓞 L)] : ℕ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.chapter01RelativeDifferentNorm F L

/-- The relative different contribution after taking the absolute degree root. -/
noncomputable def chapter13RelativeDifferentContribution
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [IsScalarTower ℚ F L]
    [Module.Finite (𝓞 F) (𝓞 L)] : ℝ :=
  Real.rpow (chapter13RelativeDiscriminantNorm F L : ℝ)
    ((chapter13Degree L : ℝ)⁻¹)

/- LOCAL_DEPENDENCY_GUESS: this is the real-valued form of the earlier
Chapter 01 tower formula, with the relative norm of the different identified
with the relative discriminant ideal. -/
theorem chapter13_rootDiscriminant_tower_formula
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [IsScalarTower ℚ F L]
    [Module.Finite (𝓞 F) (𝓞 L)] :
    chapter13RootDiscriminant L =
      chapter13RootDiscriminant F * chapter13RelativeDifferentContribution F L := by
  sorry

/- The earlier chapter supplies the canonical finite-place unramified
   predicate and its relative-different characterization.  Re-export the
   bridge under the Chapter 13 names so tower compatibility can use arithmetic
   unramifiedness rather than an unmotivated equality predicate. -/
def chapter13UnramifiedAtFinitePrimes
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] : Prop :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.chapter01UnramifiedAtFinitePrimes F L

theorem chapter13_unramifiedAtFinitePrimes_iff_relativeDiscriminantNorm_eq_one
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [IsScalarTower ℚ F L]
    [Module.Finite (𝓞 F) (𝓞 L)] :
    chapter13UnramifiedAtFinitePrimes F L ↔
      chapter13RelativeDiscriminantNorm F L = 1 := by
  exact
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.chapter01_unramifiedAtFinitePrimes_iff_relativeDifferentNorm_eq_one F L

theorem chapter13_rootDiscriminant_eq_of_unramifiedAtFinitePrimes
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [IsScalarTower ℚ F L]
    [Module.Finite (𝓞 F) (𝓞 L)]
    (hunramified : chapter13UnramifiedAtFinitePrimes F L) :
    chapter13RootDiscriminant L = chapter13RootDiscriminant F := by
  exact
    (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.chapter01_rootDiscriminant_eq_iff_unramified F L).mpr hunramified

/-- The norm of a finite place, used in the product of local different costs. -/
noncomputable def chapter13FinitePlaceNorm
    {F : Type*} [Field F] [NumberField F]
    (v : NumberField.FinitePlace F) : ℝ :=
  (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ)

/-- A finite list of normalized local different costs. -/
structure Chapter13LocalDifferentCostProfile
    (F : Type*) [Field F] [NumberField F] where
  index : Type*
  [fintype : Fintype index]
  place : index → NumberField.FinitePlace F
  place_injective : Function.Injective place
  cost : index → ℝ
  cost_nonneg : ∀ i, 0 ≤ cost i

attribute [instance] Chapter13LocalDifferentCostProfile.fintype

/-- The typical absolute ceiling in (13.3), for a finite support of local costs. -/
noncomputable def chapter13AbsoluteCeilingFromLocalCosts
    (F : Type*) [Field F] [NumberField F]
    (P : Chapter13LocalDifferentCostProfile F) : ℝ := by
  letI := P.fintype
  exact chapter13RootDiscriminant F *
    ∏ i : P.index,
      Real.rpow (chapter13FinitePlaceNorm (P.place i))
        (P.cost i / (chapter13Degree F : ℝ))

@[simp]
theorem chapter13_absolute_ceiling_from_local_costs_eq_product
    (F : Type*) [Field F] [NumberField F]
    (P : Chapter13LocalDifferentCostProfile F) :
    chapter13AbsoluteCeilingFromLocalCosts F P =
      chapter13RootDiscriminant F *
        ∏ i : P.index,
          Real.rpow (chapter13FinitePlaceNorm (P.place i))
            (P.cost i / (chapter13Degree F : ℝ)) := by
  rfl

theorem chapter13_finite_place_norm_pos
    {F : Type*} [Field F] [NumberField F]
    (v : NumberField.FinitePlace F) :
    0 < chapter13FinitePlaceNorm v := by
  sorry

theorem chapter13_absolute_ceiling_from_local_costs_pos
    (F : Type*) [Field F] [NumberField F]
    (P : Chapter13LocalDifferentCostProfile F) :
    0 < chapter13AbsoluteCeilingFromLocalCosts F P := by
  sorry

theorem chapter13_rootDiscriminant_eq_of_relative_discriminant_ideal_eq_one
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [IsScalarTower ℚ F L]
    [Module.Finite (𝓞 F) (𝓞 L)]
    (hunramified : chapter13RelativeDiscriminantIdeal F L = 1) :
    chapter13RootDiscriminant L = chapter13RootDiscriminant F := by
  sorry

theorem chapter13_absolute_degree_eq_base_degree_mul_relative_degree
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [Algebra ℚ F] [Algebra ℚ L] [IsScalarTower ℚ F L] :
    chapter13Degree L = chapter13Degree F * Module.finrank F L := by
  sorry

theorem chapter13_relative_degree_lt_of_absolute_degree_lt
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [Algebra ℚ F] [Algebra ℚ L] [IsScalarTower ℚ F L]
    {N : ℕ} (hN : chapter13Degree L < N) :
    (Module.finrank F L : ℝ) < N / (chapter13Degree F : ℝ) := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13
