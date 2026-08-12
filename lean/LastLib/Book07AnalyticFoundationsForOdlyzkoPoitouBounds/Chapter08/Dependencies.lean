import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Topology.Algebra.Support

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08

open MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

/-!
Shared interfaces for Chapter 8.  The preceding Book 7 chapters are not present in this
workspace, so the two small interfaces below record exactly the earlier hypotheses used here:
the basic test-function conditions and the equality supplied by the explicit formula.  They are
interfaces, rather than additional assumptions built into any of the conclusions.
-/

abbrev Chapter08Degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank ℚ K

abbrev Chapter08RealPlaceCount (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrRealPlaces K

abbrev Chapter08ComplexPlaceCount (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrComplexPlaces K

def Chapter08AbsoluteDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  |(NumberField.discr K : ℝ)|

abbrev Chapter08RootDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  NumberField.rootDiscr K

def chapter08SignatureProportion (K : Type*) [Field K] [NumberField K] : ℝ :=
  (Chapter08RealPlaceCount K : ℝ) / (Chapter08Degree K : ℝ)

def Chapter08Even (F : ℝ → ℝ) : Prop :=
  ∀ x, F (-x) = F x

def Chapter08PiecewiseC2 (F : ℝ → ℝ) : Prop :=
  ∃ s : Finset ℝ, ∀ x ∉ (s : Set ℝ),
    ∃ ε : ℝ, 0 < ε ∧ ContDiffOn ℝ 2 F (Set.Ioo (x - ε) (x + ε))

def Chapter08FirstDerivativeBoundedVariation (F : ℝ → ℝ) : Prop :=
  ∃ Dleft Dright : ℝ → ℝ,
    (∀ a b : ℝ, BoundedVariationOn Dleft (Set.uIcc a b)) ∧
      (∀ a b : ℝ, BoundedVariationOn Dright (Set.uIcc a b)) ∧
      (∀ x : ℝ,
        HasDerivWithinAt F (Dright x) (Set.Ici x) x ∧
          HasDerivWithinAt F (Dleft x) (Set.Iic x) x)

def Chapter08BasicallyAdmissible (F : ℝ → ℝ) : Prop :=
  Chapter08Even F ∧
    Continuous F ∧
    HasCompactSupport F ∧
    Chapter08PiecewiseC2 F ∧
    Chapter08FirstDerivativeBoundedVariation F ∧
    F 0 = 1 ∧
    IntegrableOn (fun x : ℝ => |1 - F x| / x) (Set.Ioc 0 1)

def Chapter08PointwiseNonnegative (F : ℝ → ℝ) : Prop :=
  ∀ x, 0 ≤ F x

/- The cosine form is the real-valued restriction of the angular-frequency transform for even
functions.  It is used for positivity statements so that the order relation is canonical. -/
def chapter08CosineTransform (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, F x * Real.cos (t * x)

def chapter08FourierTransform (F : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, (F x : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))

def Chapter08PositiveType (F : ℝ → ℝ) : Prop :=
  Continuous F ∧ Integrable F ∧ ∀ t, 0 ≤ chapter08CosineTransform F t

def Chapter08GRHAdmissible (F : ℝ → ℝ) : Prop :=
  Chapter08BasicallyAdmissible F ∧
    Chapter08PointwiseNonnegative F ∧
    Chapter08PositiveType F

def Chapter08UnconditionallyAdmissible (F : ℝ → ℝ) : Prop :=
  Chapter08BasicallyAdmissible F ∧
    ∃ G : ℝ → ℝ,
      Chapter08Even G ∧
        Chapter08PointwiseNonnegative G ∧
        Chapter08PositiveType G ∧
        ∀ x, F x = G x / Real.cosh (x / 2)

def chapter08A (F : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in Set.Ioi 0, F x * Real.cosh (x / 2)

def chapter08B (F : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in Set.Ioi 0, (1 - F x) / (2 * Real.sinh (x / 2))

def chapter08C (F : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in Set.Ioi 0, (1 - F x) / (2 * Real.cosh (x / 2))

/-!
This is the local dependency guess for Theorem 6.1.  The fields are the zero and prime
contributions from that theorem; no positivity is built into the structure, since positivity is
the separate input used by the Chapter 8 lower-bound theorem.
-/
structure Chapter08ExplicitFormulaData
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) where
  basicAdmissible : Chapter08BasicallyAdmissible F
  zeroContribution : ℝ
  primeContribution : ℝ
  identity :
    Real.log (Chapter08AbsoluteDiscriminant K) =
      (Chapter08Degree K : ℝ) *
          (Real.eulerMascheroniConstant + Real.log (8 * Real.pi)) +
        (Chapter08RealPlaceCount K : ℝ) * (Real.pi / 2) -
        4 * chapter08A F -
        (Chapter08Degree K : ℝ) * chapter08B F -
        (Chapter08RealPlaceCount K : ℝ) * chapter08C F +
        zeroContribution + primeContribution

theorem chapter08_fourier_transform_eq_cosine_of_even
    {F : ℝ → ℝ} (hF : Integrable F) (heven : Chapter08Even F) (t : ℝ) :
    chapter08FourierTransform F t = (chapter08CosineTransform F t : ℂ) := by
  sorry

theorem chapter08_positive_type_iff_angular_transform_nonnegative
    {F : ℝ → ℝ} (heven : Chapter08Even F) :
    Chapter08PositiveType F ↔
      Continuous F ∧ Integrable F ∧
        ∀ t, 0 ≤ (chapter08FourierTransform F t).re ∧
          (chapter08FourierTransform F t).im = 0 := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08
