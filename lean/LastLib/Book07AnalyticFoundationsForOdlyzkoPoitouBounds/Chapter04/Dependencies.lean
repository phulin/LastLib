import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02.Core
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03
open scoped BigOperators ComplexConjugate ENNReal Classical NumberField nonZeroDivisors

/-!
Shared interfaces for Chapter 4.  The definitions below retain the book's
normalizations while reusing the canonical number-field, fractional-ideal,
Minkowski-space, and Dedekind-zeta objects from Chapters 2 and 3.
-/

/-! ## 4.1. Archimedean local factors -/

/-- The degree used in the completed-zeta formulas. -/
abbrev chapter04Degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  chapter02Degree K

/-- The real and complex place counts used in the completed-zeta formulas. -/
noncomputable abbrev chapter04RealPlaces (K : Type*) [Field K] [NumberField K] : ℕ :=
  chapter02RealPlaces K

noncomputable abbrev chapter04ComplexPlaces (K : Type*) [Field K] [NumberField K] : ℕ :=
  chapter02ComplexPlaces K

/-- The absolute discriminant convention used throughout this chapter. -/
noncomputable abbrev chapter04AbsoluteDiscriminant
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  chapter02AbsoluteDiscriminant K

theorem chapter04_signature_degree (K : Type*) [Field K] [NumberField K] :
    chapter04RealPlaces K + 2 * chapter04ComplexPlaces K = chapter04Degree K := by
  exact chapter02_signature_degree K

theorem chapter04_absolute_discriminant_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter04AbsoluteDiscriminant K := by
  exact chapter02_absolute_discriminant_pos K

/-- The real gamma factor with the book's exact normalization. -/
noncomputable def chapter04GammaReal (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)

/-- The complex gamma factor with the book's exact normalization. -/
noncomputable def chapter04GammaComplex (s : ℂ) : ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s

/-- The product of all archimedean local factors. -/
noncomputable def chapter04ArchimedeanFactor
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  chapter04GammaReal s ^ chapter04RealPlaces K *
    chapter04GammaComplex s ^ chapter04ComplexPlaces K

/-- The completed Dedekind zeta function in the book's normalization. -/
noncomputable def chapter04CompletedDedekindZeta
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (chapter04AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
    chapter04ArchimedeanFactor K s * chapter03DedekindZeta K s

/-- The real Gaussian Mellin integrand, with the displayed `dx / |x|` measure
    represented in the integrand. -/
noncomputable def chapter04RealGaussianMellinIntegrand
    (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) *
    ((|x| : ℝ) : ℂ) ^ s / ((|x| : ℝ) : ℂ)

/-- The complex Gaussian Mellin integrand, with angular measure `dx dy / π`. -/
noncomputable def chapter04ComplexGaussianMellinIntegrand
    (s : ℂ) (z : ℂ) : ℂ :=
  Complex.exp (-((2 : ℂ) * (Real.pi : ℂ)) * ((‖z‖ ^ 2 : ℝ) : ℂ)) *
    ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s /
      ((Real.pi : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ))

noncomputable def chapter04RealGaussianMellin (s : ℂ) : ℂ :=
  ∫ x : ℝ, chapter04RealGaussianMellinIntegrand s x ∂volume

noncomputable def chapter04ComplexGaussianMellin (s : ℂ) : ℂ :=
  ∫ z : ℂ, chapter04ComplexGaussianMellinIntegrand s z ∂volume

/-! ## 4.2. Theta kernels and dual lattices -/

/-- The mixed Minkowski space used for the theta kernels. -/
abbrev chapter04MinkowskiSpace (K : Type*) [Field K] [NumberField K] :=
  chapter02MinkowskiSpace K

/-- Fractional ideals in the number-field fraction field. -/
abbrev Chapter04FractionalIdeal (K : Type*) [Field K] [NumberField K] :=
  FractionalIdeal (𝓞 K)⁰ K

/-- Nonzero fractional ideals represented by the canonical unit type. -/
abbrev Chapter04NonzeroFractionalIdeal
    (K : Type*) [Field K] [NumberField K] :=
  (Chapter04FractionalIdeal K)ˣ

/-- The real absolute norm of a fractional ideal. -/
noncomputable def chapter04FractionalIdealNorm
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04FractionalIdeal K) : ℝ :=
  (FractionalIdeal.absNorm a : ℝ)

theorem chapter04_fractional_ideal_norm_eq_chapter02
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) :
    chapter04FractionalIdealNorm K (a : Chapter04FractionalIdeal K) =
      chapter02FractionalIdealNorm K a := by
  rfl

/-- The positive trace pairing in the mixed coordinates. -/
noncomputable def chapter04TracePairing
    (K : Type*) [Field K] [NumberField K]
    (x y : chapter04MinkowskiSpace K) : ℝ :=
  (∑ w : {w : InfinitePlace K // IsReal w}, x.1 w * y.1 w) +
    2 * ∑ w : {w : InfinitePlace K // IsComplex w},
      ((x.2 w) * star (y.2 w)).re

noncomputable def chapter04MinkowskiNormSq
    (K : Type*) [Field K] [NumberField K]
    (x : chapter04MinkowskiSpace K) : ℝ :=
  chapter04TracePairing K x x

theorem chapter04_trace_pairing_self_nonneg
    (K : Type*) [Field K] [NumberField K]
    (x : chapter04MinkowskiSpace K) :
    0 ≤ chapter04TracePairing K x x := by
  sorry

theorem chapter04_trace_pairing_self_eq_zero_iff
    (K : Type*) [Field K] [NumberField K]
    (x : chapter04MinkowskiSpace K) :
    chapter04TracePairing K x x = 0 ↔ x = 0 := by
  sorry

/-- Ordinary and self-dual covolumes differ only by the factor coming from
    doubling Lebesgue measure in each complex coordinate. -/
noncomputable def chapter04SelfDualCovolume
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04FractionalIdeal K) : ℝ :=
  Real.sqrt (chapter04AbsoluteDiscriminant K) *
    chapter04FractionalIdealNorm K a

noncomputable def chapter04SelfDualMeasure
    (K : Type*) [Field K] [NumberField K] :
    Measure (chapter04MinkowskiSpace K) :=
  ((2 : ℝ≥0∞) ^ chapter04ComplexPlaces K) • volume

noncomputable def chapter04FractionalIdealImage
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04FractionalIdeal K) : Set (chapter04MinkowskiSpace K) :=
  {x | ∃ z : K, z ∈ (a : Set K) ∧ NumberField.mixedEmbedding K z = x}

noncomputable def chapter04NormalizationFactor
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04FractionalIdeal K) : ℝ :=
  Real.rpow (chapter04SelfDualCovolume K a)
    (-(1 / (chapter04Degree K : ℝ)))

noncomputable def chapter04NormalizedIdealLattice
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04FractionalIdeal K) : Set (chapter04MinkowskiSpace K) :=
  Set.image (fun x : chapter04MinkowskiSpace K =>
    chapter04NormalizationFactor K a • x) (chapter04FractionalIdealImage K a)

theorem chapter04_fractional_ideal_image_eq_canonical
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) :
    chapter04FractionalIdealImage K (a : Chapter04FractionalIdeal K) =
      (chapter02FractionalIdealLattice K a : Set (chapter04MinkowskiSpace K)) := by
  sorry

/-- The different, viewed as a fractional ideal. -/
noncomputable def chapter04DifferentFractionalIdeal
    (K : Type*) [Field K] [NumberField K] : Chapter04FractionalIdeal K :=
  (differentIdeal ℤ (𝓞 K) : Chapter04FractionalIdeal K)

/-- The trace-dual fractional ideal `𝔡_K⁻¹ 𝔞⁻¹`. -/
noncomputable def chapter04DualFractionalIdeal
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04FractionalIdeal K) : Chapter04FractionalIdeal K :=
  (chapter04DifferentFractionalIdeal K)⁻¹ * a⁻¹

noncomputable def chapter04CoordinateConjugation
    (K : Type*) [Field K] [NumberField K]
    (x : chapter04MinkowskiSpace K) : chapter04MinkowskiSpace K :=
  (x.1, fun v => star (x.2 v))

theorem chapter04_coordinate_conjugation_isometry
    (K : Type*) [Field K] [NumberField K]
    (x : chapter04MinkowskiSpace K) :
    chapter04MinkowskiNormSq K (chapter04CoordinateConjugation K x) =
      chapter04MinkowskiNormSq K x := by
  sorry

/- The Fourier dual below is taken with respect to the trace pairing and the
   integer character lattice.  This keeps the book's coordinate dual distinct
   from the algebraic inverse/different construction above. -/
noncomputable def chapter04LatticeDual
    (K : Type*) [Field K] [NumberField K]
    (L : Set (chapter04MinkowskiSpace K)) : Set (chapter04MinkowskiSpace K) :=
  {y | ∀ x ∈ L, ∃ m : ℤ, chapter04TracePairing K x y = (m : ℝ)}

theorem chapter04_mem_lattice_dual_iff
    (K : Type*) [Field K] [NumberField K]
    (L : Set (chapter04MinkowskiSpace K))
    (y : chapter04MinkowskiSpace K) :
    y ∈ chapter04LatticeDual K L ↔
      ∀ x ∈ L, ∃ m : ℤ, chapter04TracePairing K x y = (m : ℝ) := by
  rfl

theorem chapter04_dual_fractional_ideal_ne_zero
    (K : Type*) [Field K] [NumberField K]
    {a : Chapter04FractionalIdeal K} (ha : a ≠ 0) :
    chapter04DualFractionalIdeal K a ≠ 0 := by
  sorry

noncomputable def chapter04DualNonzeroFractionalIdeal
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) :
    Chapter04NonzeroFractionalIdeal K :=
  Units.mk0 (chapter04DualFractionalIdeal K (a : Chapter04FractionalIdeal K))
    (chapter04_dual_fractional_ideal_ne_zero K (Units.ne_zero a))

theorem chapter04_dual_nonzero_fractional_ideal_coe
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) :
    (chapter04DualNonzeroFractionalIdeal K a : Chapter04FractionalIdeal K) =
      chapter04DualFractionalIdeal K (a : Chapter04FractionalIdeal K) := by
  rfl

theorem chapter04_dual_dual_fractional_ideal
    (K : Type*) [Field K] [NumberField K]
    {a : Chapter04FractionalIdeal K} (ha : a ≠ 0) :
    chapter04DualFractionalIdeal K
        (chapter04DualFractionalIdeal K a) = a := by
  sorry

theorem chapter04_dual_fractional_ideal_norm
    (K : Type*) [Field K] [NumberField K]
    {a : Chapter04FractionalIdeal K} (ha : a ≠ 0) :
    chapter04FractionalIdealNorm K (chapter04DualFractionalIdeal K a) =
      (chapter04AbsoluteDiscriminant K)⁻¹ *
        (chapter04FractionalIdealNorm K a)⁻¹ := by
  sorry

theorem chapter04_self_dual_covolume_dual
    (K : Type*) [Field K] [NumberField K]
    {a : Chapter04FractionalIdeal K} (ha : a ≠ 0) :
    chapter04SelfDualCovolume K (chapter04DualFractionalIdeal K a) =
      (chapter04SelfDualCovolume K a)⁻¹ := by
  sorry

/-- Positive diagonal archimedean scalings of determinant one. -/
structure Chapter04ArchimedeanScaling
    (K : Type*) [Field K] [NumberField K] where
  scale : InfinitePlace K → ℝ
  positive : ∀ v, 0 < scale v
  determinant_one : ∏ v : InfinitePlace K, scale v ^ v.mult = 1

/- The scaling structure carries the measurable structure induced by its
   coordinate function, so abstract Haar measures on `Y` can be stated
   without introducing a second book-facing topology. -/
noncomputable instance chapter04ArchimedeanScalingMeasurableSpace
    (K : Type*) [Field K] [NumberField K] :
    MeasurableSpace (Chapter04ArchimedeanScaling K) :=
  MeasurableSpace.comap (fun y => y.scale)
    (⊤ : MeasurableSpace (InfinitePlace K → ℝ))

abbrev chapter04Y (K : Type*) [Field K] [NumberField K] :=
  Chapter04ArchimedeanScaling K

noncomputable def chapter04YOne
    (K : Type*) [Field K] [NumberField K] : chapter04Y K :=
  { scale := fun _ => 1
    positive := by intro v; norm_num
    determinant_one := by simp }

noncomputable def chapter04YMul
    (K : Type*) [Field K] [NumberField K]
    (y z : chapter04Y K) : chapter04Y K :=
  { scale := fun v => y.scale v * z.scale v
    positive := by intro v; exact mul_pos (y.positive v) (z.positive v)
    determinant_one := by
      sorry }

noncomputable def chapter04YInv
    (K : Type*) [Field K] [NumberField K]
    (y : chapter04Y K) : chapter04Y K :=
  { scale := fun v => (y.scale v)⁻¹
    positive := by intro v; exact inv_pos.mpr (y.positive v)
    determinant_one := by
      sorry }

theorem chapter04_y_mul_apply
    (K : Type*) [Field K] [NumberField K]
    (y z : chapter04Y K) (v : InfinitePlace K) :
    (chapter04YMul K y z).scale v = y.scale v * z.scale v :=
  rfl

theorem chapter04_y_inv_apply
    (K : Type*) [Field K] [NumberField K]
    (y : chapter04Y K) (v : InfinitePlace K) :
    (chapter04YInv K y).scale v = (y.scale v)⁻¹ :=
  rfl

theorem chapter04_y_mul_inv
    (K : Type*) [Field K] [NumberField K]
    (y : chapter04Y K) :
    chapter04YMul K y (chapter04YInv K y) = chapter04YOne K := by
  sorry

theorem chapter04_y_inv_mul
    (K : Type*) [Field K] [NumberField K]
    (y : chapter04Y K) :
    chapter04YMul K (chapter04YInv K y) y = chapter04YOne K := by
  sorry

/-- The action of an archimedean scaling on the mixed Minkowski coordinates. -/
noncomputable def chapter04YAction
    (K : Type*) [Field K] [NumberField K]
    (y : chapter04Y K) (x : chapter04MinkowskiSpace K) :
    chapter04MinkowskiSpace K :=
  (fun v => y.scale v.1 * x.1 v,
   fun v => (y.scale v.1) • x.2 v)

theorem chapter04_y_action_one
    (K : Type*) [Field K] [NumberField K]
    (x : chapter04MinkowskiSpace K) :
    chapter04YAction K (chapter04YOne K) x = x := by
  sorry

theorem chapter04_y_action_mul
    (K : Type*) [Field K] [NumberField K]
    (y z : chapter04Y K) (x : chapter04MinkowskiSpace K) :
    chapter04YAction K (chapter04YMul K y z) x =
      chapter04YAction K y (chapter04YAction K z x) := by
  sorry

theorem chapter04_y_action_inv_isometry
    (K : Type*) [Field K] [NumberField K]
    (y : chapter04Y K) (x : chapter04MinkowskiSpace K) :
    chapter04MinkowskiNormSq K
        (chapter04YAction K (chapter04YInv K y) x) =
      chapter04MinkowskiNormSq K x := by
  sorry

/-- The determinant-scale coordinate factor `t^(1/n)`. -/
noncomputable def chapter04DeterminantScale
    (K : Type*) [Field K] [NumberField K] (t : ℝ) : ℝ :=
  Real.rpow t (1 / (chapter04Degree K : ℝ))

theorem chapter04_determinant_scale_pos
    (K : Type*) [Field K] [NumberField K] {t : ℝ} (ht : 0 < t) :
    0 < chapter04DeterminantScale K t := by
  sorry

theorem chapter04_determinant_scale_pow_degree
    (K : Type*) [Field K] [NumberField K] {t : ℝ} (ht : 0 < t) :
    (chapter04DeterminantScale K t) ^ chapter04Degree K = t := by
  sorry

noncomputable def chapter04ThetaTerm
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04FractionalIdeal K) (t : ℝ) (y : chapter04Y K)
    (x : {x : chapter04MinkowskiSpace K //
      x ∈ chapter04NormalizedIdealLattice K a}) : ℝ :=
  Real.exp (-Real.pi * chapter04MinkowskiNormSq K
    (chapter04YAction K y
      (chapter04DeterminantScale K t • (x : chapter04MinkowskiSpace K))))

noncomputable def chapter04Theta
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04FractionalIdeal K) (t : ℝ) (y : chapter04Y K) : ℝ :=
  ∑' x : {x : chapter04MinkowskiSpace K //
    x ∈ chapter04NormalizedIdealLattice K a},
    chapter04ThetaTerm K a t y x

noncomputable def chapter04ThetaDerivativeTerm
    (k : ℕ) (K : Type*) [Field K] [NumberField K]
    (a : Chapter04FractionalIdeal K) (y : chapter04Y K)
    (x : {x : chapter04MinkowskiSpace K //
      x ∈ chapter04NormalizedIdealLattice K a}) (t : ℝ) : ℝ :=
  match k with
  | 0 => chapter04ThetaTerm K a t y x
  | k + 1 => deriv (fun u : ℝ =>
      chapter04ThetaDerivativeTerm k K a y x u) t

def chapter04ThetaSeriesAndDerivativeLocallyUniform
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04FractionalIdeal K) : Prop :=
  ∀ k : ℕ, ∀ y : chapter04Y K, ∀ δ R : ℝ, 0 < δ → δ ≤ R →
    SummableUniformlyOn
      (fun x : {x : chapter04MinkowskiSpace K //
        x ∈ chapter04NormalizedIdealLattice K a} =>
        fun t : ℝ => chapter04ThetaDerivativeTerm k K a y x t)
      (Set.Icc δ R)

/-- The unit logarithm hyperplane, in the determinant-weighted coordinates. -/
def chapter04UnitLogHyperplane
    (K : Type*) [Field K] [NumberField K] :
    Submodule ℝ (InfinitePlace K → ℝ) where
  carrier := {t | ∑ v : InfinitePlace K, (v.mult : ℝ) * t v = 0}
  zero_mem' := by simp
  add_mem' := by sorry
  smul_mem' := by sorry

noncomputable def chapter04UnitLogVector
    (K : Type*) [Field K] [NumberField K]
    (u : (𝓞 K)ˣ) : InfinitePlace K → ℝ :=
  fun v => Real.log (v (u : K))

noncomputable def chapter04UnitScaling
    (K : Type*) [Field K] [NumberField K]
    (u : (𝓞 K)ˣ) : chapter04Y K :=
  { scale := fun v => v (u : K)
    positive := by
      intro v
      exact InfinitePlace.pos_iff.mpr (NumberField.Units.coe_ne_zero u)
    determinant_one := by
      sorry }

noncomputable def chapter04UnitLogEmbedding
    (K : Type*) [Field K] [NumberField K] :
    Additive ((𝓞 K)ˣ) →+ chapter04UnitLogHyperplane K where
  toFun u :=
    { val := chapter04UnitLogVector K u.toMul
      property := by
        sorry }
  map_zero' := by
    ext v
    simp [chapter04UnitLogVector]
  map_add' u v := by sorry

noncomputable def chapter04UnitLogLattice
    (K : Type*) [Field K] [NumberField K] :
    Submodule ℤ (chapter04UnitLogHyperplane K) :=
  Submodule.span ℤ (Set.range (chapter04UnitLogEmbedding K))

/-- A normalized Haar fundamental domain for the unit action on `Y`. -/
structure Chapter04UnitFundamentalDomain
    (K : Type*) [Field K] [NumberField K] where
  carrier : Set (chapter04Y K)
  measure : Measure (chapter04Y K)
  measurable_carrier : MeasurableSet carrier
  normalized_volume : measure carrier = 1
  left_invariant : ∀ g : chapter04Y K, ∀ s : Set (chapter04Y K),
    MeasurableSet s →
      measure (chapter04YMul K g '' s) = measure s
  inverse_invariant : ∀ s : Set (chapter04Y K), MeasurableSet s →
    measure (chapter04YInv K '' s) = measure s
  unit_fundamental : ∀ y : chapter04Y K, ∃ u : (𝓞 K)ˣ, ∃ p ∈ carrier,
    y = chapter04YMul K (chapter04UnitScaling K u) p

noncomputable def chapter04ThetaAverage
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    (a : Chapter04FractionalIdeal K) (t : ℝ) : ℝ :=
  ∫ y in D.carrier, chapter04Theta K a t y ∂D.measure

noncomputable def chapter04MellinKernel (s : ℂ) (t : ℝ) : ℂ :=
  if 0 < t then (t : ℂ) ^ s / (t : ℂ) else 0

noncomputable def chapter04ThetaMellinIntegral
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    (a : Chapter04FractionalIdeal K) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ),
    (∫ y in D.carrier,
      ((chapter04Theta K a t y - 1 : ℝ) : ℂ) *
        chapter04MellinKernel s t ∂D.measure) ∂volume

/- DEPENDENCY_GUESS: The source leaves `c_K` dependent on Haar normalization
   and roots of unity.  This draft fixes the remaining normalization by the
   canonical torsion order; the later fixup pass should replace this body if
   the project chooses a different angular/Haar convention. -/
/- The positive orbit multiplicity left unspecified by the source's Haar
   convention. -/
noncomputable def chapter04MellinConstant
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  NumberField.Units.torsionOrder K

theorem chapter04_mellin_constant_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter04MellinConstant K := by
  exact Nat.cast_pos.mpr (NumberField.Units.torsionOrder_pos K)

theorem chapter04_mellin_constant_ne_zero
    (K : Type*) [Field K] [NumberField K] :
    chapter04MellinConstant K ≠ 0 :=
  (chapter04_mellin_constant_pos K).ne'

noncomputable def chapter04PartialZeta
    (K : Type*) [Field K] [NumberField K]
    (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  ∑' I : Chapter03IntegralIdeal K,
    if ClassGroup.mk0 I = C then chapter03IdealTerm s I else 0

noncomputable def chapter04InverseIdealClass
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) : ClassGroup (𝓞 K) :=
  (ClassGroup.mk K a)⁻¹
