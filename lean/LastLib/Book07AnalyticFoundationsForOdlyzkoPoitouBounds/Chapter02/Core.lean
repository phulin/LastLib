import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.RingTheory.TensorProduct.Basic

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02

noncomputable section

open Filter MeasureTheory NumberField NumberField.InfinitePlace
open scoped BigOperators ENNReal NNReal NumberField nonZeroDivisors TensorProduct Topology Classical

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! # Chapter 2: The geometric baseline

The source chapter is expressed using the mixed Minkowski space
`ℝ ^ r₁ × ℂ ^ r₂`.  The pinned Mathlib API uses the canonical mixed embedding,
its integral and fractional-ideal lattices, and the corresponding covolume
theorems.  The declarations below retain the book-facing names and display
the normalizations needed by the later analytic chapters.
-/

/-! ## 2.1 The Minkowski lattice -/

/-- The degree used in the geometric formulas. -/
abbrev chapter02Degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank ℚ K

/-- The number of real infinite places. -/
noncomputable abbrev chapter02RealPlaces (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrRealPlaces K

/-- The number of complex infinite places. -/
noncomputable abbrev chapter02ComplexPlaces (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrComplexPlaces K

/-- The signature `(r₁, r₂)` of a number field. -/
def chapter02Signature (K : Type*) [Field K] [NumberField K] : ℕ × ℕ :=
  (chapter02RealPlaces K, chapter02ComplexPlaces K)

/-- The degree/signature relation `n = r₁ + 2 r₂`. -/
theorem chapter02_signature_degree (K : Type*) [Field K] [NumberField K] :
    chapter02RealPlaces K + 2 * chapter02ComplexPlaces K = chapter02Degree K := by
  sorry

/-- The absolute discriminant convention used by the book. -/
noncomputable def chapter02AbsoluteDiscriminant
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  |(NumberField.discr K : ℝ)|

/-- The absolute discriminant is strictly positive. -/
theorem chapter02_absolute_discriminant_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter02AbsoluteDiscriminant K := by
  sorry

/-- The mixed model of `K ⊗[ℚ] ℝ` used for the Minkowski lattice. -/
abbrev chapter02MinkowskiSpace (K : Type*) [Field K] [NumberField K] :=
  NumberField.mixedEmbedding.mixedSpace K

/-- The tensor-product model appearing in the source. -/
abbrev chapter02TensorSpace (K : Type*) [Field K] [NumberField K] :=
  K ⊗[ℚ] ℝ

/- The source's tensor-product identification is exposed as an interface;
   all volume calculations below use the canonical mixed-space model. -/
noncomputable def chapter02_tensor_space_equiv (K : Type*) [Field K] [NumberField K] :
    chapter02TensorSpace K ≃ₗ[ℝ] chapter02MinkowskiSpace K := by
  sorry

/-- The mixed space has the expected real dimension. -/
theorem chapter02_minkowski_space_finrank
    (K : Type*) [Field K] [NumberField K] :
    Module.finrank ℝ (chapter02MinkowskiSpace K) = chapter02Degree K := by
  sorry

/-- Ordinary two-dimensional Lebesgue measure on each complex coordinate. -/
abbrev chapter02ComplexCoordinateMeasure : MeasureTheory.Measure ℂ := volume

/-- The image of `𝓞 K` in mixed Minkowski space. -/
abbrev chapter02IntegerLattice
    (K : Type*) [Field K] [NumberField K] :
    Submodule ℤ (chapter02MinkowskiSpace K) :=
  NumberField.mixedEmbedding.integerLattice K

/-- The integral lattice is a genuine `ℤ`-lattice in the mixed space. -/
theorem chapter02_integer_lattice_isZLattice
    (K : Type*) [Field K] [NumberField K] :
    IsZLattice ℝ (chapter02IntegerLattice K) := by
  infer_instance

/-- A nonzero fractional ideal, represented by the canonical unit type. -/
abbrev chapter02NonzeroFractionalIdeal
    (K : Type*) [Field K] [NumberField K] :=
  (FractionalIdeal (𝓞 K)⁰ K)ˣ

/-- The real-valued norm of a nonzero fractional ideal. -/
noncomputable def chapter02FractionalIdealNorm
    (K : Type*) [Field K] [NumberField K]
    (I : chapter02NonzeroFractionalIdeal K) : ℝ :=
  (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)

/-- The fractional-ideal lattice in the mixed space. -/
abbrev chapter02FractionalIdealLattice
    (K : Type*) [Field K] [NumberField K]
    (I : chapter02NonzeroFractionalIdeal K) :
    Submodule ℤ (chapter02MinkowskiSpace K) :=
  NumberField.mixedEmbedding.idealLattice K I

/-- Every nonzero fractional ideal has positive norm. -/
theorem chapter02_fractional_ideal_norm_pos
    (K : Type*) [Field K] [NumberField K]
    (I : chapter02NonzeroFractionalIdeal K) :
    0 < chapter02FractionalIdealNorm K I := by
  sorry

/-- The fractional-ideal lattice is a genuine `ℤ`-lattice. -/
theorem chapter02_fractional_ideal_lattice_isZLattice
    (K : Type*) [Field K] [NumberField K]
    (I : chapter02NonzeroFractionalIdeal K) :
    IsZLattice ℝ (chapter02FractionalIdealLattice K I) := by
  infer_instance

/-- Covolume of the ring-of-integers lattice, with the `2⁻ʳ²` normalization. -/
theorem chapter02_integer_lattice_covolume
    (K : Type*) [Field K] [NumberField K] :
    ZLattice.covolume (chapter02IntegerLattice K) =
      (2 : ℝ)⁻¹ ^ chapter02ComplexPlaces K *
        Real.sqrt (chapter02AbsoluteDiscriminant K) := by
  sorry

/-- Covolume of a fractional-ideal lattice. -/
theorem chapter02_fractional_ideal_lattice_covolume
    (K : Type*) [Field K] [NumberField K]
    (I : chapter02NonzeroFractionalIdeal K) :
    ZLattice.covolume (E := chapter02MinkowskiSpace K)
        (chapter02FractionalIdealLattice K I) =
      chapter02FractionalIdealNorm K I *
        (2 : ℝ)⁻¹ ^ chapter02ComplexPlaces K *
          Real.sqrt (chapter02AbsoluteDiscriminant K) := by
  sorry

/-- Membership in the fractional-ideal lattice is membership in the embedded ideal. -/
theorem chapter02_fractional_ideal_lattice_mem_iff
    (K : Type*) [Field K] [NumberField K]
    (I : chapter02NonzeroFractionalIdeal K)
    {x : chapter02MinkowskiSpace K} :
    x ∈ chapter02FractionalIdealLattice K I ↔
      ∃ y : K, y ∈ (I : Set K) ∧ NumberField.mixedEmbedding K y = x := by
  sorry

/-! ## 2.2 The convex-body argument -/

/-- The weighted `ℓ¹` gauge used by the Minkowski region. -/
noncomputable def chapter02MinkowskiGauge
    (K : Type*) [Field K] [NumberField K]
    (x : chapter02MinkowskiSpace K) : ℝ :=
  ∑ w : InfinitePlace K,
    (InfinitePlace.mult w : ℝ) * NumberField.mixedEmbedding.normAtPlace w x

/-- The closed convex symmetric body `∑real |xᵥ| + 2∑complex |zᵥ| ≤ T`. -/
noncomputable def chapter02MinkowskiRegion
    (K : Type*) [Field K] [NumberField K] (T : ℝ) :
    Set (chapter02MinkowskiSpace K) :=
  {x | chapter02MinkowskiGauge K x ≤ T}

/-- The book-facing gauge is the canonical `convexBodySumFun`. -/
theorem chapter02_minkowski_gauge_eq_canonical
    (K : Type*) [Field K] [NumberField K]
    (x : chapter02MinkowskiSpace K) :
    chapter02MinkowskiGauge K x =
      NumberField.mixedEmbedding.convexBodySumFun x :=
  rfl

/-- The book-facing region is the canonical `convexBodySum`. -/
theorem chapter02_minkowski_region_eq_canonical
    (K : Type*) [Field K] [NumberField K] (T : ℝ) :
    chapter02MinkowskiRegion K T =
      NumberField.mixedEmbedding.convexBodySum K T := by
  ext x
  rfl

/-- Expansion of the weighted gauge into real and complex coordinates. -/
theorem chapter02_minkowski_gauge_expansion
    (K : Type*) [Field K] [NumberField K]
    (x : chapter02MinkowskiSpace K) :
    chapter02MinkowskiGauge K x =
      (∑ w : {w : InfinitePlace K // IsReal w}, ‖x.1 w‖) +
        2 * ∑ w : {w : InfinitePlace K // IsComplex w}, ‖x.2 w‖ := by
  sorry

/-- Membership in the Minkowski body in the displayed source coordinates. -/
theorem chapter02_minkowski_region_mem_iff
    (K : Type*) [Field K] [NumberField K] (T : ℝ)
    (x : chapter02MinkowskiSpace K) :
    x ∈ chapter02MinkowskiRegion K T ↔
      (∑ w : {w : InfinitePlace K // IsReal w}, ‖x.1 w‖) +
          2 * ∑ w : {w : InfinitePlace K // IsComplex w}, ‖x.2 w‖ ≤ T := by
  sorry

/-- The Minkowski body is symmetric. -/
theorem chapter02_minkowski_region_neg_mem
    (K : Type*) [Field K] [NumberField K] (T : ℝ)
    {x : chapter02MinkowskiSpace K}
    (hx : x ∈ chapter02MinkowskiRegion K T) :
    -x ∈ chapter02MinkowskiRegion K T := by
  sorry

/-- The Minkowski body is convex. -/
theorem chapter02_minkowski_region_convex
    (K : Type*) [Field K] [NumberField K] (T : ℝ) :
    Convex ℝ (chapter02MinkowskiRegion K T) := by
  sorry

/-- The Minkowski body is compact whenever it is nonempty. -/
theorem chapter02_minkowski_region_compact
    (K : Type*) [Field K] [NumberField K] (T : ℝ) :
    IsCompact (chapter02MinkowskiRegion K T) := by
  sorry

/-- The elementary volume factor of the Minkowski body. -/
noncomputable def chapter02MinkowskiVolumeFactor
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  (2 : ℝ) ^ chapter02RealPlaces K *
      (Real.pi / 2) ^ chapter02ComplexPlaces K /
    (Nat.factorial (chapter02Degree K) : ℝ)

/-- Volume of the Minkowski body, including the simplex factorial. -/
theorem chapter02_minkowski_region_volume
    (K : Type*) [Field K] [NumberField K] (T : ℝ) (hT : 0 ≤ T) :
    volume (chapter02MinkowskiRegion K T) =
      ENNReal.ofReal (chapter02MinkowskiVolumeFactor K * T ^ chapter02Degree K) := by
  sorry

/-- The `2ⁿ`-times-covolume threshold in Minkowski's convex-body theorem. -/
noncomputable def chapter02MinkowskiBound
    (K : Type*) [Field K] [NumberField K]
    (I : chapter02NonzeroFractionalIdeal K) : ℝ≥0∞ :=
  NumberField.mixedEmbedding.minkowskiBound K I

/-- The canonical Minkowski threshold is `2ⁿ` times the fractional-lattice covolume. -/
theorem chapter02_minkowski_bound_eq_twopow_covolume
    (K : Type*) [Field K] [NumberField K]
    (I : chapter02NonzeroFractionalIdeal K) :
    chapter02MinkowskiBound K I =
      ENNReal.ofReal
          (ZLattice.covolume (E := chapter02MinkowskiSpace K)
            (chapter02FractionalIdealLattice K I)) *
        (2 : ℝ≥0∞) ^ chapter02Degree K := by
  sorry

/-- The strict volume hypothesis in the source's convex-body proof. -/
theorem chapter02_minkowski_lattice_witness_of_strict_threshold
    (K : Type*) [Field K] [NumberField K]
    (I : chapter02NonzeroFractionalIdeal K) (T : ℝ)
    (hT : ENNReal.ofReal
          (ZLattice.covolume (E := chapter02MinkowskiSpace K)
            (chapter02FractionalIdealLattice K I)) *
        (2 : ℝ≥0∞) ^ chapter02Degree K <
      volume (chapter02MinkowskiRegion K T)) :
    ∃ a : K, NumberField.mixedEmbedding K a ∈ chapter02MinkowskiRegion K T ∧
      a ∈ (I : Set K) ∧ a ≠ 0 ∧
        |Algebra.norm ℚ a| ≤
          (T / (chapter02Degree K : ℝ)) ^ chapter02Degree K := by
  sorry

/-- The lattice witness supplied by the convex-body theorem. -/
theorem chapter02_minkowski_lattice_witness
    (K : Type*) [Field K] [NumberField K]
    (I : chapter02NonzeroFractionalIdeal K) (T : ℝ)
    (hT : chapter02MinkowskiBound K I ≤ volume (chapter02MinkowskiRegion K T)) :
    ∃ a : K, NumberField.mixedEmbedding K a ∈ chapter02MinkowskiRegion K T ∧
      a ∈ (I : Set K) ∧ a ≠ 0 ∧
        |Algebra.norm ℚ a| ≤
          (T / (chapter02Degree K : ℝ)) ^ chapter02Degree K := by
  sorry

/-- The infinite-place product is the absolute field norm. -/
theorem chapter02_infinite_place_product_formula
    (K : Type*) [Field K] [NumberField K] (a : K) :
    ∏ w : InfinitePlace K, (w a) ^ InfinitePlace.mult w =
      |Algebra.norm ℚ a| := by
  sorry

/-- The weighted arithmetic-geometric-mean estimate used after the lattice witness. -/
theorem chapter02_norm_bound_of_minkowski_region_mem
    (K : Type*) [Field K] [NumberField K]
    {a : K} {T : ℝ}
    (ha : NumberField.mixedEmbedding K a ∈ chapter02MinkowskiRegion K T) :
    |Algebra.norm ℚ a| ≤
      (T / (chapter02Degree K : ℝ)) ^ chapter02Degree K := by
  sorry

/-- A nonzero integral element has absolute norm at least one. -/
theorem chapter02_integral_norm_ge_one
    (K : Type*) [Field K] [NumberField K]
    {a : 𝓞 K} (ha : a ≠ 0) :
    (1 : ℝ) ≤ |Algebra.norm ℚ (a : K)| := by
  sorry

/-- The field element bound obtained from a nonzero fractional ideal. -/
theorem chapter02_fractional_ideal_small_norm_element
    (K : Type*) [Field K] [NumberField K]
    (I : chapter02NonzeroFractionalIdeal K) :
    ∃ a : K, a ∈ (I : Set K) ∧ a ≠ 0 ∧
      |Algebra.norm ℚ a| ≤
        chapter02FractionalIdealNorm K I *
          (4 / Real.pi) ^ chapter02ComplexPlaces K *
            (Nat.factorial (chapter02Degree K) : ℝ) /
              (chapter02Degree K : ℝ) ^ chapter02Degree K *
                Real.sqrt (chapter02AbsoluteDiscriminant K) := by
  sorry

/-- The explicit constant in the ideal-class estimate. -/
noncomputable def chapter02MinkowskiConstant
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  (4 / Real.pi) ^ chapter02ComplexPlaces K *
      (Nat.factorial (chapter02Degree K) : ℝ) /
        (chapter02Degree K : ℝ) ^ chapter02Degree K *
          Real.sqrt (chapter02AbsoluteDiscriminant K)

/-- The small-norm estimate in the source's quotient-by-ideal-norm form. -/
theorem chapter02_fractional_ideal_small_norm_element_ratio
    (K : Type*) [Field K] [NumberField K]
    (I : chapter02NonzeroFractionalIdeal K) :
    ∃ a : K, a ∈ (I : Set K) ∧ a ≠ 0 ∧
      |Algebra.norm ℚ a| / chapter02FractionalIdealNorm K I ≤
        chapter02MinkowskiConstant K := by
  sorry

/-- The fractional ideal chosen in the proof represents the inverse class. -/
theorem chapter02_minkowski_inverse_class_witness
    (K : Type*) [Field K] [NumberField K]
    (C : ClassGroup (𝓞 K)) :
    ∃ I : chapter02NonzeroFractionalIdeal K,
      ClassGroup.mk K I = C⁻¹ ∧
        ∃ a : K, a ∈ (I : Set K) ∧ a ≠ 0 ∧
          |Algebra.norm ℚ a| / chapter02FractionalIdealNorm K I ≤
            chapter02MinkowskiConstant K := by
  sorry

/-- If `a ∈ I`, then `a I⁻¹` is an integral ideal. -/
theorem chapter02_principal_mul_inverse_is_integral
    (K : Type*) [Field K] [NumberField K]
    (I : chapter02NonzeroFractionalIdeal K) {a : K}
    (ha : a ∈ (I : Set K)) :
    ∃ J : Ideal (𝓞 K),
      (J : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ a *
          (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  sorry

/-- The integral ideal `a I⁻¹` lies in the desired class. -/
theorem chapter02_principal_mul_inverse_class
    (K : Type*) [Field K] [NumberField K]
    (C : ClassGroup (𝓞 K)) (I : chapter02NonzeroFractionalIdeal K)
    (hI : ClassGroup.mk K I = C⁻¹) {a : K}
    (ha : a ∈ (I : Set K)) (ha0 : a ≠ 0) :
    ∃ J : (Ideal (𝓞 K))⁰,
      ClassGroup.mk0 J = C ∧
        (J : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ a *
            (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  sorry

/-! Theorem 2.1. -/

/-- **Theorem 2.1 (Minkowski ideal-class estimate).**

Every ideal class contains a nonzero integral ideal whose norm is at most the
Minkowski constant. -/
theorem chapter02_minkowski_ideal_class_estimate
    (K : Type*) [Field K] [NumberField K]
    (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰,
      ClassGroup.mk0 I = C ∧
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ chapter02MinkowskiConstant K := by
  sorry

/-! ## 2.3 The exact root-discriminant inequality -/

/-- Every nonzero integral ideal has norm at least one. -/
theorem chapter02_integral_ideal_norm_ge_one
    (K : Type*) [Field K] [NumberField K]
    (I : (Ideal (𝓞 K))⁰) :
    (1 : ℝ) ≤ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) := by
  sorry

/-- The principal class forces the Minkowski constant to be at least one. -/
theorem chapter02_minkowski_constant_ge_one
    (K : Type*) [Field K] [NumberField K] :
    (1 : ℝ) ≤ chapter02MinkowskiConstant K := by
  sorry

/-- The exact absolute-discriminant lower bound. -/
theorem chapter02_discriminant_lower_bound
    (K : Type*) [Field K] [NumberField K] :
    (chapter02Degree K : ℝ) ^ (2 * chapter02Degree K) /
        ((4 / Real.pi) ^ (2 * chapter02ComplexPlaces K) *
          (Nat.factorial (chapter02Degree K) : ℝ) ^ 2) ≤
      chapter02AbsoluteDiscriminant K := by
  sorry

/-- The same discriminant bound in the source's `(π/4)^{2r₂}` form. -/
theorem chapter02_discriminant_lower_bound_book_form
    (K : Type*) [Field K] [NumberField K] :
    (Real.pi / 4) ^ (2 * chapter02ComplexPlaces K) *
        (chapter02Degree K : ℝ) ^ (2 * chapter02Degree K) /
          (Nat.factorial (chapter02Degree K) : ℝ) ^ 2 ≤
      chapter02AbsoluteDiscriminant K := by
  sorry

/-- The real proportion of embeddings that are real. -/
noncomputable def chapter02RealProportion
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  (chapter02RealPlaces K : ℝ) / (chapter02Degree K : ℝ)

/-- The signature proportion lies in `[0,1]`. -/
theorem chapter02_real_proportion_bounds
    (K : Type*) [Field K] [NumberField K] :
    0 ≤ chapter02RealProportion K ∧ chapter02RealProportion K ≤ 1 := by
  sorry

/-- The complex proportion is `1 - α` in the source notation. -/
theorem chapter02_complex_proportion_eq_one_sub_real_proportion
    (K : Type*) [Field K] [NumberField K] :
    (2 * (chapter02ComplexPlaces K : ℝ)) / (chapter02Degree K : ℝ) =
      1 - chapter02RealProportion K := by
  sorry

/-- The root discriminant. -/
noncomputable def chapter02RootDiscriminant
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  NumberField.rootDiscr K

/-- Unfolding the root-discriminant normalization. -/
theorem chapter02_root_discriminant_def
    (K : Type*) [Field K] [NumberField K] :
    chapter02RootDiscriminant K =
      Real.rpow (chapter02AbsoluteDiscriminant K)
        (chapter02Degree K : ℝ)⁻¹ := by
  sorry

/-- The factorial factor in the root-discriminant bound. -/
noncomputable def chapter02FactorialFactor (n : ℕ) : ℝ :=
  Real.rpow
    (((n : ℝ) ^ n) / (Nat.factorial n : ℝ))
    (2 / (n : ℝ))

/-- The signature-dependent geometric lower-bound expression. -/
noncomputable def chapter02GeometricLowerBound
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.rpow (Real.pi / 4) (1 - chapter02RealProportion K) *
    chapter02FactorialFactor (chapter02Degree K)

/-- Taking the degree root gives the root-discriminant inequality. -/
theorem chapter02_root_discriminant_lower_bound
    (K : Type*) [Field K] [NumberField K] :
    chapter02GeometricLowerBound K ≤ chapter02RootDiscriminant K := by
  sorry

/-- The book-facing and absolute-discriminant formulations are equivalent. -/
theorem chapter02_root_bound_equivalent_to_discriminant_bound
    (K : Type*) [Field K] [NumberField K] :
    chapter02GeometricLowerBound K ≤ chapter02RootDiscriminant K ↔
      (chapter02Degree K : ℝ) ^ (2 * chapter02Degree K) /
          ((4 / Real.pi) ^ (2 * chapter02ComplexPlaces K) *
            (Nat.factorial (chapter02Degree K) : ℝ) ^ 2) ≤
        chapter02AbsoluteDiscriminant K := by
  sorry

/-- The unrestricted-signature lower bound is obtained at `α = 0`. -/
theorem chapter02_geometric_lower_bound_ge_worst_signature
    (K : Type*) [Field K] [NumberField K] :
    Real.pi / 4 * chapter02FactorialFactor (chapter02Degree K) ≤
      chapter02GeometricLowerBound K := by
  sorry

/-- In the totally real case, the signature factor is exactly one. -/
theorem chapter02_totally_real_geometric_lower_bound_eq
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] :
    chapter02GeometricLowerBound K =
      chapter02FactorialFactor (chapter02Degree K) := by
  sorry

/-- For a totally real field, the factor `π/4` disappears. -/
theorem chapter02_totally_real_geometric_lower_bound
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] :
    chapter02FactorialFactor (chapter02Degree K) ≤ chapter02RootDiscriminant K := by
  sorry

/-! ## 2.4 Monotonicity of the factorial factor -/

/-- The auxiliary sequence `aₙ = (n!)^(1/n)/n`. -/
noncomputable def chapter02FactorialRootRatio (n : ℕ) : ℝ :=
  Real.rpow (Nat.factorial n : ℝ) ((n : ℝ)⁻¹) / (n : ℝ)

/-- `Mₙ` is the inverse square of `aₙ` at positive indices. -/
theorem chapter02_factorial_factor_eq_ratio_inv_sq
    {n : ℕ} (hn : 0 < n) :
    chapter02FactorialFactor n =
      (chapter02FactorialRootRatio n)⁻¹ ^ (2 : ℕ) := by
  sorry

/-- The adjacent comparison for `aₙ` after clearing positive powers. -/
theorem chapter02_factorial_ratio_succ_le_iff
    {n : ℕ} (hn : 0 < n) :
    chapter02FactorialRootRatio (n + 1) ≤ chapter02FactorialRootRatio n ↔
      (1 + 1 / (n : ℝ)) ^ (n * n) ≥
        (n : ℝ) ^ n / (Nat.factorial n : ℝ) := by
  sorry

/-- The integral comparison for `log(n!)`. -/
theorem chapter02_log_factorial_eq_sum_log
    {n : ℕ} (hn : 1 ≤ n) :
    Real.log (Nat.factorial n : ℝ) =
      Finset.sum (Finset.range n) (fun k => Real.log (k + 1 : ℝ)) := by
  sorry

/-- The integral comparison for `log(n!)`. -/
theorem chapter02_log_factorial_integral_comparison
    {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n + 1 =
        ∫ x in (1 : ℝ)..(n : ℝ), Real.log x ∧
      ∫ x in (1 : ℝ)..(n : ℝ), Real.log x ≤
        Real.log (Nat.factorial n : ℝ) := by
  sorry

/-- The derivative of the quadratic remainder in the logarithm estimate. -/
theorem chapter02_log_one_add_quadratic_remainder_deriv
    {u : ℝ} (hu : -1 < u) :
    HasDerivAt
      (fun v : ℝ => Real.log (1 + v) - v + v ^ 2 / 2)
      (u ^ 2 / (1 + u)) u := by
  sorry

/-- The elementary lower bound `log(1+u) ≥ u-u²/2`. -/
theorem chapter02_log_one_add_quadratic_lower
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u - u ^ 2 / 2 ≤ Real.log (1 + u) := by
  sorry

/-- The reciprocal specialization used in the monotonicity proof. -/
theorem chapter02_reciprocal_log_comparison
    {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 2 * Real.log (1 + 1 / (n : ℝ)) ≥
        (n : ℝ) - 1 / 2 ∧
      (n : ℝ) - 1 ≤ (n : ℝ) - 1 / 2 := by
  sorry

/-- The auxiliary sequence is nonincreasing at adjacent positive indices. -/
theorem chapter02_factorial_root_ratio_succ_le
    {n : ℕ} (hn : 0 < n) :
    chapter02FactorialRootRatio (n + 1) ≤ chapter02FactorialRootRatio n := by
  sorry

/-- The factorial factor is nondecreasing at adjacent positive indices. -/
theorem chapter02_factorial_factor_succ_le
    {n : ℕ} (hn : 0 < n) :
    chapter02FactorialFactor n ≤ chapter02FactorialFactor (n + 1) := by
  sorry

/-- The factorial factor is monotone on positive natural indices. -/
theorem chapter02_factorial_factor_monotone :
    MonotoneOn chapter02FactorialFactor (Set.Ioi (0 : ℕ)) := by
  sorry

/-- The main term in the Stirling expansion of `log Mₙ`. -/
noncomputable def chapter02StirlingMainTerm (n : ℕ) : ℝ :=
  2 - Real.log (2 * Real.pi * (n : ℝ)) / (n : ℝ) -
    1 / (6 * (n : ℝ) ^ 2)

/-- The Stirling error for `log Mₙ`. -/
noncomputable def chapter02StirlingError (n : ℕ) : ℝ :=
  Real.log (chapter02FactorialFactor n) - chapter02StirlingMainTerm n

/-- Stirling's two-sided remainder, recorded as an eventual `O(n⁻⁴)` bound. -/
theorem chapter02_stirling_log_factorial_factor :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop,
        |chapter02StirlingError n| ≤ C * ((n : ℝ)⁻¹) ^ (4 : ℕ) := by
  sorry

/-- The factorial factor tends to `e²`. -/
theorem chapter02_factorial_factor_tendsto :
    Tendsto chapter02FactorialFactor atTop (𝓝 (Real.exp 2)) := by
  sorry

/-- The worst-signature geometric limit. -/
theorem chapter02_worst_signature_geometric_limit :
    Tendsto
      (fun n : ℕ => Real.pi / 4 * chapter02FactorialFactor n)
      atTop (𝓝 (Real.pi / 4 * Real.exp 2)) := by
  sorry

/-- The totally real geometric limit. -/
theorem chapter02_totally_real_geometric_limit :
    Tendsto chapter02FactorialFactor atTop (𝓝 (Real.exp 2)) :=
  chapter02_factorial_factor_tendsto

/-! ## 2.5 Why geometry is not enough -/

/-- The exact real value denoted by `5^(5/4)` in the source. -/
noncomputable def chapter02FiveToFiveFourth : ℝ :=
  Real.rpow 5 ((5 : ℝ) / 4)

/-- The totally real geometric limit is below the `5^(5/4)` ceiling. -/
theorem chapter02_totally_real_limit_below_five_to_five_fourth :
    Real.exp 2 < chapter02FiveToFiveFourth := by
  sorry

/-- The unrestricted geometric limit is also below that ceiling. -/
theorem chapter02_worst_signature_limit_below_five_to_five_fourth :
    Real.pi / 4 * Real.exp 2 < chapter02FiveToFiveFourth := by
  sorry

/-- A geometric crossing transfers a strict root-discriminant ceiling to a degree cap. -/
theorem chapter02_geometric_degree_exclusion
    (K : Type*) [Field K] [NumberField K]
    {U : ℝ} {N : ℕ} (hN : 0 < N)
    (hcross : U < Real.pi / 4 * chapter02FactorialFactor N)
    (hRD : chapter02RootDiscriminant K < U) :
    chapter02Degree K < N := by
  sorry

/-- The totally real version of the geometric degree-exclusion bridge. -/
theorem chapter02_totally_real_degree_exclusion
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    {U : ℝ} {N : ℕ} (hN : 0 < N)
    (hcross : U < chapter02FactorialFactor N)
    (hRD : chapter02RootDiscriminant K < U) :
    chapter02Degree K < N := by
  sorry

end
end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02
