import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite

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
  exact NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K

/-- The absolute discriminant convention used by the book. -/
noncomputable def chapter02AbsoluteDiscriminant
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  |(NumberField.discr K : ℝ)|

/-- The absolute discriminant is strictly positive. -/
theorem chapter02_absolute_discriminant_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter02AbsoluteDiscriminant K := by
  rw [chapter02AbsoluteDiscriminant, abs_pos]
  exact_mod_cast NumberField.discr_ne_zero K

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
  let e₁ : chapter02TensorSpace K ≃ₗ[ℝ] (ℝ ⊗[ℚ] K) :=
    (Algebra.TensorProduct.commRight ℚ ℝ K).symm.toLinearEquiv
  let e₂ : (ℝ ⊗[ℚ] K) ≃ₗ[ℝ] chapter02MinkowskiSpace K :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [Module.finrank_baseChange, NumberField.mixedEmbedding.finrank K])
  exact e₁.trans e₂

/-- The mixed space has the expected real dimension. -/
theorem chapter02_minkowski_space_finrank
    (K : Type*) [Field K] [NumberField K] :
    Module.finrank ℝ (chapter02MinkowskiSpace K) = chapter02Degree K := by
  exact NumberField.mixedEmbedding.finrank K

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
  have hne : FractionalIdeal.absNorm I.1 ≠ 0 := by
    intro hzero
    exact Units.ne_zero I (FractionalIdeal.absNorm_eq_zero_iff.mp hzero)
  have hpos : (0 : ℚ) < FractionalIdeal.absNorm I.1 :=
    lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I.1) (Ne.symm hne)
  change (0 : ℝ) < (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
  exact_mod_cast hpos

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
  simpa [chapter02AbsoluteDiscriminant] using
    (NumberField.mixedEmbedding.covolume_integerLattice K)

/-- Covolume of a fractional-ideal lattice. -/
theorem chapter02_fractional_ideal_lattice_covolume
    (K : Type*) [Field K] [NumberField K]
    (I : chapter02NonzeroFractionalIdeal K) :
    ZLattice.covolume (E := chapter02MinkowskiSpace K)
        (chapter02FractionalIdealLattice K I) =
      chapter02FractionalIdealNorm K I *
        (2 : ℝ)⁻¹ ^ chapter02ComplexPlaces K *
          Real.sqrt (chapter02AbsoluteDiscriminant K) := by
  simpa [chapter02FractionalIdealNorm, chapter02AbsoluteDiscriminant] using
    (NumberField.mixedEmbedding.covolume_idealLattice K I)

/-- Membership in the fractional-ideal lattice is membership in the embedded ideal. -/
theorem chapter02_fractional_ideal_lattice_mem_iff
    (K : Type*) [Field K] [NumberField K]
    (I : chapter02NonzeroFractionalIdeal K)
    {x : chapter02MinkowskiSpace K} :
    x ∈ chapter02FractionalIdealLattice K I ↔
      ∃ y : K, y ∈ (I : Set K) ∧ NumberField.mixedEmbedding K y = x := by
  exact NumberField.mixedEmbedding.mem_idealLattice K I

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
  exact NumberField.mixedEmbedding.convexBodySumFun_apply' x

/-- Membership in the Minkowski body in the displayed source coordinates. -/
theorem chapter02_minkowski_region_mem_iff
    (K : Type*) [Field K] [NumberField K] (T : ℝ)
    (x : chapter02MinkowskiSpace K) :
    x ∈ chapter02MinkowskiRegion K T ↔
      (∑ w : {w : InfinitePlace K // IsReal w}, ‖x.1 w‖) +
          2 * ∑ w : {w : InfinitePlace K // IsComplex w}, ‖x.2 w‖ ≤ T := by
  change chapter02MinkowskiGauge K x ≤ T ↔ _
  rw [chapter02_minkowski_gauge_expansion]

/-- The Minkowski body is symmetric. -/
theorem chapter02_minkowski_region_neg_mem
    (K : Type*) [Field K] [NumberField K] (T : ℝ)
    {x : chapter02MinkowskiSpace K}
    (hx : x ∈ chapter02MinkowskiRegion K T) :
    -x ∈ chapter02MinkowskiRegion K T := by
  rw [chapter02_minkowski_region_eq_canonical] at hx ⊢
  exact NumberField.mixedEmbedding.convexBodySum_neg_mem K T hx

/-- The Minkowski body is convex. -/
theorem chapter02_minkowski_region_convex
    (K : Type*) [Field K] [NumberField K] (T : ℝ) :
    Convex ℝ (chapter02MinkowskiRegion K T) := by
  rw [chapter02_minkowski_region_eq_canonical]
  exact NumberField.mixedEmbedding.convexBodySum_convex K T

/-- The Minkowski body is compact whenever it is nonempty. -/
theorem chapter02_minkowski_region_compact
    (K : Type*) [Field K] [NumberField K] (T : ℝ) :
    IsCompact (chapter02MinkowskiRegion K T) := by
  rw [chapter02_minkowski_region_eq_canonical]
  exact NumberField.mixedEmbedding.convexBodySum_compact K T

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
  rw [chapter02_minkowski_region_eq_canonical]
  rw [ENNReal.ofReal_mul' (pow_nonneg hT _), ENNReal.ofReal_pow hT]
  have hF : 0 ≤ chapter02MinkowskiVolumeFactor K := by
    unfold chapter02MinkowskiVolumeFactor
    positivity
  rw [ENNReal.ofReal_eq_coe_nnreal hF]
  convert (NumberField.mixedEmbedding.convexBodySum_volume (K := K) (B := T)) using 1
  congr 1

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
  rw [chapter02MinkowskiBound, NumberField.mixedEmbedding.minkowskiBound]
  have hfd := NumberField.mixedEmbedding.fundamentalDomain_idealLattice K I
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain
    (chapter02FractionalIdealLattice K I) volume hfd
  have htop :
      volume (ZSpan.fundamentalDomain
        (NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I)) < ∞ :=
    Bornology.IsBounded.measure_lt_top (μ := volume)
      (ZSpan.fundamentalDomain_isBounded
        (NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I))
  have hof : ENNReal.ofReal
      (volume.real (ZSpan.fundamentalDomain
        (NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I))) =
      volume (ZSpan.fundamentalDomain
        (NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I)) := by
    change ENNReal.ofReal
      (volume (ZSpan.fundamentalDomain
        (NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I))).toReal = _
    exact ENNReal.ofReal_toReal (ne_of_lt htop)
  rw [hcov, hof, chapter02_minkowski_space_finrank]

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
  have hstrict : NumberField.mixedEmbedding.minkowskiBound K I <
      volume (NumberField.mixedEmbedding.convexBodySum K T) := by
    change chapter02MinkowskiBound K I < volume (chapter02MinkowskiRegion K T)
    rw [chapter02_minkowski_bound_eq_twopow_covolume K I]
    exact lt_of_lt_of_le hT (le_refl _)
  have h_fund := ZSpan.isAddFundamentalDomain'
    (NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I) volume
  have hcount : Countable (Submodule.span ℤ (Set.range
      (NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range
      (NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I)))
    infer_instance
  obtain ⟨⟨x, hx⟩, hx_nz, hx_mem⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure h_fund
      (fun _ ↦ NumberField.mixedEmbedding.convexBodySum_neg_mem K T)
      (NumberField.mixedEmbedding.convexBodySum_convex K T) hstrict
  rw [Submodule.mem_toAddSubgroup,
    NumberField.mixedEmbedding.mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨a, ?_, ?_, by simpa using hx_nz, ?_⟩
  · rw [chapter02_minkowski_region_eq_canonical]
    exact hx_mem
  · simpa using ha
  · have h1 : 0 < (chapter02Degree K : ℝ)⁻¹ :=
      by
        exact inv_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos)
    change |Algebra.norm ℚ a| ≤
      (T / (Module.finrank ℚ K : ℝ)) ^ Module.finrank ℚ K
    have h2 : 0 ≤ T / (chapter02Degree K : ℝ) := by
      have hT0 : 0 ≤ T := by
        contrapose! hstrict
        rw [NumberField.mixedEmbedding.convexBodySum_volume_eq_zero_of_le_zero K
          (le_of_lt hstrict)]
        exact (NumberField.mixedEmbedding.minkowskiBound_pos K I).le
      exact div_nonneg hT0 (Nat.cast_nonneg _)
    rw [← Real.rpow_natCast, ← Real.rpow_le_rpow_iff
        (by simp only [Rat.cast_abs, abs_nonneg])
        (Real.rpow_nonneg h2 _) h1, ← Real.rpow_mul h2,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt Module.finrank_pos)),
        Real.rpow_one, le_div_iff₀' (Nat.cast_pos.mpr Module.finrank_pos)]
    refine le_trans ?_ ((NumberField.mixedEmbedding.convexBodySum_mem K T).mp hx_mem)
    rw [← le_div_iff₀' (Nat.cast_pos.mpr Module.finrank_pos)]
    change |Algebra.norm ℚ a| ^ ((Module.finrank ℚ K : ℝ)⁻¹) ≤
      (∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) * w a) /
        (Module.finrank ℚ K : ℝ)
    rw [← NumberField.InfinitePlace.sum_mult_eq, Nat.cast_sum]
    refine le_trans ?_ (Real.geom_mean_le_arith_mean Finset.univ _ _
      (fun _ _ ↦ Nat.cast_nonneg _) ?_ (fun _ _ ↦ AbsoluteValue.nonneg _ _))
    · simp_rw [← NumberField.InfinitePlace.prod_eq_abs_norm, Real.rpow_natCast]
      exact le_of_eq rfl
    · rw [← Nat.cast_sum, sum_mult_eq, Nat.cast_pos]
      exact Module.finrank_pos

/-- The lattice witness supplied by the convex-body theorem. -/
theorem chapter02_minkowski_lattice_witness
    (K : Type*) [Field K] [NumberField K]
    (I : chapter02NonzeroFractionalIdeal K) (T : ℝ)
    (hT : chapter02MinkowskiBound K I ≤ volume (chapter02MinkowskiRegion K T)) :
    ∃ a : K, NumberField.mixedEmbedding K a ∈ chapter02MinkowskiRegion K T ∧
      a ∈ (I : Set K) ∧ a ≠ 0 ∧
        |Algebra.norm ℚ a| ≤
          (T / (chapter02Degree K : ℝ)) ^ chapter02Degree K := by
  have hle : NumberField.mixedEmbedding.minkowskiBound K I ≤
      volume (NumberField.mixedEmbedding.convexBodySum K T) := by
    change chapter02MinkowskiBound K I ≤ volume (chapter02MinkowskiRegion K T)
    exact hT
  have h_fund := ZSpan.isAddFundamentalDomain'
    (NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I) volume
  have hcount : Countable (Submodule.span ℤ (Set.range
      (NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range
      (NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I)))
    infer_instance
  obtain ⟨⟨x, hx⟩, hx_nz, hx_mem⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure h_fund
      (fun _ ↦ NumberField.mixedEmbedding.convexBodySum_neg_mem K T)
      (NumberField.mixedEmbedding.convexBodySum_convex K T)
      (NumberField.mixedEmbedding.convexBodySum_compact K T) hle
  rw [Submodule.mem_toAddSubgroup,
    NumberField.mixedEmbedding.mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨a, ?_, ?_, by simpa using hx_nz, ?_⟩
  · rw [chapter02_minkowski_region_eq_canonical]
    exact hx_mem
  · simpa using ha
  · have hT0 : 0 ≤ T := by
      contrapose! hT
      rw [chapter02_minkowski_region_eq_canonical,
        NumberField.mixedEmbedding.convexBodySum_volume_eq_zero_of_le_zero K
          (le_of_lt hT)]
      exact NumberField.mixedEmbedding.minkowskiBound_pos K I
    have h1 : 0 < (chapter02Degree K : ℝ)⁻¹ :=
      inv_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos)
    change |Algebra.norm ℚ a| ≤
      (T / (Module.finrank ℚ K : ℝ)) ^ Module.finrank ℚ K
    have h2 : 0 ≤ T / (chapter02Degree K : ℝ) :=
      div_nonneg hT0 (Nat.cast_nonneg _)
    rw [← Real.rpow_natCast, ← Real.rpow_le_rpow_iff
        (by simp only [Rat.cast_abs, abs_nonneg])
        (Real.rpow_nonneg h2 _) h1, ← Real.rpow_mul h2,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt Module.finrank_pos)),
        Real.rpow_one, le_div_iff₀' (Nat.cast_pos.mpr Module.finrank_pos)]
    refine le_trans ?_ ((NumberField.mixedEmbedding.convexBodySum_mem K T).mp hx_mem)
    rw [← le_div_iff₀' (Nat.cast_pos.mpr Module.finrank_pos)]
    change |Algebra.norm ℚ a| ^ ((Module.finrank ℚ K : ℝ)⁻¹) ≤
      (∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) * w a) /
        (Module.finrank ℚ K : ℝ)
    rw [← NumberField.InfinitePlace.sum_mult_eq, Nat.cast_sum]
    refine le_trans ?_ (Real.geom_mean_le_arith_mean Finset.univ _ _
      (fun _ _ ↦ Nat.cast_nonneg _) ?_ (fun _ _ ↦ AbsoluteValue.nonneg _ _))
    · simp_rw [← NumberField.InfinitePlace.prod_eq_abs_norm, Real.rpow_natCast]
      exact le_of_eq rfl
    · rw [← Nat.cast_sum, sum_mult_eq, Nat.cast_pos]
      exact Module.finrank_pos

/-- The infinite-place product is the absolute field norm. -/
theorem chapter02_infinite_place_product_formula
    (K : Type*) [Field K] [NumberField K] (a : K) :
    ∏ w : InfinitePlace K, (w a) ^ InfinitePlace.mult w =
      |Algebra.norm ℚ a| := by
  exact NumberField.InfinitePlace.prod_eq_abs_norm a

/-- The weighted arithmetic-geometric-mean estimate used after the lattice witness. -/
theorem chapter02_norm_bound_of_minkowski_region_mem
    (K : Type*) [Field K] [NumberField K]
    {a : K} {T : ℝ}
    (ha : NumberField.mixedEmbedding K a ∈ chapter02MinkowskiRegion K T) :
    |Algebra.norm ℚ a| ≤
      (T / (chapter02Degree K : ℝ)) ^ chapter02Degree K := by
  rw [chapter02_minkowski_region_eq_canonical] at ha
  have hT0 : 0 ≤ T := by
    have hsum := NumberField.mixedEmbedding.convexBodySumFun_nonneg
      (NumberField.mixedEmbedding K a)
    have hsum' : 0 ≤ ∑ w : InfinitePlace K,
        (InfinitePlace.mult w : ℝ) * w a := by
      simpa only [NumberField.mixedEmbedding.convexBodySumFun_apply,
        NumberField.mixedEmbedding.normAtPlace_apply] using hsum
    exact le_trans hsum' ((NumberField.mixedEmbedding.convexBodySum_mem K T).mp ha)
  have h1 : 0 < (chapter02Degree K : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos)
  have h2 : 0 ≤ T / (chapter02Degree K : ℝ) :=
    div_nonneg hT0 (Nat.cast_nonneg _)
  change |Algebra.norm ℚ a| ≤
    (T / (Module.finrank ℚ K : ℝ)) ^ Module.finrank ℚ K
  rw [← Real.rpow_natCast, ← Real.rpow_le_rpow_iff
      (by simp only [Rat.cast_abs, abs_nonneg])
      (Real.rpow_nonneg h2 _) h1, ← Real.rpow_mul h2,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt Module.finrank_pos)),
      Real.rpow_one, le_div_iff₀' (Nat.cast_pos.mpr Module.finrank_pos)]
  refine le_trans ?_ ((NumberField.mixedEmbedding.convexBodySum_mem K T).mp ha)
  rw [← le_div_iff₀' (Nat.cast_pos.mpr Module.finrank_pos)]
  change |Algebra.norm ℚ a| ^ ((Module.finrank ℚ K : ℝ)⁻¹) ≤
    (∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) * w a) /
      (Module.finrank ℚ K : ℝ)
  rw [← NumberField.InfinitePlace.sum_mult_eq, Nat.cast_sum]
  refine le_trans ?_ (Real.geom_mean_le_arith_mean Finset.univ _ _
    (fun _ _ ↦ Nat.cast_nonneg _) ?_ (fun _ _ ↦ AbsoluteValue.nonneg _ _))
  · simp_rw [← NumberField.InfinitePlace.prod_eq_abs_norm, Real.rpow_natCast]
    exact le_of_eq rfl
  · rw [← Nat.cast_sum, sum_mult_eq, Nat.cast_pos]
    exact Module.finrank_pos

/-- A nonzero integral element has absolute norm at least one. -/
theorem chapter02_integral_norm_ge_one
    (K : Type*) [Field K] [NumberField K]
    {a : 𝓞 K} (ha : a ≠ 0) :
    (1 : ℝ) ≤ |Algebra.norm ℚ (a : K)| := by
  rw [← Algebra.coe_norm_int, ← Int.cast_one, ← Int.cast_abs, Rat.cast_intCast, Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)

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
  obtain ⟨a, ha, ha0, hnorm⟩ :=
    NumberField.exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr K I
  refine ⟨a, ?_, ha0, ?_⟩
  · simpa using ha
  · simpa [chapter02FractionalIdealNorm, chapter02AbsoluteDiscriminant,
      chapter02Degree, chapter02ComplexPlaces] using hnorm

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
  obtain ⟨a, ha, ha0, hnorm⟩ := chapter02_fractional_ideal_small_norm_element K I
  refine ⟨a, ha, ha0, ?_⟩
  apply (div_le_iff₀ (chapter02_fractional_ideal_norm_pos K I)).2
  convert hnorm using 1
  · rfl
  · simp only [chapter02MinkowskiConstant]
    ring

/-- The fractional ideal chosen in the proof represents the inverse class. -/
theorem chapter02_minkowski_inverse_class_witness
    (K : Type*) [Field K] [NumberField K]
    (C : ClassGroup (𝓞 K)) :
    ∃ I : chapter02NonzeroFractionalIdeal K,
      ClassGroup.mk K I = C⁻¹ ∧
        ∃ a : K, a ∈ (I : Set K) ∧ a ≠ 0 ∧
            |Algebra.norm ℚ a| / chapter02FractionalIdealNorm K I ≤
            chapter02MinkowskiConstant K := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective (C⁻¹)
  let I : chapter02NonzeroFractionalIdeal K := FractionalIdeal.mk0 K J
  refine ⟨I, ?_, chapter02_fractional_ideal_small_norm_element_ratio K I⟩
  change ClassGroup.mk K (FractionalIdeal.mk0 K J) = C⁻¹
  rw [ClassGroup.mk_mk0]
  exact hJ

/-- If `a ∈ I`, then `a I⁻¹` is an integral ideal. -/
theorem chapter02_principal_mul_inverse_is_integral
    (K : Type*) [Field K] [NumberField K]
    (I : chapter02NonzeroFractionalIdeal K) {a : K}
    (ha : a ∈ (I : Set K)) :
    ∃ J : Ideal (𝓞 K),
      (J : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ a *
          (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  have hunit :
      I.1 * I.1⁻¹ = 1 := by
    exact (FractionalIdeal.mul_inv_cancel_iff_isUnit K).2 I.isUnit
  have hprod :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ a *
          I.1⁻¹ ≤ 1 := by
    rw [FractionalIdeal.spanSingleton_mul_le_iff]
    intro z hz
    have hInv : I.1 ≠ 0 := Units.ne_zero I
    have hz' := (FractionalIdeal.mem_inv_iff hInv).mp hz a ha
    simpa [mul_comm] using hz'
  obtain ⟨J, hJ⟩ :=
    (FractionalIdeal.le_one_iff_exists_coeIdeal).mp hprod
  exact ⟨J, hJ⟩

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
  obtain ⟨J, hJ⟩ := chapter02_principal_mul_inverse_is_integral K I ha
  have hJ0 : J ≠ 0 := by
    intro hzero
    have hzero' : (J : FractionalIdeal (𝓞 K)⁰ K) = 0 := by simp [hzero]
    rw [hzero'] at hJ
    exact (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha0)
      (inv_ne_zero (Units.ne_zero I))) hJ.symm
  let J0 : (Ideal (𝓞 K))⁰ := ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ0⟩
  let Junit : chapter02NonzeroFractionalIdeal K :=
    FractionalIdeal.mk0 K J0
  have hunit : I.1⁻¹ * I.1 = 1 := by
    rw [mul_comm]
    exact (FractionalIdeal.mul_inv_cancel_iff_isUnit K).2 I.isUnit
  have hmul : J * I.1 = FractionalIdeal.spanSingleton (𝓞 K)⁰ a := by
    rw [hJ, mul_assoc, hunit, mul_one]
  have hclass : ClassGroup.mk K Junit * ClassGroup.mk K I = 1 := by
    rw [← map_mul]
    apply (ClassGroup.mk_eq_one_iff).2
    refine { principal := ?_ }
    refine ⟨a, ?_⟩
    simp only [Junit, Units.val_mul, FractionalIdeal.coe_mk0]
    rw [hmul, FractionalIdeal.coe_spanSingleton]
  have hclass' : ClassGroup.mk K Junit * C⁻¹ = 1 := by
    simpa [hI] using hclass
  have hJclass : ClassGroup.mk K Junit = C := by
    calc
      ClassGroup.mk K Junit = ClassGroup.mk K Junit * 1 := (mul_one _).symm
      _ = ClassGroup.mk K Junit * (C⁻¹ * C) := by rw [inv_mul_cancel]
      _ = (ClassGroup.mk K Junit * C⁻¹) * C := by ac_rfl
      _ = 1 * C := by rw [hclass']
      _ = C := one_mul _
  refine ⟨J0, ?_, hJ⟩
  simpa [J0, Junit] using hJclass

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
  convert (NumberField.exists_ideal_in_class_of_norm_le (K := K) C) using 1 ;
    simp [chapter02MinkowskiConstant, chapter02Degree, chapter02ComplexPlaces,
      chapter02AbsoluteDiscriminant] ; ring_nf

/-! ## 2.3 The exact root-discriminant inequality -/

/-- Every nonzero integral ideal has norm at least one. -/
theorem chapter02_integral_ideal_norm_ge_one
    (K : Type*) [Field K] [NumberField K]
    (I : (Ideal (𝓞 K))⁰) :
    (1 : ℝ) ≤ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) := by
  exact_mod_cast
    (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_ne_zero_of_nonZeroDivisors I))

/-- The principal class forces the Minkowski constant to be at least one. -/
theorem chapter02_minkowski_constant_ge_one
    (K : Type*) [Field K] [NumberField K] :
    (1 : ℝ) ≤ chapter02MinkowskiConstant K := by
  obtain ⟨I, _, hI⟩ := chapter02_minkowski_ideal_class_estimate K 1
  exact (chapter02_integral_ideal_norm_ge_one K I).trans hI

/-- The exact absolute-discriminant lower bound. -/
theorem chapter02_discriminant_lower_bound
    (K : Type*) [Field K] [NumberField K] :
    (chapter02Degree K : ℝ) ^ (2 * chapter02Degree K) /
        ((4 / Real.pi) ^ (2 * chapter02ComplexPlaces K) *
          (Nat.factorial (chapter02Degree K) : ℝ) ^ 2) ≤
      chapter02AbsoluteDiscriminant K := by
  simpa [chapter02Degree, chapter02ComplexPlaces, chapter02AbsoluteDiscriminant] using
    (NumberField.abs_discr_ge' K)

/-- The same discriminant bound in the source's `(π/4)^{2r₂}` form. -/
theorem chapter02_discriminant_lower_bound_book_form
    (K : Type*) [Field K] [NumberField K] :
    (Real.pi / 4) ^ (2 * chapter02ComplexPlaces K) *
        (chapter02Degree K : ℝ) ^ (2 * chapter02Degree K) /
          (Nat.factorial (chapter02Degree K) : ℝ) ^ 2 ≤
      chapter02AbsoluteDiscriminant K := by
  convert chapter02_discriminant_lower_bound K using 1
  have hpow :
      (Real.pi / 4) ^ (2 * chapter02ComplexPlaces K) *
          (4 / Real.pi) ^ (2 * chapter02ComplexPlaces K) = 1 := by
    rw [← mul_pow]
    field_simp [Real.pi_ne_zero]
    simp
  field_simp [Real.pi_ne_zero]
  exact hpow

/-- The real proportion of embeddings that are real. -/
noncomputable def chapter02RealProportion
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  (chapter02RealPlaces K : ℝ) / (chapter02Degree K : ℝ)

/-- The signature proportion lies in `[0,1]`. -/
theorem chapter02_real_proportion_bounds
    (K : Type*) [Field K] [NumberField K] :
    0 ≤ chapter02RealProportion K ∧ chapter02RealProportion K ≤ 1 := by
  have hdeg : 0 < chapter02Degree K := Module.finrank_pos
  have hreal : chapter02RealPlaces K ≤ chapter02Degree K := by
    have hsig := chapter02_signature_degree K
    omega
  constructor
  · unfold chapter02RealProportion
    positivity
  · unfold chapter02RealProportion
    have hdegR : 0 < (chapter02Degree K : ℝ) := by exact_mod_cast hdeg
    exact (div_le_one hdegR).2 (by exact_mod_cast hreal)

/-- The complex proportion is `1 - α` in the source notation. -/
theorem chapter02_complex_proportion_eq_one_sub_real_proportion
    (K : Type*) [Field K] [NumberField K] :
    (2 * (chapter02ComplexPlaces K : ℝ)) / (chapter02Degree K : ℝ) =
      1 - chapter02RealProportion K := by
  have hdegpos : 0 < (chapter02Degree K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  have hdeg : (chapter02Degree K : ℝ) ≠ 0 := ne_of_gt hdegpos
  have hsig := chapter02_signature_degree K
  have hsigR : (chapter02RealPlaces K : ℝ) +
      2 * (chapter02ComplexPlaces K : ℝ) = (chapter02Degree K : ℝ) := by
    exact_mod_cast hsig
  unfold chapter02RealProportion
  apply (div_eq_iff hdeg).2
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hdeg]
  linarith

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
  simpa [chapter02RootDiscriminant, chapter02AbsoluteDiscriminant, chapter02Degree] using
    (NumberField.rootDiscr_def K)

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
  have hdeg : 0 < (chapter02Degree K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  have hdeg0 : (chapter02Degree K : ℝ) ≠ 0 := ne_of_gt hdeg
  have hdisc : 0 ≤ chapter02AbsoluteDiscriminant K :=
    (chapter02_absolute_discriminant_pos K).le
  have hfactor : 0 ≤ chapter02FactorialFactor (chapter02Degree K) := by
    unfold chapter02FactorialFactor
    exact Real.rpow_nonneg (div_nonneg (pow_nonneg (le_of_lt hdeg) _)
      (by positivity)) _
  have hpi : 0 ≤ Real.pi / 4 := by positivity
  have hpiFactor : 0 ≤ Real.rpow (Real.pi / 4)
      (1 - chapter02RealProportion K) := Real.rpow_nonneg hpi _
  have hgeom : 0 ≤ chapter02GeometricLowerBound K := by
    unfold chapter02GeometricLowerBound
    exact mul_nonneg (Real.rpow_nonneg hpi _) hfactor
  have hratio : 0 ≤
      ((chapter02Degree K : ℝ) ^ chapter02Degree K) /
        (Nat.factorial (chapter02Degree K) : ℝ) := by
    exact div_nonneg (pow_nonneg (le_of_lt hdeg) _) (by positivity)
  have hαpow :
      (1 - chapter02RealProportion K) * (chapter02Degree K : ℝ) =
        2 * (chapter02ComplexPlaces K : ℝ) := by
    rw [← chapter02_complex_proportion_eq_one_sub_real_proportion K]
    field_simp [hdeg0]
  have hfacpow :
      2 / (chapter02Degree K : ℝ) * (chapter02Degree K : ℝ) = 2 := by
    field_simp [hdeg0]
  have hpow :
      (chapter02GeometricLowerBound K) ^ (chapter02Degree K : ℝ) =
        (Real.pi / 4) ^ (2 * chapter02ComplexPlaces K) *
          (chapter02Degree K : ℝ) ^ (2 * chapter02Degree K) /
            (Nat.factorial (chapter02Degree K) : ℝ) ^ 2 := by
    calc
      (chapter02GeometricLowerBound K) ^ (chapter02Degree K : ℝ) =
          (Real.rpow (Real.pi / 4) (1 - chapter02RealProportion K)) ^
              (chapter02Degree K : ℝ) *
            (chapter02FactorialFactor (chapter02Degree K)) ^
              (chapter02Degree K : ℝ) := by
        rw [chapter02GeometricLowerBound, Real.mul_rpow hpiFactor hfactor]
      _ = Real.rpow (Real.pi / 4)
            ((1 - chapter02RealProportion K) * (chapter02Degree K : ℝ)) *
          Real.rpow
            (((chapter02Degree K : ℝ) ^ chapter02Degree K) /
              (Nat.factorial (chapter02Degree K) : ℝ))
            (2 / (chapter02Degree K : ℝ) * (chapter02Degree K : ℝ)) := by
        have hpiPow :
            (Real.rpow (Real.pi / 4) (1 - chapter02RealProportion K)) ^
                (chapter02Degree K : ℝ) =
              Real.rpow (Real.pi / 4)
                ((1 - chapter02RealProportion K) * (chapter02Degree K : ℝ)) :=
          (Real.rpow_mul hpi (1 - chapter02RealProportion K)
            (chapter02Degree K : ℝ)).symm
        unfold chapter02FactorialFactor
        have hfactorPow :
            (Real.rpow
              (((chapter02Degree K : ℝ) ^ chapter02Degree K) /
                (Nat.factorial (chapter02Degree K) : ℝ))
              (2 / (chapter02Degree K : ℝ))) ^ (chapter02Degree K : ℝ) =
              Real.rpow
                (((chapter02Degree K : ℝ) ^ chapter02Degree K) /
                  (Nat.factorial (chapter02Degree K) : ℝ))
                (2 / (chapter02Degree K : ℝ) * (chapter02Degree K : ℝ)) :=
          (Real.rpow_mul hratio (2 / (chapter02Degree K : ℝ))
            (chapter02Degree K : ℝ)).symm
        rw [hpiPow, hfactorPow]
      _ = Real.rpow (Real.pi / 4) (2 * chapter02ComplexPlaces K) *
          Real.rpow
            (((chapter02Degree K : ℝ) ^ chapter02Degree K) /
              (Nat.factorial (chapter02Degree K) : ℝ)) 2 := by
        rw [hαpow, hfacpow]
      _ = (Real.pi / 4) ^ (2 * chapter02ComplexPlaces K) *
          ((chapter02Degree K : ℝ) ^ chapter02Degree K /
            (Nat.factorial (chapter02Degree K) : ℝ)) ^ 2 := by
        congr 1
        · rw [← Real.rpow_natCast]
          norm_num [Nat.cast_mul]
        · exact Real.rpow_two _
      _ = (Real.pi / 4) ^ (2 * chapter02ComplexPlaces K) *
          (chapter02Degree K : ℝ) ^ (2 * chapter02Degree K) /
            (Nat.factorial (chapter02Degree K) : ℝ) ^ 2 := by
        have hnum :
            ((chapter02Degree K : ℝ) ^ chapter02Degree K) ^ 2 =
              (chapter02Degree K : ℝ) ^ (2 * chapter02Degree K) := by
          rw [← pow_mul, Nat.mul_comm]
        have hquot :
            ((chapter02Degree K : ℝ) ^ chapter02Degree K /
                (Nat.factorial (chapter02Degree K) : ℝ)) ^ 2 =
              ((chapter02Degree K : ℝ) ^ chapter02Degree K) ^ 2 /
                (Nat.factorial (chapter02Degree K) : ℝ) ^ 2 := by
          exact div_pow _ _ _
        rw [hquot, hnum]
        ring
  rw [chapter02_root_discriminant_def]
  apply (Real.le_rpow_inv_iff_of_pos hgeom hdisc hdeg).2
  rw [hpow]
  exact chapter02_discriminant_lower_bound_book_form K

/-- The book-facing and absolute-discriminant formulations are equivalent. -/
theorem chapter02_root_bound_equivalent_to_discriminant_bound
    (K : Type*) [Field K] [NumberField K] :
    chapter02GeometricLowerBound K ≤ chapter02RootDiscriminant K ↔
      (chapter02Degree K : ℝ) ^ (2 * chapter02Degree K) /
          ((4 / Real.pi) ^ (2 * chapter02ComplexPlaces K) *
            (Nat.factorial (chapter02Degree K) : ℝ) ^ 2) ≤
        chapter02AbsoluteDiscriminant K := by
  have hdeg : 0 < (chapter02Degree K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  have hdeg0 : (chapter02Degree K : ℝ) ≠ 0 := ne_of_gt hdeg
  have hdisc : 0 ≤ chapter02AbsoluteDiscriminant K :=
    (chapter02_absolute_discriminant_pos K).le
  have hfactor : 0 ≤ chapter02FactorialFactor (chapter02Degree K) := by
    unfold chapter02FactorialFactor
    exact Real.rpow_nonneg (div_nonneg (pow_nonneg (le_of_lt hdeg) _)
      (by positivity)) _
  have hpi : 0 ≤ Real.pi / 4 := by positivity
  have hpiFactor : 0 ≤ Real.rpow (Real.pi / 4)
      (1 - chapter02RealProportion K) := Real.rpow_nonneg hpi _
  have hgeom : 0 ≤ chapter02GeometricLowerBound K := by
    unfold chapter02GeometricLowerBound
    exact mul_nonneg (Real.rpow_nonneg hpi _) hfactor
  have hratio : 0 ≤
      ((chapter02Degree K : ℝ) ^ chapter02Degree K) /
        (Nat.factorial (chapter02Degree K) : ℝ) := by
    exact div_nonneg (pow_nonneg (le_of_lt hdeg) _) (by positivity)
  have hαpow :
      (1 - chapter02RealProportion K) * (chapter02Degree K : ℝ) =
        2 * (chapter02ComplexPlaces K : ℝ) := by
    rw [← chapter02_complex_proportion_eq_one_sub_real_proportion K]
    field_simp [hdeg0]
  have hfacpow :
      2 / (chapter02Degree K : ℝ) * (chapter02Degree K : ℝ) = 2 := by
    field_simp [hdeg0]
  have hpow :
      (chapter02GeometricLowerBound K) ^ (chapter02Degree K : ℝ) =
        (Real.pi / 4) ^ (2 * chapter02ComplexPlaces K) *
          (chapter02Degree K : ℝ) ^ (2 * chapter02Degree K) /
            (Nat.factorial (chapter02Degree K) : ℝ) ^ 2 := by
    calc
      (chapter02GeometricLowerBound K) ^ (chapter02Degree K : ℝ) =
          (Real.rpow (Real.pi / 4) (1 - chapter02RealProportion K)) ^
              (chapter02Degree K : ℝ) *
            (chapter02FactorialFactor (chapter02Degree K)) ^
              (chapter02Degree K : ℝ) := by
        rw [chapter02GeometricLowerBound, Real.mul_rpow hpiFactor hfactor]
      _ = Real.rpow (Real.pi / 4)
            ((1 - chapter02RealProportion K) * (chapter02Degree K : ℝ)) *
          Real.rpow
            (((chapter02Degree K : ℝ) ^ chapter02Degree K) /
              (Nat.factorial (chapter02Degree K) : ℝ))
            (2 / (chapter02Degree K : ℝ) * (chapter02Degree K : ℝ)) := by
        have hpiPow :
            (Real.rpow (Real.pi / 4) (1 - chapter02RealProportion K)) ^
                (chapter02Degree K : ℝ) =
              Real.rpow (Real.pi / 4)
                ((1 - chapter02RealProportion K) * (chapter02Degree K : ℝ)) :=
          (Real.rpow_mul hpi (1 - chapter02RealProportion K)
            (chapter02Degree K : ℝ)).symm
        unfold chapter02FactorialFactor
        have hfactorPow :
            (Real.rpow
              (((chapter02Degree K : ℝ) ^ chapter02Degree K) /
                (Nat.factorial (chapter02Degree K) : ℝ))
              (2 / (chapter02Degree K : ℝ))) ^ (chapter02Degree K : ℝ) =
              Real.rpow
                (((chapter02Degree K : ℝ) ^ chapter02Degree K) /
                  (Nat.factorial (chapter02Degree K) : ℝ))
                (2 / (chapter02Degree K : ℝ) * (chapter02Degree K : ℝ)) :=
          (Real.rpow_mul hratio (2 / (chapter02Degree K : ℝ))
            (chapter02Degree K : ℝ)).symm
        rw [hpiPow, hfactorPow]
      _ = Real.rpow (Real.pi / 4) (2 * chapter02ComplexPlaces K) *
          Real.rpow
            (((chapter02Degree K : ℝ) ^ chapter02Degree K) /
              (Nat.factorial (chapter02Degree K) : ℝ)) 2 := by
        rw [hαpow, hfacpow]
      _ = (Real.pi / 4) ^ (2 * chapter02ComplexPlaces K) *
          ((chapter02Degree K : ℝ) ^ chapter02Degree K /
            (Nat.factorial (chapter02Degree K) : ℝ)) ^ 2 := by
        congr 1
        · rw [← Real.rpow_natCast]
          norm_num [Nat.cast_mul]
        · exact Real.rpow_two _
      _ = (Real.pi / 4) ^ (2 * chapter02ComplexPlaces K) *
          (chapter02Degree K : ℝ) ^ (2 * chapter02Degree K) /
            (Nat.factorial (chapter02Degree K) : ℝ) ^ 2 := by
        have hnum :
            ((chapter02Degree K : ℝ) ^ chapter02Degree K) ^ 2 =
              (chapter02Degree K : ℝ) ^ (2 * chapter02Degree K) := by
          rw [← pow_mul, Nat.mul_comm]
        have hquot :
            ((chapter02Degree K : ℝ) ^ chapter02Degree K /
                (Nat.factorial (chapter02Degree K) : ℝ)) ^ 2 =
              ((chapter02Degree K : ℝ) ^ chapter02Degree K) ^ 2 /
                (Nat.factorial (chapter02Degree K) : ℝ) ^ 2 := by
          exact div_pow _ _ _
        rw [hquot, hnum]
        ring
  rw [chapter02_root_discriminant_def]
  have hbook_eq :
      (Real.pi / 4) ^ (2 * chapter02ComplexPlaces K) *
          (chapter02Degree K : ℝ) ^ (2 * chapter02Degree K) /
            (Nat.factorial (chapter02Degree K) : ℝ) ^ 2 =
        (chapter02Degree K : ℝ) ^ (2 * chapter02Degree K) /
          ((4 / Real.pi) ^ (2 * chapter02ComplexPlaces K) *
            (Nat.factorial (chapter02Degree K) : ℝ) ^ 2) := by
    have hpiPow :
        (Real.pi / 4) ^ (2 * chapter02ComplexPlaces K) *
            (4 / Real.pi) ^ (2 * chapter02ComplexPlaces K) = 1 := by
      rw [← mul_pow]
      field_simp [Real.pi_ne_zero]
      simp
    field_simp [Real.pi_ne_zero]
    exact hpiPow
  constructor
  · intro h
    have hp := (Real.le_rpow_inv_iff_of_pos hgeom hdisc hdeg).1 h
    rw [hpow, hbook_eq] at hp
    exact hp
  · intro h
    apply (Real.le_rpow_inv_iff_of_pos hgeom hdisc hdeg).2
    rw [hpow, hbook_eq]
    exact h

/-- The unrestricted-signature lower bound is obtained at `α = 0`. -/
theorem chapter02_geometric_lower_bound_ge_worst_signature
    (K : Type*) [Field K] [NumberField K] :
    Real.pi / 4 * chapter02FactorialFactor (chapter02Degree K) ≤
      chapter02GeometricLowerBound K := by
  have hα := (chapter02_real_proportion_bounds K).1
  have hpow : (Real.pi / 4) ^ (1 : ℝ) ≤
      (Real.pi / 4) ^ (1 - chapter02RealProportion K) := by
    apply Real.rpow_le_rpow_of_exponent_ge (by positivity) (by
      have := Real.pi_lt_four
      linarith) 
    linarith
  have hfac : 0 ≤ chapter02FactorialFactor (chapter02Degree K) := by
    unfold chapter02FactorialFactor
    have hdeg : 0 < (chapter02Degree K : ℝ) := by
      exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
    apply Real.rpow_nonneg
    positivity
  unfold chapter02GeometricLowerBound
  exact mul_le_mul_of_nonneg_right (by simpa using hpow) hfac

/-- In the totally real case, the signature factor is exactly one. -/
theorem chapter02_totally_real_geometric_lower_bound_eq
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] :
    chapter02GeometricLowerBound K =
      chapter02FactorialFactor (chapter02Degree K) := by
  have hcomplex : chapter02ComplexPlaces K = 0 :=
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero K
  have hreal : chapter02RealPlaces K = chapter02Degree K := by
    simpa [hcomplex] using (chapter02_signature_degree K)
  have hdegpos : 0 < (chapter02Degree K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  have hdeg : (chapter02Degree K : ℝ) ≠ 0 := ne_of_gt hdegpos
  rw [chapter02GeometricLowerBound, chapter02RealProportion, hreal,
    div_self hdeg, sub_self]
  simp

/-- For a totally real field, the factor `π/4` disappears. -/
theorem chapter02_totally_real_geometric_lower_bound
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] :
    chapter02FactorialFactor (chapter02Degree K) ≤ chapter02RootDiscriminant K := by
  rw [← chapter02_totally_real_geometric_lower_bound_eq K]
  exact chapter02_root_discriminant_lower_bound K

/-! ## 2.4 Monotonicity of the factorial factor -/

/-- The auxiliary sequence `aₙ = (n!)^(1/n)/n`. -/
noncomputable def chapter02FactorialRootRatio (n : ℕ) : ℝ :=
  Real.rpow (Nat.factorial n : ℝ) ((n : ℝ)⁻¹) / (n : ℝ)

/-- `Mₙ` is the inverse square of `aₙ` at positive indices. -/
theorem chapter02_factorial_factor_eq_ratio_inv_sq
    {n : ℕ} (hn : 0 < n) :
    chapter02FactorialFactor n =
      (chapter02FactorialRootRatio n)⁻¹ ^ (2 : ℕ) := by
  unfold chapter02FactorialFactor chapter02FactorialRootRatio
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hfac : 0 < (Nat.factorial n : ℝ) := by positivity
  have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hratio : 0 ≤ Real.rpow (Nat.factorial n : ℝ) ((n : ℝ)⁻¹) / (n : ℝ) := by
    exact div_nonneg (Real.rpow_nonneg hfac.le _) hnnonneg
  rw [← Real.rpow_natCast
    ((Real.rpow (Nat.factorial n : ℝ) ((n : ℝ)⁻¹) / (n : ℝ))⁻¹) 2]
  rw [inv_div]
  have hdiv :
      ((n : ℝ) / Real.rpow (Nat.factorial n : ℝ) ((n : ℝ)⁻¹)) ^ ((2 : ℕ) : ℝ) =
        (n : ℝ) ^ ((2 : ℕ) : ℝ) /
          (Real.rpow (Nat.factorial n : ℝ) ((n : ℝ)⁻¹)) ^ ((2 : ℕ) : ℝ) := by
    exact Real.div_rpow hnnonneg (Real.rpow_nonneg hfac.le _) 2
  rw [hdiv]
  have hpowfac :
      (Real.rpow (Nat.factorial n : ℝ) ((n : ℝ)⁻¹)) ^ ((2 : ℕ) : ℝ) =
        Real.rpow (Nat.factorial n : ℝ) ((n : ℝ)⁻¹ * (2 : ℝ)) := by
    symm
    exact Real.rpow_mul hfac.le ((n : ℝ)⁻¹) 2
  rw [hpowfac]
  have hdivleft :
      Real.rpow ((n : ℝ) ^ n / (Nat.factorial n : ℝ)) (2 / (n : ℝ)) =
        Real.rpow ((n : ℝ) ^ n) (2 / (n : ℝ)) /
          Real.rpow (Nat.factorial n : ℝ) (2 / (n : ℝ)) := by
    exact Real.div_rpow (x := (n : ℝ) ^ n) (y := (Nat.factorial n : ℝ))
      (by positivity) hfac.le (2 / (n : ℝ))
  rw [hdivleft]
  have hpow_n :
      Real.rpow ((n : ℝ) ^ n) (2 / (n : ℝ)) =
        Real.rpow (n : ℝ) ((2 : ℕ) : ℝ) := by
    have hpow :
        Real.rpow (Real.rpow (n : ℝ) (n : ℝ)) (2 / (n : ℝ)) =
          Real.rpow (n : ℝ) ((n : ℝ) * (2 / (n : ℝ))) := by
      symm
      exact Real.rpow_mul hnnonneg (n : ℝ) (2 / (n : ℝ))
    calc
      Real.rpow ((n : ℝ) ^ n) (2 / (n : ℝ)) =
          Real.rpow (Real.rpow (n : ℝ) (n : ℝ)) (2 / (n : ℝ)) := by
            have hcast : Real.rpow (n : ℝ) (n : ℝ) = (n : ℝ) ^ n :=
              Real.rpow_natCast (n : ℝ) n
            rw [hcast]
      _ = Real.rpow (n : ℝ) ((n : ℝ) * (2 / (n : ℝ))) := hpow
      _ = Real.rpow (n : ℝ) ((2 : ℕ) : ℝ) := by
        congr 1
        field_simp [hn0]
        norm_num
  rw [hpow_n]
  congr 1
  ring_nf

/-- The adjacent comparison for `aₙ` after clearing positive powers. -/
theorem chapter02_factorial_ratio_succ_le_iff
    {n : ℕ} (hn : 0 < n) :
    chapter02FactorialRootRatio (n + 1) ≤ chapter02FactorialRootRatio n ↔
      (1 + 1 / (n : ℝ)) ^ (n * n) ≥
        (n : ℝ) ^ n / (Nat.factorial n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hsuccpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hfacpos : ∀ m : ℕ, 0 < (Nat.factorial m : ℝ) := by
    intro m
    positivity
  have hratio_pos : ∀ {m : ℕ}, 0 < m → 0 < chapter02FactorialRootRatio m := by
    intro m hm
    unfold chapter02FactorialRootRatio
    exact div_pos (Real.rpow_pos_of_pos (hfacpos m) _) (Nat.cast_pos.mpr hm)
  have hratio_n : 0 < chapter02FactorialRootRatio n := hratio_pos hn
  have hratio_succ : 0 < chapter02FactorialRootRatio (n + 1) := by
    apply hratio_pos
    omega
  constructor
  · intro h
    have hlog := (Real.log_le_log_iff hratio_succ hratio_n).2 h
    change Real.log
        (Real.rpow (Nat.factorial (n + 1) : ℝ) (((n + 1 : ℕ) : ℝ)⁻¹) /
          ((n + 1 : ℕ) : ℝ)) ≤
      Real.log (Real.rpow (Nat.factorial n : ℝ) ((n : ℝ)⁻¹) / (n : ℝ)) at hlog
    have hlogdiv_succ :
        Real.log (Real.rpow (Nat.factorial (n + 1) : ℝ) (((n + 1 : ℕ) : ℝ)⁻¹) /
            ((n + 1 : ℕ) : ℝ)) =
          Real.log (Real.rpow (Nat.factorial (n + 1) : ℝ) (((n + 1 : ℕ) : ℝ)⁻¹)) -
            Real.log ((n + 1 : ℕ) : ℝ) := by
      exact Real.log_div (ne_of_gt (Real.rpow_pos_of_pos (hfacpos (n + 1)) _))
        (ne_of_gt hsuccpos)
    have hlogdiv_n :
        Real.log (Real.rpow (Nat.factorial n : ℝ) ((n : ℝ)⁻¹) / (n : ℝ)) =
          Real.log (Real.rpow (Nat.factorial n : ℝ) ((n : ℝ)⁻¹)) -
            Real.log (n : ℝ) := by
      exact Real.log_div (ne_of_gt (Real.rpow_pos_of_pos (hfacpos n) _))
        (ne_of_gt hnpos)
    have hlogrpow_succ :
        Real.log (Real.rpow (Nat.factorial (n + 1) : ℝ) (((n + 1 : ℕ) : ℝ)⁻¹)) =
          ((n + 1 : ℕ) : ℝ)⁻¹ * Real.log (Nat.factorial (n + 1) : ℝ) := by
      exact Real.log_rpow (hfacpos (n + 1)) _
    have hlogrpow_n :
        Real.log (Real.rpow (Nat.factorial n : ℝ) ((n : ℝ)⁻¹)) =
          (n : ℝ)⁻¹ * Real.log (Nat.factorial n : ℝ) := by
      exact Real.log_rpow (hfacpos n) _
    rw [hlogdiv_succ, hlogdiv_n, hlogrpow_succ, hlogrpow_n] at hlog
    rw [Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (ne_of_gt (hfacpos n))] at hlog
    have hbase_left : 0 < (1 + 1 / (n : ℝ)) ^ (n * n) := by
      exact pow_pos (by positivity) _
    have hbase_right : 0 < (n : ℝ) ^ n / (Nat.factorial n : ℝ) := by
      exact div_pos (pow_pos hnpos _) (hfacpos n)
    apply (Real.log_le_log_iff hbase_right hbase_left).mp
    have hlog_right :
        Real.log ((n : ℝ) ^ n / (Nat.factorial n : ℝ)) =
          (n : ℝ) * Real.log (n : ℝ) - Real.log (Nat.factorial n : ℝ) := by
      rw [Real.log_div (by positivity) (ne_of_gt (hfacpos n)), Real.log_pow]
    have hlog_left :
        Real.log ((1 + 1 / (n : ℝ)) ^ (n * n)) =
          ((n * n : ℕ) : ℝ) * Real.log (1 + 1 / (n : ℝ)) := by
      exact Real.log_pow _ _
    have hlog_one :
        Real.log (1 + 1 / (n : ℝ)) =
          Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
      have heq : 1 + 1 / (n : ℝ) = ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
        field_simp [hn0]
        norm_num [Nat.cast_add]
      rw [heq, Real.log_div (ne_of_gt hsuccpos) (ne_of_gt hnpos)]
    rw [hlog_right, hlog_left, hlog_one]
    have hscaled := mul_le_mul_of_nonneg_left hlog
      (le_of_lt (mul_pos hnpos hsuccpos))
    field_simp [hn0, ne_of_gt hsuccpos] at hscaled
    norm_num [Nat.cast_add, Nat.cast_mul] at hscaled ⊢
    linarith
  · intro h
    have hbase_left : 0 < (1 + 1 / (n : ℝ)) ^ (n * n) := by
      exact pow_pos (by positivity) _
    have hbase_right : 0 < (n : ℝ) ^ n / (Nat.factorial n : ℝ) := by
      exact div_pos (pow_pos hnpos _) (hfacpos n)
    have hlog_right :
        Real.log ((n : ℝ) ^ n / (Nat.factorial n : ℝ)) =
          (n : ℝ) * Real.log (n : ℝ) - Real.log (Nat.factorial n : ℝ) := by
      rw [Real.log_div (by positivity) (ne_of_gt (hfacpos n)), Real.log_pow]
    have hlog_left :
        Real.log ((1 + 1 / (n : ℝ)) ^ (n * n)) =
          ((n * n : ℕ) : ℝ) * Real.log (1 + 1 / (n : ℝ)) := by
      exact Real.log_pow _ _
    have hlog_one :
        Real.log (1 + 1 / (n : ℝ)) =
          Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
      have heq : 1 + 1 / (n : ℝ) = ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
        field_simp [hn0]
        norm_num [Nat.cast_add]
      rw [heq, Real.log_div (ne_of_gt hsuccpos) (ne_of_gt hnpos)]
    have hlog_target := (Real.log_le_log_iff hbase_right hbase_left).2 h
    rw [hlog_right, hlog_left, hlog_one] at hlog_target
    norm_num [Nat.cast_add, Nat.cast_mul] at hlog_target
    have hlog :
        ((n + 1 : ℕ) : ℝ)⁻¹ *
              (Real.log ((n + 1 : ℕ) : ℝ) + Real.log (Nat.factorial n : ℝ)) -
            Real.log ((n + 1 : ℕ) : ℝ) ≤
          (n : ℝ)⁻¹ * Real.log (Nat.factorial n : ℝ) - Real.log (n : ℝ) := by
      field_simp [hn0, ne_of_gt hsuccpos]
      norm_num [Nat.cast_add] at hlog_target ⊢
      linarith
    have hlogdiv_succ :
        Real.log (Real.rpow (Nat.factorial (n + 1) : ℝ) (((n + 1 : ℕ) : ℝ)⁻¹) /
            ((n + 1 : ℕ) : ℝ)) =
          Real.log (Real.rpow (Nat.factorial (n + 1) : ℝ) (((n + 1 : ℕ) : ℝ)⁻¹)) -
            Real.log ((n + 1 : ℕ) : ℝ) := by
      exact Real.log_div (ne_of_gt (Real.rpow_pos_of_pos (hfacpos (n + 1)) _))
        (ne_of_gt hsuccpos)
    have hlogdiv_n :
        Real.log (Real.rpow (Nat.factorial n : ℝ) ((n : ℝ)⁻¹) / (n : ℝ)) =
          Real.log (Real.rpow (Nat.factorial n : ℝ) ((n : ℝ)⁻¹)) -
            Real.log (n : ℝ) := by
      exact Real.log_div (ne_of_gt (Real.rpow_pos_of_pos (hfacpos n) _))
        (ne_of_gt hnpos)
    have hlogrpow_succ :
        Real.log (Real.rpow (Nat.factorial (n + 1) : ℝ) (((n + 1 : ℕ) : ℝ)⁻¹)) =
          ((n + 1 : ℕ) : ℝ)⁻¹ * Real.log (Nat.factorial (n + 1) : ℝ) := by
      exact Real.log_rpow (hfacpos (n + 1)) _
    have hlogrpow_n :
        Real.log (Real.rpow (Nat.factorial n : ℝ) ((n : ℝ)⁻¹)) =
          (n : ℝ)⁻¹ * Real.log (Nat.factorial n : ℝ) := by
      exact Real.log_rpow (hfacpos n) _
    apply (Real.log_le_log_iff hratio_succ hratio_n).1
    change Real.log
        (Real.rpow (Nat.factorial (n + 1) : ℝ) (((n + 1 : ℕ) : ℝ)⁻¹) /
          ((n + 1 : ℕ) : ℝ)) ≤
      Real.log (Real.rpow (Nat.factorial n : ℝ) ((n : ℝ)⁻¹) / (n : ℝ))
    rw [hlogdiv_succ, hlogdiv_n, hlogrpow_succ, hlogrpow_n]
    have hfaclog :
        Real.log (Nat.factorial (n + 1) : ℝ) =
          Real.log ((n + 1 : ℕ) : ℝ) + Real.log (Nat.factorial n : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul,
        Real.log_mul (by positivity) (ne_of_gt (hfacpos n))]
    rw [hfaclog]
    exact hlog

/-- The integral comparison for `log(n!)`. -/
theorem chapter02_log_factorial_eq_sum_log
    {n : ℕ} (hn : 1 ≤ n) :
    Real.log (Nat.factorial n : ℝ) =
      Finset.sum (Finset.range n) (fun k => Real.log (k + 1 : ℝ)) := by
  have _ := hn
  rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
  rw [Real.log_prod]
  · simp_rw [Nat.cast_add, Nat.cast_one]
  · intro k hk
    positivity

/-- The integral comparison for `log(n!)`. -/
theorem chapter02_log_factorial_integral_comparison
    {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n + 1 =
        ∫ x in (1 : ℝ)..(n : ℝ), Real.log x ∧
      ∫ x in (1 : ℝ)..(n : ℝ), Real.log x ≤
        Real.log (Nat.factorial n : ℝ) := by
  constructor
  · simp
  · have hmono : MonotoneOn Real.log
        (Set.Icc ((1 : ℕ) : ℝ) ((n : ℕ) : ℝ)) := by
      apply Real.strictMonoOn_log.monotoneOn.mono
      intro x hx
      have hx' : (1 : ℝ) ≤ x := by simpa using hx.1
      exact lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) hx'
    have hsum := MonotoneOn.integral_le_sum_Ico (f := Real.log) hn hmono
    calc
      ∫ x in (1 : ℝ)..(n : ℝ), Real.log x ≤
          ∑ x ∈ Finset.Ico 1 n, Real.log (x + 1 : ℝ) := by
            simpa only [Nat.cast_add, Nat.cast_one] using hsum
      _ = ∑ k ∈ Finset.range n, Real.log (k + 1 : ℝ) := by
        rw [← Nat.Ico_zero_eq_range]
        have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
        rw [← Finset.insert_Ico_add_one_left_eq_Ico (a := 0) (b := n) hn0]
        rw [Finset.sum_insert]
        · simp
        · simp
      _ = Real.log (Nat.factorial n : ℝ) :=
        (chapter02_log_factorial_eq_sum_log hn).symm

/-- The derivative of the quadratic remainder in the logarithm estimate. -/
theorem chapter02_log_one_add_quadratic_remainder_deriv
    {u : ℝ} (hu : -1 < u) :
    HasDerivAt
      (fun v : ℝ => Real.log (1 + v) - v + v ^ 2 / 2)
      (u ^ 2 / (1 + u)) u := by
  have h1 : (1 + u : ℝ) ≠ 0 := by linarith
  have hlog : HasDerivAt (fun v : ℝ => Real.log (1 + v))
      ((1 + u)⁻¹) u := by
    simpa [one_div] using
      (((hasDerivAt_id u).const_add (1 : ℝ)).log h1)
  have h_id : HasDerivAt (fun v : ℝ => v) 1 u := hasDerivAt_id u
  have hpoly := (hasDerivAt_id u).pow 2
  convert (hlog.sub h_id).add (hpoly.div_const 2) using 1
  · exact AddCommGroup.ext (by rfl)
  · apply Module.ext'
    intro r x
    rfl
  · funext v
    simp [id]
  · simp [id]
    field_simp [h1]
    ring

/-- The elementary lower bound `log(1+u) ≥ u-u²/2`. -/
theorem chapter02_log_one_add_quadratic_lower
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u - u ^ 2 / 2 ≤ Real.log (1 + u) := by
  have hcont : ContinuousOn
      (fun v : ℝ => Real.log (1 + v) - v + v ^ 2 / 2)
      (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.add
    · apply ContinuousOn.sub
      · apply ContinuousOn.log (continuousOn_const.add continuousOn_id)
        intro x hx
        change (1 : ℝ) + x ≠ 0
        exact ne_of_gt (by linarith [hx.1])
      · exact continuousOn_id
    · exact (continuousOn_id.pow 2).div_const 2
  have hdiff : DifferentiableOn ℝ
      (fun v : ℝ => Real.log (1 + v) - v + v ^ 2 / 2)
      (interior (Set.Icc (0 : ℝ) 1)) := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hx
    have hx' : -1 < x := by
      have hx0 : 0 < x := hxIoo.1
      linarith
    exact ((chapter02_log_one_add_quadratic_remainder_deriv hx').differentiableAt).differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Set.Icc (0 : ℝ) 1),
      0 ≤ deriv
        (fun v : ℝ => Real.log (1 + v) - v + v ^ 2 / 2) x := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hx
    have hx' : -1 < x := by
      have hx0 : 0 < x := hxIoo.1
      linarith
    rw [(chapter02_log_one_add_quadratic_remainder_deriv hx').deriv]
    exact div_nonneg (sq_nonneg _) (by linarith)
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
    hcont hdiff hderiv
  have h := hmono (by simp) (by exact ⟨hu0, hu1⟩) hu0
  dsimp at h
  simp at h
  linarith

/-- The logarithmic comparisons used in the monotonicity proof. -/
theorem chapter02_reciprocal_log_comparison
    {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 2 * Real.log (1 + 1 / (n : ℝ)) ≥
        (n : ℝ) - 1 / 2 ∧
      Real.log (((n : ℝ) ^ n) / (Nat.factorial n : ℝ)) ≤
        (n : ℝ) - 1 := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have hinv0 : 0 ≤ (n : ℝ)⁻¹ := (inv_pos.mpr hnpos).le
  have hinv1 : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
  have hlog := chapter02_log_one_add_quadratic_lower hinv0 hinv1
  have hscaled := mul_le_mul_of_nonneg_left hlog (sq_nonneg (n : ℝ))
  have hfirst' : (n : ℝ) - 1 / 2 ≤
      (n : ℝ) ^ 2 * Real.log (((n : ℝ) + 1) / (n : ℝ)) := by
    field_simp [hn0] at hscaled
    nlinarith [hscaled]
  have heq : 1 + 1 / (n : ℝ) = ((n : ℝ) + 1) / (n : ℝ) := by
    field_simp [hn0]
  have hfirst : (n : ℝ) - 1 / 2 ≤
      (n : ℝ) ^ 2 * Real.log (1 + 1 / (n : ℝ)) := by
    rw [heq]
    exact hfirst'
  constructor
  · exact hfirst
  · have hcomp := chapter02_log_factorial_integral_comparison
        (n := n) (Nat.succ_le_iff.mpr hn)
    have hfac : (n : ℝ) * Real.log n - n + 1 ≤
        Real.log (Nat.factorial n : ℝ) := by
      calc
        (n : ℝ) * Real.log n - n + 1 =
            ∫ x in (1 : ℝ)..(n : ℝ), Real.log x := hcomp.1
        _ ≤ Real.log (Nat.factorial n : ℝ) := hcomp.2
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
    linarith

/-- The auxiliary sequence is nonincreasing at adjacent positive indices. -/
theorem chapter02_factorial_root_ratio_succ_le
    {n : ℕ} (hn : 0 < n) :
    chapter02FactorialRootRatio (n + 1) ≤ chapter02FactorialRootRatio n := by
  apply (chapter02_factorial_ratio_succ_le_iff hn).2
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hleftpos : 0 < (1 + 1 / (n : ℝ)) ^ (n * n) := by
    exact pow_pos (by positivity) _
  have hrightpos : 0 < (n : ℝ) ^ n / (Nat.factorial n : ℝ) := by
    exact div_pos (pow_pos hnpos _) (by positivity)
  have hlogleft :
      Real.log ((1 + 1 / (n : ℝ)) ^ (n * n)) =
        (n : ℝ) ^ 2 * Real.log (1 + 1 / (n : ℝ)) := by
    rw [Real.log_pow]
    congr 1
    norm_num [Nat.cast_mul]
    ring
  have hlogright :
      Real.log ((n : ℝ) ^ n / (Nat.factorial n : ℝ)) =
        (n : ℝ) * Real.log (n : ℝ) - Real.log (Nat.factorial n : ℝ) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
  apply (Real.log_le_log_iff hrightpos hleftpos).mp
  rw [hlogright, hlogleft]
  have hcomp := chapter02_reciprocal_log_comparison hn
  linarith [hcomp.1, hcomp.2]

/-- The factorial factor is nondecreasing at adjacent positive indices. -/
theorem chapter02_factorial_factor_succ_le
    {n : ℕ} (hn : 0 < n) :
    chapter02FactorialFactor n ≤ chapter02FactorialFactor (n + 1) := by
  rw [chapter02_factorial_factor_eq_ratio_inv_sq hn,
    chapter02_factorial_factor_eq_ratio_inv_sq (by omega)]
  have hratio := chapter02_factorial_root_ratio_succ_le hn
  have hpos_n : 0 < chapter02FactorialRootRatio n := by
    unfold chapter02FactorialRootRatio
    exact div_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Nat.cast_pos.mpr hn)
  have hpos_succ : 0 < chapter02FactorialRootRatio (n + 1) := by
    unfold chapter02FactorialRootRatio
    exact div_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Nat.cast_pos.mpr (by omega))
  have hinv : (chapter02FactorialRootRatio n)⁻¹ ≤
      (chapter02FactorialRootRatio (n + 1))⁻¹ :=
    (inv_le_inv₀ hpos_n hpos_succ).2 hratio
  exact (sq_le_sq₀ (inv_nonneg.mpr hpos_n.le) (inv_nonneg.mpr hpos_succ.le)).2 hinv

/-- The factorial factor is monotone on positive natural indices. -/
theorem chapter02_factorial_factor_monotone :
    MonotoneOn chapter02FactorialFactor (Set.Ioi (0 : ℕ)) := by
  intro a ha b hb hab
  change 0 < a at ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      have hak : a + k ∈ Set.Ioi (0 : ℕ) := by
        change 0 < a + k
        omega
      have hakle : a ≤ a + k := Nat.le_add_right a k
      exact (ih hak hakle).trans (by
        simpa [Nat.add_assoc] using
          (chapter02_factorial_factor_succ_le (n := a + k) (by omega)))

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
  let b : ℕ → ℝ := fun n => 1 / (12 * (n : ℝ) * (n + 1 : ℝ))
  have hstep_lower : ∀ {n : ℕ}, 0 < n →
      b n - ((n : ℝ)⁻¹) ^ (4 : ℕ) ≤
        Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq (n + 1)) := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    let x : ℝ := 1 / (2 * (m + 1 : ℝ) + 1)
    have hseries := Stirling.log_stirlingSeq_sdiff_hasSum m
    have hfinite : HasSum
        (fun k : ℕ => if k < 2 then
          (1 : ℝ) / (2 * (k + 1 : ℝ) + 1) *
            (x ^ 2) ^ (k + 1) else 0)
        (x ^ 2 / 3 + x ^ 4 / 5) := by
      classical
      have hs := hasSum_sum_of_ne_finset_zero
        (L := SummationFilter.unconditional ℕ)
        (f := fun k : ℕ => if k < 2 then
          (1 : ℝ) / (2 * (k + 1 : ℝ) + 1) *
            (x ^ 2) ^ (k + 1) else 0)
        (s := Finset.range 2) (by
          intro k hk
          simp only [Finset.mem_range, not_lt] at hk
          rw [if_neg]
          omega)
      convert hs using 1
      norm_num [Finset.sum_range_succ]
      ring
    have hterm : ∀ k : ℕ,
        (if k < 2 then
          (1 : ℝ) / (2 * (k + 1 : ℝ) + 1) *
            (x ^ 2) ^ (k + 1) else 0) ≤
          (1 : ℝ) / (2 * (k + 1 : ℝ) + 1) *
            ((1 / (2 * (m + 1 : ℝ) + 1)) ^ 2) ^ (k + 1) := by
      intro k
      by_cases hk : k < 2
      · interval_cases k <;> simp [hk, x]
      · simp [hk]
        positivity
    have hlower : x ^ 2 / 3 + x ^ 4 / 5 ≤
        Real.log (Stirling.stirlingSeq (m + 1)) -
          Real.log (Stirling.stirlingSeq (m + 2)) := by
      exact hasSum_le hterm hfinite (by simpa [x] using hseries)
    have halg : b (m + 1) - (((m + 1 : ℕ) : ℝ)⁻¹) ^ (4 : ℕ) ≤
        x ^ 2 / 3 + x ^ 4 / 5 := by
      have hgeneric : ∀ t : ℝ, 0 < t →
          1 / (12 * t * (t + 1)) - t⁻¹ ^ (4 : ℕ) ≤
            (1 / (2 * t + 1)) ^ 2 / 3 +
              (1 / (2 * t + 1)) ^ 4 / 5 := by
        intro t ht
        have hden : 0 < 2 * t + 1 := by linarith
        field_simp
        ring_nf
        have hp : 0 ≤ 180 + 1620 * t + 5760 * t ^ 2 +
            10065 * t ^ 3 + 8616 * t ^ 4 + 2856 * t ^ 5 := by
          positivity
        nlinarith
      simpa [b, x, Nat.cast_add, Nat.cast_one] using
        hgeneric ((m + 1 : ℕ) : ℝ) (by positivity)
    exact halg.trans hlower
  have hstep_upper : ∀ {n : ℕ}, 0 < n →
      Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq (n + 1)) ≤
        1 / (12 * (n : ℝ)) -
          1 / (12 * ((n + 1 : ℕ) : ℝ)) := by
    intro n hn
    have h := Stirling.log_stirlingSeq_sdiff_le n
    calc
      Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq (n + 1)) ≤ b n := by
        simpa [b, Nat.cast_add, Nat.cast_one] using h
      _ = 1 / (12 * (n : ℝ)) -
          1 / (12 * ((n + 1 : ℕ) : ℝ)) := by
        dsimp [b]
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
        norm_num [Nat.cast_add, Nat.cast_one]
        field_simp [hn0]
        ring
  have hrecip_generic : ∀ t : ℝ, 1 < t →
      t⁻¹ ^ (4 : ℕ) ≤ (t - 1)⁻¹ ^ (3 : ℕ) - t⁻¹ ^ (3 : ℕ) := by
    intro t ht
    have htm : 0 < t - 1 := by linarith
    field_simp
    ring_nf
    nlinarith [mul_nonneg (show 0 ≤ t by positivity)
      (sub_nonneg.mpr (le_of_lt ht))]
  have hrecip : ∀ {n : ℕ}, 2 ≤ n →
      ((n : ℝ)⁻¹) ^ (4 : ℕ) ≤
        (((n - 1 : ℕ) : ℝ)⁻¹) ^ (3 : ℕ) - ((n : ℝ)⁻¹) ^ (3 : ℕ) := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn1]
      norm_num
    rw [hcast]
    exact hrecip_generic (n : ℝ) (by exact_mod_cast hn)
  have hstep_lower' : ∀ {n : ℕ}, 2 ≤ n →
      1 / (12 * (n : ℝ)) -
          1 / (12 * ((n + 1 : ℕ) : ℝ)) -
          ((((n - 1 : ℕ) : ℝ)⁻¹) ^ (3 : ℕ) -
            ((n : ℝ)⁻¹) ^ (3 : ℕ)) ≤
        Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq (n + 1)) := by
    intro n hn
    have hl := hstep_lower (n := n) (by omega)
    have hr := hrecip hn
    have hb : b n = 1 / (12 * (n : ℝ)) -
        1 / (12 * ((n + 1 : ℕ) : ℝ)) := by
      dsimp [b]
      have hn0 : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
      norm_num [Nat.cast_add, Nat.cast_one]
      field_simp [hn0]
      ring
    linarith
  have hloglim : Tendsto
      (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) atTop
        (𝓝 (Real.log (Real.sqrt Real.pi))) := by
    exact Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)
  have hfinite_upper : ∀ {n : ℕ}, 0 < n → ∀ N : ℕ,
      Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq (n + N)) ≤
        1 / (12 * (n : ℝ)) -
          1 / (12 * ((n + N : ℕ) : ℝ)) := by
    intro n hn N
    let f : ℕ → ℝ := fun k => Real.log (Stirling.stirlingSeq (n + k))
    let g : ℕ → ℝ := fun k => 1 / (12 * ((n + k : ℕ) : ℝ))
    calc
      Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq (n + N)) =
          ∑ k ∈ Finset.range N, (f k - f (k + 1)) := by
        rw [Finset.sum_range_sub']
        simp [f]
      _ ≤ ∑ k ∈ Finset.range N, (g k - g (k + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa [f, g, Nat.add_assoc] using
          (hstep_upper (n := n + k) (by omega))
      _ = g 0 - g N := by
        rw [Finset.sum_range_sub']
      _ = 1 / (12 * (n : ℝ)) -
          1 / (12 * ((n + N : ℕ) : ℝ)) := by
        simp [g]
  have hfinite_lower : ∀ {n : ℕ}, 2 ≤ n → ∀ N : ℕ,
      1 / (12 * (n : ℝ)) -
          1 / (12 * ((n + N : ℕ) : ℝ)) -
          ((((n - 1 : ℕ) : ℝ)⁻¹) ^ (3 : ℕ) -
            (((n + N - 1 : ℕ) : ℝ)⁻¹) ^ (3 : ℕ)) ≤
        Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq (n + N)) := by
    intro n hn N
    let f : ℕ → ℝ := fun k => Real.log (Stirling.stirlingSeq (n + k))
    let q : ℕ → ℝ := fun k => 1 / (12 * ((n + k : ℕ) : ℝ))
    let r : ℕ → ℝ := fun k => (((n + k - 1 : ℕ) : ℝ)⁻¹) ^ (3 : ℕ)
    calc
      1 / (12 * (n : ℝ)) -
          1 / (12 * ((n + N : ℕ) : ℝ)) -
          ((((n - 1 : ℕ) : ℝ)⁻¹) ^ (3 : ℕ) -
            (((n + N - 1 : ℕ) : ℝ)⁻¹) ^ (3 : ℕ)) =
          ∑ k ∈ Finset.range N,
            ((q k - q (k + 1)) - (r k - r (k + 1))) := by
        rw [Finset.sum_sub_distrib, Finset.sum_range_sub',
          Finset.sum_range_sub']
        simp [q, r]
      _ ≤ ∑ k ∈ Finset.range N, (f k - f (k + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa [f, q, r, Nat.add_assoc] using
          (hstep_lower' (n := n + k) (by omega))
      _ = Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq (n + N)) := by
        rw [Finset.sum_range_sub']
        simp [f]
  have hD_upper : ∀ {n : ℕ}, 0 < n →
      Real.log (Stirling.stirlingSeq n) -
          Real.log (Real.sqrt Real.pi) ≤ 1 / (12 * (n : ℝ)) := by
    intro n hn
    have hadd : Tendsto (fun N : ℕ => n + N) atTop atTop := by
      convert tendsto_add_atTop_nat n using 1
      funext N
      omega
    have hshift : Tendsto
        (fun N : ℕ => ((n + N : ℕ) : ℝ)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp hadd
    have htail : Tendsto
        (fun N : ℕ => 1 / (12 * ((n + N : ℕ) : ℝ))) atTop (𝓝 0) := by
      have hshift12 : Tendsto
          (fun N : ℕ => ((n + N : ℕ) : ℝ) * 12) atTop atTop :=
        hshift.atTop_mul_const (by norm_num)
      have h : Tendsto
          (fun N : ℕ => (1 : ℝ) / (((n + N : ℕ) : ℝ) * 12)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hshift12
      convert h using 1
      funext N
      field_simp
    have hleft : Tendsto
        (fun N : ℕ => Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq (n + N))) atTop
        (𝓝 (Real.log (Stirling.stirlingSeq n) -
          Real.log (Real.sqrt Real.pi))) := by
      simpa using
        (tendsto_const_nhds.sub (hloglim.comp hadd))
    have hright : Tendsto
        (fun N : ℕ => 1 / (12 * (n : ℝ)) -
          1 / (12 * ((n + N : ℕ) : ℝ))) atTop
        (𝓝 (1 / (12 * (n : ℝ)) - 0)) := by
      simpa using (tendsto_const_nhds.sub htail)
    have hle := le_of_tendsto_of_tendsto hleft hright
      (Eventually.of_forall (hfinite_upper (n := n) hn))
    simpa using hle
  have hD_lower : ∀ {n : ℕ}, 2 ≤ n →
      1 / (12 * (n : ℝ)) - (((n - 1 : ℕ) : ℝ)⁻¹) ^ (3 : ℕ) ≤
        Real.log (Stirling.stirlingSeq n) -
          Real.log (Real.sqrt Real.pi) := by
    intro n hn
    have hadd : Tendsto (fun N : ℕ => n + N) atTop atTop := by
      convert tendsto_add_atTop_nat n using 1
      funext N
      omega
    have hshift : Tendsto
        (fun N : ℕ => ((n + N : ℕ) : ℝ)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp hadd
    have htail : Tendsto
        (fun N : ℕ => 1 / (12 * ((n + N : ℕ) : ℝ))) atTop (𝓝 0) := by
      have hshift12 : Tendsto
          (fun N : ℕ => ((n + N : ℕ) : ℝ) * 12) atTop atTop :=
        hshift.atTop_mul_const (by norm_num)
      have h : Tendsto
          (fun N : ℕ => (1 : ℝ) / (((n + N : ℕ) : ℝ) * 12)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hshift12
      convert h using 1
      funext N
      field_simp
    have hshiftm : Tendsto
        (fun N : ℕ => ((n + N - 1 : ℕ) : ℝ)) atTop atTop := by
      have h : Tendsto
          (fun N : ℕ => ((N + (n - 1) : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat (n - 1))
      convert h using 1
      funext N
      congr 1
      omega
    have htailm : Tendsto
        (fun N : ℕ => (((n + N - 1 : ℕ) : ℝ)⁻¹) ^ (3 : ℕ)) atTop
          (𝓝 0) := by
      have h0 : Tendsto
          (fun N : ℕ => (1 : ℝ) / ((n + N - 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
        have h := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hshiftm
        simpa using h
      have h := h0.pow (3 : ℕ)
      simpa using h
    have hleft : Tendsto
        (fun N : ℕ => Real.log (Stirling.stirlingSeq n) -
          Real.log (Stirling.stirlingSeq (n + N))) atTop
        (𝓝 (Real.log (Stirling.stirlingSeq n) -
          Real.log (Real.sqrt Real.pi))) := by
      simpa using
        (tendsto_const_nhds.sub (hloglim.comp hadd))
    have hright : Tendsto
        (fun N : ℕ => 1 / (12 * (n : ℝ)) -
          1 / (12 * ((n + N : ℕ) : ℝ)) -
          ((((n - 1 : ℕ) : ℝ)⁻¹) ^ (3 : ℕ) -
            (((n + N - 1 : ℕ) : ℝ)⁻¹) ^ (3 : ℕ))) atTop
        (𝓝 (1 / (12 * (n : ℝ)) - 0 -
          ((((n - 1 : ℕ) : ℝ)⁻¹) ^ (3 : ℕ) - 0))) := by
      simpa using
        ((tendsto_const_nhds.sub htail).sub
          (tendsto_const_nhds.sub htailm))
    have hle := le_of_tendsto_of_tendsto hright hleft
      (Eventually.of_forall (hfinite_lower (n := n) hn))
    simpa using hle
  have herror_identity : ∀ {n : ℕ}, 0 < n →
      chapter02StirlingError n =
        (2 / (n : ℝ)) *
          (1 / (12 * (n : ℝ)) -
            (Real.log (Stirling.stirlingSeq n) -
              Real.log (Real.sqrt Real.pi))) := by
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    have hfaclog := Stirling.log_stirlingSeq_formula n
    rw [Real.log_div (by positivity) (by positivity), Real.log_exp] at hfaclog
    have hlogM : Real.log (chapter02FactorialFactor n) =
        2 - 2 * Real.log (Stirling.stirlingSeq n) / (n : ℝ) -
          Real.log (2 * (n : ℝ)) / (n : ℝ) := by
      unfold chapter02FactorialFactor
      have hnum0 : ((n : ℝ) ^ n) ≠ 0 := pow_ne_zero n hn0
      have hfac0 : (Nat.factorial n : ℝ) ≠ 0 := by positivity
      have hquotpos : 0 < ((n : ℝ) ^ n) / (Nat.factorial n : ℝ) :=
        div_pos (by positivity) (by positivity)
      have hpow : Real.rpow (((n : ℝ) ^ n) / (Nat.factorial n : ℝ))
          (2 / (n : ℝ)) =
          Real.exp (Real.log (((n : ℝ) ^ n) / (Nat.factorial n : ℝ)) *
            (2 / (n : ℝ))) :=
        Real.rpow_def_of_pos hquotpos _
      have hlogpow : Real.log ((n : ℝ) ^ n) =
          (n : ℝ) * Real.log (n : ℝ) := Real.log_pow (n : ℝ) n
      rw [hpow, Real.log_exp, Real.log_div hnum0 hfac0, hlogpow]
      rw [hfaclog]
      field_simp [hn0]
      ring
    have hlogprod : Real.log (2 * Real.pi * (n : ℝ)) =
        Real.log (2 * (n : ℝ)) + Real.log Real.pi := by
      rw [show 2 * Real.pi * (n : ℝ) = (2 * (n : ℝ)) * Real.pi by ring,
        Real.log_mul (by positivity) (by positivity)]
    rw [chapter02StirlingError, chapter02StirlingMainTerm, hlogM, hlogprod]
    field_simp [hn0]
    rw [Real.log_sqrt (by positivity)]
    ring
  refine ⟨16, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hnpos : 0 < n := by omega
  have hupper := hD_upper (n := n) hnpos
  have hlower := hD_lower (n := n) hn
  have hgap_nonneg : 0 ≤
      1 / (12 * (n : ℝ)) -
        (Real.log (Stirling.stirlingSeq n) -
          Real.log (Real.sqrt Real.pi)) := by
    linarith
  have hgap_le :
      1 / (12 * (n : ℝ)) -
          (Real.log (Stirling.stirlingSeq n) -
            Real.log (Real.sqrt Real.pi)) ≤
        (((n - 1 : ℕ) : ℝ)⁻¹) ^ (3 : ℕ) := by
    linarith
  have hn1 : 1 ≤ n := by omega
  have hrel : (n : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn1]
    norm_num [Nat.cast_one]
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hcube : (n : ℝ) ^ (3 : ℕ) ≤
      (2 * ((n - 1 : ℕ) : ℝ)) ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hrel 3
  have hbound :
      (2 / (n : ℝ)) * (((n - 1 : ℕ) : ℝ)⁻¹) ^ (3 : ℕ) ≤
        16 * ((n : ℝ)⁻¹) ^ (4 : ℕ) := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
    have hnm0 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
      have : 0 < n - 1 := by omega
      exact_mod_cast (Nat.ne_of_gt this)
    field_simp [hn0, hnm0]
    nlinarith [hcube]
  have hE_nonneg : 0 ≤
      (2 / (n : ℝ)) *
        (1 / (12 * (n : ℝ)) -
          (Real.log (Stirling.stirlingSeq n) -
            Real.log (Real.sqrt Real.pi))) := by
    exact mul_nonneg (by positivity) hgap_nonneg
  calc
    |chapter02StirlingError n| =
        |(2 / (n : ℝ)) *
          (1 / (12 * (n : ℝ)) -
            (Real.log (Stirling.stirlingSeq n) -
              Real.log (Real.sqrt Real.pi)))| := by
      rw [herror_identity hnpos]
    _ = (2 / (n : ℝ)) *
          (1 / (12 * (n : ℝ)) -
            (Real.log (Stirling.stirlingSeq n) -
              Real.log (Real.sqrt Real.pi))) := abs_of_nonneg hE_nonneg
    _ ≤ (2 / (n : ℝ)) * (((n - 1 : ℕ) : ℝ)⁻¹) ^ (3 : ℕ) := by
      exact mul_le_mul_of_nonneg_left hgap_le (by positivity)
    _ ≤ 16 * ((n : ℝ)⁻¹) ^ (4 : ℕ) := hbound

/-- The factorial factor tends to `e²`. -/
theorem chapter02_factorial_factor_tendsto :
    Tendsto chapter02FactorialFactor atTop (𝓝 (Real.exp 2)) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hstir := Stirling.tendsto_stirlingSeq_sqrt_pi
  have hlogstir : Tendsto
      (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) := by
    exact hstir.log (by positivity)
  have hlogstir_div : Tendsto
      (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ)) atTop
      (𝓝 0) := hlogstir.div_atTop hden
  have hlogn : Tendsto (fun n : ℕ => Real.log (2 * (n : ℝ)) / (n : ℝ)) atTop
      (𝓝 0) := by
    have h2n : Tendsto (fun n : ℕ => (n : ℝ) * 2) atTop atTop :=
      hden.atTop_mul_const (by norm_num)
    have hlogn' := (Real.tendsto_pow_log_div_mul_add_atTop
      (1 : ℝ) 0 1 one_ne_zero).comp h2n
    have hscaled := hlogn'.const_mul 2
    have hscaled' : Tendsto
        (fun n : ℕ => 2 * (Real.log ((n : ℝ) * 2) / ((n : ℝ) * 2))) atTop
        (𝓝 0) := by
      simpa [Function.comp_def, pow_one, one_mul] using hscaled
    convert hscaled' using 1
    · funext n
      cases n with
      | zero => simp
      | succ n =>
          field_simp
  have hlogM : Tendsto (fun n : ℕ => Real.log (chapter02FactorialFactor n)) atTop
      (𝓝 (2 : ℝ)) := by
    have hmain : Tendsto
        (fun n : ℕ => (2 : ℝ) - 2 *
          (Real.log (Stirling.stirlingSeq n) / (n : ℝ))) atTop
        (𝓝 ((2 : ℝ) - 2 * 0)) :=
      tendsto_const_nhds.sub (hlogstir_div.const_mul 2)
    have hmain' : Tendsto
        (fun n : ℕ => (2 : ℝ) - 2 *
          (Real.log (Stirling.stirlingSeq n) / (n : ℝ)) -
            Real.log (2 * (n : ℝ)) / (n : ℝ)) atTop
        (𝓝 (((2 : ℝ) - 2 * 0) - 0)) :=
      hmain.sub hlogn
    apply Tendsto.congr' ?_ (by simpa using hmain')
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hfaclog := Stirling.log_stirlingSeq_formula n
    rw [Real.log_div (by positivity) (by positivity), Real.log_exp] at hfaclog
    have hlog : Real.log (chapter02FactorialFactor n) =
        2 - 2 * Real.log (Stirling.stirlingSeq n) / (n : ℝ) -
          Real.log (2 * (n : ℝ)) / (n : ℝ) := by
      unfold chapter02FactorialFactor
      have hnum0 : ((n : ℝ) ^ n) ≠ 0 := pow_ne_zero n hn0
      have hfac0 : (Nat.factorial n : ℝ) ≠ 0 := by positivity
      have hquotpos : 0 < ((n : ℝ) ^ n) / (Nat.factorial n : ℝ) :=
        div_pos (by positivity) (by positivity)
      have hpow : Real.rpow (((n : ℝ) ^ n) / (Nat.factorial n : ℝ))
          (2 / (n : ℝ)) =
          Real.exp (Real.log (((n : ℝ) ^ n) / (Nat.factorial n : ℝ)) *
            (2 / (n : ℝ))) :=
        Real.rpow_def_of_pos hquotpos _
      have hlogpow : Real.log ((n : ℝ) ^ n) =
          (n : ℝ) * Real.log (n : ℝ) := Real.log_pow (n : ℝ) n
      rw [hpow, Real.log_exp, Real.log_div hnum0 hfac0, hlogpow]
      rw [hfaclog]
      field_simp [hn0]
      ring
    rw [hlog]
    ring
  have hMpos : ∀ n : ℕ, 0 < chapter02FactorialFactor n := by
    intro n
    cases n with
    | zero => simp [chapter02FactorialFactor]
    | succ n =>
        unfold chapter02FactorialFactor
        apply Real.rpow_pos_of_pos
        exact div_pos (by positivity) (by positivity)
  have hexp : Tendsto
      (fun n : ℕ => Real.exp (Real.log (chapter02FactorialFactor n))) atTop
      (𝓝 (Real.exp 2)) := by
    exact Real.continuous_exp.continuousAt.tendsto.comp hlogM
  apply Tendsto.congr' ?_ hexp
  filter_upwards [] with n
  rw [Real.exp_log (hMpos n)]

/-- The worst-signature geometric limit. -/
theorem chapter02_worst_signature_geometric_limit :
    Tendsto
      (fun n : ℕ => Real.pi / 4 * chapter02FactorialFactor n)
      atTop (𝓝 (Real.pi / 4 * Real.exp 2)) := by
  simpa only [Function.comp_def] using
    (chapter02_factorial_factor_tendsto.const_mul (Real.pi / 4))

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
  unfold chapter02FiveToFiveFourth
  have hrpow : Real.rpow (5 : ℝ) ((5 : ℝ) / 4) =
      Real.exp (Real.log (5 : ℝ) * ((5 : ℝ) / 4)) :=
    Real.rpow_def_of_pos (x := (5 : ℝ)) (y := (5 : ℝ) / 4) (by norm_num)
  rw [hrpow]
  apply Real.exp_lt_exp.mpr
  have h2 : (842 / 1215 : ℝ) ≤ Real.log 2 := by
    have h := Real.sum_range_le_log_div (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 3
    have h' := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
    norm_num [Finset.sum_range_succ] at h'
    nlinarith [h']
  have h32 : (2 / 5 : ℝ) ≤ Real.log ((3 : ℝ) / 2) := by
    convert Real.le_log_one_add_of_nonneg (x := (1 / 2 : ℝ)) (by norm_num) using 1 <;>
      norm_num
  have h43 : (2 / 7 : ℝ) ≤ Real.log ((4 : ℝ) / 3) := by
    convert Real.le_log_one_add_of_nonneg (x := (1 / 3 : ℝ)) (by norm_num) using 1 <;>
      norm_num
  have h54 : (2 / 9 : ℝ) ≤ Real.log ((5 : ℝ) / 4) := by
    convert Real.le_log_one_add_of_nonneg (x := (1 / 4 : ℝ)) (by norm_num) using 1 <;>
      norm_num
  have hlog : Real.log (5 : ℝ) =
      Real.log 2 + Real.log ((3 : ℝ) / 2) + Real.log ((4 : ℝ) / 3) +
        Real.log ((5 : ℝ) / 4) := by
    calc
      Real.log (5 : ℝ) =
          Real.log ((2 : ℝ) * (3 / 2) * (4 / 3) * (5 / 4)) := by norm_num
      _ = Real.log 2 + Real.log ((3 : ℝ) / 2) + Real.log ((4 : ℝ) / 3) +
          Real.log ((5 : ℝ) / 4) := by
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity)]
  rw [hlog]
  nlinarith

/-- The unrestricted geometric limit is also below that ceiling. -/
theorem chapter02_worst_signature_limit_below_five_to_five_fourth :
    Real.pi / 4 * Real.exp 2 < chapter02FiveToFiveFourth := by
  have hpi : Real.pi / 4 ≤ (1 : ℝ) := by
    have h := Real.pi_lt_four
    linarith
  have hmul : Real.pi / 4 * Real.exp 2 ≤ Real.exp 2 := by
    have h := mul_le_mul_of_nonneg_right hpi (Real.exp_pos 2).le
    simpa using h
  exact hmul.trans_lt chapter02_totally_real_limit_below_five_to_five_fourth

/-- A geometric crossing transfers a strict root-discriminant ceiling to a degree cap. -/
theorem chapter02_geometric_degree_exclusion
    (K : Type*) [Field K] [NumberField K]
    {U : ℝ} {N : ℕ} (hN : 0 < N)
    (hcross : U < Real.pi / 4 * chapter02FactorialFactor N)
    (hRD : chapter02RootDiscriminant K < U) :
    chapter02Degree K < N := by
  by_contra hnot
  have hNle : N ≤ chapter02Degree K := Nat.le_of_not_gt hnot
  have hdegpos : 0 < chapter02Degree K := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  have hmon : chapter02FactorialFactor N ≤
      chapter02FactorialFactor (chapter02Degree K) :=
    chapter02_factorial_factor_monotone (a := N) (b := chapter02Degree K) hN hdegpos hNle
  have hmul : Real.pi / 4 * chapter02FactorialFactor N ≤
      Real.pi / 4 * chapter02FactorialFactor (chapter02Degree K) :=
    mul_le_mul_of_nonneg_left hmon (by positivity)
  have hroot : Real.pi / 4 * chapter02FactorialFactor (chapter02Degree K) ≤
      chapter02RootDiscriminant K :=
    (chapter02_geometric_lower_bound_ge_worst_signature K).trans
      (chapter02_root_discriminant_lower_bound K)
  exact (lt_irrefl _ (hRD.trans (hcross.trans_le (hmul.trans hroot))))

/-- The totally real version of the geometric degree-exclusion bridge. -/
theorem chapter02_totally_real_degree_exclusion
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    {U : ℝ} {N : ℕ} (hN : 0 < N)
    (hcross : U < chapter02FactorialFactor N)
    (hRD : chapter02RootDiscriminant K < U) :
    chapter02Degree K < N := by
  by_contra hnot
  have hNle : N ≤ chapter02Degree K := Nat.le_of_not_gt hnot
  have hdegpos : 0 < chapter02Degree K := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  have hmon : chapter02FactorialFactor N ≤
      chapter02FactorialFactor (chapter02Degree K) :=
    chapter02_factorial_factor_monotone (a := N) (b := chapter02Degree K) hN hdegpos hNle
  have hroot : chapter02FactorialFactor (chapter02Degree K) ≤
      chapter02RootDiscriminant K :=
    chapter02_totally_real_geometric_lower_bound K
  exact (lt_irrefl _ (hRD.trans (hcross.trans_le (hmon.trans hroot))))

end
end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02
