import LastLib.Book04AdelesAndIdeles.Chapter02.Core

namespace LastLib.Book04AdelesAndIdeles.Chapter02

noncomputable section

open NumberField
open NumberField.HeightOneSpectrum
open scoped BigOperators WithZero

/-! ## 2.2. The global normalization -/

/-- The finite-place value attached to a height-one prime. -/
def Chapter02FiniteNormalizedValue
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : K) : ℝ :=
  NumberField.FinitePlace.mk v x

/-- The integer-valued order of a nonzero element at a finite prime. -/
noncomputable def Chapter02FiniteOrder
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Kˣ) : ℤ :=
  (WithZero.unzero
      ((v.valuation K).ne_zero_iff.mpr x.ne_zero)).toAdd

/-- The finite normalization is `N(v)^(-ord_v)` on `Kˣ`. -/
theorem chapter02_finite_normalization_formula
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    Chapter02FiniteNormalizedValue v (x : K) =
      (v.asIdeal.absNorm : ℝ) ^ (-Chapter02FiniteOrder v x) := by
  sorry

/-- The real-place convention. -/
def Chapter02RealNormalizedValue {K : Type*} [Field K]
    (σ : K →+* ℝ) (x : K) : ℝ := |σ x|

/-- The complex-place convention, with the square required by the product
formula and by two-dimensional Haar measure. -/
def Chapter02ComplexNormalizedValue {K : Type*} [Field K]
    (σ : K →+* ℂ) (x : K) : ℝ := ‖σ x‖ ^ 2

/-- Conjugate complex embeddings give the same squared normalized value. -/
theorem chapter02_complex_normalized_value_conjugate_invariant
    {K : Type*} [Field K] (σ : K →+* ℂ) (x : K) :
    Chapter02ComplexNormalizedValue (ComplexEmbedding.conjugate σ) x =
      Chapter02ComplexNormalizedValue σ x := by
  sorry

/-- The normalized value attached to an infinite place. -/
def Chapter02InfiniteNormalizedValue
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (x : K) : ℝ := w x ^ w.mult

theorem chapter02_real_infinite_place_uses_real_embedding
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (hw : w.IsReal) :
    ∃ σ : K →+* ℝ, ∀ x : K,
      Chapter02InfiniteNormalizedValue w x = Chapter02RealNormalizedValue σ x := by
  sorry

theorem chapter02_complex_infinite_place_uses_conjugate_pair
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (hw : w.IsComplex) :
    ∃ σ : K →+* ℂ, ¬ComplexEmbedding.IsReal σ ∧
      ∀ x : K,
        Chapter02InfiniteNormalizedValue w x = Chapter02ComplexNormalizedValue σ x := by
  sorry

/-- The archimedean part of the product formula. -/
theorem chapter02_infinite_part_product_formula
    {K : Type*} [Field K] [NumberField K] (x : K) :
    (∏ w : Chapter02InfinitePlace K, w x ^ w.mult) =
      |Algebra.norm ℚ x| := by
  exact NumberField.InfinitePlace.prod_eq_abs_norm x

/-- The finite part of the product formula. -/
theorem chapter02_finite_part_product_formula
    {K : Type*} [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    (∏ᶠ w : Chapter02FinitePlace K, w x) =
      |Algebra.norm ℚ x|⁻¹ := by
  exact NumberField.FinitePlace.prod_eq_inv_abs_norm hx

/-- Only finitely many finite factors differ from one. -/
theorem chapter02_finite_factors_eventually_one
    {K : Type*} [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    (fun w : Chapter02FinitePlace K => w x).HasFiniteMulSupport := by
  exact NumberField.FinitePlace.hasFiniteMulSupport hx

/-- Theorem 2.1, in the canonical finite-product/infinite-product split. -/
theorem chapter02_product_formula
    {K : Type*} [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    Chapter02GlobalProduct x = 1 := by
  exact NumberField.prod_abs_eq_one hx

/-- The scalar by which multiplication by `z` scales real two-dimensional Haar
measure on `ℂ`. -/
def Chapter02ComplexHaarScalingFactor (z : ℂ) : ℝ := Complex.normSq z

theorem chapter02_complex_haar_scaling_factor_is_the_square
    (z : ℂ) : Chapter02ComplexHaarScalingFactor z = ‖z‖ ^ 2 := by
  sorry

theorem chapter02_complex_normalized_value_is_the_haar_scaling_factor
    {K : Type*} [Field K] (σ : K →+* ℂ) (x : K) :
    Chapter02ComplexNormalizedValue σ x =
      Chapter02ComplexHaarScalingFactor (σ x) := by
  sorry

/-- The exact relation between the unweighted complex absolute value and the
book's normalized complex factor. -/
def Chapter02UnweightedInfiniteValue
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (x : K) : ℝ := w x

theorem chapter02_complex_weight_is_two
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (hw : w.IsComplex) (x : K) :
    Chapter02InfiniteNormalizedValue w x =
      Chapter02UnweightedInfiniteValue w x ^ 2 := by
  sorry

theorem chapter02_complex_unweighted_and_squared_conventions_differ
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (hw : w.IsComplex) :
    ∃ x : K,
      Chapter02InfiniteNormalizedValue w x ≠ Chapter02UnweightedInfiniteValue w x := by
  sorry

theorem chapter02_mixing_squared_and_unsquared_complex_conventions_changes_the_product
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (hw : w.IsComplex) :
    (∀ x : K, Chapter02InfiniteNormalizedValue w x =
        Chapter02UnweightedInfiniteValue w x) ↔
      ∀ x : K, Chapter02UnweightedInfiniteValue w x ^ 2 =
        Chapter02UnweightedInfiniteValue w x := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter02
