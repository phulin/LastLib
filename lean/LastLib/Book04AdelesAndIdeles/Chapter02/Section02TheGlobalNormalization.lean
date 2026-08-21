import LastLib.Book04AdelesAndIdeles.Chapter02.Core
import LastLib.Book04AdelesAndIdeles.Chapter01.Dependencies
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.RingTheory.Complex

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

/-- The finite normalization is `N(v)^(-ord_v)` on `Kˣ`. -/
theorem chapter02_finite_normalization_formula
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    Chapter02FiniteNormalizedValue v (x : K) =
      (v.asIdeal.absNorm : ℝ) ^
        (-LastLib.Book04AdelesAndIdeles.Chapter01.chapter01UnitOrder v x) := by
  classical
  obtain ⟨r, s, hxs⟩ :=
    IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 K)) (x : K)
  have hxs0 : (x : K) ≠ 0 := Units.ne_zero x
  have hr : r ≠ 0 := by
    intro hr
    apply hxs0
    rw [← hxs, hr, IsLocalization.mk'_zero]
  have hs : (s : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero s.property
  have h_aJ :
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (x : K) =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
            ((algebraMap (𝓞 K) K) (s : 𝓞 K))⁻¹ *
          (Ideal.span ({r} : Set (𝓞 K)) :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [← hxs, IsFractionRing.mk'_eq_div,
      ← FractionalIdeal.spanSingleton_div_spanSingleton,
      FractionalIdeal.div_spanSingleton,
      ← FractionalIdeal.coeIdeal_span_singleton]
  have hI :
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (x : K) ≠ 0 := by
    simp [FractionalIdeal.spanSingleton_eq_zero_iff, hxs0]
  have horder :
      LastLib.Book04AdelesAndIdeles.Chapter01.chapter01UnitOrder v x =
        ((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {r} : Ideal (𝓞 K))).factors -
         (Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {(s : 𝓞 K)} : Ideal (𝓞 K))).factors : ℤ) := by
    change FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (x : K)) = _
    exact FractionalIdeal.count_well_defined K v hI h_aJ
  have hvr := v.intValuation_if_neg hr
  have hvs := v.intValuation_if_neg hs
  have hvr0 : v.intValuation r ≠ 0 := by
    rw [hvr]
    exact WithZero.exp_ne_zero
  have hvs0 : v.intValuation (s : 𝓞 K) ≠ 0 := by
    rw [hvs]
    exact WithZero.exp_ne_zero
  have hpowr :
      (WithZero.unzero hvr0).toAdd =
        -((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {r} : Ideal (𝓞 K))).factors : ℤ) := by
    rw [WithZero.toAdd_unzero_eq_log hvr0, hvr]
    simp
  have hpow_s :
      (WithZero.unzero hvs0).toAdd =
        -((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {(s : 𝓞 K)} : Ideal (𝓞 K))).factors : ℤ) := by
    rw [WithZero.toAdd_unzero_eq_log hvs0, hvs]
    simp
  rw [← hxs]
  simp only [Chapter02FiniteNormalizedValue, NumberField.FinitePlace.mk_apply,
    NumberField.FinitePlace.norm_embedding]
  change v.adicAbv (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)
      (IsLocalization.mk' K r s) =
    (v.asIdeal.absNorm : ℝ) ^
      (-LastLib.Book04AdelesAndIdeles.Chapter01.chapter01UnitOrder v x)
  rw [v.adicAbv_of_mk']
  simp [IsDedekindDomain.HeightOneSpectrum.intAdicAbv,
    IsDedekindDomain.HeightOneSpectrum.intAdicAbvDef]
  rw [WithZeroMulInt.toNNReal_neg_apply
        (NumberField.HeightOneSpectrum.absNorm_ne_zero v) hvr0,
    WithZeroMulInt.toNNReal_neg_apply
        (NumberField.HeightOneSpectrum.absNorm_ne_zero v) hvs0,
    hpowr, hpow_s, horder]
  have hNnat : 0 < v.asIdeal.absNorm :=
    lt_trans Nat.zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  have hN : (v.asIdeal.absNorm : ℝ) ≠ 0 := by
    exact_mod_cast hNnat.ne'
  simp only [NNReal.coe_zpow, NNReal.coe_natCast]
  rw [← zpow_sub₀ hN]
  rw [← zpow_neg]
  congr 1
  ring

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
  simp [Chapter02ComplexNormalizedValue, ComplexEmbedding.conjugate_coe_eq]

/-- The normalized value attached to an infinite place. -/
def Chapter02InfiniteNormalizedValue
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (x : K) : ℝ := w x ^ w.mult

theorem chapter02_real_infinite_place_uses_real_embedding
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (hw : w.IsReal) :
    ∃ σ : K →+* ℝ, ∀ x : K,
      Chapter02InfiniteNormalizedValue w x = Chapter02RealNormalizedValue σ x := by
  refine ⟨NumberField.InfinitePlace.embedding_of_isReal hw, ?_⟩
  intro x
  simpa [Chapter02InfiniteNormalizedValue, Chapter02RealNormalizedValue,
    hw.mult_eq_one, Real.norm_eq_abs] using
    (NumberField.InfinitePlace.norm_embedding_of_isReal hw x).symm

theorem chapter02_complex_infinite_place_uses_conjugate_pair
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (hw : w.IsComplex) :
    ∃ σ : K →+* ℂ, ¬ComplexEmbedding.IsReal σ ∧
      ∀ x : K,
        Chapter02InfiniteNormalizedValue w x = Chapter02ComplexNormalizedValue σ x := by
  refine ⟨w.embedding, NumberField.InfinitePlace.isComplex_iff.mp hw, ?_⟩
  intro x
  simp [Chapter02InfiniteNormalizedValue, Chapter02ComplexNormalizedValue,
    hw.mult_eq_two, NumberField.InfinitePlace.norm_embedding_eq]

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
  simpa [Chapter02ComplexHaarScalingFactor] using Complex.normSq_eq_norm_sq z

theorem chapter02_complex_normalized_value_is_the_haar_scaling_factor
    {K : Type*} [Field K] (σ : K →+* ℂ) (x : K) :
    Chapter02ComplexNormalizedValue σ x =
      Chapter02ComplexHaarScalingFactor (σ x) := by
  simpa [Chapter02ComplexNormalizedValue, Chapter02ComplexHaarScalingFactor] using
    (Complex.normSq_eq_norm_sq (σ x)).symm

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
  rw [Chapter02InfiniteNormalizedValue, Chapter02UnweightedInfiniteValue,
    hw.mult_eq_two]

theorem chapter02_complex_unweighted_and_squared_conventions_differ
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (hw : w.IsComplex) :
    ∃ x : K,
      Chapter02InfiniteNormalizedValue w x ≠ Chapter02UnweightedInfiniteValue w x := by
  refine ⟨(2 : K), ?_⟩
  have hw2 : w (2 : K) = 2 := w.map_natCast 2
  simp [Chapter02InfiniteNormalizedValue, Chapter02UnweightedInfiniteValue,
    hw.mult_eq_two, hw2]
  norm_num

theorem chapter02_mixing_squared_and_unsquared_complex_conventions_differ_at_the_place
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (hw : w.IsComplex) :
    ¬(∀ x : K, Chapter02InfiniteNormalizedValue w x =
        Chapter02UnweightedInfiniteValue w x) := by
  obtain ⟨x, hx⟩ := chapter02_complex_unweighted_and_squared_conventions_differ w hw
  exact fun h => hx (h x)

/-- The global product obtained by replacing one complex normalized factor by
the unsquared convention. -/
noncomputable def Chapter02MixedComplexGlobalProduct
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (x : K) : ℝ := by
  classical
  exact
    (∏ w' : Chapter02InfinitePlace K,
      if w' = w then Chapter02UnweightedInfiniteValue w' x
      else Chapter02InfiniteNormalizedValue w' x) *
      ∏ᶠ w' : Chapter02FinitePlace K, w' x

theorem chapter02_mixing_squared_and_unsquared_complex_conventions_changes_the_product
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (hw : w.IsComplex) :
    ∃ x : K, Chapter02MixedComplexGlobalProduct w x ≠ 1 := by
  classical
  refine ⟨(2 : K), ?_⟩
  have h2 : (2 : K) ≠ 0 := by norm_num
  have hw2 : w (2 : K) = 2 := w.map_natCast 2
  have hnormw : Chapter02InfiniteNormalizedValue w (2 : K) ≠ 0 := by
    simp [Chapter02InfiniteNormalizedValue, hw2, hw.mult_eq_two]
  have hpoint (w' : Chapter02InfinitePlace K) :
      (if w' = w then Chapter02UnweightedInfiniteValue w' (2 : K)
        else Chapter02InfiniteNormalizedValue w' (2 : K)) =
        (if w' = w then
            Chapter02UnweightedInfiniteValue w' (2 : K) /
              Chapter02InfiniteNormalizedValue w' (2 : K)
          else 1) * Chapter02InfiniteNormalizedValue w' (2 : K) := by
    by_cases h : w' = w
    · subst w'
      simp only [ite_true]
      exact (div_mul_cancel₀ _ hnormw).symm
    · simp [h]
  have hprod :
      (∏ w' : Chapter02InfinitePlace K,
        if w' = w then Chapter02UnweightedInfiniteValue w' (2 : K)
        else Chapter02InfiniteNormalizedValue w' (2 : K)) =
        (Chapter02UnweightedInfiniteValue w (2 : K) /
          Chapter02InfiniteNormalizedValue w (2 : K)) *
          (∏ w' : Chapter02InfinitePlace K,
            Chapter02InfiniteNormalizedValue w' (2 : K)) := by
    calc
      (∏ w' : Chapter02InfinitePlace K,
          if w' = w then Chapter02UnweightedInfiniteValue w' (2 : K)
          else Chapter02InfiniteNormalizedValue w' (2 : K)) =
          ∏ w' : Chapter02InfinitePlace K,
            ((if w' = w then
                Chapter02UnweightedInfiniteValue w' (2 : K) /
                  Chapter02InfiniteNormalizedValue w' (2 : K)
              else 1) * Chapter02InfiniteNormalizedValue w' (2 : K)) := by
        apply Finset.prod_congr rfl
        intro w' hw'
        exact hpoint w'
      _ = (∏ w' : Chapter02InfinitePlace K,
            if w' = w then
              Chapter02UnweightedInfiniteValue w' (2 : K) /
                Chapter02InfiniteNormalizedValue w' (2 : K)
            else 1) *
            (∏ w' : Chapter02InfinitePlace K,
              Chapter02InfiniteNormalizedValue w' (2 : K)) := by
        rw [Finset.prod_mul_distrib]
      _ = (Chapter02UnweightedInfiniteValue w (2 : K) /
            Chapter02InfiniteNormalizedValue w (2 : K)) *
            (∏ w' : Chapter02InfinitePlace K,
              Chapter02InfiniteNormalizedValue w' (2 : K)) := by
        rw [Finset.prod_ite_eq' (Finset.univ) w]
        simp
  have hglobal : Chapter02GlobalProduct (2 : K) = 1 :=
    chapter02_product_formula h2
  have hratio :
      Chapter02UnweightedInfiniteValue w (2 : K) /
        Chapter02InfiniteNormalizedValue w (2 : K) = (1 / 2 : ℝ) := by
    simp [Chapter02UnweightedInfiniteValue, Chapter02InfiniteNormalizedValue,
      hw2, hw.mult_eq_two]
    norm_num
  rw [Chapter02MixedComplexGlobalProduct, hprod, hratio]
  have hglobal' :
      (∏ w' : Chapter02InfinitePlace K,
        Chapter02InfiniteNormalizedValue w' (2 : K)) *
        ∏ᶠ w' : Chapter02FinitePlace K, w' (2 : K) = 1 := hglobal
  have hmix :
      ((1 / 2 : ℝ) *
          (∏ w' : Chapter02InfinitePlace K,
            Chapter02InfiniteNormalizedValue w' (2 : K))) *
        ∏ᶠ w' : Chapter02FinitePlace K, w' (2 : K) = (1 / 2 : ℝ) := by
    calc
      ((1 / 2 : ℝ) *
          (∏ w' : Chapter02InfinitePlace K,
            Chapter02InfiniteNormalizedValue w' (2 : K))) *
          ∏ᶠ w' : Chapter02FinitePlace K, w' (2 : K) =
          (1 / 2 : ℝ) *
            ((∏ w' : Chapter02InfinitePlace K,
              Chapter02InfiniteNormalizedValue w' (2 : K)) *
              ∏ᶠ w' : Chapter02FinitePlace K, w' (2 : K)) := by ring
      _ = (1 / 2 : ℝ) := by rw [hglobal']; ring
  rw [hmix]
  norm_num

end

end LastLib.Book04AdelesAndIdeles.Chapter02
