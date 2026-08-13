import LastLib.Book04AdelesAndIdeles.Chapter09.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter09

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

/-!
## 9.7. The module as a Haar modulus
-/

def chapter09IdeleMulAddEquiv
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter09Idele K) : Chapter09Adele K ≃+ Chapter09Adele K where
  toFun a := (x : Chapter09Adele K) * a
  invFun a := (x⁻¹ : Chapter09Idele K) * a
  left_inv a := by
    simp
  right_inv a := by
    simp
  map_add' a b := by
    simp [mul_add]

@[simp]
theorem chapter09IdeleMulAddEquiv_apply
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter09Idele K) (a : Chapter09Adele K) :
    chapter09IdeleMulAddEquiv K x a = (x : Chapter09Adele K) * a :=
  rfl

def chapter09HaarModulus
    (K : Type*) [Field K] [NumberField K] :
    Chapter09Idele K →* ℝ≥0 where
  toFun x := (chapter09IdeleModuleHom K x : ℝ≥0)
  map_one' := by
    change ((chapter09IdeleModuleHom K (1 : Chapter09Idele K) :
      Chapter09PositiveReal) : ℝ≥0) = 1
    rw [(chapter09IdeleModuleHom K).map_one]
    rfl
  map_mul' x y := by
    change ((chapter09IdeleModuleHom K (x * y) : Chapter09PositiveReal) : ℝ≥0) =
      (chapter09IdeleModuleHom K x : ℝ≥0) *
        (chapter09IdeleModuleHom K y : ℝ≥0)
    rw [(chapter09IdeleModuleHom K).map_mul]
    rfl

@[simp]
theorem chapter09HaarModulus_apply
    {K : Type*} [Field K] [NumberField K] (x : Chapter09Idele K) :
    chapter09HaarModulus K x = (chapter09IdeleModuleHom K x : ℝ≥0) :=
  rfl

theorem chapter09_additive_haar_scaling
    (K : Type*) [Field K] [NumberField K]
    (μ : Measure (Chapter09Adele K)) [μ.IsAddHaarMeasure] [Measure.Regular μ]
    (x : Chapter09Idele K) :
    ∀ s : Set (Chapter09Adele K), MeasurableSet s →
      μ (chapter09IdeleMulAddEquiv K x '' s) =
        ((chapter09HaarModulus K x : ℝ≥0) : ℝ≥0∞) * μ s := by
  sorry

theorem chapter09_normOne_iff_additive_haar_preserving
    (K : Type*) [Field K] [NumberField K]
    (μ : Measure (Chapter09Adele K)) [μ.IsAddHaarMeasure] [Measure.Regular μ]
    (x : Chapter09Idele K) :
    chapter09HaarModulus K x = 1 ↔
      Measure.map (chapter09IdeleMulAddEquiv K x) μ = μ := by
  sorry

theorem chapter09_normOne_is_exactly_volume_preserving
    (K : Type*) [Field K] [NumberField K]
    (μ : Measure (Chapter09Adele K)) [μ.IsAddHaarMeasure] [Measure.Regular μ] :
    ∀ x : Chapter09Idele K,
      x ∈ chapter09NormOneIdeles K ↔
        Measure.map (chapter09IdeleMulAddEquiv K x) μ = μ := by
  sorry

theorem chapter09_principal_idele_preserves_additive_lattice
    (K : Type*) [Field K] [NumberField K] (a : Kˣ) :
    chapter09IdeleMulAddEquiv K (chapter09PrincipalIdele K a) ''
        (NumberField.AdeleRing.principalSubgroup (𝓞 K) K :
          Set (Chapter09Adele K)) =
      (NumberField.AdeleRing.principalSubgroup (𝓞 K) K :
        Set (Chapter09Adele K)) := by
  sorry

theorem chapter09_principal_idele_has_haar_modulus_one
    (K : Type*) [Field K] [NumberField K] (a : Kˣ) :
    chapter09HaarModulus K (chapter09PrincipalIdele K a) = 1 := by
  simpa [chapter09HaarModulus] using chapter09PrincipalIdele_module_eq_one a

/- The ambient norm gives the archimedean instance of the local density.  At
finite places the book's normalized absolute value is not the ambient adic
norm, so the finite-place version is recorded separately below. -/
def chapter09LocalMultiplicativeHaarDensity
    {F : Type*} [NormedField F] (u : Fˣ) : ℝ≥0 :=
  ‖(u : F)‖₊⁻¹

theorem chapter09_local_multiplicative_haar_density
    {F : Type*} [NormedField F] (u : Fˣ) :
    chapter09LocalMultiplicativeHaarDensity u = ‖(u : F)‖₊⁻¹ :=
  rfl

def chapter09FiniteMultiplicativeHaarDensity
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) : ℝ≥0 :=
  ((chapter09FiniteNormUnit v u : Chapter09PositiveReal) : ℝ≥0)⁻¹

theorem chapter09_finite_multiplicative_haar_density
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    chapter09FiniteMultiplicativeHaarDensity v u =
      ((chapter09FiniteNormUnit v u : Chapter09PositiveReal) : ℝ≥0)⁻¹ :=
  rfl

/- The restricted-product normalization is recorded on the local multiplicative
groups, not on the additive local fields: the local integral unit subgroup has
volume one at almost every finite place. -/
def chapter09FiniteMultiplicativeHaarNormalization
    (K : Type*) [Field K] [NumberField K]
    (μ : ∀ v : HeightOneSpectrum (𝓞 K), Measure ((v.adicCompletion K)ˣ)) : Prop :=
  ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
    μ v ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ) = 1

theorem chapter09_multiplicative_haar_units_are_normalized_almost_everywhere
    (K : Type*) [Field K] [NumberField K]
    (μ : ∀ v : HeightOneSpectrum (𝓞 K), Measure ((v.adicCompletion K)ˣ))
    (hμ : chapter09FiniteMultiplicativeHaarNormalization K μ) :
    ({v : HeightOneSpectrum (𝓞 K) |
      μ v ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
        Set (v.adicCompletion K)ˣ) ≠ 1}).Finite := by
  exact Filter.eventually_cofinite.mp hμ

end

end LastLib.Book04AdelesAndIdeles.Chapter09
