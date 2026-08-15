import LastLib.Book04AdelesAndIdeles.Chapter09.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter09

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal Pointwise RestrictedProduct

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
  intro s hs
  have hmod :
      chapter09HaarModulus K x =
        MeasureTheory.distribHaarChar (G := Chapter09Idele K)
          (A := Chapter09Adele K) x := by
    change chapter09IdeleModuleNNRealHom K x = _
    rw [chapter09IdeleModuleNNRealHom_eq_distribHaarChar K]
  rw [hmod]
  change μ ((fun a : Chapter09Adele K => (x : Chapter09Adele K) * a) '' s) = _
  have hmap :
      (fun a : Chapter09Adele K => (x : Chapter09Adele K) * a) =
        (fun a : Chapter09Adele K => x • a) := by
    funext a
    simp [Units.smul_def, smul_eq_mul]
  rw [hmap]
  exact (MeasureTheory.distribHaarChar_mul (A := Chapter09Adele K) (μ := μ) x s).symm

theorem chapter09_normOne_iff_additive_haar_preserving
    (K : Type*) [Field K] [NumberField K]
    (μ : Measure (Chapter09Adele K)) [μ.IsAddHaarMeasure] [Measure.Regular μ]
    (x : Chapter09Idele K) :
    chapter09HaarModulus K x = 1 ↔
      Measure.map (chapter09IdeleMulAddEquiv K x) μ = μ := by
  constructor
  · intro hx
    let e : Chapter09Adele K ≃ᵐ Chapter09Adele K := MeasurableEquiv.smul x
    have hef :
        (e : Chapter09Adele K → Chapter09Adele K) =
          chapter09IdeleMulAddEquiv K x := by
      funext a
      simp [e, chapter09IdeleMulAddEquiv, Units.smul_def, smul_eq_mul]
    have hpres : Measure.map e μ = μ := by
      apply Measure.ext
      intro s hs
      rw [Measure.map_apply e.measurable hs]
      have hsc := chapter09_additive_haar_scaling K μ x (e ⁻¹' s)
        (e.measurable hs)
      rw [← hef, e.image_preimage, hx] at hsc
      simpa using hsc.symm
    rw [← hef]
    exact hpres
  · intro hμ
    let e : Chapter09Adele K ≃ᵐ Chapter09Adele K := MeasurableEquiv.smul x
    have hef :
        (e : Chapter09Adele K → Chapter09Adele K) =
          chapter09IdeleMulAddEquiv K x := by
      funext a
      simp [e, chapter09IdeleMulAddEquiv, Units.smul_def, smul_eq_mul]
    have hμe : Measure.map e μ = μ := by
      rw [hef]
      exact hμ
    rcases (Measure.Regular.exists_isCompact_not_null (μ := μ)).2 (NeZero.ne μ) with
      ⟨C, hC, hCμ⟩
    have hT2completion :
        ∀ v : HeightOneSpectrum (𝓞 K), T2Space (v.adicCompletion K) :=
      fun v => inferInstance
    have hT2finite : T2Space (Chapter09FiniteAdele K) := by
      change T2Space
        (Πʳ v : HeightOneSpectrum (𝓞 K),
          [v.adicCompletion K, v.adicCompletionIntegers K])
      exact @RestrictedProduct.instT2Space
        (HeightOneSpectrum (𝓞 K))
        (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
        (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletionIntegers K)
        Filter.cofinite _ hT2completion
    have hT2infinite :
        ∀ v : InfinitePlace K, T2Space v.Completion :=
      fun v => inferInstance
    have hT2inf : T2Space (Chapter09InfiniteAdele K) := by
      change T2Space (∀ v : InfinitePlace K, v.Completion)
      exact @Pi.t2Space (InfinitePlace K) (fun v => v.Completion) _ hT2infinite
    have hT2adele : T2Space (Chapter09Adele K) := by
      change T2Space (Chapter09InfiniteAdele K × Chapter09FiniteAdele K)
      exact @Prod.t2Space (Chapter09InfiniteAdele K) (Chapter09FiniteAdele K)
        _ hT2inf _ hT2finite
    have hCmeas : MeasurableSet C :=
      @IsCompact.measurableSet (Chapter09Adele K) C _ _ _ hT2adele hC
    have himageμ : μ (chapter09IdeleMulAddEquiv K x '' C) = μ C := by
      have h := congrArg (fun ν : Measure (Chapter09Adele K) => ν (e '' C)) hμe
      rw [Measure.map_apply e.measurable (e.measurableSet_image.2 hCmeas),
        e.preimage_image] at h
      rw [← hef]
      exact h.symm
    have hfun :
        (fun a : Chapter09Adele K => (x : Chapter09Adele K) * a) =
          (fun a : Chapter09Adele K => x • a) := by
      funext a
      simp [Units.smul_def, smul_eq_mul]
    have hset : chapter09IdeleMulAddEquiv K x '' C = x • C := by
      change (fun a : Chapter09Adele K => (x : Chapter09Adele K) * a) '' C = _
      rw [hfun]
      rfl
    have hμxC : μ (x • C) = (1 : ℝ≥0) * μ C := by
      rw [← hset]
      simpa using himageμ
    have hchar :
        MeasureTheory.distribHaarChar (G := Chapter09Idele K)
            (A := Chapter09Adele K) x = 1 :=
      MeasureTheory.distribHaarChar_eq_of_measure_smul_eq_mul
        (g := x) hCμ hC.measure_lt_top.ne hμxC
    change chapter09IdeleModuleNNRealHom K x = 1
    rw [chapter09IdeleModuleNNRealHom_eq_distribHaarChar K]
    exact hchar

theorem chapter09_normOne_is_exactly_volume_preserving
    (K : Type*) [Field K] [NumberField K]
    (μ : Measure (Chapter09Adele K)) [μ.IsAddHaarMeasure] [Measure.Regular μ] :
    ∀ x : Chapter09Idele K,
      x ∈ chapter09NormOneIdeles K ↔
        Measure.map (chapter09IdeleMulAddEquiv K x) μ = μ := by
  intro x
  rw [chapter09NormOneIdeles_mem_iff]
  constructor
  · intro hx
    apply (chapter09_normOne_iff_additive_haar_preserving K μ x).1
    change ((chapter09IdeleModuleHom K x : Chapter09PositiveReal) : ℝ≥0) = 1
    rw [hx]
    rfl
  · intro hμ
    have hx : chapter09HaarModulus K x = 1 :=
      (chapter09_normOne_iff_additive_haar_preserving K μ x).2 hμ
    apply Units.ext
    change ((chapter09IdeleModuleHom K x : Chapter09PositiveReal) : ℝ≥0) = 1
    exact hx

theorem chapter09_principal_idele_preserves_additive_lattice
    (K : Type*) [Field K] [NumberField K] (a : Kˣ) :
    chapter09IdeleMulAddEquiv K (chapter09PrincipalIdele K a) ''
        (NumberField.AdeleRing.principalSubgroup (𝓞 K) K :
          Set (Chapter09Adele K)) =
      (NumberField.AdeleRing.principalSubgroup (𝓞 K) K :
        Set (Chapter09Adele K)) := by
  apply Set.Subset.antisymm
  · rintro z ⟨y, ⟨b, rfl⟩, rfl⟩
    refine ⟨(a : K) * b, ?_⟩
    simp [chapter09IdeleMulAddEquiv, chapter09PrincipalIdele]
  · rintro z ⟨b, rfl⟩
    refine ⟨algebraMap K (Chapter09Adele K) ((a : K)⁻¹ * b), ?_, ?_⟩
    · exact ⟨(a : K)⁻¹ * b, rfl⟩
    · change ((algebraMap K (Chapter09Adele K)) ↑a) *
        ((algebraMap K (Chapter09Adele K)) ((a : K)⁻¹ * b)) =
        (algebraMap K (Chapter09Adele K)) b
      rw [← map_mul]
      simp

theorem chapter09_principal_idele_has_haar_modulus_one
    (K : Type*) [Field K] [NumberField K] (a : Kˣ) :
    chapter09HaarModulus K (chapter09PrincipalIdele K a) = 1 := by
  simpa [chapter09HaarModulus] using chapter09PrincipalIdele_module_eq_one a

/- The local density uses the book's normalized local module.  In particular,
at a complex place the ambient norm is squared through `v.mult`. -/
def chapter09LocalMultiplicativeHaarDensity
    {K : Type*} [Field K] [NumberField K]
    (v : InfinitePlace K) (u : v.Completionˣ) : ℝ≥0 :=
  ((chapter09NormUnit u ^ v.mult : Chapter09PositiveReal) : ℝ≥0)⁻¹

theorem chapter09_local_multiplicative_haar_density
    {K : Type*} [Field K] [NumberField K]
    (v : InfinitePlace K) (u : v.Completionˣ) :
    chapter09LocalMultiplicativeHaarDensity v u =
      ((chapter09NormUnit u ^ v.mult : Chapter09PositiveReal) : ℝ≥0)⁻¹ :=
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
  (∀ v : HeightOneSpectrum (𝓞 K), Measure.IsHaarMeasure (μ v)) ∧
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
  exact Filter.eventually_cofinite.mp hμ.2

end

end LastLib.Book04AdelesAndIdeles.Chapter09
