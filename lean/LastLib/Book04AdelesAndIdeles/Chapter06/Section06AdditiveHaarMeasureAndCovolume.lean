import LastLib.Book04AdelesAndIdeles.Chapter06.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter06

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-! # Book 4, Chapter 6, Section 6.6: Additive Haar measure and covolume -/

universe uK uO uInf uFin uHat

variable {K : Type uK} {O : Type uO} {KInf : Type uInf} {Af : Type uFin}
  {Ohat : Type uHat}
variable [Field K] [CommRing O] [AddCommGroup KInf] [AddCommGroup Af]
  [AddCommGroup Ohat] [TopologicalSpace KInf] [TopologicalSpace Af]
  [TopologicalSpace Ohat]

theorem chapter06_haar_measure_exists
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [T2Space G] [BorelSpace G] :
    ∃ μ : Measure G, Chapter06IsAdditiveHaarMeasure G μ := by
  let μ : Measure G := Measure.addHaar
  refine ⟨μ, ?_⟩
  exact ⟨inferInstance, inferInstance⟩

theorem chapter06_haar_measure_unique_up_to_scale
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [T2Space G] [BorelSpace G]
    (μ ν : Measure G)
    (hμ : Chapter06IsAdditiveHaarMeasure G μ)
    (hν : Chapter06IsAdditiveHaarMeasure G ν) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ν = c • μ := by
  let _ : Measure.IsAddHaarMeasure μ := hμ.1
  let _ : Measure.Regular μ := hμ.2
  let _ : Measure.IsAddHaarMeasure ν := hν.1
  let _ : Measure.Regular ν := hν.2
  let c : ℝ≥0∞ := (Measure.addHaarScalarFactor ν μ : ℝ≥0∞)
  refine ⟨c, ?_, ?_, ?_⟩
  · exact ENNReal.coe_pos.mpr
      (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν μ)
  · exact ENNReal.coe_ne_top
  · change ν = (Measure.addHaarScalarFactor ν μ : ℝ≥0∞) • μ
    exact Measure.isAddLeftInvariant_eq_smul_of_regular ν μ

/-- A compact open nonempty set can be normalized to have mass one. -/
theorem chapter06_normalized_local_haar_measure_exists
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [T2Space G] [BorelSpace G]
    (O : Set G) (hOopen : IsOpen O) (hOcompact : IsCompact O)
    (hOnonempty : O.Nonempty) :
    ∃ μ : Measure G,
      Chapter06IsAdditiveHaarMeasure G μ ∧ μ O = 1 := by
  let K : TopologicalSpace.PositiveCompacts G :=
    { carrier := O
      isCompact' := hOcompact
      interior_nonempty' := by simpa [hOopen.interior_eq] using hOnonempty }
  refine ⟨Measure.addHaarMeasure K, ⟨inferInstance, inferInstance⟩, ?_⟩
  exact Measure.addHaarMeasure_self

@[simp] theorem chapter06_complex_local_size_eq_squared_norm (z : ℂ) :
    chapter06ComplexLocalSize z = ‖z‖ ^ 2 := rfl

@[simp] theorem chapter06_real_local_size_eq_absolute_value (x : ℝ) :
    chapter06RealLocalSize x = |x| := rfl

@[simp] theorem chapter06_self_dual_complex_measure_scale (μ : Measure ℂ) :
    chapter06SelfDualComplexMeasure μ =
      (2 : ℝ≥0∞) • μ := rfl

@[simp] theorem chapter06_self_dual_global_scaling_apply (r₂ : ℕ) :
    chapter06SelfDualGlobalScaling r₂ = (2 : ℝ≥0∞) ^ r₂ := rfl

theorem chapter06_product_formula_iff_principal_volume_preserving
    (Place : Type*) (size : Place → K → ℝ≥0∞)
    (adelicProduct : K → ℝ≥0∞)
    (hfinite : ∀ a : K, a ≠ 0 → ∃ S : Finset Place,
      (∀ v, v ∉ S → size v a = 1) ∧
        (adelicProduct a = ∏ v ∈ S, size v a)) :
    Chapter06ProductFormula K Place size adelicProduct ↔
      ∀ a : K, a ≠ 0 → adelicProduct a = 1 := by
  constructor
  · intro h a ha
    obtain ⟨S, _htail, _hproduct, hprincipal⟩ := h a ha
    exact hprincipal
  · intro h a ha
    obtain ⟨S, htail, hproduct⟩ := hfinite a ha
    exact ⟨S, htail, hproduct, h a ha⟩

theorem chapter06_adelic_product_measure_fundamental_set_mass
    {P : Chapter06AdeleData K O KInf Af Ohat} {D : Set KInf}
    [MeasurableSpace KInf] [MeasurableSpace Af]
    (M : Chapter06AdelicMeasureData P D)
    [SFinite M.finiteMeasure] :
    chapter06AdelicFundamentalSetMass M =
      ENNReal.ofReal (chapter06OrdinaryCovolume M.r₂ M.discriminant) := by
  change (M.infiniteMeasure.prod M.finiteMeasure)
      (D ×ˢ Set.range P.finiteIntegralEmbedding) = _
  rw [Measure.prod_prod]
  rw [M.archimedean_cell_volume, M.finiteIntegral_measure_one]
  simp

theorem chapter06_adelic_quotient_covolume
    {P : Chapter06AdeleData K O KInf Af Ohat} {D : Set KInf}
    [MeasurableSpace KInf] [MeasurableSpace Af]
    (M : Chapter06AdelicMeasureData P D)
    [SFinite M.finiteMeasure]
    (Q : Chapter06AdelicQuotientVolumeData M)
    (hQ : Q.quotientVolume = chapter06AdelicFundamentalSetMass M) :
    chapter06AdelicQuotientCovolume M Q =
      ENNReal.ofReal (chapter06OrdinaryCovolume M.r₂ M.discriminant) := by
  change Q.quotientVolume = _
  rw [hQ]
  exact chapter06_adelic_product_measure_fundamental_set_mass M

/-- With ordinary Lebesgue measure at real places and ordinary planar measure
    at complex places, the quotient has the displayed covolume. -/
theorem chapter06_ordinary_adelic_covolume_formula
    {P : Chapter06AdeleData K O KInf Af Ohat} {D : Set KInf}
    [MeasurableSpace KInf] [MeasurableSpace Af]
    (M : Chapter06AdelicMeasureData P D)
    [SFinite M.finiteMeasure]
    (Q : Chapter06AdelicQuotientVolumeData M)
    (hQ : Q.quotientVolume = chapter06AdelicFundamentalSetMass M) :
    chapter06AdelicQuotientCovolume M Q =
      ENNReal.ofReal
        ((1 / 2 : ℝ) ^ M.r₂ * Real.sqrt |M.discriminant|) := by
  simpa [chapter06OrdinaryCovolume] using
    chapter06_adelic_quotient_covolume M Q hQ

/-- The normalization data needed for the self-dual volume calculation.

The quotient-volume scaling is recorded, while the self-dual cancellation is
proved separately rather than being included as a field of the data. -/
structure Chapter06SelfDualVolumeData where
  quotientVolume : ℝ≥0∞
  ordinaryVolume : ℝ≥0∞
  selfDualScale : ℝ≥0∞
  ordinaryVolume_ne_zero : ordinaryVolume ≠ 0
  ordinaryVolume_ne_top : ordinaryVolume ≠ ⊤
  quotientVolume_eq_scaled : quotientVolume = selfDualScale * ordinaryVolume

theorem chapter06_self_dual_quotient_volume_one
    (M : Chapter06SelfDualVolumeData)
    (hscale : M.selfDualScale = M.ordinaryVolume⁻¹) :
    M.quotientVolume = 1 := by
  rw [M.quotientVolume_eq_scaled, hscale]
  exact ENNReal.inv_mul_cancel M.ordinaryVolume_ne_zero M.ordinaryVolume_ne_top

end

end LastLib.Book04AdelesAndIdeles.Chapter06
