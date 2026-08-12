import LastLib.Book04AdelesAndIdeles.Chapter06.Section05TheRationalFundamentalDomain

namespace LastLib.Book04AdelesAndIdeles.Chapter06

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! # Book 4, Chapter 6, Section 6.6: Additive Haar measure and covolume -/

/- SOURCE_ISSUE (books/004-adeles-and-ideles.md:958): “Every locally compact
group admits a nonzero translation-invariant Haar measure, unique up to
scaling” is underspecified in a formal setting.  The minimal correction is
“Every locally compact Hausdorff group admits ...”, with the usual measurable
and regular-measure conventions for uniqueness; the declarations below expose
`T2Space` explicitly. -/

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
  sorry

theorem chapter06_haar_measure_unique_up_to_scale
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [T2Space G] [BorelSpace G]
    [SecondCountableTopology G] (μ ν : Measure G)
    (hμ : Chapter06IsAdditiveHaarMeasure G μ)
    (hν : Chapter06IsAdditiveHaarMeasure G ν) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ν = c • μ := by
  sorry

/-- A compact open nonempty subgroup can be normalized to have mass one. -/
theorem chapter06_normalized_local_haar_measure_exists
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [T2Space G] [BorelSpace G]
    (O : Set G) (hOopen : IsOpen O) (hOcompact : IsCompact O)
    (hOnonempty : O.Nonempty) :
    ∃ μ : Measure G,
      Chapter06IsAdditiveHaarMeasure G μ ∧ μ O = 1 := by
  sorry

theorem chapter06_local_measure_scales_by_absolute_value
    {F : Type*} [Field F] [MeasurableSpace F]
    (μ : Measure F) (size : F → ℝ≥0∞)
    (hmodule : Chapter06LocalMeasureModule F μ size) (a : Fˣ) :
    Measure.map (fun x : F => (a : F) * x) μ = size (a : F) • μ := by
  exact hmodule a

@[simp] theorem chapter06_complex_local_size_eq_squared_norm (z : ℂ) :
    chapter06ComplexLocalSize z = ‖z‖ ^ 2 := rfl

@[simp] theorem chapter06_real_local_size_eq_absolute_value (x : ℝ) :
    chapter06RealLocalSize x = |x| := rfl

@[simp] theorem chapter06_self_dual_complex_measure_scale (μ : Measure ℂ) :
    chapter06SelfDualComplexMeasure μ =
      (2 : ℝ≥0∞) • μ := rfl

@[simp] theorem chapter06_self_dual_global_scaling_apply (r₂ : ℕ) :
    chapter06SelfDualGlobalScaling r₂ = (2 : ℝ≥0∞) ^ r₂ := rfl

theorem chapter06_product_formula_principal_scalar
    (Place : Type*) (size : Place → K → ℝ≥0∞)
    (adelicProduct : K → ℝ≥0∞)
    (hformula : Chapter06ProductFormula K Place size adelicProduct)
    (a : Kˣ) : adelicProduct (a : K) = 1 := by
  exact hformula a

theorem chapter06_product_formula_iff_principal_volume_preserving
    (Place : Type*) (size : Place → K → ℝ≥0∞)
    (adelicProduct : K → ℝ≥0∞) :
    Chapter06ProductFormula K Place size adelicProduct ↔
      ∀ a : Kˣ, adelicProduct (a : K) = 1 := Iff.rfl

theorem chapter06_adelic_product_measure_covolume
    {P : Chapter06AdeleData K O KInf Af Ohat} {D : Set KInf}
    [MeasurableSpace KInf] [MeasurableSpace Af]
    (M : Chapter06AdelicMeasureData P D) :
    chapter06AdelicQuotientCovolume M =
      ENNReal.ofReal (chapter06OrdinaryCovolume M.r₂ M.discriminant) := by
  sorry

/-- With ordinary Lebesgue measure at real places and ordinary planar measure
at complex places, the fundamental region has the displayed covolume. -/
theorem chapter06_ordinary_adelic_covolume_formula
    {P : Chapter06AdeleData K O KInf Af Ohat} {D : Set KInf}
    [MeasurableSpace KInf] [MeasurableSpace Af]
    (M : Chapter06AdelicMeasureData P D) :
    chapter06AdelicQuotientCovolume M =
      ENNReal.ofReal
        ((1 / 2 : ℝ) ^ M.r₂ * Real.sqrt |M.discriminant|) := by
  simpa [chapter06OrdinaryCovolume] using
    chapter06_adelic_product_measure_covolume M

/-- Self-dual normalizations are recorded separately from the ordinary planar
normalization. -/
structure Chapter06SelfDualVolumeData (Q : Type*) where
  quotientVolume : ℝ≥0∞
  normalized : quotientVolume = 1

theorem chapter06_self_dual_quotient_volume_one
    {Q : Type*} (M : Chapter06SelfDualVolumeData Q) :
    M.quotientVolume = 1 := M.normalized

end

end LastLib.Book04AdelesAndIdeles.Chapter06
