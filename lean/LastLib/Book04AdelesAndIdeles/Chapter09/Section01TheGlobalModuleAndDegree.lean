import LastLib.Book04AdelesAndIdeles.Chapter09.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter09

noncomputable section

open scoped BigOperators NNReal

open NumberField IsDedekindDomain

/-!
## 9.1. The global module and degree
-/

def chapter09Degree
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter09Idele K) : ℝ :=
  -Real.log (((chapter09IdeleModule x : Chapter09PositiveReal) : ℝ≥0) : ℝ)

@[simp]
theorem chapter09Degree_def
    {K : Type*} [Field K] [NumberField K] (x : Chapter09Idele K) :
    chapter09Degree x =
      -Real.log (((chapter09IdeleModule x : Chapter09PositiveReal) : ℝ≥0) : ℝ) :=
  rfl

def chapter09DegreeHom
    (K : Type*) [Field K] [NumberField K] :
    Chapter09Idele K →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd (chapter09Degree x)
  map_one' := by
    sorry
  map_mul' x y := by
    sorry

@[simp]
theorem chapter09DegreeHom_apply
    {K : Type*} [Field K] [NumberField K] (x : Chapter09Idele K) :
    chapter09DegreeHom K x = Multiplicative.ofAdd (chapter09Degree x) :=
  rfl

/- The restricted-product support is finite, while the archimedean index is
finite.  These are the two finiteness assertions behind the displayed
idele-module product. -/
theorem chapter09FiniteIdeleModule_eventually_one
    {K : Type*} [Field K] [NumberField K] (x : (Chapter09FiniteAdele K)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      chapter09NormUnit
        ((RestrictedProduct.unitsEquiv
          (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x) v) = 1 := by
  sorry

theorem chapter09FiniteIdeleModule_support_finite
    {K : Type*} [Field K] [NumberField K] (x : (Chapter09FiniteAdele K)ˣ) :
    ({v : HeightOneSpectrum (𝓞 K) |
      chapter09NormUnit
        ((RestrictedProduct.unitsEquiv
          (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x) v) ≠ 1}).Finite := by
  sorry

/- Mathlib indexes the finite local factors by maximal ideals, while the
book's notation indexes them by finite places.  This reindexing bridge keeps
the displayed module independent of that implementation choice. -/
theorem chapter09FiniteIdeleModule_reindexed_finite_places
    {K : Type*} [Field K] [NumberField K]
    (x : (Chapter09FiniteAdele K)ˣ) :
    chapter09FiniteIdeleModule x =
      ∏ᶠ w : NumberField.FinitePlace K,
        chapter09NormUnit
          ((RestrictedProduct.unitsEquiv
            (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x)
            (NumberField.FinitePlace.maximalIdeal w)) := by
  sorry

theorem chapter09InfiniteIdeleModule_is_finite_product
    {K : Type*} [Field K] [NumberField K] (x : (Chapter09InfiniteAdele K)ˣ) :
    chapter09InfiniteIdeleModule x =
      ∏ v : InfinitePlace K,
        (chapter09NormUnit ((MulEquiv.piUnits x) v)) ^ v.mult :=
  rfl

theorem chapter09IdeleModule_coe_pos
    {K : Type*} [Field K] [NumberField K] (x : Chapter09Idele K) :
    0 < (((chapter09IdeleModule x : Chapter09PositiveReal) : ℝ≥0) : ℝ) := by
  sorry

theorem chapter09IdeleModule_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (chapter09IdeleModuleHom K) := by
  sorry

theorem chapter09Degree_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (chapter09DegreeHom K) := by
  sorry

theorem chapter09IdeleModule_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter09IdeleModuleHom K) := by
  sorry

theorem chapter09Degree_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter09DegreeHom K) := by
  sorry

theorem chapter09Degree_ker_eq_normOne
    (K : Type*) [Field K] [NumberField K] :
    (chapter09DegreeHom K).ker = chapter09NormOneIdeles K := by
  sorry

theorem chapter09Module_ker_eq_degree_ker
    (K : Type*) [Field K] [NumberField K] :
    (chapter09IdeleModuleHom K).ker = (chapter09DegreeHom K).ker := by
  rw [chapter09Degree_ker_eq_normOne]
  rfl

/- A finite-place uniformizer is represented by an idele that is one at all
other places.  The local norm is the inverse residue-field cardinality. -/
structure Chapter09UniformizerIdeleData
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) where
  idele : Chapter09Idele K
  infinite_components_one :
    ∀ w : InfinitePlace K,
      (MulEquiv.piUnits ((chapter09IdeleProductEquiv K idele).1) w) = 1
  finite_component_at :
    ((chapter09NormUnit
      ((RestrictedProduct.unitsEquiv
        (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
        ((chapter09IdeleProductEquiv K idele).2)) v) : Chapter09PositiveReal) : ℝ≥0) =
      (Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹
  finite_components_off :
    ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v →
      (RestrictedProduct.unitsEquiv
        (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
        ((chapter09IdeleProductEquiv K idele).2) w) = 1

theorem chapter09_uniformizer_data_local_norm
    {K : Type*} [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 K)}
    (d : Chapter09UniformizerIdeleData K v) :
    ((chapter09NormUnit
      ((RestrictedProduct.unitsEquiv
        (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      ((chapter09IdeleProductEquiv K d.idele).2)) v) : Chapter09PositiveReal) : ℝ≥0) =
      (Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹ := by
  exact d.finite_component_at

theorem chapter09_exists_uniformizer_idele_data
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty (Chapter09UniformizerIdeleData K v) := by
  sorry

theorem chapter09_uniformizer_data_degree
    {K : Type*} [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 K)}
    (d : Chapter09UniformizerIdeleData K v) :
    chapter09Degree d.idele = Real.log (Ideal.absNorm v.asIdeal) ∧
      0 < chapter09Degree d.idele := by
  sorry

/- A finite-place uniformizer has local size `q_v⁻¹`; the sign in the
definition of degree therefore makes its degree `log q_v`. -/
theorem chapter09_exists_uniformizer_idele_degree
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ x : Chapter09Idele K,
      chapter09Degree x = Real.log (Ideal.absNorm v.asIdeal) ∧
        0 < chapter09Degree x := by
  rcases chapter09_exists_uniformizer_idele_data K v with ⟨d⟩
  exact ⟨d.idele, (chapter09_uniformizer_data_degree d).1,
    (chapter09_uniformizer_data_degree d).2⟩

theorem chapter09_principal_idele_in_normOne
    {K : Type*} [Field K] [NumberField K] (a : Kˣ) :
    chapter09PrincipalIdele K a ∈ chapter09NormOneIdeles K := by
  rw [chapter09NormOneIdeles_mem_iff]
  simpa using chapter09PrincipalIdele_module_eq_one a

theorem chapter09_principal_idele_degree_zero
    {K : Type*} [Field K] [NumberField K] (a : Kˣ) :
    chapter09Degree (chapter09PrincipalIdele K a) = 0 := by
  sorry

def chapter09IdeleClassDegree
    (K : Type*) [Field K] [NumberField K] :
    Chapter09IdeleClassGroup K →* Multiplicative ℝ :=
  QuotientGroup.lift (chapter09PrincipalIdeleSubgroup K)
    (chapter09DegreeHom K) (by
      intro x hx
      sorry)

theorem chapter09IdeleClassDegree_apply
    {K : Type*} [Field K] [NumberField K] (x : Chapter09Idele K) :
    chapter09IdeleClassDegree K (QuotientGroup.mk x) =
      chapter09DegreeHom K x := by
  rfl

theorem chapter09IdeleClassDegree_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter09IdeleClassDegree K) := by
  sorry

theorem chapter09IdeleClassDegree_ker_eq_classNormOne
    (K : Type*) [Field K] [NumberField K] :
    (chapter09IdeleClassDegree K).ker = chapter09ClassNormOne K := by
  sorry

theorem chapter09_module_descends_to_idele_class_group
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter09IdeleClassModule K) := by
  sorry

theorem chapter09_class_module_kernel_is_normOne_class_group
    (K : Type*) [Field K] [NumberField K] :
    chapter09ClassNormOne K = (chapter09IdeleClassModule K).ker :=
  rfl

/- The finite-unit subgroup records the warning that norm one is a global
condition, not the same condition as being a finite unit idele. -/
theorem chapter09_normOne_is_not_finite_unit_condition
    (K : Type*) [Field K] [NumberField K] :
    ∃ x : Chapter09Idele K,
      x ∈ chapter09NormOneIdeles K ∧
        x ∉ chapter09FiniteUnitIdeleSubgroup K := by
  sorry

/- The number-field degree in this chapter is real-valued and uses the
archimedean magnitude.  In the separate function-field theory with constant
field `𝔽_q`, the normalization is `-log_q |x|_A : ℤ`; that complete-curve
product formula is intentionally not identified with this number-field map.
The surjectivity statement above is the formal number-field assertion. -/

end

end LastLib.Book04AdelesAndIdeles.Chapter09
