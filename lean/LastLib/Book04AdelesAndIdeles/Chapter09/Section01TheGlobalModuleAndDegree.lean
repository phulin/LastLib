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
    apply Multiplicative.ext
    change chapter09Degree (1 : Chapter09Idele K) = 0
    rw [chapter09Degree_def]
    have hmodule : chapter09IdeleModule (1 : Chapter09Idele K) = 1 := by
      exact (chapter09IdeleModuleHom K).map_one
    rw [hmodule]
    simp
  map_mul' x y := by
    apply Multiplicative.ext
    change chapter09Degree (x * y) = chapter09Degree x + chapter09Degree y
    rw [chapter09Degree_def, chapter09Degree_def, chapter09Degree_def]
    have hmodule : chapter09IdeleModule (x * y) =
        chapter09IdeleModule x * chapter09IdeleModule y := by
      change (chapter09IdeleModuleHom K) (x * y) =
        (chapter09IdeleModuleHom K) x * (chapter09IdeleModuleHom K) y
      exact (chapter09IdeleModuleHom K).map_mul x y
    rw [hmodule]
    simp only [Units.val_mul, NNReal.coe_mul]
    have hx0 : (((chapter09IdeleModule x : Chapter09PositiveReal) : ℝ≥0) : ℝ) ≠ 0 := by
      exact_mod_cast (Units.ne_zero (chapter09IdeleModule x))
    have hy0 : (((chapter09IdeleModule y : Chapter09PositiveReal) : ℝ≥0) : ℝ) ≠ 0 := by
      exact_mod_cast (Units.ne_zero (chapter09IdeleModule y))
    rw [Real.log_mul hx0 hy0]
    ring

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
      chapter09FiniteNormUnit v
        ((RestrictedProduct.unitsEquiv
          (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x) v) = 1 := by
  filter_upwards [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_order_eventually_eq_zero x]
    with v hv
  apply Units.ext
  change (Ideal.absNorm v.asIdeal : ℝ≥0) ^
    (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
      (↑((RestrictedProduct.unitsEquiv
        (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x) v) :
        v.adicCompletion K)) = 1
  have heq : (↑((RestrictedProduct.unitsEquiv
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x) v) :
      v.adicCompletion K) =
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent x v :=
    RestrictedProduct.unitsEquiv_apply v x
  rw [heq]
  change (Ideal.absNorm v.asIdeal : ℝ≥0) ^
    (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleOrder x v) = 1
  rw [hv]
  simp

theorem chapter09FiniteIdeleModule_support_finite
    {K : Type*} [Field K] [NumberField K] (x : (Chapter09FiniteAdele K)ˣ) :
    ({v : HeightOneSpectrum (𝓞 K) |
      chapter09FiniteNormUnit v
        ((RestrictedProduct.unitsEquiv
          (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x) v) ≠ 1}).Finite := by
  exact Filter.eventually_cofinite.mp
    (chapter09FiniteIdeleModule_eventually_one x)

/- Mathlib indexes the finite local factors by maximal ideals, while the
book's notation indexes them by finite places.  This reindexing bridge keeps
the displayed module independent of that implementation choice. -/
theorem chapter09FiniteIdeleModule_reindexed_finite_places
    {K : Type*} [Field K] [NumberField K]
    (x : (Chapter09FiniteAdele K)ˣ) :
    chapter09FiniteIdeleModule x =
      ∏ᶠ w : NumberField.FinitePlace K,
        chapter09FiniteNormUnit (NumberField.FinitePlace.maximalIdeal w)
          ((RestrictedProduct.unitsEquiv
            (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x)
            (NumberField.FinitePlace.maximalIdeal w)) := by
  rw [chapter09FiniteIdeleModule]
  exact (finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum).symm

theorem chapter09InfiniteIdeleModule_is_finite_product
    {K : Type*} [Field K] [NumberField K] (x : (Chapter09InfiniteAdele K)ˣ) :
    chapter09InfiniteIdeleModule x =
      ∏ v : InfinitePlace K,
        (chapter09NormUnit ((MulEquiv.piUnits x) v)) ^ v.mult :=
  rfl

theorem chapter09IdeleModule_coe_pos
    {K : Type*} [Field K] [NumberField K] (x : Chapter09Idele K) :
    0 < (((chapter09IdeleModule x : Chapter09PositiveReal) : ℝ≥0) : ℝ) := by
  exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))

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
  ext x
  constructor
  · intro hx
    change chapter09Degree x = 0 at hx
    rw [chapter09Degree_def] at hx
    have hmoduleNN : ((chapter09IdeleModule x : Chapter09PositiveReal) : ℝ≥0) = 1 := by
      apply NNReal.eq
      exact Real.eq_one_of_pos_of_log_eq_zero (chapter09IdeleModule_coe_pos x) (by linarith)
    have hmodule : chapter09IdeleModule x = 1 := by
      apply Units.ext
      exact hmoduleNN
    apply (chapter09NormOneIdeles_mem_iff).2
    change chapter09IdeleModule x = 1
    exact hmodule
  · intro hx
    have hmodule : chapter09IdeleModule x = 1 := by
      apply Units.ext
      have hhom := (chapter09NormOneIdeles_mem_iff).1 hx
      change chapter09IdeleModule x = 1 at hhom
      exact congrArg Units.val hhom
    change chapter09Degree x = 0
    rw [chapter09Degree_def, hmodule]
    simp

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
    ((chapter09FiniteNormUnit v
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
    ((chapter09FiniteNormUnit v
      ((RestrictedProduct.unitsEquiv
        (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      ((chapter09IdeleProductEquiv K d.idele).2)) v) : Chapter09PositiveReal) : ℝ≥0) =
      (Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹ := by
  exact d.finite_component_at

theorem chapter09_exists_uniformizer_idele_data
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty (Chapter09UniformizerIdeleData K v) := by
  classical
  let localUnit : ∀ w : HeightOneSpectrum (𝓞 K), (w.adicCompletion K)ˣ := fun w =>
    if hw : w = v then
      Units.mk0
        (Classical.choose
          (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
            K w (WithZero.exp (-1)))) (by
          have hval := Classical.choose_spec
            (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
              K w (WithZero.exp (-1)))
          intro hz
          rw [hz, map_zero] at hval
          exact WithZero.exp_ne_zero hval.symm)
    else 1
  have hlocal : ∀ w : HeightOneSpectrum (𝓞 K),
      Valued.v (localUnit w : w.adicCompletion K) =
        if w = v then WithZero.exp (-1) else 1 := by
    intro w
    by_cases hw : w = v
    · subst w
      dsimp [localUnit]
      simp only [if_pos rfl]
      exact Classical.choose_spec
        (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
          K v (WithZero.exp (-1)))
    · dsimp [localUnit]
      simp only [if_neg hw]
      exact Valuation.map_one _
  have hunit : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      localUnit w ∈ (Submonoid.ofClass (w.adicCompletionIntegers K)).units := by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw
    have hoff : localUnit w = 1 := by
      simp only [localUnit, dif_neg hw]
    rw [hoff]
    apply (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).2
    exact Valuation.map_one _
  let z : (Chapter09FiniteAdele K)ˣ :=
    RestrictedProduct.mkUnit (fun w => localUnit w) hunit
  let x : Chapter09Idele K :=
    (chapter09IdeleProductEquiv K).symm (1, z)
  have horder :
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
        (localUnit v : v.adicCompletion K) = 1 := by
    unfold LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder
    have hlocal_at : Valued.v (localUnit v : v.adicCompletion K) =
        WithZero.exp (-1) := by
      simpa only [if_pos rfl] using hlocal v
    have hzero : Valued.v (localUnit v : v.adicCompletion K) ≠ 0 := by
      rw [hlocal_at]
      exact WithZero.exp_ne_zero
    rw [dif_neg hzero, hlocal_at, WithZero.toAdd_unzero_eq_log,
      WithZero.log_exp]
    norm_num
  have hxprod : chapter09IdeleProductEquiv K x = (1, z) := by
    simp [x]
  refine ⟨⟨x, ?_, ?_, ?_⟩⟩
  · intro w
    change MulEquiv.piUnits ((chapter09IdeleProductEquiv K x).1) w = 1
    rw [hxprod]
    have hpi : MulEquiv.piUnits (1 : (Chapter09InfiniteAdele K)ˣ) = 1 :=
      (MulEquiv.piUnits).map_one
    rw [hpi]
    rfl
  · change ((chapter09FiniteNormUnit v
      ((RestrictedProduct.unitsEquiv
        (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) z) v) :
        Chapter09PositiveReal) : ℝ≥0) =
      (Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹
    change ((chapter09FiniteNormUnit v (localUnit v) : Chapter09PositiveReal) : ℝ≥0) =
      (Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹
    rw [chapter09FiniteNormUnit_coe, horder]
    simp
  · intro w hw
    change (RestrictedProduct.unitsEquiv
      (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) z) w = 1
    change localUnit w = 1
    simp only [localUnit, dif_neg hw]

theorem chapter09_uniformizer_data_degree
    {K : Type*} [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 K)}
    (d : Chapter09UniformizerIdeleData K v) :
    chapter09Degree d.idele = Real.log (Ideal.absNorm v.asIdeal) ∧
      0 < chapter09Degree d.idele := by
  have hinf : chapter09InfiniteIdeleModule
      ((chapter09IdeleProductEquiv K d.idele).1) = 1 := by
    unfold chapter09InfiniteIdeleModule
    apply Finset.prod_eq_one
    intro w hw
    rw [d.infinite_components_one w]
    simp [chapter09NormUnit]
  let f : HeightOneSpectrum (𝓞 K) → Chapter09PositiveReal := fun w =>
    chapter09FiniteNormUnit w
      ((RestrictedProduct.unitsEquiv
        (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
        ((chapter09IdeleProductEquiv K d.idele).2)) w)
  have hoff : ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v → f w = 1 := by
    intro w hw
    dsimp [f]
    rw [d.finite_components_off w hw]
    apply Units.ext
    change (Ideal.absNorm w.asIdeal : ℝ≥0) ^
      (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder w
        (1 : w.adicCompletion K)) = 1
    have horder :
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder w
          (1 : w.adicCompletion K) = 0 := by
      have hone : (1 : w.adicCompletion K) ≠ 0 := one_ne_zero
      apply (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_local_order_eq_zero_iff_valued_eq_one
        w (1 : w.adicCompletion K) hone).2
      exact Valuation.map_one _
    rw [horder]
    simp
  have hfin : chapter09FiniteIdeleModule
      ((chapter09IdeleProductEquiv K d.idele).2) = f v := by
    unfold chapter09FiniteIdeleModule
    exact finprod_eq_single f v hoff
  have hfin_coe : ((f v : Chapter09PositiveReal) : ℝ≥0) =
      (Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹ := by
    exact d.finite_component_at
  have hmodule :
      (((chapter09IdeleModule d.idele : Chapter09PositiveReal) : ℝ≥0) : ℝ) =
        ((Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹ : ℝ) := by
    rw [chapter09IdeleModule_eq_infinite_mul_finite,
      hfin, hinf, one_mul]
    exact_mod_cast hfin_coe
  constructor
  · rw [chapter09Degree_def, hmodule]
    rw [Real.log_inv]
    simp
  · rw [chapter09Degree_def, hmodule]
    have hq : 1 < ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ) := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    rw [Real.log_inv]
    simpa only [neg_neg] using Real.log_pos hq

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
  rw [chapter09Degree_def, chapter09PrincipalIdele_module_eq_one]
  simp

def chapter09IdeleClassDegree
    (K : Type*) [Field K] [NumberField K] :
    Chapter09IdeleClassGroup K →* Multiplicative ℝ :=
  QuotientGroup.lift (chapter09PrincipalIdeleSubgroup K)
    (chapter09DegreeHom K) (by
      intro x hx
      rcases hx with ⟨a, rfl⟩
      change Multiplicative.ofAdd
        (chapter09Degree (chapter09PrincipalIdele K a)) = 1
      rw [chapter09_principal_idele_degree_zero]
      rfl)

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
  ext x
  rcases QuotientGroup.mk_surjective x with ⟨g, rfl⟩
  change g ∈ (chapter09DegreeHom K).ker ↔
    g ∈ (chapter09IdeleModuleHom K).ker
  rw [chapter09Degree_ker_eq_normOne K]
  rfl

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
