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

theorem chapter09FiniteNormUnit_continuous
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (chapter09FiniteNormUnit v) := by
  apply continuous_iff_continuousAt.2
  intro u
  apply ContinuousAt.congr (f := fun _ => chapter09FiniteNormUnit v u)
    continuousAt_const
  have hval :
      {y : v.adicCompletion K |
        Valued.v y = Valued.v (u : v.adicCompletion K)} ∈
        nhds (u : v.adicCompletion K) := by
    exact Valued.locally_const (R := v.adicCompletion K)
      (by simp)
  have hpre :
      {y : (v.adicCompletion K)ˣ |
        Valued.v (y : v.adicCompletion K) = Valued.v (u : v.adicCompletion K)} ∈
        nhds u := by
    exact Units.continuous_val.continuousAt.preimage_mem_nhds hval
  filter_upwards [hpre] with y hy
  have horder :
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
          (y : v.adicCompletion K) =
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
          (u : v.adicCompletion K) := by
    unfold LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder
    have hy0 : Valued.v (y : v.adicCompletion K) ≠ 0 := by
      simp
    have hu0 : Valued.v (u : v.adicCompletion K) ≠ 0 := by
      simp
    rw [dif_neg hy0, dif_neg hu0]
    rw [WithZero.toAdd_unzero_eq_log, WithZero.toAdd_unzero_eq_log]
    exact congrArg (fun z => -WithZero.log z) hy
  simp [chapter09FiniteNormUnit, horder]

private theorem chapter09FiniteIdeleFactor_continuous
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (fun x : (Chapter09FiniteAdele K)ˣ =>
      chapter09FiniteNormUnit v
        ((RestrictedProduct.unitsEquiv
          (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x) v)) := by
  let U := RestrictedProduct.unitsEquiv
    (𝓕 := Filter.cofinite)
    (B := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletionIntegers K)
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
  have hU : Continuous (fun x : (Chapter09FiniteAdele K)ˣ => U x v) := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun x : (Chapter09FiniteAdele K)ˣ =>
        ((x : Chapter09FiniteAdele K) v))
      exact RestrictedProduct.continuous_eval v |>.comp Units.continuous_val
    · change Continuous (fun x : (Chapter09FiniteAdele K)ˣ =>
        ((↑(x⁻¹) : Chapter09FiniteAdele K) v))
      exact RestrictedProduct.continuous_eval v |>.comp Units.continuous_coe_inv
  exact (chapter09FiniteNormUnit_continuous v).comp hU

private theorem chapter09FiniteNormUnit_eq_one_of_mem_units
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ)
    (hu : u ∈ (v.adicCompletionIntegers K).units) :
    chapter09FiniteNormUnit v u = 1 := by
  have hu0 : (u : v.adicCompletion K) ≠ 0 := Units.ne_zero u
  have huv : Valued.v (u : v.adicCompletion K) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).1 hu
  have horder :
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
          (u : v.adicCompletion K) = 0 :=
    (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_local_order_eq_zero_iff_valued_eq_one
      v (u : v.adicCompletion K) hu0).2 huv
  apply Units.ext
  rw [chapter09FiniteNormUnit_coe, horder]
  simp

private theorem chapter09FiniteIdeleModule_locallyFinite
    {K : Type*} [Field K] [NumberField K] :
    LocallyFinite (fun v : HeightOneSpectrum (𝓞 K) =>
      Function.mulSupport (fun x : (Chapter09FiniteAdele K)ˣ =>
        chapter09FiniteNormUnit v
          ((RestrictedProduct.unitsEquiv
            (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x) v))) := by
  classical
  let U := RestrictedProduct.unitsEquiv
    (𝓕 := Filter.cofinite)
    (B := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletionIntegers K)
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
  intro x
  let S : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | (x : Chapter09FiniteAdele K) v ∈ v.adicCompletionIntegers K ∧
      ((↑(x⁻¹) : Chapter09FiniteAdele K) v ∈ v.adicCompletionIntegers K)}
  have hS_mem : S ∈ Filter.cofinite := by
    filter_upwards [x.1.2, (x⁻¹).1.2] with v hv hv'
    exact ⟨hv, hv'⟩
  have hopen : ∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    intro v
    exact Valued.isOpen_valuationSubring (v.adicCompletion K)
  have hval_open : IsOpen {z : Chapter09FiniteAdele K |
      ∀ v, v ∈ S → z v ∈ v.adicCompletionIntegers K} := by
    exact RestrictedProduct.isOpen_forall_imp_mem hopen
  have hval_mem : (x : Chapter09FiniteAdele K) ∈
      {z : Chapter09FiniteAdele K | ∀ v, v ∈ S → z v ∈ v.adicCompletionIntegers K} := by
    intro v hv
    exact hv.1
  have hinv_mem : (↑(x⁻¹) : Chapter09FiniteAdele K) ∈
      {z : Chapter09FiniteAdele K | ∀ v, v ∈ S → z v ∈ v.adicCompletionIntegers K} := by
    intro v hv
    exact hv.2
  have hval_nhds : {y : (Chapter09FiniteAdele K)ˣ |
      ∀ v, v ∈ S → (y : Chapter09FiniteAdele K) v ∈ v.adicCompletionIntegers K} ∈ nhds x := by
    exact Units.continuous_val.continuousAt.preimage_mem_nhds
      (hval_open.mem_nhds hval_mem)
  have hinv_nhds : {y : (Chapter09FiniteAdele K)ˣ |
      ∀ v, v ∈ S → ((↑(y⁻¹) : Chapter09FiniteAdele K) v ∈ v.adicCompletionIntegers K)} ∈
      nhds x := by
    exact Units.continuous_coe_inv.continuousAt.preimage_mem_nhds
      (hval_open.mem_nhds hinv_mem)
  refine ⟨{y : (Chapter09FiniteAdele K)ˣ |
      ∀ v, v ∈ S →
        ((y : Chapter09FiniteAdele K) v ∈ v.adicCompletionIntegers K ∧
          ((↑(y⁻¹) : Chapter09FiniteAdele K) v ∈ v.adicCompletionIntegers K))},
    ?_, ?_⟩
  · filter_upwards [hval_nhds, hinv_nhds] with y hy hy'
    intro v hv
    exact ⟨hy v hv, hy' v hv⟩
  have hSc : Sᶜ.Finite := Filter.eventually_cofinite.mp hS_mem
  apply hSc.subset
  intro v hv
  by_contra hvScompl
  have hvS : v ∈ S := by
    simpa only [Set.mem_compl_iff, not_not] using hvScompl
  rcases hv with ⟨y, hy_support, hy_neighborhood⟩
  change chapter09FiniteNormUnit v (U y v) ≠ 1 at hy_support
  apply hy_support
  apply chapter09FiniteNormUnit_eq_one_of_mem_units v
  apply Submonoid.mem_units_of_val_mem_inv_val_mem
  · change ((y : Chapter09FiniteAdele K) v) ∈ v.adicCompletionIntegers K
    exact (hy_neighborhood v hvS).1
  · change ((↑(y⁻¹) : Chapter09FiniteAdele K) v) ∈ v.adicCompletionIntegers K
    exact (hy_neighborhood v hvS).2

private theorem chapter09FiniteIdeleModule_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (chapter09FiniteIdeleModule : (Chapter09FiniteAdele K)ˣ →
      Chapter09PositiveReal) := by
  change Continuous (fun x : (Chapter09FiniteAdele K)ˣ =>
    ∏ᶠ v : HeightOneSpectrum (𝓞 K),
      chapter09FiniteNormUnit v
        ((RestrictedProduct.unitsEquiv
          (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x) v))
  exact continuous_finprod
    (fun v => chapter09FiniteIdeleFactor_continuous v)
    chapter09FiniteIdeleModule_locallyFinite

private theorem chapter09NormUnit_continuous
    {F : Type*} [NormedField F] :
    Continuous (chapter09NormUnit : Fˣ → Chapter09PositiveReal) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun u : Fˣ => ‖(u : F)‖₊)
    exact continuous_nnnorm.comp Units.continuous_val
  · have h : Continuous (fun u : Fˣ => ‖(↑(u⁻¹) : F)‖₊) :=
      continuous_nnnorm.comp Units.continuous_coe_inv
    simpa [chapter09NormUnit, nnnorm_inv] using h

private theorem chapter09InfiniteIdeleModule_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (chapter09InfiniteIdeleModule : (Chapter09InfiniteAdele K)ˣ →
      Chapter09PositiveReal) := by
  change Continuous (fun x : (Chapter09InfiniteAdele K)ˣ =>
    ∏ v : InfinitePlace K,
      (chapter09NormUnit ((MulEquiv.piUnits x) v)) ^ v.mult)
  apply continuous_finsetProd Finset.univ
  intro v hv
  have hpi : Continuous (fun x : (Chapter09InfiniteAdele K)ˣ =>
      (MulEquiv.piUnits x) v) := by
    exact continuous_apply v |>.comp
      (ContinuousMulEquiv.piUnits (M := fun v : InfinitePlace K => v.Completion)).continuous
  exact (chapter09NormUnit_continuous.comp hpi).pow v.mult

theorem chapter09IdeleModule_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (chapter09IdeleModuleHom K) := by
  change Continuous (fun x : Chapter09Idele K => chapter09IdeleModule x)
  rw [show (fun x : Chapter09Idele K => chapter09IdeleModule x) =
      (fun x =>
        chapter09InfiniteIdeleModule
            ((chapter09IdeleProductEquiv K x).1) *
          chapter09FiniteIdeleModule ((chapter09IdeleProductEquiv K x).2)) by
    funext x
    exact chapter09IdeleModule_eq_infinite_mul_finite x]
  have hpair : Continuous (fun x : Chapter09Idele K =>
      chapter09IdeleProductEquiv K x) :=
    (chapter09IdeleProductContinuousEquiv K).continuous
  have hprod : Continuous (fun p :
      (Chapter09InfiniteAdele K)ˣ × (Chapter09FiniteAdele K)ˣ =>
      chapter09InfiniteIdeleModule p.1 * chapter09FiniteIdeleModule p.2) := by
    exact (chapter09InfiniteIdeleModule_continuous K).comp continuous_fst |>.mul
      ((chapter09FiniteIdeleModule_continuous K).comp continuous_snd)
  exact hprod.comp hpair

theorem chapter09Degree_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (chapter09DegreeHom K) := by
  apply continuous_iff_continuousAt.2
  intro x
  change ContinuousAt (fun x : Chapter09Idele K =>
    Multiplicative.ofAdd (chapter09Degree x)) x
  have hmodule : ContinuousAt (fun x : Chapter09Idele K =>
      chapter09IdeleModule x) x :=
    (chapter09IdeleModule_continuous K).continuousAt
  have hmodule_nnreal : ContinuousAt (fun x : Chapter09Idele K =>
      ((chapter09IdeleModule x : Chapter09PositiveReal) : ℝ≥0)) x :=
    Units.continuous_val.continuousAt.comp hmodule
  have hmodule_real : ContinuousAt (fun x : Chapter09Idele K =>
      (((chapter09IdeleModule x : Chapter09PositiveReal) : ℝ≥0) : ℝ)) x :=
    NNReal.continuous_coe.continuousAt.comp hmodule_nnreal
  have hlog : ContinuousAt (fun x : Chapter09Idele K =>
      Real.log (((chapter09IdeleModule x : Chapter09PositiveReal) : ℝ≥0) : ℝ)) x :=
    (Real.continuousAt_log (ne_of_gt (chapter09IdeleModule_coe_pos x))).comp'
      (f := fun x : Chapter09Idele K =>
        (((chapter09IdeleModule x : Chapter09PositiveReal) : ℝ≥0) : ℝ)) hmodule_real
  have hdegree : ContinuousAt (fun x : Chapter09Idele K =>
      chapter09Degree x) x := by
    change ContinuousAt (fun x : Chapter09Idele K =>
      -Real.log (((chapter09IdeleModule x : Chapter09PositiveReal) : ℝ≥0) : ℝ)) x
    exact hlog.neg
  exact continuous_ofAdd.continuousAt.comp hdegree

theorem chapter09IdeleModule_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter09IdeleModuleHom K) := by
  intro t
  classical
  let v : InfinitePlace K :=
    Classical.choice (inferInstance : Nonempty (InfinitePlace K))
  rcases v.isReal_or_isComplex with hv | hv
  · let e := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv
    let z : v.Completion := e.symm (t : ℝ)
    have ht : 0 < (t : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero t))
    have hzero : e (0 : v.Completion) = 0 := by
      dsimp [e]
      exact (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).map_zero
    have hzt : e z = (t : ℝ) := by
      simp [z]
    have hz : z ≠ 0 := by
      intro hz
      have hzero_t : (t : ℝ) = 0 := by
        calc
          (t : ℝ) = e z := hzt.symm
          _ = e 0 := by rw [hz]
          _ = 0 := hzero
      exact (ne_of_gt ht) hzero_t
    let u : v.Completionˣ := Units.mk0 z hz
    have hnormz : ‖z‖ = (t : ℝ) := by
      have hdist := e.symm.isometry.dist_eq (0 : ℝ) (t : ℝ)
      have hzero' : e.symm (0 : ℝ) = (0 : v.Completion) := by
        dsimp [e]
        exact (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.map_zero
      have hzt' : e.symm (t : ℝ) = z := by
        rfl
      rw [hzero', hzt'] at hdist
      simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_pos ht] using hdist
    have hnormu : chapter09NormUnit u = t := by
      apply Units.ext
      apply NNReal.eq
      change ‖(u : v.Completion)‖ = (t : ℝ)
      change ‖z‖ = (t : ℝ)
      exact hnormz
    let y : ∀ w : InfinitePlace K, w.Completionˣ := fun w =>
      dite (w = v) (fun h => h ▸ u) (fun _ => 1)
    let xinf : (Chapter09InfiniteAdele K)ˣ := (MulEquiv.piUnits).symm y
    let x : Chapter09Idele K :=
      (chapter09IdeleProductEquiv K).symm (xinf, 1)
    have hyv : y v = u := by simp [y]
    have hyoff : ∀ w : InfinitePlace K, w ≠ v → y w = 1 := by
      intro w hw
      simp [y, hw]
    refine ⟨x, ?_⟩
    change chapter09IdeleModule x = t
    rw [chapter09IdeleModule_eq_infinite_mul_finite]
    have hdecomp : chapter09IdeleProductEquiv K x = (xinf, 1) := by
      simp [x]
    rw [hdecomp]
    have hfin : chapter09FiniteIdeleModule (1 : (Chapter09FiniteAdele K)ˣ) = 1 := by
      unfold chapter09FiniteIdeleModule
      apply finprod_eq_one_of_forall_eq_one
      intro w
      exact (chapter09FiniteUnitIdeles_mem_iff.mp (Subgroup.one_mem _) w)
    rw [hfin, mul_one]
    unfold chapter09InfiniteIdeleModule
    have hpi : MulEquiv.piUnits xinf = y :=
      (MulEquiv.piUnits).apply_symm_apply y
    rw [hpi, Fintype.prod_eq_single v]
    · rw [hyv, hnormu, hv.mult_eq_one]
      simp
    · intro w hw
      rw [hyoff w hw]
      simp [chapter09NormUnit]
  · let e := NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv
    let s : ℝ≥0 := NNReal.sqrt (t : ℝ≥0)
    let z : v.Completion := e.symm (Complex.ofReal (s : ℝ))
    have ht : 0 < (t : ℝ≥0) :=
      pos_iff_ne_zero.mpr (Units.ne_zero t)
    have hs : 0 < s := by
      dsimp [s]
      exact NNReal.sqrt_pos.2 ht
    have hzero : e (0 : v.Completion) = 0 := by
      dsimp [e]
      exact (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).map_zero
    have hzt : e z = Complex.ofReal (s : ℝ) := by
      simp [z]
    have hz : z ≠ 0 := by
      intro hz
      have hzero_z : Complex.ofReal (s : ℝ) = 0 := by
        calc
          Complex.ofReal (s : ℝ) = e z := hzt.symm
          _ = e 0 := by rw [hz]
          _ = 0 := hzero
      exact (ne_of_gt (NNReal.coe_pos.mpr hs)) (by
        simpa using congrArg Complex.re hzero_z)
    let u : v.Completionˣ := Units.mk0 z hz
    have hnormz : ‖z‖ = (s : ℝ) := by
      have hs_real : 0 < (s : ℝ) := NNReal.coe_pos.mpr hs
      have hdist := e.symm.isometry.dist_eq (0 : ℂ) (Complex.ofReal (s : ℝ))
      have hzero' : e.symm (0 : ℂ) = (0 : v.Completion) := by
        dsimp [e]
        exact (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.map_zero
      have hzt' : e.symm (Complex.ofReal (s : ℝ)) = z := by
        rfl
      rw [hzero', hzt'] at hdist
      simpa [dist_eq_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs_real] using hdist
    have hnormu : (chapter09NormUnit u) ^ v.mult = t := by
      apply Units.ext
      apply NNReal.eq
      change ‖(u : v.Completion)‖ ^ v.mult = (t : ℝ)
      change ‖z‖ ^ v.mult = (t : ℝ)
      rw [hnormz, hv.mult_eq_two]
      exact_mod_cast NNReal.sq_sqrt (t : ℝ≥0)
    let y : ∀ w : InfinitePlace K, w.Completionˣ := fun w =>
      dite (w = v) (fun h => h ▸ u) (fun _ => 1)
    let xinf : (Chapter09InfiniteAdele K)ˣ := (MulEquiv.piUnits).symm y
    let x : Chapter09Idele K :=
      (chapter09IdeleProductEquiv K).symm (xinf, 1)
    have hyv : y v = u := by simp [y]
    have hyoff : ∀ w : InfinitePlace K, w ≠ v → y w = 1 := by
      intro w hw
      simp [y, hw]
    refine ⟨x, ?_⟩
    change chapter09IdeleModule x = t
    rw [chapter09IdeleModule_eq_infinite_mul_finite]
    have hdecomp : chapter09IdeleProductEquiv K x = (xinf, 1) := by
      simp [x]
    rw [hdecomp]
    have hfin : chapter09FiniteIdeleModule (1 : (Chapter09FiniteAdele K)ˣ) = 1 := by
      unfold chapter09FiniteIdeleModule
      apply finprod_eq_one_of_forall_eq_one
      intro w
      exact (chapter09FiniteUnitIdeles_mem_iff.mp (Subgroup.one_mem _) w)
    rw [hfin, mul_one]
    unfold chapter09InfiniteIdeleModule
    have hpi : MulEquiv.piUnits xinf = y :=
      (MulEquiv.piUnits).apply_symm_apply y
    rw [hpi, Fintype.prod_eq_single v]
    · rw [hyv, hnormu]
    · intro w hw
      rw [hyoff w hw]
      simp [chapter09NormUnit]

theorem chapter09Degree_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter09DegreeHom K) := by
  intro y
  let r : ℝ := Multiplicative.toAdd y
  let a : ℝ≥0 := ⟨Real.exp (-r), (Real.exp_pos _).le⟩
  let t : Chapter09PositiveReal := Units.mk0 a (by
    dsimp [a]
    apply pos_iff_ne_zero.mp
    change 0 < Real.exp (-r)
    exact Real.exp_pos _)
  rcases chapter09IdeleModule_surjective K t with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply Multiplicative.ext
  change chapter09Degree x = r
  change chapter09IdeleModule x = t at hx
  rw [chapter09Degree_def, hx]
  change -Real.log (Real.exp (-r)) = r
  rw [Real.log_exp]
  ring

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
  let z : v.adicCompletion K :=
    Classical.choose
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
        K v (WithZero.exp (-1 : ℤ)))
  have hz : Valued.v z = WithZero.exp (-1 : ℤ) :=
    Classical.choose_spec
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
        K v (WithZero.exp (-1 : ℤ)))
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hz
    exact WithZero.exp_ne_zero hz.symm
  let u : (v.adicCompletion K)ˣ := Units.mk0 z hz0
  let localUnit : ∀ w : HeightOneSpectrum (𝓞 K), (w.adicCompletion K)ˣ :=
    fun w => dite (w = v) (fun h => h ▸ u) (fun _ => 1)
  have hunit : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      localUnit w ∈ (Submonoid.ofClass (w.adicCompletionIntegers K)).units := by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw
    have hw' : w ≠ v := by simpa using hw
    simp [localUnit, hw']
  let finite : (Chapter09FiniteAdele K)ˣ :=
    RestrictedProduct.mkUnit localUnit hunit
  let x : Chapter09Idele K :=
    (chapter09IdeleProductEquiv K).symm (1, finite)
  have hx : chapter09IdeleProductEquiv K x = (1, finite) := by
    simp [x]
  have hlocal : localUnit v = u := by
    simp [localUnit]
  have horder :
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v z = 1 := by
    unfold LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder
    rw [hz, dif_neg WithZero.exp_ne_zero,
      WithZero.toAdd_unzero_eq_log, WithZero.log_exp]
    ring
  refine ⟨{
    idele := x
    infinite_components_one := ?_
    finite_component_at := ?_
    finite_components_off := ?_ }⟩
  · intro w
    rw [hx]
    have hpi : MulEquiv.piUnits (1 : (Chapter09InfiniteAdele K)ˣ) = 1 :=
      (MulEquiv.piUnits).map_one
    rw [hpi]
    rfl
  · rw [hx]
    have hcomp :
        (↑((RestrictedProduct.unitsEquiv
          (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) finite) v) :
          v.adicCompletion K) = z := by
      rw [RestrictedProduct.unitsEquiv_apply]
      change (localUnit v : v.adicCompletion K) = z
      rw [hlocal]
      rfl
    change (Ideal.absNorm v.asIdeal : ℝ≥0) ^
      (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
        ((RestrictedProduct.unitsEquiv
          (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) finite) v)) =
      (Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹
    rw [hcomp, horder]
    simp
  · intro w hw
    rw [hx]
    apply Units.ext
    have hcomp :
        (↑((RestrictedProduct.unitsEquiv
          (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) finite) w) :
          w.adicCompletion K) = 1 := by
      rw [RestrictedProduct.unitsEquiv_apply]
      change (localUnit w : w.adicCompletion K) = 1
      simp [localUnit, hw]
    exact hcomp

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
  intro y
  rcases chapter09Degree_surjective K y with ⟨x, hx⟩
  refine ⟨QuotientGroup.mk x, ?_⟩
  rw [chapter09IdeleClassDegree_apply]
  exact hx

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
  intro t
  rcases chapter09IdeleModule_surjective K t with ⟨x, hx⟩
  refine ⟨QuotientGroup.mk x, ?_⟩
  rw [chapter09IdeleClassModule_apply]
  exact hx

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
  let a : Kˣ := -1
  refine ⟨chapter09PrincipalIdele K a,
    chapter09_principal_idele_in_normOne a, ?_⟩
  intro hx
  change (chapter09PrincipalIdele K a) ∈
    Subgroup.map (chapter09FiniteUnitIdeleEmbedding K)
      (chapter09FiniteUnitIdeles K) at hx
  have hx' : (chapter09PrincipalIdele K a) ∈
      (↑(Subgroup.map (chapter09FiniteUnitIdeleEmbedding K)
        (chapter09FiniteUnitIdeles K)) : Set (Chapter09Idele K)) := hx
  rw [Subgroup.coe_map] at hx'
  rcases hx' with ⟨u, hu, hux⟩
  have hfirst := congrArg (fun y : Chapter09Idele K =>
      (chapter09IdeleProductEquiv K y).1) hux
  have hprincipal :
      (chapter09IdeleProductEquiv K (chapter09PrincipalIdele K a)).1 =
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele a := by
    rfl
  have hbad :
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele a ≠
        (1 : (Chapter09InfiniteAdele K)ˣ) := by
    intro h
    have hval := congrArg Units.val h
    change algebraMap K (Chapter09InfiniteAdele K) (a : K) = 1 at hval
    simp [a] at hval
    let w : InfinitePlace K :=
      Classical.choice (inferInstance : Nonempty (InfinitePlace K))
    have hval' := congrArg (fun z : Chapter09InfiniteAdele K => z w) hval
    change -(1 : w.Completion) = 1 at hval'
    rcases w.isReal_or_isComplex with hw | hw
    · let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
      have hval'' := congrArg e hval'
      have hreal : (-1 : ℝ) = 1 := by simpa [e] using hval''
      norm_num at hreal
    · let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      have hval'' := congrArg e hval'
      have hcomplex : (-1 : ℂ) = 1 := by simpa [e] using hval''
      norm_num at hcomplex
  apply hbad
  rw [← hprincipal]
  simpa [chapter09FiniteUnitIdeleEmbedding] using hfirst.symm

/- The number-field degree in this chapter is real-valued and uses the
archimedean magnitude.  In the separate function-field theory with constant
field `𝔽_q`, the normalization is `-log_q |x|_A : ℤ`; that complete-curve
product formula is intentionally not identified with this number-field map.
The surjectivity statement above is the formal number-field assertion. -/

end

end LastLib.Book04AdelesAndIdeles.Chapter09
