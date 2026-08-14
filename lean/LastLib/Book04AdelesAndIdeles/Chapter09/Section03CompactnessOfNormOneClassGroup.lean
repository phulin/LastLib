import LastLib.Book04AdelesAndIdeles.Chapter09.Section02DirichletUnitLattice
import LastLib.Book04AdelesAndIdeles.Chapter01.Section02NumberFieldsAndIntegers

namespace LastLib.Book04AdelesAndIdeles.Chapter09

noncomputable section

open NumberField IsDedekindDomain
open Topology
open scoped RestrictedProduct WithZero

/-!
## 9.3. Compactness of the norm-one class group
-/

abbrev Chapter09ArchimedeanUnitQuotient
    (K : Type*) [Field K] [NumberField K] :=
  (chapter09KInfinityOne K) ⧸ (chapter09ArchimedeanUnitEmbedding K).range

theorem chapter09_finite_unit_ideles_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (chapter09FiniteUnitIdeles K)) := by
  classical
  let R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K
  let A := fun v : HeightOneSpectrum (𝓞 K) =>
    (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  have hA : ∀ v : HeightOneSpectrum (𝓞 K), IsCompact (A v) := by
    intro v
    have hsub : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
      have hsubtype : IsCompact (Set.univ : Set (v.adicCompletionIntegers K)) :=
        isCompact_univ_iff.mpr
          (LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_completion_integers_compact
            (K := K) v)
      have hcompact_image :=
        (Subtype.isCompact_iff (s := (Set.univ : Set (v.adicCompletionIntegers K)))).mp
          hsubtype
      have hset :
          (Subtype.val '' (Set.univ : Set (v.adicCompletionIntegers K))) =
            (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
        ext x
        constructor
        · rintro ⟨y, -, rfl⟩
          exact y.property
        · intro hx
          exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
      rw [hset] at hcompact_image
      exact hcompact_image
    simpa [A, R] using hsub
  let P := Πʳ v : HeightOneSpectrum (𝓞 K), [R v, A v]_[⊤]
  have hP : IsCompact (Set.univ : Set P) := by
    let htop := RestrictedProduct.homeoTop (R := R) (A := A)
    have hAsub : ∀ v : HeightOneSpectrum (𝓞 K),
        IsCompact (Set.univ : Set (A v)) := by
      intro v
      rw [Subtype.isCompact_iff]
      simpa using hA v
    have hprod : IsCompact (Set.univ : Set (∀ v : HeightOneSpectrum (𝓞 K), A v)) := by
      simpa using (isCompact_univ_pi (fun v => hAsub v))
    simpa [P] using hprod.image htop.continuous
  let inc : P → Chapter09FiniteAdele K :=
    RestrictedProduct.inclusion R A (le_top : Filter.cofinite ≤ (⊤ : Filter _))
  let integral : Set (Chapter09FiniteAdele K) :=
    {x | ∀ v : HeightOneSpectrum (𝓞 K), x v ∈ v.adicCompletionIntegers K}
  have hinc : Continuous inc := by
    exact RestrictedProduct.continuous_inclusion (R := R) (A := A)
      (le_top : Filter.cofinite ≤ (⊤ : Filter _))
  have hinc_range : inc '' (Set.univ : Set P) = integral := by
    calc
      inc '' (Set.univ : Set P) = Set.range inc := Set.image_univ
      _ = {x : Chapter09FiniteAdele K |
          ∀ᶠ v : HeightOneSpectrum (𝓞 K) in (⊤ : Filter _), x v ∈ A v} := by
        change Set.range (RestrictedProduct.inclusion R A
          (le_top : Filter.cofinite ≤ (⊤ : Filter _))) = _
        exact RestrictedProduct.range_inclusion R A
          (le_top : Filter.cofinite ≤ (⊤ : Filter _))
      _ = integral := by
        ext x
        simp [integral, A]
  have hintegral : IsCompact integral := by
    rw [← hinc_range]
    exact hP.image hinc
  have hintegral_inv : IsCompact (MulOpposite.op '' integral) :=
    hintegral.image MulOpposite.continuous_op
  have hprod : IsCompact (integral ×ˢ (MulOpposite.op '' integral)) :=
    hintegral.prod hintegral_inv
  let hT1 : T1Space (Chapter09FiniteAdele K) := by
    change T1Space (Πʳ v : HeightOneSpectrum (𝓞 K),
      [v.adicCompletion K, v.adicCompletionIntegers K])
    infer_instance
  have hembed : IsCompact
      ((Units.embedProduct (Chapter09FiniteAdele K)) ⁻¹'
        (integral ×ˢ (MulOpposite.op '' integral))) :=
    (@Units.isClosedEmbedding_embedProduct (Chapter09FiniteAdele K)
      _ _ hT1 _).isCompact_preimage hprod
  have heq : (Units.embedProduct (Chapter09FiniteAdele K)) ⁻¹'
        (integral ×ˢ (MulOpposite.op '' integral)) =
      (chapter09FiniteUnitIdeles K : Set ((Chapter09FiniteAdele K)ˣ)) := by
    ext x
    constructor
    · intro hx
      apply (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_integral_unit_iff_local_valued_eq_one
        x).2
      intro v
      have hxmem : (x : Chapter09FiniteAdele K) v ∈ v.adicCompletionIntegers K := hx.1 v
      have hxinv : ((x⁻¹ : (Chapter09FiniteAdele K)ˣ) : Chapter09FiniteAdele K) v ∈
          v.adicCompletionIntegers K := by
        rcases hx.2 with ⟨z, hz, hzx⟩
        have hzx' : MulOpposite.op z =
            MulOpposite.op ((x⁻¹ : (Chapter09FiniteAdele K)ˣ) : Chapter09FiniteAdele K) := by
          simpa [Units.embedProduct_apply] using hzx
        have hz' : ((x⁻¹ : (Chapter09FiniteAdele K)ˣ) : Chapter09FiniteAdele K) = z :=
          MulOpposite.op_injective hzx'.symm
        rw [hz']
        exact hz v
      have hxle : Valued.v ((x : Chapter09FiniteAdele K) v) ≤ 1 := by
        exact hxmem
      have hxinvle : Valued.v
          (((x⁻¹ : (Chapter09FiniteAdele K)ˣ) : Chapter09FiniteAdele K) v) ≤ 1 := by
        exact hxinv
      have hx0 : (x : Chapter09FiniteAdele K) v ≠ 0 := by
        exact LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_component_ne_zero x v
      have hxinvle' : Valued.v (((x : Chapter09FiniteAdele K) v)⁻¹) ≤ 1 := by
        have hinv : ((x⁻¹ : (Chapter09FiniteAdele K)ˣ) : Chapter09FiniteAdele K) v =
            ((x : Chapter09FiniteAdele K) v)⁻¹ := by
          have hfun := congrArg (fun f : Chapter09FiniteAdele K => f v) x.inv_val
          change ((x⁻¹ : (Chapter09FiniteAdele K)ˣ) : Chapter09FiniteAdele K) v *
              ((x : Chapter09FiniteAdele K) v) = 1 at hfun
          exact eq_inv_of_mul_eq_one_left hfun
        rw [hinv] at hxinvle
        exact hxinvle
      have hxge : (1 : ℤᵐ⁰) ≤ Valued.v ((x : Chapter09FiniteAdele K) v) := by
        simpa [inv_le_one_iff₀, hx0] using hxinvle'
      exact le_antisymm hxle hxge
    · intro hx
      have hval : ∀ v : HeightOneSpectrum (𝓞 K),
          Valued.v ((x : Chapter09FiniteAdele K) v) = 1 :=
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_integral_unit_iff_local_valued_eq_one
          x).1 hx
      refine ⟨?_, ?_⟩
      · intro v
        change Valued.v ((x : Chapter09FiniteAdele K) v) ≤ 1
        simp [hval v]
      · refine ⟨((x⁻¹ : (Chapter09FiniteAdele K)ˣ) : Chapter09FiniteAdele K), ?_, rfl⟩
        intro v
        change Valued.v
          (((x⁻¹ : (Chapter09FiniteAdele K)ˣ) : Chapter09FiniteAdele K) v) ≤ 1
        have hinv : ((x⁻¹ : (Chapter09FiniteAdele K)ˣ) : Chapter09FiniteAdele K) v =
            ((x : Chapter09FiniteAdele K) v)⁻¹ := by
          have hfun := congrArg (fun f : Chapter09FiniteAdele K => f v) x.inv_val
          change ((x⁻¹ : (Chapter09FiniteAdele K)ˣ) : Chapter09FiniteAdele K) v *
              ((x : Chapter09FiniteAdele K) v) = 1 at hfun
          exact eq_inv_of_mul_eq_one_left hfun
        rw [hinv]
        simp [hval v]
  rw [heq] at hembed
  rw [Subtype.isCompact_iff]
  have hset :
      (Subtype.val '' (Set.univ : Set (chapter09FiniteUnitIdeles K))) =
        (chapter09FiniteUnitIdeles K : Set ((Chapter09FiniteAdele K)ˣ)) := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  rw [hset]
  exact hembed

theorem chapter09_infinite_idele_module_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter09InfiniteIdeleModuleHom K) := by
  classical
  let v : InfinitePlace K :=
    Classical.choice (inferInstance : Nonempty (InfinitePlace K))
  intro t
  rcases v.isReal_or_isComplex with hv | hv
  · let r := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv
    let e := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv
    let hlocal : Chapter09PositiveReal → v.Completionˣ := fun t =>
      Units.mk0 (e.symm (t : ℝ)) (by
        intro hz
        change r.symm (t : ℝ) = 0 at hz
        have ht : (t : ℝ) = 0 := by
          simpa using congrArg r hz
        exact (ne_of_gt (NNReal.coe_pos.mpr
          (pos_iff_ne_zero.mpr (Units.ne_zero t)))) ht)
    have hlocal_norm (t : Chapter09PositiveReal) :
        chapter09NormUnit (hlocal t) ^ v.mult = t := by
      apply Units.ext
      apply NNReal.eq
      change ‖(hlocal t : v.Completion)‖ ^ v.mult = (t : ℝ)
      change ‖e.symm (t : ℝ)‖ ^ v.mult = (t : ℝ)
      have ht : 0 < (t : ℝ) :=
        NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero t))
      have hdist := e.symm.isometry.dist_eq (0 : ℝ) (t : ℝ)
      have hzero : e.symm (0 : ℝ) = (0 : v.Completion) := by
        dsimp [e]
        exact r.symm.map_zero
      rw [hzero] at hdist
      rw [hv.mult_eq_one]
      simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_pos ht] using hdist
    let hinf : (Chapter09InfiniteAdele K)ˣ :=
      (MulEquiv.piUnits (M := fun w : InfinitePlace K => w.Completion)).symm
        (Pi.mulSingle v (hlocal t))
    refine ⟨hinf, ?_⟩
    change chapter09InfiniteIdeleModule hinf = t
    unfold chapter09InfiniteIdeleModule
    have hpi : MulEquiv.piUnits hinf = Pi.mulSingle v (hlocal t) := by
      change MulEquiv.piUnits
          ((MulEquiv.piUnits).symm (Pi.mulSingle v (hlocal t))) =
        Pi.mulSingle v (hlocal t)
      exact (MulEquiv.piUnits).apply_symm_apply _
    rw [hpi, Fintype.prod_eq_single v]
    · rw [Pi.mulSingle_eq_same, hlocal_norm]
    · intro w hw
      have hoff : Pi.mulSingle (M := fun w : InfinitePlace K => w.Completionˣ)
          v (hlocal t) w = 1 := Pi.mulSingle_eq_of_ne
            (M := fun w : InfinitePlace K => w.Completionˣ) hw (hlocal t)
      rw [hoff]
      simp [chapter09NormUnit]
  · let r := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
    let e := NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv
    let hlocal : Chapter09PositiveReal → v.Completionˣ := fun t =>
      Units.mk0 (e.symm (Complex.ofReal (Real.sqrt (t : ℝ)))) (by
        intro hz
        change r.symm (Complex.ofReal (Real.sqrt (t : ℝ))) = 0 at hz
        have hz' : Complex.ofReal (Real.sqrt (t : ℝ)) = 0 := by
          simpa using congrArg r hz
        have ht : 0 < (t : ℝ) :=
          NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero t))
        exact (ne_of_gt (Real.sqrt_pos.2 ht)) (by
          simpa using congrArg Complex.re hz'))
    have hlocal_norm (t : Chapter09PositiveReal) :
        chapter09NormUnit (hlocal t) ^ v.mult = t := by
      apply Units.ext
      apply NNReal.eq
      change ‖(hlocal t : v.Completion)‖ ^ v.mult = (t : ℝ)
      change ‖e.symm (Complex.ofReal (Real.sqrt (t : ℝ)))‖ ^ v.mult = (t : ℝ)
      have ht : 0 < (t : ℝ) :=
        NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero t))
      have hdist := e.symm.isometry.dist_eq (0 : ℂ)
        (Complex.ofReal (Real.sqrt (t : ℝ)))
      have hzero : e.symm (0 : ℂ) = (0 : v.Completion) := by
        dsimp [e]
        exact r.symm.map_zero
      rw [hzero] at hdist
      rw [hv.mult_eq_two]
      have hs : 0 ≤ Real.sqrt (t : ℝ) := Real.sqrt_nonneg _
      have hnorm : ‖e.symm (Complex.ofReal (Real.sqrt (t : ℝ)))‖ =
          Real.sqrt (t : ℝ) := by
        simpa [dist_eq_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hs] using hdist
      rw [hnorm]
      exact Real.sq_sqrt (NNReal.coe_nonneg t)
    let hinf : (Chapter09InfiniteAdele K)ˣ :=
      (MulEquiv.piUnits (M := fun w : InfinitePlace K => w.Completion)).symm
        (Pi.mulSingle v (hlocal t))
    refine ⟨hinf, ?_⟩
    change chapter09InfiniteIdeleModule hinf = t
    unfold chapter09InfiniteIdeleModule
    have hpi : MulEquiv.piUnits hinf = Pi.mulSingle v (hlocal t) := by
      change MulEquiv.piUnits
          ((MulEquiv.piUnits).symm (Pi.mulSingle v (hlocal t))) =
        Pi.mulSingle v (hlocal t)
      exact (MulEquiv.piUnits).apply_symm_apply _
    rw [hpi, Fintype.prod_eq_single v]
    · rw [Pi.mulSingle_eq_same, hlocal_norm]
    · intro w hw
      have hoff : Pi.mulSingle (M := fun w : InfinitePlace K => w.Completionˣ)
          v (hlocal t) w = 1 := Pi.mulSingle_eq_of_ne
            (M := fun w : InfinitePlace K => w.Completionˣ) hw (hlocal t)
      rw [hoff]
      simp [chapter09NormUnit]

private theorem chapter09_archimedean_log_section
    (K : Type*) [Field K] [NumberField K] :
    ∃ s : chapter09LogHyperplane K → chapter09KInfinityOne K,
      Continuous s ∧
        ∀ t, chapter09InfiniteLogVector (s t).1 = t.1 := by
  classical
  let hlocal : ∀ v : InfinitePlace K, chapter09LogHyperplane K → v.Completionˣ :=
    fun v t =>
      if hv : NumberField.InfinitePlace.IsReal v then
        let r := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv
        let e := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv
        Units.mk0 (e.symm (Real.exp (t.1 v))) (by
          intro hz
          change r.symm (Real.exp (t.1 v)) = 0 at hz
          have hz' : Real.exp (t.1 v) = 0 := by
            simpa using congrArg r hz
          exact (ne_of_gt (Real.exp_pos _)) hz')
      else
        let hv : NumberField.InfinitePlace.IsComplex v :=
          (v.isReal_or_isComplex).resolve_left hv
        let r := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
        let e := NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv
        Units.mk0
          (e.symm (Complex.ofReal (Real.sqrt (Real.exp (t.1 v))))) (by
            intro hz
            change r.symm
              (Complex.ofReal (Real.sqrt (Real.exp (t.1 v)))) = 0 at hz
            have hz' : Complex.ofReal (Real.sqrt (Real.exp (t.1 v))) = 0 := by
              simpa using congrArg r hz
            exact (ne_of_gt (Real.sqrt_pos.2 (Real.exp_pos _))) (by
              simpa using congrArg Complex.re hz'))
  have hlocal_cont : ∀ v : InfinitePlace K,
      Continuous (hlocal v) := by
    intro v
    rcases v.isReal_or_isComplex with hv | hv
    · let r := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv
      let e := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv
      have ht : Continuous (fun t : chapter09LogHyperplane K => t.1 v) :=
        (continuous_apply v).comp continuous_subtype_val
      have hcoe : Continuous (fun t : chapter09LogHyperplane K =>
          e.symm (Real.exp (t.1 v))) :=
        e.symm.continuous.comp (Real.continuous_exp.comp ht)
      have hzero : e.symm (0 : ℝ) = (0 : v.Completion) := by
        dsimp [e]
        exact r.symm.map_zero
      have hne : ∀ t : chapter09LogHyperplane K,
          e.symm (Real.exp (t.1 v)) ≠ 0 := by
        intro t hz
        have hz' : e.symm (Real.exp (t.1 v)) = e.symm (0 : ℝ) := by
          rw [hzero]
          exact hz
        have hz'' := e.symm.injective hz'
        exact (ne_of_gt (Real.exp_pos _)) hz''
      have hcoe_inv : Continuous (fun t : chapter09LogHyperplane K =>
          (e.symm (Real.exp (t.1 v)))⁻¹) := hcoe.inv₀ hne
      apply Units.continuous_iff.mpr
      constructor
      · simpa only [Function.comp_def, hlocal, dif_pos hv, Units.val_mk0] using hcoe
      · simpa only [Function.comp_def, hlocal, dif_pos hv,
          Units.val_inv_eq_inv_val, Units.val_mk0] using hcoe_inv
    · let r := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
      let e := NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv
      have hnot : ¬NumberField.InfinitePlace.IsReal v :=
        NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hv
      have ht : Continuous (fun t : chapter09LogHyperplane K => t.1 v) :=
        (continuous_apply v).comp continuous_subtype_val
      have hcoe : Continuous (fun t : chapter09LogHyperplane K =>
          e.symm (Complex.ofReal (Real.sqrt (Real.exp (t.1 v))))) :=
        e.symm.continuous.comp
          (Complex.continuous_ofReal.comp
            (Real.continuous_sqrt.comp (Real.continuous_exp.comp ht)))
      have hzero : e.symm (0 : ℂ) = (0 : v.Completion) := by
        dsimp [e]
        exact r.symm.map_zero
      have hne : ∀ t : chapter09LogHyperplane K,
          e.symm (Complex.ofReal (Real.sqrt (Real.exp (t.1 v)))) ≠ 0 := by
        intro t hz
        have hz' : e.symm (Complex.ofReal (Real.sqrt (Real.exp (t.1 v)))) =
            e.symm (0 : ℂ) := by
          rw [hzero]
          exact hz
        have hz'' := e.symm.injective hz'
        exact (ne_of_gt (Real.sqrt_pos.2 (Real.exp_pos _))) (by
          simpa using congrArg Complex.re hz'')
      have hcoe_inv : Continuous (fun t : chapter09LogHyperplane K =>
          (e.symm (Complex.ofReal (Real.sqrt (Real.exp (t.1 v)))))⁻¹) := by
        exact hcoe.inv₀ hne
      apply Units.continuous_iff.mpr
      constructor
      · simpa only [Function.comp_def, hlocal, dif_neg hnot, Units.val_mk0] using hcoe
      · simpa only [Function.comp_def, hlocal, dif_neg hnot,
          Units.val_inv_eq_inv_val, Units.val_mk0] using hcoe_inv
  have hlocal_norm : ∀ (v : InfinitePlace K) (t : chapter09LogHyperplane K),
      (((chapter09NormUnit (hlocal v t) ^ v.mult : Chapter09PositiveReal) :
        NNReal) : ℝ) = Real.exp (t.1 v) := by
    intro v t
    rcases v.isReal_or_isComplex with hv | hv
    · let r := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv
      let e := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv
      simp only [hlocal, dif_pos hv]
      change ‖e.symm (Real.exp (t.1 v))‖ ^ v.mult = Real.exp (t.1 v)
      have ht : 0 < Real.exp (t.1 v) := Real.exp_pos _
      have hdist := e.symm.isometry.dist_eq (0 : ℝ) (Real.exp (t.1 v))
      have hzero : e.symm (0 : ℝ) = (0 : v.Completion) := by
        dsimp [e]
        exact r.symm.map_zero
      rw [hzero] at hdist
      rw [hv.mult_eq_one]
      simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_pos ht] using hdist
    · let r := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
      let e := NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv
      have hnot : ¬NumberField.InfinitePlace.IsReal v :=
        NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hv
      simp only [hlocal, dif_neg hnot]
      change ‖e.symm
          (Complex.ofReal (Real.sqrt (Real.exp (t.1 v))))‖ ^ v.mult =
        Real.exp (t.1 v)
      have hdist := e.symm.isometry.dist_eq (0 : ℂ)
        (Complex.ofReal (Real.sqrt (Real.exp (t.1 v))))
      have hzero : e.symm (0 : ℂ) = (0 : v.Completion) := by
        dsimp [e]
        exact r.symm.map_zero
      rw [hzero] at hdist
      rw [hv.mult_eq_two]
      have hs : 0 ≤ Real.sqrt (Real.exp (t.1 v)) := Real.sqrt_nonneg _
      have hnorm : ‖e.symm
          (Complex.ofReal (Real.sqrt (Real.exp (t.1 v))))‖ =
          Real.sqrt (Real.exp (t.1 v)) := by
        simpa [dist_eq_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hs] using hdist
      rw [hnorm]
      exact Real.sq_sqrt (le_of_lt (Real.exp_pos _))
  let hcoord : chapter09LogHyperplane K →
      (∀ v : InfinitePlace K, v.Completionˣ) := fun t v => hlocal v t
  let hinf : chapter09LogHyperplane K → (Chapter09InfiniteAdele K)ˣ := fun t =>
    (MulEquiv.piUnits (M := fun v : InfinitePlace K => v.Completion)).symm
      (hcoord t)
  have hcoord_cont : Continuous hcoord := by
    exact continuous_pi fun v => hlocal_cont v
  have hinf_cont : Continuous hinf := by
    exact (ContinuousMulEquiv.piUnits
      (M := fun v : InfinitePlace K => v.Completion)).symm.continuous.comp hcoord_cont
  have hpi (t : chapter09LogHyperplane K) :
      MulEquiv.piUnits (hinf t) = hcoord t := by
    change MulEquiv.piUnits
        ((MulEquiv.piUnits).symm (hcoord t)) = hcoord t
    exact (MulEquiv.piUnits).apply_symm_apply _
  have hmodule (t : chapter09LogHyperplane K) :
      chapter09InfiniteIdeleModule (hinf t) = 1 := by
    apply Units.ext
    change (Units.coeHom NNReal)
      (∏ v : InfinitePlace K,
        chapter09NormUnit ((MulEquiv.piUnits (hinf t)) v) ^ v.mult) = 1
    rw [map_prod, hpi]
    apply NNReal.eq
    simp only [NNReal.coe_prod, NNReal.coe_one]
    calc
      (∏ v : InfinitePlace K,
          ‖(hcoord t v : v.Completion)‖ ^ v.mult) =
          ∏ v : InfinitePlace K, Real.exp (t.1 v) := by
        apply Finset.prod_congr rfl
        intro v hv
        exact hlocal_norm v t
      _ = Real.exp (∑ v : InfinitePlace K, t.1 v) := by
        rw [Real.exp_sum]
      _ = 1 := by
        rw [t.property]
        simp
  have hmem (t : chapter09LogHyperplane K) : hinf t ∈ chapter09KInfinityOne K := by
    change chapter09InfiniteIdeleModule (hinf t) = 1
    exact hmodule t
  let s : chapter09LogHyperplane K → chapter09KInfinityOne K := fun t =>
    ⟨hinf t, hmem t⟩
  refine ⟨s, hinf_cont.subtype_mk (fun t => hmem t), ?_⟩
  intro t
  funext v
  unfold chapter09InfiniteLogVector
  rw [hpi]
  rw [hlocal_norm]
  exact Real.log_exp _

theorem chapter09_archimedean_unit_quotient_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (Chapter09ArchimedeanUnitQuotient K)) := by
  classical
  obtain ⟨s, hs, hslog⟩ := chapter09_archimedean_log_section K
  obtain ⟨B, hB, hred⟩ := chapter09_unit_log_reduction K
  have hlog_sum : ∀ x : chapter09KInfinityOne K,
      ∑ v : InfinitePlace K, chapter09InfiniteLogVector x.1 v = 0 := by
    intro x
    unfold chapter09InfiniteLogVector
    have hmodule : chapter09InfiniteIdeleModule x.1 = 1 := by
      change chapter09InfiniteIdeleModuleHom K x.1 = 1
      exact x.property
    have hprod :
        (∏ v : InfinitePlace K,
          ((((chapter09NormUnit ((MulEquiv.piUnits x.1) v) ^ v.mult :
            Chapter09PositiveReal) : NNReal) : ℝ))) = 1 := by
      have h := congrArg (fun z : Chapter09PositiveReal =>
        ((z : NNReal) : ℝ)) hmodule
      simpa [chapter09InfiniteIdeleModule] using h
    rw [← Real.log_prod]
    · rw [hprod]
      simp
    · intro v hv
      exact_mod_cast Units.ne_zero
        (chapter09NormUnit ((MulEquiv.piUnits x.1) v) ^ v.mult)
  have hphase_mem : ∀ p : chapter09InfiniteLogKernel K,
      p.1 ∈ chapter09KInfinityOne K := by
    intro p
    have hlog : chapter09InfiniteLogVector p.1 = 0 := by
      have hp : chapter09InfiniteLogMap K p.1 = 1 :=
        (MonoidHom.mem_ker).1 p.2
      change Multiplicative.ofAdd (chapter09InfiniteLogVector p.1) = 1 at hp
      exact congrArg Multiplicative.toAdd hp
    have hfactor : ∀ v : InfinitePlace K,
        ((((chapter09NormUnit ((MulEquiv.piUnits p.1) v) ^ v.mult :
          Chapter09PositiveReal) : NNReal) : ℝ)) = 1 := by
      intro v
      have hv := congrFun hlog v
      change Real.log
        ((((chapter09NormUnit ((MulEquiv.piUnits p.1) v) ^ v.mult :
          Chapter09PositiveReal) : NNReal) : ℝ)) = 0 at hv
      have hpos : 0 <
          ((((chapter09NormUnit ((MulEquiv.piUnits p.1) v) ^ v.mult :
            Chapter09PositiveReal) : NNReal) : ℝ)) := by
        exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
      exact Real.eq_one_of_pos_of_log_eq_zero hpos hv
    change chapter09InfiniteIdeleModule p.1 = 1
    apply Units.ext
    change (Units.coeHom NNReal)
      (∏ v : InfinitePlace K,
        chapter09NormUnit ((MulEquiv.piUnits p.1) v) ^ v.mult) = 1
    rw [map_prod]
    apply NNReal.eq
    simp only [NNReal.coe_prod, NNReal.coe_one]
    calc
      (∏ v : InfinitePlace K,
          ‖((MulEquiv.piUnits p.1) v : v.Completion)‖ ^ v.mult) =
          ∏ v : InfinitePlace K,
            ((((chapter09NormUnit ((MulEquiv.piUnits p.1) v) ^ v.mult :
              Chapter09PositiveReal) : NNReal) : ℝ)) := by
        rfl
      _ = 1 := by
        apply Finset.prod_eq_one
        intro v hv
        exact hfactor v
  let F : chapter09InfiniteLogKernel K × chapter09LogHyperplane K →
      chapter09KInfinityOne K := fun z =>
    ⟨z.1.1 * (s z.2).1,
      (chapter09KInfinityOne K).mul_mem (hphase_mem z.1) (s z.2).property⟩
  have hF : Continuous F := by
    have hraw : Continuous (fun z :
        chapter09InfiniteLogKernel K × chapter09LogHyperplane K =>
        z.1.1 * (s z.2).1) := by
      exact (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp (hs.comp continuous_snd))
    exact hraw.subtype_mk (fun z =>
      (chapter09KInfinityOne K).mul_mem (hphase_mem z.1) (s z.2).property)
  have hprod : IsCompact
      ((Set.univ : Set (chapter09InfiniteLogKernel K)) ×ˢ B) :=
    (chapter09_infinite_log_kernel_compact K).prod hB
  let S : Set (chapter09KInfinityOne K) :=
    F '' ((Set.univ : Set (chapter09InfiniteLogKernel K)) ×ˢ B)
  have hS : IsCompact S := by
    exact hprod.image hF
  let q : chapter09KInfinityOne K → Chapter09ArchimedeanUnitQuotient K :=
    QuotientGroup.mk' (chapter09ArchimedeanUnitEmbedding K).range
  have hq : Continuous q := QuotientGroup.continuous_mk
  have hqimage : q '' S = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    rcases QuotientGroup.mk'_surjective
      (chapter09ArchimedeanUnitEmbedding K).range y with ⟨x, rfl⟩
    let t : chapter09LogHyperplane K :=
      ⟨chapter09InfiniteLogVector x.1, by
        exact hlog_sum x⟩
    obtain ⟨u, hu⟩ := hred t
    let b : chapter09LogHyperplane K :=
      t - chapter09GlobalUnitLogEmbedding K u
    let g : chapter09KInfinityOne K :=
      chapter09ArchimedeanUnitEmbedding K u.toMul
    let z : chapter09KInfinityOne K :=
      ⟨x.1 * g.1⁻¹ * (s b).1⁻¹,
        (chapter09KInfinityOne K).mul_mem
          ((chapter09KInfinityOne K).mul_mem x.property
            ((chapter09KInfinityOne K).inv_mem g.property))
          ((chapter09KInfinityOne K).inv_mem (s b).property)⟩
    have hlog_mul : ∀ a c : (Chapter09InfiniteAdele K)ˣ,
        chapter09InfiniteLogVector (a * c) =
          chapter09InfiniteLogVector a + chapter09InfiniteLogVector c := by
      intro a c
      have h := (chapter09InfiniteLogMap K).map_mul a c
      exact congrArg Multiplicative.toAdd h
    have hlog_inv : ∀ a : (Chapter09InfiniteAdele K)ˣ,
        chapter09InfiniteLogVector a⁻¹ =
          -chapter09InfiniteLogVector a := by
      intro a
      have h := (chapter09InfiniteLogMap K).map_inv a
      exact congrArg Multiplicative.toAdd h
    have hglog : chapter09InfiniteLogVector g.1 =
        chapter09GlobalUnitLogEmbedding K u := by
      rfl
    have hzlog : chapter09InfiniteLogVector z.1 = 0 := by
      rw [hlog_mul, hlog_mul, hlog_inv, hlog_inv, hslog]
      rw [hglog]
      funext v
      simp [b, t]
      abel
    have hz : z.1 ∈ chapter09InfiniteLogKernel K := by
      apply (MonoidHom.mem_ker).2
      change Multiplicative.ofAdd (chapter09InfiniteLogVector z.1) = 1
      rw [hzlog]
      rfl
    let p : chapter09InfiniteLogKernel K := ⟨z.1, hz⟩
    have hzmem : F (p, b) ∈ S := by
      exact ⟨(p, b), ⟨Set.mem_univ _, hu⟩, rfl⟩
    refine ⟨F (p, b), hzmem, ?_⟩
    apply (QuotientGroup.eq_iff_div_mem).2
    refine ⟨u.toMul⁻¹, ?_⟩
    apply Subtype.ext
    change (g.1)⁻¹ = (p.1 * (s b).1) / x.1
    simp [p, z]
  rw [← hqimage]
  exact hS.image hq

theorem chapter09_archimedean_unit_compact_representatives
    (K : Type*) [Field K] [NumberField K] :
    ∃ S : Set (chapter09KInfinityOne K), IsCompact S ∧
      ∀ x : Chapter09ArchimedeanUnitQuotient K, ∃ s ∈ S,
        QuotientGroup.mk' (chapter09ArchimedeanUnitEmbedding K).range s = x := by
  classical
  obtain ⟨s, hs, hslog⟩ := chapter09_archimedean_log_section K
  obtain ⟨B, hB, hred⟩ := chapter09_unit_log_reduction K
  have hlog_sum : ∀ x : chapter09KInfinityOne K,
      ∑ v : InfinitePlace K, chapter09InfiniteLogVector x.1 v = 0 := by
    intro x
    unfold chapter09InfiniteLogVector
    have hmodule : chapter09InfiniteIdeleModule x.1 = 1 := by
      change chapter09InfiniteIdeleModuleHom K x.1 = 1
      exact x.property
    have hprod :
        (∏ v : InfinitePlace K,
          ((((chapter09NormUnit ((MulEquiv.piUnits x.1) v) ^ v.mult :
            Chapter09PositiveReal) : NNReal) : ℝ))) = 1 := by
      have h := congrArg (fun z : Chapter09PositiveReal =>
        ((z : NNReal) : ℝ)) hmodule
      simpa [chapter09InfiniteIdeleModule] using h
    rw [← Real.log_prod]
    · rw [hprod]
      simp
    · intro v hv
      exact_mod_cast Units.ne_zero
        (chapter09NormUnit ((MulEquiv.piUnits x.1) v) ^ v.mult)
  have hphase_mem : ∀ p : chapter09InfiniteLogKernel K,
      p.1 ∈ chapter09KInfinityOne K := by
    intro p
    have hlog : chapter09InfiniteLogVector p.1 = 0 := by
      have hp : chapter09InfiniteLogMap K p.1 = 1 :=
        (MonoidHom.mem_ker).1 p.2
      change Multiplicative.ofAdd (chapter09InfiniteLogVector p.1) = 1 at hp
      exact congrArg Multiplicative.toAdd hp
    have hfactor : ∀ v : InfinitePlace K,
        ((((chapter09NormUnit ((MulEquiv.piUnits p.1) v) ^ v.mult :
          Chapter09PositiveReal) : NNReal) : ℝ)) = 1 := by
      intro v
      have hv := congrFun hlog v
      change Real.log
        ((((chapter09NormUnit ((MulEquiv.piUnits p.1) v) ^ v.mult :
          Chapter09PositiveReal) : NNReal) : ℝ)) = 0 at hv
      have hpos : 0 <
          ((((chapter09NormUnit ((MulEquiv.piUnits p.1) v) ^ v.mult :
            Chapter09PositiveReal) : NNReal) : ℝ)) := by
        exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
      exact Real.eq_one_of_pos_of_log_eq_zero hpos hv
    change chapter09InfiniteIdeleModule p.1 = 1
    apply Units.ext
    change (Units.coeHom NNReal)
      (∏ v : InfinitePlace K,
        chapter09NormUnit ((MulEquiv.piUnits p.1) v) ^ v.mult) = 1
    rw [map_prod]
    apply NNReal.eq
    simp only [NNReal.coe_prod, NNReal.coe_one]
    calc
      (∏ v : InfinitePlace K,
          ‖((MulEquiv.piUnits p.1) v : v.Completion)‖ ^ v.mult) =
          ∏ v : InfinitePlace K,
            ((((chapter09NormUnit ((MulEquiv.piUnits p.1) v) ^ v.mult :
              Chapter09PositiveReal) : NNReal) : ℝ)) := by
        rfl
      _ = 1 := by
        apply Finset.prod_eq_one
        intro v hv
        exact hfactor v
  let F : chapter09InfiniteLogKernel K × chapter09LogHyperplane K →
      chapter09KInfinityOne K := fun z =>
    ⟨z.1.1 * (s z.2).1,
      (chapter09KInfinityOne K).mul_mem (hphase_mem z.1) (s z.2).property⟩
  have hF : Continuous F := by
    have hraw : Continuous (fun z :
        chapter09InfiniteLogKernel K × chapter09LogHyperplane K =>
        z.1.1 * (s z.2).1) := by
      exact (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp (hs.comp continuous_snd))
    exact hraw.subtype_mk (fun z =>
      (chapter09KInfinityOne K).mul_mem (hphase_mem z.1) (s z.2).property)
  have hprod : IsCompact
      ((Set.univ : Set (chapter09InfiniteLogKernel K)) ×ˢ B) :=
    (chapter09_infinite_log_kernel_compact K).prod hB
  let S : Set (chapter09KInfinityOne K) :=
    F '' ((Set.univ : Set (chapter09InfiniteLogKernel K)) ×ˢ B)
  have hS : IsCompact S := by
    exact hprod.image hF
  let q : chapter09KInfinityOne K → Chapter09ArchimedeanUnitQuotient K :=
    QuotientGroup.mk' (chapter09ArchimedeanUnitEmbedding K).range
  have hq : Continuous q := QuotientGroup.continuous_mk
  have hqimage : q '' S = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    rcases QuotientGroup.mk'_surjective
      (chapter09ArchimedeanUnitEmbedding K).range y with ⟨x, rfl⟩
    let t : chapter09LogHyperplane K :=
      ⟨chapter09InfiniteLogVector x.1, by
        exact hlog_sum x⟩
    obtain ⟨u, hu⟩ := hred t
    let b : chapter09LogHyperplane K :=
      t - chapter09GlobalUnitLogEmbedding K u
    let g : chapter09KInfinityOne K :=
      chapter09ArchimedeanUnitEmbedding K u.toMul
    let z : chapter09KInfinityOne K :=
      ⟨x.1 * g.1⁻¹ * (s b).1⁻¹,
        (chapter09KInfinityOne K).mul_mem
          ((chapter09KInfinityOne K).mul_mem x.property
            ((chapter09KInfinityOne K).inv_mem g.property))
          ((chapter09KInfinityOne K).inv_mem (s b).property)⟩
    have hlog_mul : ∀ a c : (Chapter09InfiniteAdele K)ˣ,
        chapter09InfiniteLogVector (a * c) =
          chapter09InfiniteLogVector a + chapter09InfiniteLogVector c := by
      intro a c
      have h := (chapter09InfiniteLogMap K).map_mul a c
      exact congrArg Multiplicative.toAdd h
    have hlog_inv : ∀ a : (Chapter09InfiniteAdele K)ˣ,
        chapter09InfiniteLogVector a⁻¹ =
          -chapter09InfiniteLogVector a := by
      intro a
      have h := (chapter09InfiniteLogMap K).map_inv a
      exact congrArg Multiplicative.toAdd h
    have hglog : chapter09InfiniteLogVector g.1 =
        chapter09GlobalUnitLogEmbedding K u := by
      rfl
    have hzlog : chapter09InfiniteLogVector z.1 = 0 := by
      rw [hlog_mul, hlog_mul, hlog_inv, hlog_inv, hslog]
      rw [hglog]
      funext v
      simp [b, t]
      abel
    have hz : z.1 ∈ chapter09InfiniteLogKernel K := by
      apply (MonoidHom.mem_ker).2
      change Multiplicative.ofAdd (chapter09InfiniteLogVector z.1) = 1
      rw [hzlog]
      rfl
    let p : chapter09InfiniteLogKernel K := ⟨z.1, hz⟩
    have hzmem : F (p, b) ∈ S := by
      exact ⟨(p, b), ⟨Set.mem_univ _, hu⟩, rfl⟩
    refine ⟨F (p, b), hzmem, ?_⟩
    apply (QuotientGroup.eq_iff_div_mem).2
    refine ⟨u.toMul⁻¹, ?_⟩
    apply Subtype.ext
    change (g.1)⁻¹ = (p.1 * (s b).1) / x.1
    simp [p, z]
  refine ⟨S, hS, ?_⟩
  intro y
  have hy : y ∈ q '' S := by
    rw [hqimage]
    trivial
  rcases hy with ⟨z, hz, rfl⟩
  exact ⟨z, hz, rfl⟩

/- The finite class group contributes only finitely many choices of a finite
idele representative.  The following interface is the precise reduction
statement used in the compactness proof; it contains no compactness claim. -/
structure Chapter09FiniteClassRepresentativeData
    (K : Type*) [Field K] [NumberField K] where
  representatives : Fin (Fintype.card (ClassGroup (𝓞 K))) → (Chapter09FiniteAdele K)ˣ
  represents_every_class :
    ∀ c : ClassGroup (𝓞 K), ∃ i,
      (chapter09CanonicalIdeleIdealData K).idealClassMap (representatives i) = c

theorem chapter09_finite_class_representatives_exist
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (Chapter09FiniteClassRepresentativeData K) := by
  classical
  let e : ClassGroup (𝓞 K) ≃ Fin (Fintype.card (ClassGroup (𝓞 K))) :=
    Fintype.equivFin (ClassGroup (𝓞 K))
  refine ⟨{
    representatives := fun i =>
      Classical.choose ((chapter09CanonicalIdeleIdealData K).surjective (e.symm i))
    represents_every_class := ?_ }⟩
  intro c
  refine ⟨e c, ?_⟩
  simpa using Classical.choose_spec
    ((chapter09CanonicalIdeleIdealData K).surjective (e.symm (e c)))

private theorem chapter09_global_unit_of_finite_principal_mem
    (K : Type*) [Field K] [NumberField K] (a : Kˣ)
    (ha : chapter09FinitePrincipalIdele K a ∈ chapter09FiniteUnitIdeles K) :
    ∃ u : (𝓞 K)ˣ,
      a = Units.map (algebraMap (𝓞 K) K).toMonoidHom u := by
  have hfinite : chapter09FinitePrincipalIdele K a =
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a := by
    apply Units.ext
    rfl
  have hideal :
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) = 1 := by
    have ha' : LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a ∈
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIntegralUnits := by
      have ha0 : chapter09FinitePrincipalIdele K a ∈
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIntegralUnits := by
        change chapter09FinitePrincipalIdele K a ∈ chapter09FiniteUnitIdeles K at ha
        exact ha
      rw [hfinite] at ha0
      exact ha0
    have hker : LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a ∈
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K).ker := by
      rw [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_kernel]
      exact ha'
    exact (MonoidHom.mem_ker).1 hker
  have hprincipal : toPrincipalIdeal (𝓞 K) K a = 1 := by
    rw [← LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_principal a]
    exact hideal
  have hspan : Submodule.span (𝓞 K) {(a : K)} = 1 := by
    have hcoe := congrArg (fun I :
        LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08IdealGroup K =>
        ((I : LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08FractionalIdeal K) :
          Submodule (𝓞 K) K)) hprincipal
    simpa [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton] using hcoe
  obtain ⟨u, hu⟩ := (Submodule.span_singleton_eq_one_iff).1 hspan
  refine ⟨u, ?_⟩
  apply Units.ext
  simpa using hu

private theorem chapter09_normOneClassGroup_equiv_classNormOne_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (chapter09NormOneClassGroup_equiv_classNormOne (K := K) :
      Chapter09NormOneClassGroup K → chapter09ClassNormOne K) := by
  classical
  let N := chapter09NormOneIdeles K
  let P := (chapter09NormOnePrincipalIdele K).range
  let P₀ := chapter09PrincipalIdeleSubgroup K
  let e := chapter09NormOneClassGroup_equiv_classNormOne (K := K)
  let g : Chapter09NormOneClassGroup K →* Chapter09IdeleClassGroup K :=
    (chapter09ClassNormOne K).subtype.comp e.toMonoidHom
  have hcomm :
      g.comp (QuotientGroup.mk' P) =
        (QuotientGroup.mk' P₀).comp N.subtype := by
    ext x
    rfl
  have hsat :
      (QuotientGroup.mk' P₀ : Chapter09Idele K → Chapter09IdeleClassGroup K) ⁻¹'
          (QuotientGroup.mk' P₀ '' Set.range N.subtype) ⊆ Set.range N.subtype := by
    intro x hx
    rcases hx with ⟨y, ⟨z, rfl⟩, hxy⟩
    have hp : x / (z : Chapter09Idele K) ∈ P₀ :=
      (QuotientGroup.eq_iff_div_mem).1 hxy.symm
    rcases hp with ⟨a, ha⟩
    have hfactor : x = chapter09PrincipalIdele K a * (z : Chapter09Idele K) := by
      have h := congrArg (fun w : Chapter09Idele K => w * (z : Chapter09Idele K)) ha
      simpa [div_eq_mul_inv, mul_assoc] using h.symm
    have hxnorm : x ∈ N := by
      change chapter09IdeleModuleHom K x = 1
      have hz : chapter09IdeleModule (z : Chapter09Idele K) = 1 := by
        change chapter09IdeleModuleHom K (z : Chapter09Idele K) = 1
        exact z.property
      have hpa : chapter09IdeleModuleHom K (chapter09PrincipalIdele K a) = 1 := by
        simpa only [chapter09IdeleModuleHom_apply] using
          chapter09PrincipalIdele_module_eq_one a
      have hz' : chapter09IdeleModuleHom K (z : Chapter09Idele K) = 1 := by
        simpa only [chapter09IdeleModuleHom_apply] using hz
      rw [hfactor, (chapter09IdeleModuleHom K).map_mul, hpa, hz']
      simp
    exact ⟨⟨x, hxnorm⟩, rfl⟩
  have hg_inj : Function.Injective g := by
    intro x y hxy
    apply e.injective
    exact Subtype.ext hxy
  have hcomm_fun :
      (g : Chapter09NormOneClassGroup K → Chapter09IdeleClassGroup K) ∘
          (QuotientGroup.mk : N → Chapter09NormOneClassGroup K) =
          (QuotientGroup.mk : Chapter09Idele K → Chapter09IdeleClassGroup K) ∘
          N.subtype := by
    ext x
    exact congrArg (fun h : N →* Chapter09IdeleClassGroup K => h x) hcomm
  have hgemb : IsEmbedding g :=
    isEmbedding_of_isOpenQuotientMap_of_isInducing
      (f := (N.subtype : N → Chapter09Idele K))
      (g := (g : Chapter09NormOneClassGroup K → Chapter09IdeleClassGroup K))
      (p := (QuotientGroup.mk : N → Chapter09NormOneClassGroup K))
      (q := (QuotientGroup.mk : Chapter09Idele K → Chapter09IdeleClassGroup K))
      hcomm_fun IsInducing.subtypeVal (QuotientGroup.isQuotientMap_mk P)
      (QuotientGroup.isOpenQuotientMap_mk (N := P₀)) hg_inj hsat
  have hemb : IsEmbedding (e : Chapter09NormOneClassGroup K →
      chapter09ClassNormOne K) := by
    exact (Topology.IsEmbedding.of_comp_iff (f := e)
      (g := (chapter09ClassNormOne K).subtype) IsEmbedding.subtypeVal).mp hgemb
  exact hemb.continuous

private theorem chapter09_normOne_compact_representatives
    (K : Type*) [Field K] [NumberField K] :
    ∃ S : Set (chapter09NormOneIdeles K), IsCompact S ∧
      ∀ x : chapter09ClassNormOne K, ∃ s ∈ S,
        chapter09NormOneClassGroup_equiv_classNormOne (K := K)
            (QuotientGroup.mk s) = x := by
  classical
  obtain ⟨Sarch, hSarch, harch⟩ :=
    chapter09_archimedean_unit_compact_representatives K
  obtain ⟨d⟩ := chapter09_finite_class_representatives_exist K
  let reps := d.representatives
  let corr : Fin (Fintype.card (ClassGroup (𝓞 K))) →
      (Chapter09InfiniteAdele K)ˣ := fun i =>
    Classical.choose (chapter09_infinite_idele_module_surjective K
      (chapter09FiniteIdeleModule (reps i))⁻¹)
  have hcorr (i : Fin (Fintype.card (ClassGroup (𝓞 K)))) :
      chapter09InfiniteIdeleModuleHom K (corr i) =
        (chapter09FiniteIdeleModule (reps i))⁻¹ := by
    exact Classical.choose_spec (chapter09_infinite_idele_module_surjective K
      (chapter09FiniteIdeleModule (reps i))⁻¹)
  have hunitmodule (u : chapter09FiniteUnitIdeles K) :
      chapter09FiniteIdeleModule (u : (Chapter09FiniteAdele K)ˣ) = 1 := by
    unfold chapter09FiniteIdeleModule
    apply finprod_eq_one_of_forall_eq_one
    intro v
    exact (chapter09FiniteUnitIdeles_mem_iff).1 u.property v
  have hfinite_embed (a : (Chapter09FiniteAdele K)ˣ) :
      chapter09IdeleModule (chapter09FiniteUnitIdeleEmbedding K a) =
        chapter09FiniteIdeleModule a := by
    have hdecomp : chapter09IdeleProductEquiv K
        (chapter09FiniteUnitIdeleEmbedding K a) = (1, a) := by
      simp [chapter09FiniteUnitIdeleEmbedding]
    rw [chapter09IdeleModule_eq_infinite_mul_finite, hdecomp]
    have hinf : chapter09InfiniteIdeleModule
        (1 : (Chapter09InfiniteAdele K)ˣ) = 1 := by
      change chapter09InfiniteIdeleModuleHom K 1 = 1
      simp
    rw [hinf]
    simp
  have hfinite_mul (a b : (Chapter09FiniteAdele K)ˣ) :
      chapter09FiniteIdeleModule (a * b) =
        chapter09FiniteIdeleModule a * chapter09FiniteIdeleModule b := by
    calc
      chapter09FiniteIdeleModule (a * b) =
          chapter09IdeleModule (chapter09FiniteUnitIdeleEmbedding K (a * b)) :=
        (hfinite_embed (a * b)).symm
      _ = chapter09IdeleModule
          (chapter09FiniteUnitIdeleEmbedding K a *
            chapter09FiniteUnitIdeleEmbedding K b) := by
        rw [(chapter09FiniteUnitIdeleEmbedding K).map_mul]
      _ = chapter09IdeleModule (chapter09FiniteUnitIdeleEmbedding K a) *
          chapter09IdeleModule (chapter09FiniteUnitIdeleEmbedding K b) :=
        (chapter09IdeleModuleHom K).map_mul _ _
      _ = chapter09FiniteIdeleModule a * chapter09FiniteIdeleModule b := by
        rw [hfinite_embed, hfinite_embed]
  let raw :
      Fin (Fintype.card (ClassGroup (𝓞 K))) ×
        (chapter09KInfinityOne K × chapter09FiniteUnitIdeles K) →
        Chapter09Idele K := fun z =>
    (chapter09IdeleProductEquiv K).symm
      (z.2.1.1 * corr z.1, reps z.1 * (z.2.2 : (Chapter09FiniteAdele K)ˣ))
  have hraw_decomp (z :
      Fin (Fintype.card (ClassGroup (𝓞 K))) ×
        (chapter09KInfinityOne K × chapter09FiniteUnitIdeles K)) :
      chapter09IdeleProductEquiv K (raw z) =
        (z.2.1.1 * corr z.1, reps z.1 * (z.2.2 : (Chapter09FiniteAdele K)ˣ)) := by
    exact (chapter09IdeleProductEquiv K).apply_symm_apply _
  have hraw_norm (z :
      Fin (Fintype.card (ClassGroup (𝓞 K))) ×
        (chapter09KInfinityOne K × chapter09FiniteUnitIdeles K)) :
      raw z ∈ chapter09NormOneIdeles K := by
    change chapter09IdeleModuleHom K (raw z) = 1
    change chapter09IdeleModule (raw z) = 1
    rw [chapter09IdeleModule_eq_infinite_mul_finite, hraw_decomp z]
    have hs : chapter09InfiniteIdeleModuleHom K z.2.1.1 = 1 := by
      exact z.2.1.property
    have hu : chapter09FiniteIdeleModule
        (z.2.2 : (Chapter09FiniteAdele K)ˣ) = 1 := hunitmodule z.2.2
    change chapter09InfiniteIdeleModuleHom K (z.2.1.1 * corr z.1) *
      chapter09FiniteIdeleModule
        (reps z.1 * (z.2.2 : (Chapter09FiniteAdele K)ˣ)) = 1
    rw [(chapter09InfiniteIdeleModuleHom K).map_mul, hfinite_mul, hs,
      hcorr z.1, hu]
    simp
  let G :
      Fin (Fintype.card (ClassGroup (𝓞 K))) ×
        (chapter09KInfinityOne K × chapter09FiniteUnitIdeles K) →
        chapter09NormOneIdeles K := fun z => ⟨raw z, hraw_norm z⟩
  have hcorr_cont : Continuous
      (fun i : Fin (Fintype.card (ClassGroup (𝓞 K))) => corr i) :=
    continuous_of_discreteTopology
  have hreps_cont : Continuous
      (fun i : Fin (Fintype.card (ClassGroup (𝓞 K))) => reps i) :=
    continuous_of_discreteTopology
  have hraw_cont : Continuous raw := by
    have hi : Continuous (fun z :
        Fin (Fintype.card (ClassGroup (𝓞 K))) ×
          (chapter09KInfinityOne K × chapter09FiniteUnitIdeles K) =>
        z.2.1.1) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
    have hc : Continuous (fun z :
        Fin (Fintype.card (ClassGroup (𝓞 K))) ×
          (chapter09KInfinityOne K × chapter09FiniteUnitIdeles K) => corr z.1) :=
      hcorr_cont.comp continuous_fst
    have hr : Continuous (fun z :
        Fin (Fintype.card (ClassGroup (𝓞 K))) ×
          (chapter09KInfinityOne K × chapter09FiniteUnitIdeles K) => reps z.1) :=
      hreps_cont.comp continuous_fst
    have hu : Continuous (fun z :
        Fin (Fintype.card (ClassGroup (𝓞 K))) ×
          (chapter09KInfinityOne K × chapter09FiniteUnitIdeles K) =>
        (z.2.2 : (Chapter09FiniteAdele K)ˣ)) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    exact (chapter09IdeleProductContinuousEquiv K).symm.continuous.comp
      ((hi.mul hc).prodMk (hr.mul hu))
  have hG : Continuous G := hraw_cont.subtype_mk (fun z => hraw_norm z)
  let T : Set (Fin (Fintype.card (ClassGroup (𝓞 K))) ×
      (chapter09KInfinityOne K × chapter09FiniteUnitIdeles K)) :=
    (Set.univ : Set (Fin (Fintype.card (ClassGroup (𝓞 K))))) ×ˢ
      (Sarch ×ˢ (Set.univ : Set (chapter09FiniteUnitIdeles K)))
  have hT : IsCompact T := by
    exact isCompact_univ.prod
      (hSarch.prod (chapter09_finite_unit_ideles_compact K))
  let S : Set (chapter09NormOneIdeles K) := G '' T
  have hS : IsCompact S := hT.image hG
  refine ⟨S, hS, ?_⟩
  intro x
  let e := chapter09NormOneClassGroup_equiv_classNormOne (K := K)
  let qx : Chapter09NormOneClassGroup K := e.symm x
  obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective qx
  let b : (Chapter09FiniteAdele K)ˣ :=
    (chapter09IdeleProductEquiv K z.1).2
  let c : ClassGroup (𝓞 K) :=
    (chapter09CanonicalIdeleIdealData K).idealClassMap b
  obtain ⟨i, hi⟩ := d.represents_every_class c
  let y : (Chapter09FiniteAdele K)ˣ := b / reps i
  have hyker : y ∈ (chapter09CanonicalIdeleIdealData K).idealClassMap.ker := by
    apply (MonoidHom.mem_ker).2
    change (chapter09CanonicalIdeleIdealData K).idealClassMap y = 1
    rw [show y = b * (reps i)⁻¹ by rfl, map_mul, map_inv, hi]
    simp [c]
  have hysup : y ∈
      (chapter09FinitePrincipalIdele K).range ⊔ chapter09FiniteUnitIdeles K := by
    rw [← (chapter09CanonicalIdeleIdealData K).kernel_eq_principal_mul_units]
    exact hyker
  rcases Subgroup.mem_sup.mp hysup with ⟨p, hp, u, hu, hpu⟩
  rcases hp with ⟨a, rfl⟩
  have humodule : chapter09FiniteIdeleModule u = 1 := by
    unfold chapter09FiniteIdeleModule
    apply finprod_eq_one_of_forall_eq_one
    intro v
    exact (chapter09FiniteUnitIdeles_mem_iff).1 hu v
  have hfinrel : b = chapter09FinitePrincipalIdele K a *
      (u : (Chapter09FiniteAdele K)ˣ) * reps i := by
    have h := congrArg (fun q : (Chapter09FiniteAdele K)ˣ => q * reps i) hpu
    simpa [y, div_eq_mul_inv, mul_assoc] using h.symm
  have hzmod : chapter09IdeleModule z.1 = 1 := by
    change chapter09IdeleModuleHom K z.1 = 1
    exact z.property
  have hzmodpair : chapter09InfiniteIdeleModule
      (chapter09IdeleProductEquiv K z.1).1 *
      chapter09FiniteIdeleModule b = 1 := by
    rw [chapter09IdeleModule_eq_infinite_mul_finite] at hzmod
    simpa [b] using hzmod
  have hmodb : chapter09FiniteIdeleModule b =
      chapter09FiniteIdeleModule (chapter09FinitePrincipalIdele K a) *
        chapter09FiniteIdeleModule (reps i) := by
    rw [hfinrel, hfinite_mul, hfinite_mul, humodule]
    simp
  have hpa_decomp : chapter09IdeleProductEquiv K
      (chapter09PrincipalIdele K a) =
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele a,
        chapter09FinitePrincipalIdele K a) := by
    apply Prod.ext <;> rfl
  have hmodp : chapter09InfiniteIdeleModule
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele a) *
      chapter09FiniteIdeleModule (chapter09FinitePrincipalIdele K a) = 1 := by
    have h := chapter09PrincipalIdele_module_eq_one a
    rw [chapter09IdeleModule_eq_infinite_mul_finite, hpa_decomp] at h
    exact h
  let w : (Chapter09InfiniteAdele K)ˣ :=
    (chapter09IdeleProductEquiv K z.1).1 *
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele a)⁻¹
  have hmodw : chapter09InfiniteIdeleModuleHom K w =
      (chapter09FiniteIdeleModule (reps i))⁻¹ := by
    have hPfin : chapter09FiniteIdeleModule
        (chapter09FinitePrincipalIdele K a) =
        (chapter09InfiniteIdeleModule
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele a))⁻¹ :=
      eq_inv_of_mul_eq_one_right hmodp
    have h := hzmodpair
    rw [hmodb, hPfin] at h
    apply eq_inv_of_mul_eq_one_left
    change chapter09InfiniteIdeleModuleHom K w *
        chapter09FiniteIdeleModule (reps i) = 1
    change chapter09InfiniteIdeleModuleHom K
        ((chapter09IdeleProductEquiv K z.1).1 *
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele a)⁻¹) *
        chapter09FiniteIdeleModule (reps i) = 1
    rw [(chapter09InfiniteIdeleModuleHom K).map_mul,
      (chapter09InfiniteIdeleModuleHom K).map_inv]
    change chapter09InfiniteIdeleModuleHom K
        ((chapter09IdeleProductEquiv K z.1).1) *
        ((chapter09InfiniteIdeleModuleHom K
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele a))⁻¹ *
          chapter09FiniteIdeleModule (reps i)) = 1 at h
    simpa [mul_assoc] using h
  let v : chapter09KInfinityOne K :=
    ⟨w * (corr i)⁻¹, by
      change chapter09InfiniteIdeleModuleHom K (w * (corr i)⁻¹) = 1
      rw [(chapter09InfiniteIdeleModuleHom K).map_mul,
        (chapter09InfiniteIdeleModuleHom K).map_inv, hmodw, hcorr]
      simp⟩
  obtain ⟨s, hs, hs_eq⟩ := harch v
  have hdiv : v / s ∈ (chapter09ArchimedeanUnitEmbedding K).range := by
    exact (QuotientGroup.eq_iff_div_mem).1 hs_eq.symm
  rcases hdiv with ⟨g, hg⟩
  have hvrel : v.1 = (chapter09ArchimedeanUnitEmbedding K g).1 * s.1 := by
    have h := congrArg (fun q : chapter09KInfinityOne K => q * s) hg
    have h' := congrArg Subtype.val h
    simpa [div_eq_mul_inv, mul_assoc] using h'.symm
  let ug : Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom g
  have hinfug : (chapter09ArchimedeanUnitEmbedding K g).1 =
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele ug := by
    rfl
  have hfinug : (chapter09FiniteUnitSubtypeEmbedding K g :
      (Chapter09FiniteAdele K)ˣ) = chapter09FinitePrincipalIdele K ug := by
    apply Units.ext
    rfl
  let ugunit : chapter09FiniteUnitIdeles K :=
    chapter09FiniteUnitSubtypeEmbedding K g
  let u' : chapter09FiniteUnitIdeles K :=
    ⟨(ugunit : (Chapter09FiniteAdele K)ˣ)⁻¹ * u,
      (chapter09FiniteUnitIdeles K).mul_mem
        ((chapter09FiniteUnitIdeles K).inv_mem ugunit.property) hu⟩
  have hinf_eq :
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele (a * ug) *
          (s.1 * corr i) = (chapter09IdeleProductEquiv K z.1).1 := by
    have hv := congrArg (fun q : (Chapter09InfiniteAdele K)ˣ => q * corr i) hvrel
    have hv' : (chapter09IdeleProductEquiv K z.1).1 *
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele a)⁻¹ =
        (chapter09ArchimedeanUnitEmbedding K g).1 * s.1 * corr i := by
      simpa [v, w, mul_assoc] using hv
    calc
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele (a * ug) *
          (s.1 * corr i) =
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele a *
          ((chapter09ArchimedeanUnitEmbedding K g).1 * s.1 * corr i) := by
            simp [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele,
              hinfug, mul_assoc]
      _ = (chapter09IdeleProductEquiv K z.1).1 := by
        rw [← hv']
        simp
  have hfin_eq :
      chapter09FinitePrincipalIdele K (a * ug) *
          (reps i * (u' : (Chapter09FiniteAdele K)ˣ)) = b := by
    rw [(chapter09FinitePrincipalIdele K).map_mul]
    simp [u', ugunit, hfinug, hfinrel, mul_assoc, mul_left_comm, mul_comm]
  have hprod : chapter09PrincipalIdele K (a * ug) *
      raw (i, (s, u')) = z.1 := by
    apply (chapter09IdeleProductEquiv K).injective
    rw [(chapter09IdeleProductEquiv K).map_mul]
    rw [show chapter09IdeleProductEquiv K
        (chapter09PrincipalIdele K (a * ug)) =
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele (a * ug),
          chapter09FinitePrincipalIdele K (a * ug)) by
          apply Prod.ext <;> rfl, hraw_decomp]
    exact Prod.ext hinf_eq hfin_eq
  have hmem : G (i, (s, u')) ∈ S := by
    exact ⟨(i, (s, u')), ⟨Set.mem_univ _, ⟨hs, Set.mem_univ _⟩⟩, rfl⟩
  refine ⟨G (i, (s, u')), hmem, ?_⟩
  rw [← e.apply_symm_apply x]
  change e (QuotientGroup.mk (G (i, (s, u')))) = e (e.symm x)
  apply congrArg e
  change QuotientGroup.mk (G (i, (s, u'))) = qx
  rw [← hz]
  apply (QuotientGroup.eq_iff_div_mem).2
  refine ⟨(a * ug)⁻¹, ?_⟩
  apply Subtype.ext
  change chapter09PrincipalIdele K ((a * ug)⁻¹) =
    raw (i, (s, u')) / z.1
  rw [← hprod]
  simp [div_eq_mul_inv, mul_assoc]

theorem chapter09_normOne_class_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (chapter09ClassNormOne K)) := by
  obtain ⟨S, hS, hrep⟩ := chapter09_normOne_compact_representatives K
  let q : chapter09NormOneIdeles K → chapter09ClassNormOne K := fun s =>
    chapter09NormOneClassGroup_equiv_classNormOne (K := K)
      (QuotientGroup.mk s)
  have hq : Continuous q := by
    exact (chapter09_normOneClassGroup_equiv_classNormOne_continuous K).comp
      QuotientGroup.continuous_mk
  have hqimage : q '' S = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rcases hrep x with ⟨s, hs, hsx⟩
    refine ⟨s, hs, ?_⟩
    change chapter09NormOneClassGroup_equiv_classNormOne (K := K)
      (QuotientGroup.mk s) = x
    exact hsx
  rw [← hqimage]
  exact hS.image hq

noncomputable instance chapter09CompactSpaceClassNormOne
    (K : Type*) [Field K] [NumberField K] : CompactSpace (chapter09ClassNormOne K) :=
  ⟨chapter09_normOne_class_compact K⟩

theorem chapter09_normOne_class_has_compact_representatives
    (K : Type*) [Field K] [NumberField K] :
    ∃ S : Set (chapter09NormOneIdeles K), IsCompact S ∧
      ∀ x : chapter09ClassNormOne K, ∃ s ∈ S,
        chapter09NormOneClassGroup_equiv_classNormOne (K := K)
            (QuotientGroup.mk s) = x := by
  exact chapter09_normOne_compact_representatives K

/- Finite local units are profinite, while the archimedean logarithmic part is
compact only after quotienting by the global unit lattice.  This is the API
form of the source's warning that `C_K^1` is generally disconnected. -/
theorem chapter09_normOne_class_finite_unit_factor_is_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (chapter09FiniteUnitIdeles K)) :=
  chapter09_finite_unit_ideles_compact K

end

end LastLib.Book04AdelesAndIdeles.Chapter09
