import LastLib.Book04AdelesAndIdeles.Chapter09.Section01TheGlobalModuleAndDegree
import LastLib.Book04AdelesAndIdeles.Chapter09.Section03CompactnessOfNormOneClassGroup

namespace LastLib.Book04AdelesAndIdeles.Chapter09

noncomputable section

open NumberField IsDedekindDomain

/-!
## 9.4. Structure of the full idele class group
-/

def chapter09ClassNormOneInclusion
    (K : Type*) [Field K] [NumberField K] :
    chapter09ClassNormOne K →* Chapter09IdeleClassGroup K :=
  (chapter09ClassNormOne K).subtype

theorem chapter09ClassModule_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (chapter09IdeleClassModule K) := by
  apply (QuotientGroup.isQuotientMap_mk
    (chapter09PrincipalIdeleSubgroup K)).continuous_iff.mpr
  change Continuous (fun x : Chapter09Idele K =>
    chapter09IdeleClassModule K (QuotientGroup.mk x))
  have hcomp : (fun x : Chapter09Idele K =>
      chapter09IdeleClassModule K (QuotientGroup.mk x)) =
      chapter09IdeleModuleHom K := by
    funext x
    exact chapter09IdeleClassModule_apply x
  rw [hcomp]
  exact chapter09IdeleModule_continuous K

theorem chapter09ClassModule_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter09IdeleClassModule K) := by
  exact chapter09_module_descends_to_idele_class_group K

def chapter09ClassModule_short_exact
    (K : Type*) [Field K] [NumberField K] :
    Chapter09ShortExactGroup
      (chapter09ClassNormOne K) (Chapter09IdeleClassGroup K) Chapter09PositiveReal := by
  refine
    { left := chapter09ClassNormOneInclusion K
      right := chapter09IdeleClassModule K
      left_injective := ?_
      exact := ?_
      right_surjective := ?_ }
  · intro x y h
    exact Subtype.ext h
  · intro y
    change chapter09IdeleClassModule K y = 1 ↔
      y ∈ Set.range (chapter09ClassNormOneInclusion K)
    constructor
    · intro h
      exact ⟨⟨y, h⟩, rfl⟩
    · rintro ⟨z, hz⟩
      rw [← hz]
      exact z.property
  · exact chapter09ClassModule_surjective K

/- The splitting is stated as a choice-dependent section.  At a real place its
coordinate is `t`; at a complex place it is `sqrt t`, because the normalized
complex absolute value is the square of the usual modulus. -/
theorem chapter09_exists_class_module_section
    (K : Type*) [Field K] [NumberField K]
    (v : InfinitePlace K) :
    ∃ s : Chapter09PositiveReal →* Chapter09IdeleClassGroup K,
      Continuous s ∧
        (chapter09IdeleClassModule K).comp s = MonoidHom.id _ := by
  classical
  rcases v.isReal_or_isComplex with hv | hv
  · let r := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv
    let e := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv
    let hlocal : Chapter09PositiveReal →* v.Completionˣ :=
      { toFun := fun t => Units.mk0 (e.symm (t : ℝ)) (by
          intro hz
          change r.symm (t : ℝ) = 0 at hz
          have ht : (t : ℝ) = 0 := by
            simpa using congrArg r hz
          exact (ne_of_gt (NNReal.coe_pos.mpr
            (pos_iff_ne_zero.mpr (Units.ne_zero t)))) ht)
        map_one' := by
          apply Units.ext
          change r.symm (1 : ℝ) = 1
          simp [r]
        map_mul' := by
          intro x y
          apply Units.ext
          change r.symm ((x : ℝ) * (y : ℝ)) =
            r.symm (x : ℝ) * r.symm (y : ℝ)
          rw [← r.symm.map_mul] }
    have hlocal_cont : Continuous hlocal := by
      apply Units.continuous_iff.mpr
      constructor
      · change Continuous (fun t : Chapter09PositiveReal => e.symm (t : ℝ))
        have ht : Continuous (fun t : Chapter09PositiveReal => (t : ℝ)) :=
          NNReal.continuous_coe.comp Units.continuous_val
        exact e.symm.continuous.comp ht
      · have hcoe : Continuous (fun t : Chapter09PositiveReal =>
            (hlocal t : v.Completion)) := by
          change Continuous (fun t : Chapter09PositiveReal => e.symm (t : ℝ))
          have ht : Continuous (fun t : Chapter09PositiveReal => (t : ℝ)) :=
            NNReal.continuous_coe.comp Units.continuous_val
          exact e.symm.continuous.comp ht
        have hi := hcoe.comp (continuous_inv :
          Continuous (fun t : Chapter09PositiveReal => t⁻¹))
        have heq : (fun t : Chapter09PositiveReal =>
            (hlocal (t⁻¹) : v.Completion)) =
            (fun t : Chapter09PositiveReal =>
              (↑((hlocal t)⁻¹) : v.Completion)) := by
          funext t
          exact congrArg Units.val (map_inv hlocal t)
        rw [← heq]
        change Continuous (fun t : Chapter09PositiveReal =>
          (hlocal (t⁻¹) : v.Completion)) at hi
        exact hi
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
    let hcoord : Chapter09PositiveReal →*
        (∀ w : InfinitePlace K, w.Completionˣ) :=
      (MonoidHom.mulSingle (fun w : InfinitePlace K => w.Completionˣ) v).comp hlocal
    let hinf : Chapter09PositiveReal →* (Chapter09InfiniteAdele K)ˣ :=
      (MulEquiv.piUnits (M := fun w : InfinitePlace K => w.Completion)).symm.toMonoidHom.comp
        hcoord
    let hpair : Chapter09PositiveReal →*
        (Chapter09InfiniteAdele K)ˣ × (Chapter09FiniteAdele K)ˣ :=
      { toFun := fun t => (hinf t, 1)
        map_one' := by simp
        map_mul' := by intro x y; simp }
    let hfull : Chapter09PositiveReal →* Chapter09Idele K :=
      (chapter09IdeleProductEquiv K).symm.toMonoidHom.comp hpair
    let s : Chapter09PositiveReal →* Chapter09IdeleClassGroup K :=
      (QuotientGroup.mk' (chapter09PrincipalIdeleSubgroup K)).comp hfull
    have hcoord_cont : Continuous hcoord := by
      change Continuous (fun t : Chapter09PositiveReal => hcoord t)
      exact continuous_pi fun w => by
        by_cases hw : w = v
        · subst w
          simpa [hcoord] using hlocal_cont
        · have hconst : (fun t : Chapter09PositiveReal => hcoord t w) =
              (fun _ => (1 : w.Completionˣ)) := by
            funext t
            change Pi.mulSingle (M := fun w : InfinitePlace K => w.Completionˣ)
              v (hlocal t) w = 1
            exact Pi.mulSingle_eq_of_ne (M := fun w : InfinitePlace K => w.Completionˣ)
              hw (hlocal t)
          rw [hconst]
          exact continuous_const
    have hinf_cont : Continuous hinf := by
      exact (ContinuousMulEquiv.piUnits
        (M := fun w : InfinitePlace K => w.Completion)).symm.continuous.comp hcoord_cont
    have hfull_cont : Continuous hfull := by
      exact (chapter09IdeleProductContinuousEquiv K).symm.continuous.comp
        (hinf_cont.prodMk continuous_const)
    have hs : Continuous s := by
      exact QuotientGroup.continuous_mk.comp hfull_cont
    refine ⟨s, hs, ?_⟩
    apply MonoidHom.ext
    intro t
    change chapter09IdeleClassModule K (QuotientGroup.mk (hfull t)) = t
    rw [chapter09IdeleClassModule_apply]
    change chapter09IdeleModule (hfull t) = t
    rw [chapter09IdeleModule_eq_infinite_mul_finite]
    have hdecomp : chapter09IdeleProductEquiv K (hfull t) = (hinf t, 1) := by
      simp [hfull, hpair]
    rw [hdecomp]
    have hfin : chapter09FiniteIdeleModule
        (1 : (Chapter09FiniteAdele K)ˣ) = 1 := by
      unfold chapter09FiniteIdeleModule
      apply finprod_eq_one_of_forall_eq_one
      intro w
      exact (chapter09FiniteUnitIdeles_mem_iff.mp (Subgroup.one_mem _) w)
    rw [hfin, mul_one]
    unfold chapter09InfiniteIdeleModule
    have hpi : MulEquiv.piUnits (hinf t) = Pi.mulSingle v (hlocal t) := by
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
    let hlocal : Chapter09PositiveReal →* v.Completionˣ :=
      { toFun := fun t => Units.mk0
            (e.symm (Complex.ofReal (Real.sqrt (t : ℝ)))) (by
          intro hz
          change r.symm (Complex.ofReal (Real.sqrt (t : ℝ))) = 0 at hz
          have hz' : Complex.ofReal (Real.sqrt (t : ℝ)) = 0 := by
            simpa using congrArg r hz
          have ht : 0 < (t : ℝ) :=
            NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero t))
          exact (ne_of_gt (Real.sqrt_pos.2 ht)) (by
            simpa using congrArg Complex.re hz'))
        map_one' := by
          apply Units.ext
          change e.symm (Complex.ofReal (Real.sqrt (1 : ℝ))) =
            (1 : v.Completion)
          rw [Real.sqrt_one, Complex.ofReal_one]
          change r.symm (1 : ℂ) = 1
          exact r.symm.map_one
        map_mul' := by
          intro x y
          apply Units.ext
          change r.symm (Complex.ofReal (Real.sqrt ((x * y : Chapter09PositiveReal) : ℝ))) =
            r.symm (Complex.ofReal (Real.sqrt (x : ℝ))) *
              r.symm (Complex.ofReal (Real.sqrt (y : ℝ)))
          rw [← r.symm.map_mul]
          rw [← Complex.ofReal_mul]
          congr 1
          have hxy : ((x * y : Chapter09PositiveReal) : ℝ) =
              (x : ℝ) * (y : ℝ) := by simp
          rw [hxy, Real.sqrt_mul]
          exact NNReal.coe_nonneg _ }
    have hlocal_cont : Continuous hlocal := by
      apply Units.continuous_iff.mpr
      constructor
      · change Continuous (fun t : Chapter09PositiveReal =>
          e.symm (Complex.ofReal (Real.sqrt (t : ℝ))))
        have ht : Continuous (fun t : Chapter09PositiveReal => (t : ℝ)) :=
          NNReal.continuous_coe.comp Units.continuous_val
        have hrt : Continuous (fun t : Chapter09PositiveReal =>
            Complex.ofReal (Real.sqrt (t : ℝ))) :=
          Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp ht)
        exact e.symm.continuous.comp hrt
      · have hcoe : Continuous (fun t : Chapter09PositiveReal =>
            (hlocal t : v.Completion)) := by
          change Continuous (fun t : Chapter09PositiveReal =>
            e.symm (Complex.ofReal (Real.sqrt (t : ℝ))))
          have ht : Continuous (fun t : Chapter09PositiveReal => (t : ℝ)) :=
            NNReal.continuous_coe.comp Units.continuous_val
          have hrt : Continuous (fun t : Chapter09PositiveReal =>
              Complex.ofReal (Real.sqrt (t : ℝ))) :=
            Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp ht)
          exact e.symm.continuous.comp hrt
        have hi := hcoe.comp (continuous_inv :
          Continuous (fun t : Chapter09PositiveReal => t⁻¹))
        have heq : (fun t : Chapter09PositiveReal =>
            (hlocal (t⁻¹) : v.Completion)) =
            (fun t : Chapter09PositiveReal =>
              (↑((hlocal t)⁻¹) : v.Completion)) := by
          funext t
          exact congrArg Units.val (map_inv hlocal t)
        rw [← heq]
        change Continuous (fun t : Chapter09PositiveReal =>
          (hlocal (t⁻¹) : v.Completion)) at hi
        exact hi
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
    let hcoord : Chapter09PositiveReal →*
        (∀ w : InfinitePlace K, w.Completionˣ) :=
      (MonoidHom.mulSingle (fun w : InfinitePlace K => w.Completionˣ) v).comp hlocal
    let hinf : Chapter09PositiveReal →* (Chapter09InfiniteAdele K)ˣ :=
      (MulEquiv.piUnits (M := fun w : InfinitePlace K => w.Completion)).symm.toMonoidHom.comp
        hcoord
    let hpair : Chapter09PositiveReal →*
        (Chapter09InfiniteAdele K)ˣ × (Chapter09FiniteAdele K)ˣ :=
      { toFun := fun t => (hinf t, 1)
        map_one' := by simp
        map_mul' := by intro x y; simp }
    let hfull : Chapter09PositiveReal →* Chapter09Idele K :=
      (chapter09IdeleProductEquiv K).symm.toMonoidHom.comp hpair
    let s : Chapter09PositiveReal →* Chapter09IdeleClassGroup K :=
      (QuotientGroup.mk' (chapter09PrincipalIdeleSubgroup K)).comp hfull
    have hcoord_cont : Continuous hcoord := by
      change Continuous (fun t : Chapter09PositiveReal => hcoord t)
      exact continuous_pi fun w => by
        by_cases hw : w = v
        · subst w
          simpa [hcoord] using hlocal_cont
        · have hconst : (fun t : Chapter09PositiveReal => hcoord t w) =
              (fun _ => (1 : w.Completionˣ)) := by
            funext t
            change Pi.mulSingle (M := fun w : InfinitePlace K => w.Completionˣ)
              v (hlocal t) w = 1
            exact Pi.mulSingle_eq_of_ne (M := fun w : InfinitePlace K => w.Completionˣ)
              hw (hlocal t)
          rw [hconst]
          exact continuous_const
    have hinf_cont : Continuous hinf := by
      exact (ContinuousMulEquiv.piUnits
        (M := fun w : InfinitePlace K => w.Completion)).symm.continuous.comp hcoord_cont
    have hfull_cont : Continuous hfull := by
      exact (chapter09IdeleProductContinuousEquiv K).symm.continuous.comp
        (hinf_cont.prodMk continuous_const)
    have hs : Continuous s := by
      exact QuotientGroup.continuous_mk.comp hfull_cont
    refine ⟨s, hs, ?_⟩
    apply MonoidHom.ext
    intro t
    change chapter09IdeleClassModule K (QuotientGroup.mk (hfull t)) = t
    rw [chapter09IdeleClassModule_apply]
    change chapter09IdeleModule (hfull t) = t
    rw [chapter09IdeleModule_eq_infinite_mul_finite]
    have hdecomp : chapter09IdeleProductEquiv K (hfull t) = (hinf t, 1) := by
      simp [hfull, hpair]
    rw [hdecomp]
    have hfin : chapter09FiniteIdeleModule
        (1 : (Chapter09FiniteAdele K)ˣ) = 1 := by
      unfold chapter09FiniteIdeleModule
      apply finprod_eq_one_of_forall_eq_one
      intro w
      exact (chapter09FiniteUnitIdeles_mem_iff.mp (Subgroup.one_mem _) w)
    rw [hfin, mul_one]
    unfold chapter09InfiniteIdeleModule
    have hpi : MulEquiv.piUnits (hinf t) = Pi.mulSingle v (hlocal t) := by
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

noncomputable def chapter09ClassModuleSection
    (K : Type*) [Field K] [NumberField K]
    (v : InfinitePlace K) :
    Chapter09PositiveReal →* Chapter09IdeleClassGroup K :=
  Classical.choose (chapter09_exists_class_module_section K v)

theorem chapter09ClassModuleSection_continuous
    (K : Type*) [Field K] [NumberField K]
    (v : InfinitePlace K) :
    Continuous (chapter09ClassModuleSection K v) := by
  exact (Classical.choose_spec (chapter09_exists_class_module_section K v)).1

theorem chapter09ClassModuleSection_right_inverse
    (K : Type*) [Field K] [NumberField K]
    (v : InfinitePlace K) :
    (chapter09IdeleClassModule K).comp (chapter09ClassModuleSection K v) =
      MonoidHom.id _ := by
  exact (Classical.choose_spec (chapter09_exists_class_module_section K v)).2

theorem chapter09_idele_class_group_split
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (Chapter09IdeleClassGroup K ≃ₜ*
      chapter09ClassNormOne K × Chapter09PositiveReal) := by
  classical
  let v : InfinitePlace K :=
    Classical.choice (inferInstance : Nonempty (InfinitePlace K))
  let s : Chapter09PositiveReal →* Chapter09IdeleClassGroup K :=
    chapter09ClassModuleSection K v
  have hs : Continuous s :=
    chapter09ClassModuleSection_continuous K v
  have hsright :
      (chapter09IdeleClassModule K).comp s = MonoidHom.id _ :=
    chapter09ClassModuleSection_right_inverse K v
  have hsright_apply (t : Chapter09PositiveReal) :
      chapter09IdeleClassModule K (s t) = t := by
    have h := congrArg
      (fun f : Chapter09PositiveReal →* Chapter09PositiveReal => f t) hsright
    simpa using h
  let : CommGroup (Chapter09IdeleClassGroup K) := by infer_instance
  let p : Chapter09IdeleClassGroup K →*
      chapter09ClassNormOne K :=
    { toFun := fun x =>
        ⟨x * (s (chapter09IdeleClassModule K x))⁻¹, by
          apply (chapter09ClassNormOne_mem_iff).2
          simpa only [map_mul, map_inv,
            hsright_apply (chapter09IdeleClassModule K x)] using
            mul_inv_cancel (chapter09IdeleClassModule K x)
        ⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change x * y * (s (chapter09IdeleClassModule K (x * y)))⁻¹ =
          (x * (s (chapter09IdeleClassModule K x))⁻¹) *
            (y * (s (chapter09IdeleClassModule K y))⁻¹)
        rw [(chapter09IdeleClassModule K).map_mul, s.map_mul, mul_inv_rev]
        ac_rfl }
  let φ : Chapter09IdeleClassGroup K →*
      chapter09ClassNormOne K × Chapter09PositiveReal :=
    { toFun := fun x => (p x, chapter09IdeleClassModule K x)
      map_one' := by simp [p]
      map_mul' := by
        intro x y
        simp [p, mul_inv_rev]
        ac_rfl }
  let ψ : (chapter09ClassNormOne K × Chapter09PositiveReal) →*
      Chapter09IdeleClassGroup K :=
    { toFun := fun z => (z.1 : Chapter09IdeleClassGroup K) * s z.2
      map_one' := by simp
      map_mul' := by
        intro x y
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        change (x.1 : Chapter09IdeleClassGroup K) * (y.1 : Chapter09IdeleClassGroup K) *
            (s x.2 * s y.2) =
          (x.1 : Chapter09IdeleClassGroup K) * s x.2 *
            ((y.1 : Chapter09IdeleClassGroup K) * s y.2)
        ac_rfl }
  let ealg : Chapter09IdeleClassGroup K ≃*
      chapter09ClassNormOne K × Chapter09PositiveReal :=
    { toFun := φ
      invFun := ψ
      left_inv := by
        intro x
        change (p x : Chapter09IdeleClassGroup K) * s
            (chapter09IdeleClassModule K x) = x
        change (x * (s (chapter09IdeleClassModule K x))⁻¹) *
            s (chapter09IdeleClassModule K x) = x
        rw [mul_assoc, inv_mul_cancel, mul_one]
      right_inv := by
        intro z
        have hz : chapter09IdeleClassModule K (z.1 :
            Chapter09IdeleClassGroup K) = 1 :=
          (chapter09ClassNormOne_mem_iff).1 z.1.property
        apply Prod.ext
        · apply Subtype.ext
          change (z.1 : Chapter09IdeleClassGroup K) * s z.2 *
              (s (chapter09IdeleClassModule K
                ((z.1 : Chapter09IdeleClassGroup K) * s z.2)))⁻¹ = z.1
          rw [map_mul, hz, one_mul, hsright_apply]
          simp
        · change chapter09IdeleClassModule K
            ((z.1 : Chapter09IdeleClassGroup K) * s z.2) = z.2
          rw [map_mul, hz, one_mul, hsright_apply]
      map_mul' := by
        intro x y
        exact φ.map_mul x y }
  have hp_cont : Continuous p := by
    apply Continuous.subtype_mk
    · have hss : Continuous (fun x : Chapter09IdeleClassGroup K =>
          s (chapter09IdeleClassModule K x)) :=
        hs.comp (chapter09ClassModule_continuous K)
      exact continuous_id.mul hss.inv
  have hφ_cont : Continuous φ := by
    exact hp_cont.prodMk (chapter09ClassModule_continuous K)
  have hψ_cont : Continuous ψ := by
    change Continuous (fun z : chapter09ClassNormOne K ×
        Chapter09PositiveReal =>
        (z.1 : Chapter09IdeleClassGroup K) * s z.2)
    exact (continuous_subtype_val.comp continuous_fst).mul
      (hs.comp continuous_snd)
  exact ⟨ContinuousMulEquiv.mk ealg hφ_cont hψ_cont⟩

theorem chapter09_positive_real_compact_subgroup_trivial
    (H : Subgroup Chapter09PositiveReal)
    (hH : IsCompact (H : Set Chapter09PositiveReal)) :
    H = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  have hcompact :
      IsCompact ((fun x : Chapter09PositiveReal => Units.val x) ''
        (H : Set Chapter09PositiveReal)) :=
    hH.image Units.continuous_val
  rcases hcompact.bddAbove with ⟨B, hB⟩
  intro x hx
  by_contra hxone
  have hval : Units.val x ≠ 1 := by
    intro hval
    apply hxone
    exact Units.ext hval
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have hinvval : (1 : NNReal) < Units.val (x⁻¹) := by
      simpa using
        ((one_lt_inv₀ (pos_iff_ne_zero.mpr (Units.ne_zero x))).2 hlt)
    rcases pow_unbounded_of_one_lt B (show 1 < Units.val (x⁻¹) from
      hinvval) with ⟨n, hn⟩
    have hpow : x⁻¹ ^ n ∈ H := H.pow_mem (H.inv_mem hx) n
    have hbound : Units.val (x⁻¹ ^ n) ≤ B :=
      hB ⟨x⁻¹ ^ n, hpow, rfl⟩
    exact (not_lt_of_ge hbound) (by simpa using hn)
  · rcases pow_unbounded_of_one_lt B hgt with ⟨n, hn⟩
    have hpow : x ^ n ∈ H := H.pow_mem hx n
    have hbound : Units.val (x ^ n) ≤ B :=
      hB ⟨x ^ n, hpow, rfl⟩
    exact (not_lt_of_ge hbound) (by simpa using hn)

theorem chapter09_compact_subgroup_le_classNormOne
    (K : Type*) [Field K] [NumberField K]
    (H : Subgroup (Chapter09IdeleClassGroup K))
    (hH : IsCompact (H : Set (Chapter09IdeleClassGroup K))) :
    H ≤ chapter09ClassNormOne K := by
  let M : Subgroup Chapter09PositiveReal :=
    Subgroup.map (chapter09IdeleClassModule K) H
  have hMcompact : IsCompact (M : Set Chapter09PositiveReal) := by
    rw [Subgroup.coe_map]
    exact hH.image (chapter09ClassModule_continuous K)
  have hM : M = ⊥ := chapter09_positive_real_compact_subgroup_trivial M hMcompact
  intro x hx
  change chapter09IdeleClassModule K x = 1
  have hmem : chapter09IdeleClassModule K x ∈ (M : Set Chapter09PositiveReal) := by
    rw [Subgroup.coe_map]
    exact ⟨x, hx, rfl⟩
  rw [hM] at hmem
  simpa using hmem

theorem chapter09_classNormOne_is_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (chapter09ClassNormOne K : Set (Chapter09IdeleClassGroup K)) := by
  simpa using (chapter09_normOne_class_compact K).image
    (continuous_subtype_val : Continuous
      (fun x : chapter09ClassNormOne K =>
        (x : Chapter09IdeleClassGroup K)))

theorem chapter09_classNormOne_is_unique_maximal_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (chapter09ClassNormOne K : Set (Chapter09IdeleClassGroup K)) ∧
      ∀ H : Subgroup (Chapter09IdeleClassGroup K),
        IsCompact (H : Set (Chapter09IdeleClassGroup K)) →
          H ≤ chapter09ClassNormOne K := by
  exact ⟨chapter09_classNormOne_is_compact K,
    fun H hH => chapter09_compact_subgroup_le_classNormOne K H hH⟩

theorem chapter09_idele_class_group_is_not_compact
    (K : Type*) [Field K] [NumberField K] :
    ¬ IsCompact (Set.univ : Set (Chapter09IdeleClassGroup K)) := by
  intro hcompact
  have himage : IsCompact (Set.range (chapter09IdeleClassModule K)) := by
    rw [← Set.image_univ]
    exact hcompact.image (chapter09ClassModule_continuous K)
  have huniv : Set.range (chapter09IdeleClassModule K) =
      (Set.univ : Set Chapter09PositiveReal) :=
    Set.range_eq_univ.mpr (chapter09ClassModule_surjective K)
  have hcompact' : IsCompact (Set.univ : Set Chapter09PositiveReal) := by
    rw [← huniv]
    exact himage
  have hbounded : IsCompact
      ((fun x : Chapter09PositiveReal => Units.val x) ''
        (Set.univ : Set Chapter09PositiveReal)) :=
    hcompact'.image Units.continuous_val
  rcases hbounded.bddAbove with ⟨B, hB⟩
  have htwo : (2 : NNReal) ≠ 0 := by norm_num
  let t : Chapter09PositiveReal := Units.mk0 (2 : NNReal) htwo
  rcases pow_unbounded_of_one_lt B (show 1 < Units.val t by
    norm_num [t]) with ⟨n, hn⟩
  have hbound : Units.val (t ^ n) ≤ B :=
    hB ⟨t ^ n, Set.mem_univ _, rfl⟩
  exact (not_lt_of_ge hbound) (by simpa using hn)

end

end LastLib.Book04AdelesAndIdeles.Chapter09
