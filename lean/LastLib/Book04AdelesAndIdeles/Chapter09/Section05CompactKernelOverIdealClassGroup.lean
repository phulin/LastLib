import LastLib.Book04AdelesAndIdeles.Chapter09.Section03CompactnessOfNormOneClassGroup

namespace LastLib.Book04AdelesAndIdeles.Chapter09

noncomputable section

open NumberField IsDedekindDomain

/-!
## 9.5. The compact kernel over the ideal class group
-/

/- This is the representative-level map on norm-one ideles.  The exact
sequence below uses `chapter09NormOneClassIdealClassMap`, the map descended to
the norm-one idele class group. -/
def chapter09NormOneIdealClassMap
    (K : Type*) [Field K] [NumberField K] :
    chapter09NormOneIdeles K →* ClassGroup (𝓞 K) :=
  (chapter09CanonicalIdeleIdealData K).idealClassMap.comp
    ((chapter09FiniteIdelePartHom K).comp (chapter09NormOneIdeles K).subtype)

theorem chapter09NormOneIdealClassMap_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter09NormOneIdealClassMap K) := by
  intro c
  obtain ⟨y, hy⟩ := (chapter09CanonicalIdeleIdealData K).surjective c
  obtain ⟨h, hh⟩ := chapter09_infinite_idele_module_surjective K
    (chapter09FiniteIdeleModule y)⁻¹
  let x : Chapter09Idele K :=
    (chapter09IdeleProductEquiv K).symm (h, y)
  have hdecomp : chapter09IdeleProductEquiv K x = (h, y) := by
    exact (chapter09IdeleProductEquiv K).apply_symm_apply _
  have hx : x ∈ chapter09NormOneIdeles K := by
    change chapter09IdeleModuleHom K x = 1
    change chapter09IdeleModule x = 1
    rw [chapter09IdeleModule_eq_infinite_mul_finite, hdecomp]
    change chapter09InfiniteIdeleModuleHom K h * chapter09FiniteIdeleModule y = 1
    rw [hh]
    simp
  refine ⟨⟨x, hx⟩, ?_⟩
  change (chapter09CanonicalIdeleIdealData K).idealClassMap
      (chapter09FiniteIdelePartHom K x) = c
  rw [chapter09FiniteIdelePartHom_apply, hdecomp]
  exact hy

def chapter09ArchFiniteToClassNormOne
    (K : Type*) [Field K] [NumberField K] :
    Chapter09ArchFiniteUnitKernel K →* chapter09ClassNormOne K :=
  (chapter09NormOneClassGroup_equiv_classNormOne (K := K)).toMonoidHom.comp
    (chapter09ArchFiniteToNormOneClassGroup K)

theorem chapter09ArchFiniteToClassNormOne_apply
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter09ArchFiniteUnitKernel K) :
    chapter09ArchFiniteToClassNormOne K x =
      (chapter09NormOneClassGroup_equiv_classNormOne (K := K))
        (chapter09ArchFiniteToNormOneClassGroup K x) :=
  rfl

private theorem chapter09_arch_finite_to_norm_one_class_group_injective
    (K : Type*) [Field K] [NumberField K] :
    Function.Injective (chapter09ArchFiniteToNormOneClassGroup K) := by
  have hglobal : ∀ {c : Kˣ},
      toPrincipalIdeal (𝓞 K) K c = 1 →
        ∃ u : (𝓞 K)ˣ,
          c = Units.map (algebraMap (𝓞 K) K).toMonoidHom u := by
    intro c hc
    have hspan : Submodule.span (𝓞 K) {(c : K)} = 1 := by
      have hcoe := congrArg (fun I :
          LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08IdealGroup K =>
          ((I : LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08FractionalIdeal K) :
            Submodule (𝓞 K) K)) hc
      simpa [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton] using hcoe
    obtain ⟨u, hu⟩ := (Submodule.span_singleton_eq_one_iff).1 hspan
    refine ⟨u, ?_⟩
    apply Units.ext
    simpa using hu
  let ψ : Chapter09ArchFiniteUnitNumerator K →*
      Chapter09NormOneClassGroup K :=
    (QuotientGroup.mk' (chapter09NormOnePrincipalIdele K).range).comp
      (chapter09ArchFiniteToNormOneIdele K)
  have hker : MonoidHom.ker ψ =
      (chapter09GlobalUnitDiagonal K).range := by
    ext x
    constructor
    · intro hx
      change ψ x = 1 at hx
      change QuotientGroup.mk' (chapter09NormOnePrincipalIdele K).range
        (chapter09ArchFiniteToNormOneIdele K x) = 1 at hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      obtain ⟨a, ha⟩ := hx
      have hprod := congrArg (fun z : chapter09NormOneIdeles K =>
          chapter09IdeleProductEquiv K z.1) ha
      have hfinite := congrArg Prod.snd hprod
      change chapter09FinitePrincipalIdele K a = x.2.1 at hfinite
      have hxker : x.2.1 ∈ MonoidHom.ker
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K) := by
        rw [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_kernel]
        exact x.2.property
      have hxideal := (MonoidHom.mem_ker.mp hxker)
      have hfinite0 : chapter09FinitePrincipalIdele K a =
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a := by
        apply Units.ext
        rfl
      have hprincipal :
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K
            (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) = 1 := by
        rw [← hfinite0, hfinite]
        exact hxideal
      have hpa : toPrincipalIdeal (𝓞 K) K a = 1 := by
        rw [← LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_principal a,
          hprincipal]
      obtain ⟨u, hu⟩ := hglobal hpa
      refine ⟨u, ?_⟩
      change (chapter09ArchimedeanUnitEmbedding K u,
        chapter09FiniteUnitSubtypeEmbedding K u) = x
      apply Prod.ext
      · apply Subtype.ext
        have hfirst := congrArg Prod.fst hprod
        change LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele a =
          x.1.1 at hfirst
        change Units.map (algebraMap K (Chapter09InfiniteAdele K))
            (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) = x.1.1
        change Units.map (algebraMap K (Chapter09InfiniteAdele K)) a = x.1.1 at hfirst
        simpa [hu] using hfirst
      · change chapter09FiniteUnitSubtypeEmbedding K u = x.2
        apply Subtype.ext
        apply Units.ext
        change (chapter09FiniteUnitEmbedding K u : Chapter09FiniteAdele K) = x.2.1
        have hsecond := congrArg Prod.snd hprod
        change chapter09FinitePrincipalIdele K a = x.2.1 at hsecond
        have hsecond0 :
            LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a =
              x.2.1 := by
          rw [← hfinite0]
          exact hsecond
        have hunit_eq :
            (chapter09FiniteUnitEmbedding K u : Chapter09FiniteAdele K) =
              (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele
                (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) :
                Chapter09FiniteAdele K) := by
          rfl
        rw [hunit_eq]
        have hsecond0' := congrArg (fun z : (Chapter09FiniteAdele K)ˣ =>
          (z : Chapter09FiniteAdele K)) hsecond0
        simpa [hu] using hsecond0'
    · rintro ⟨u, rfl⟩
      let b : Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom u
      change QuotientGroup.mk' (chapter09NormOnePrincipalIdele K).range
        (chapter09ArchFiniteToNormOneIdele K
          (chapter09GlobalUnitDiagonal K u)) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      refine ⟨b, ?_⟩
      apply Subtype.ext
      rfl
  have hN : (chapter09GlobalUnitDiagonal K).range ≤ MonoidHom.ker ψ := by
    rw [hker]
  have hinj : Function.Injective
      (QuotientGroup.lift (chapter09GlobalUnitDiagonal K).range ψ hN) :=
    (QuotientGroup.injective_lift_iff
      (N := (chapter09GlobalUnitDiagonal K).range) ψ hN).2 hker.symm
  simpa [chapter09ArchFiniteToNormOneClassGroup, ψ] using hinj

def chapter09CompactKernel_short_exact
    (K : Type*) [Field K] [NumberField K] :
      Chapter09ShortExactGroup
      (Chapter09ArchFiniteUnitKernel K) (chapter09ClassNormOne K)
        (ClassGroup (𝓞 K)) := by
  refine
    { left := chapter09ArchFiniteToClassNormOne K
      right := chapter09NormOneClassIdealClassMap K
      left_injective := ?_
      exact := ?_
      right_surjective := ?_ }
  · intro x y hxy
    change (chapter09NormOneClassGroup_equiv_classNormOne (K := K))
        (chapter09ArchFiniteToNormOneClassGroup K x) =
      (chapter09NormOneClassGroup_equiv_classNormOne (K := K))
        (chapter09ArchFiniteToNormOneClassGroup K y) at hxy
    apply chapter09_arch_finite_to_norm_one_class_group_injective K
    exact (chapter09NormOneClassGroup_equiv_classNormOne (K := K)).injective hxy
  · intro z
    change chapter09NormOneClassIdealClassMap K z = 1 ↔
      z ∈ Set.range (chapter09ArchFiniteToClassNormOne K)
    constructor
    · intro hz
      obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective z.1
      have hnorm : g ∈ chapter09NormOneIdeles K := by
        change chapter09IdeleModuleHom K g = 1
        have hmodule : chapter09IdeleClassModule K (QuotientGroup.mk g) = 1 := by
          rw [hg]
          exact z.property
        rw [chapter09IdeleClassModule_apply] at hmodule
        exact hmodule
      have hideal :
          (chapter09CanonicalIdeleIdealData K).idealClassMap
            (chapter09FiniteIdelePartHom K g) = 1 := by
        have hz' := hz
        change chapter09IdeleClassIdealClassMap K z.1 = 1 at hz'
        rw [← hg, chapter09IdeleClassIdealClassMap_apply] at hz'
        exact hz'
      have hmem : chapter09FiniteIdelePartHom K g ∈
          (chapter09CanonicalIdeleIdealData K).idealClassMap.ker := by
        exact (MonoidHom.mem_ker).2 hideal
      rw [(chapter09CanonicalIdeleIdealData K).kernel_eq_principal_mul_units] at hmem
      rcases Subgroup.mem_sup.mp hmem with ⟨p, hp, u, hu, hpu⟩
      rcases hp with ⟨a, rfl⟩
      let g' : Chapter09Idele K := (chapter09PrincipalIdele K a)⁻¹ * g
      have hfinite : chapter09FiniteIdelePartHom K g' = u := by
        change chapter09FiniteIdelePartHom K
          ((chapter09PrincipalIdele K a)⁻¹ * g) = u
        rw [(chapter09FiniteIdelePartHom K).map_mul,
          (chapter09FiniteIdelePartHom K).map_inv]
        change (chapter09FinitePrincipalIdele K a)⁻¹ *
          chapter09FiniteIdelePartHom K g = u
        rw [← hpu]
        simp
      have hpa : chapter09PrincipalIdele K a ∈ chapter09NormOneIdeles K :=
        (chapter09NormOnePrincipalIdele K a).property
      have hg' : g' ∈ chapter09NormOneIdeles K := by
        change (chapter09PrincipalIdele K a)⁻¹ * g ∈ chapter09NormOneIdeles K
        exact (chapter09NormOneIdeles K).mul_mem
          ((chapter09NormOneIdeles K).inv_mem hpa) hnorm
      have hfin : chapter09FiniteIdeleModule u = 1 := by
        unfold chapter09FiniteIdeleModule
        apply finprod_eq_one_of_forall_eq_one
        intro v
        exact (chapter09FiniteUnitIdeles_mem_iff).1 hu v
      have hfinite' : (chapter09IdeleProductEquiv K g').2 = u := by
        exact hfinite
      have hinf : chapter09InfiniteIdeleModuleHom K
          (chapter09IdeleProductEquiv K g').1 = 1 := by
        have hfull : chapter09IdeleModule g' = 1 := by
          change chapter09IdeleModuleHom K g' = 1
          exact hg'
        rw [chapter09IdeleModule_eq_infinite_mul_finite] at hfull
        change chapter09InfiniteIdeleModuleHom K
            (chapter09IdeleProductEquiv K g').1 *
          chapter09FiniteIdeleModule ((chapter09IdeleProductEquiv K g').2) = 1 at hfull
        rw [hfinite', hfin] at hfull
        simpa using hfull
      let xraw : Chapter09ArchFiniteUnitNumerator K :=
        (⟨(chapter09IdeleProductEquiv K g').1, hinf⟩, ⟨u, hu⟩)
      have hmap : chapter09ArchFiniteToNormOneIdele K xraw =
          ⟨g', hg'⟩ := by
        apply Subtype.ext
        apply Units.ext
        dsimp [chapter09ArchFiniteToNormOneIdele, xraw]
        rw [← hfinite']
        exact congrArg (fun z : Chapter09Idele K => (z : Chapter09Adele K))
          ((chapter09IdeleProductEquiv K).symm_apply_apply g')
      have hclass : chapter09ArchFiniteToNormOneClassGroup K
          (QuotientGroup.mk xraw) = QuotientGroup.mk ⟨g', hg'⟩ := by
        change QuotientGroup.mk' (chapter09NormOnePrincipalIdele K).range
            (chapter09ArchFiniteToNormOneIdele K xraw) = QuotientGroup.mk ⟨g', hg'⟩
        rw [hmap]
        rfl
      have hclass_z : chapter09ArchFiniteToClassNormOne K
          (QuotientGroup.mk xraw) = z := by
        apply Subtype.ext
        change (chapter09NormOneClassGroup_equiv_classNormOne (K := K))
            (chapter09ArchFiniteToNormOneClassGroup K (QuotientGroup.mk xraw)) = z.1
        rw [hclass]
        change QuotientGroup.mk g' = z.1
        rw [← hg]
        apply (QuotientGroup.eq_iff_div_mem).2
        refine ⟨a⁻¹, ?_⟩
        simp [g', div_eq_mul_inv, mul_assoc]
      exact ⟨QuotientGroup.mk xraw, hclass_z⟩
    · rintro ⟨x, hx⟩
      rw [← hx]
      obtain ⟨xraw, hxraw⟩ := QuotientGroup.mk'_surjective
        (chapter09GlobalUnitDiagonal K).range x
      rw [← hxraw]
      change (chapter09CanonicalIdeleIdealData K).idealClassMap
          (chapter09FiniteIdelePartHom K
            (chapter09ArchFiniteToNormOneIdele K xraw)) = 1
      apply (MonoidHom.mem_ker).1
      rw [(chapter09CanonicalIdeleIdealData K).kernel_eq_principal_mul_units]
      exact Subgroup.mem_sup.mpr
        ⟨1, (chapter09FinitePrincipalIdele K).range.one_mem, xraw.2.1,
          xraw.2.2, by simp [chapter09ArchFiniteToNormOneIdele]⟩
  · intro c
    obtain ⟨z, hz⟩ := chapter09NormOneIdealClassMap_surjective K c
    refine ⟨⟨QuotientGroup.mk z, ?_⟩, ?_⟩
    · change chapter09IdeleClassModule K (QuotientGroup.mk z) = 1
      rw [chapter09IdeleClassModule_apply]
      exact z.property
    · change chapter09IdeleClassIdealClassMap K (QuotientGroup.mk z) = c
      rw [chapter09IdeleClassIdealClassMap_apply]
      exact hz

theorem chapter09_compact_kernel_over_class_group
    (K : Type*) [Field K] [NumberField K] :
    Function.MulExact (chapter09ArchFiniteToClassNormOne K)
      (chapter09NormOneClassIdealClassMap K) := by
  exact (chapter09CompactKernel_short_exact K).exact

theorem chapter09NormOneClassIdealClassMap_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter09NormOneClassIdealClassMap K) := by
  exact (chapter09CompactKernel_short_exact K).right_surjective

private theorem chapter09_compact_kernel_archimedean_log_section
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

private theorem chapter09_compact_kernel_archimedean_representatives
    (K : Type*) [Field K] [NumberField K] :
    ∃ S : Set (chapter09KInfinityOne K), IsCompact S ∧
      ∀ x : Chapter09ArchimedeanUnitQuotient K, ∃ s ∈ S,
        QuotientGroup.mk' (chapter09ArchimedeanUnitEmbedding K).range s = x := by
  classical
  obtain ⟨s, hs, hslog⟩ := chapter09_compact_kernel_archimedean_log_section K
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

theorem chapter09ArchFiniteUnitKernel_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (Chapter09ArchFiniteUnitKernel K)) := by
  classical
  obtain ⟨Sarch, hSarch, harch⟩ :=
    chapter09_compact_kernel_archimedean_representatives K
  let D := (chapter09GlobalUnitDiagonal K).range
  let F : Chapter09ArchFiniteUnitNumerator K → Chapter09ArchFiniteUnitKernel K :=
    QuotientGroup.mk' D
  have hF : Continuous F := by
    exact QuotientGroup.continuous_mk
  have hprod : IsCompact
      (Sarch ×ˢ (Set.univ : Set (chapter09FiniteUnitIdeles K))) :=
    hSarch.prod (chapter09_finite_unit_ideles_compact K)
  let S : Set (Chapter09ArchFiniteUnitKernel K) :=
    F '' (Sarch ×ˢ (Set.univ : Set (chapter09FiniteUnitIdeles K)))
  have hS : IsCompact S := by
    exact hprod.image hF
  have hS_univ : S = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective D x
    obtain ⟨s, hs, hsq⟩ := harch
      (QuotientGroup.mk' (chapter09ArchimedeanUnitEmbedding K).range z.1)
    have hrel : z.1 / s ∈ (chapter09ArchimedeanUnitEmbedding K).range :=
      (QuotientGroup.eq_iff_div_mem).1 hsq.symm
    obtain ⟨u, hu⟩ := hrel
    let v : chapter09FiniteUnitIdeles K :=
      ⟨(chapter09FiniteUnitSubtypeEmbedding K u)⁻¹ * z.2.1,
        (chapter09FiniteUnitIdeles K).mul_mem
          ((chapter09FiniteUnitIdeles K).inv_mem
            (chapter09FiniteUnitSubtypeEmbedding K u).property)
          z.2.2⟩
    let w : Chapter09ArchFiniteUnitNumerator K := (s, v)
    have hfirst : chapter09ArchimedeanUnitEmbedding K u * s = z.1 := by
      calc
        chapter09ArchimedeanUnitEmbedding K u * s = (z.1 / s) * s := by rw [hu]
        _ = z.1 := by simp [div_eq_mul_inv, mul_assoc]
    have hsecond : chapter09FiniteUnitSubtypeEmbedding K u * v = z.2 := by
      apply Subtype.ext
      apply Units.ext
      change (chapter09FiniteUnitEmbedding K u : Chapter09FiniteAdele K) *
          (v.1 : Chapter09FiniteAdele K) = z.2.1
      simp [v, chapter09FiniteUnitSubtypeEmbedding]
    have hdiag : chapter09GlobalUnitDiagonal K u * w = z := by
      change (chapter09ArchimedeanUnitEmbedding K u,
          chapter09FiniteUnitSubtypeEmbedding K u) * (s, v) = z
      apply Prod.ext
      · simpa [w] using hfirst
      · simpa [w] using hsecond
    have hq : F w = x := by
      have hq' := congrArg (QuotientGroup.mk' D) hdiag
      change QuotientGroup.mk' D w = x
      rw [← hz]
      rw [(QuotientGroup.mk' D).map_mul] at hq'
      have hone : QuotientGroup.mk' D (chapter09GlobalUnitDiagonal K u) = 1 := by
        apply (QuotientGroup.eq_one_iff _).2
        exact ⟨u, rfl⟩
      rw [hone] at hq'
      calc
        F w = (1 : Chapter09ArchFiniteUnitKernel K) * F w :=
          (one_mul (F w)).symm
        _ = F z := hq'
    exact ⟨w, ⟨hs, Set.mem_univ _⟩, hq⟩
  rw [← hS_univ]
  exact hS

theorem chapter09KInfinityOne_is_archimedean_norm_one
    (K : Type*) [Field K] [NumberField K]
    (x : (Chapter09InfiniteAdele K)ˣ) :
    x ∈ chapter09KInfinityOne K ↔
      chapter09InfiniteIdeleModule x = 1 := by
  rfl

theorem chapter09CompactKernel_finite_factor_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (chapter09FiniteUnitIdeles K)) := by
  exact chapter09_finite_unit_ideles_compact K

theorem chapter09CompactKernel_archimedean_factor_compact_mod_units
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (Chapter09ArchimedeanUnitQuotient K)) := by
  exact chapter09_archimedean_unit_quotient_compact K

/- The quotient is structural rather than a canonical direct product: the
global-unit range is the diagonal gluing between the archimedean and finite
unit factors. -/

end

end LastLib.Book04AdelesAndIdeles.Chapter09
