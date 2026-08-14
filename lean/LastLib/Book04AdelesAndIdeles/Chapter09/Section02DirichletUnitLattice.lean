import LastLib.Book04AdelesAndIdeles.Chapter09.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter09

noncomputable section

open scoped BigOperators NNReal

open NumberField IsDedekindDomain

/-!
## 9.2. Dirichlet's unit lattice
-/

def chapter09LogHyperplane
    (K : Type*) [Field K] [NumberField K] :
    Submodule ℝ (InfinitePlace K → ℝ) where
  carrier := {t | ∑ v : InfinitePlace K, t v = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (∑ v : InfinitePlace K, (x v + y v)) = 0
    change (∑ v : InfinitePlace K, x v = 0) at hx
    change (∑ v : InfinitePlace K, y v = 0) at hy
    rw [Finset.sum_add_distrib, hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change (∑ v : InfinitePlace K, ((c • x) v)) = 0
    change (∑ v : InfinitePlace K, x v = 0) at hx
    simp only [Pi.smul_apply]
    rw [← Finset.smul_sum, hx, smul_zero]

theorem chapter09LogHyperplane_mem_iff
    {K : Type*} [Field K] [NumberField K] {t : InfinitePlace K → ℝ} :
    t ∈ chapter09LogHyperplane K ↔ ∑ v : InfinitePlace K, t v = 0 :=
  Iff.rfl

def chapter09InfiniteLogVector
    {K : Type*} [Field K] [NumberField K]
    (x : (Chapter09InfiniteAdele K)ˣ) : InfinitePlace K → ℝ :=
  fun v => Real.log
    (((chapter09NormUnit ((MulEquiv.piUnits x) v) ^ v.mult : Chapter09PositiveReal) :
      ℝ≥0) : ℝ)

def chapter09InfiniteLogMap
    (K : Type*) [Field K] [NumberField K] :
    (Chapter09InfiniteAdele K)ˣ →* Multiplicative (InfinitePlace K → ℝ) where
  toFun x := Multiplicative.ofAdd (chapter09InfiniteLogVector x)
  map_one' := by
    apply Multiplicative.ext
    change chapter09InfiniteLogVector (1 : (Chapter09InfiniteAdele K)ˣ) = 0
    funext v
    unfold chapter09InfiniteLogVector
    have hpi : MulEquiv.piUnits (1 : (Chapter09InfiniteAdele K)ˣ) = 1 :=
      (MulEquiv.piUnits).map_one
    rw [hpi]
    simp [chapter09NormUnit]
  map_mul' x y := by
    apply Multiplicative.ext
    change chapter09InfiniteLogVector (x * y) =
      chapter09InfiniteLogVector x + chapter09InfiniteLogVector y
    funext v
    unfold chapter09InfiniteLogVector
    have hpi : MulEquiv.piUnits (x * y) = MulEquiv.piUnits x * MulEquiv.piUnits y :=
      (MulEquiv.piUnits).map_mul x y
    rw [hpi]
    simp only [Pi.mul_apply]
    have hnorm : chapter09NormUnit ((MulEquiv.piUnits x) v *
        (MulEquiv.piUnits y) v) =
        chapter09NormUnit ((MulEquiv.piUnits x) v) *
          chapter09NormUnit ((MulEquiv.piUnits y) v) :=
      (chapter09NormUnitHom).map_mul _ _
    rw [hnorm, mul_pow]
    simp only [Units.val_mul, NNReal.coe_mul, Pi.add_apply]
    have hx0 : (((chapter09NormUnit ((MulEquiv.piUnits x) v) ^ v.mult :
        Chapter09PositiveReal) : ℝ≥0) : ℝ) ≠ 0 := by
      exact_mod_cast pow_ne_zero _
        (Units.ne_zero (chapter09NormUnit ((MulEquiv.piUnits x) v)))
    have hy0 : (((chapter09NormUnit ((MulEquiv.piUnits y) v) ^ v.mult :
        Chapter09PositiveReal) : ℝ≥0) : ℝ) ≠ 0 := by
      exact_mod_cast pow_ne_zero _
        (Units.ne_zero (chapter09NormUnit ((MulEquiv.piUnits y) v)))
    rw [Real.log_mul hx0 hy0]

@[simp]
theorem chapter09InfiniteLogMap_apply
    {K : Type*} [Field K] [NumberField K]
    (x : (Chapter09InfiniteAdele K)ˣ) :
    chapter09InfiniteLogMap K x = Multiplicative.ofAdd (chapter09InfiniteLogVector x) :=
  rfl

def chapter09RealSignGroup : Subgroup ℝˣ where
  carrier := {u | ‖(u : ℝ)‖ = 1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change ‖(u : ℝ)‖ = 1 at hu
    change ‖(v : ℝ)‖ = 1 at hv
    change ‖((u * v : ℝˣ) : ℝ)‖ = 1
    simp [Units.val_mul, hu, hv]
  inv_mem' := by
    intro u hu
    change ‖(u : ℝ)‖ = 1 at hu
    change ‖((u⁻¹ : ℝˣ) : ℝ)‖ = 1
    simp [norm_inv, hu]

def chapter09ComplexUnitCircle : Subgroup ℂˣ where
  carrier := {u | ‖(u : ℂ)‖ = 1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change ‖(u : ℂ)‖ = 1 at hu
    change ‖(v : ℂ)‖ = 1 at hv
    change ‖((u * v : ℂˣ) : ℂ)‖ = 1
    simp [Units.val_mul, hu, hv]
  inv_mem' := by
    intro u hu
    change ‖(u : ℂ)‖ = 1 at hu
    change ‖((u⁻¹ : ℂˣ) : ℂ)‖ = 1
    simp [norm_inv, hu]

abbrev Chapter09ArchimedeanPhaseModel
    (K : Type*) [Field K] [NumberField K] :=
  ({w : InfinitePlace K // NumberField.InfinitePlace.IsReal w} →
      chapter09RealSignGroup) ×
    ({w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w} →
      chapter09ComplexUnitCircle)

def chapter09InfiniteLogKernel
    (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter09InfiniteAdele K)ˣ :=
  (chapter09InfiniteLogMap K).ker

theorem chapter09_infinite_log_kernel_equiv_phase_model
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (chapter09InfiniteLogKernel K ≃*
      Chapter09ArchimedeanPhaseModel K) := by
  let rmap : ∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w},
      w.1.Completionˣ →* ℝˣ :=
    fun w => Units.map
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal w.2).toMonoidHom
  let cmap : ∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w},
      w.1.Completionˣ →* ℂˣ :=
    fun w => Units.map
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2).toMonoidHom
  have hlog (x : chapter09InfiniteLogKernel K) :
      chapter09InfiniteLogVector x.1 = 0 := by
    have hx : chapter09InfiniteLogMap K x.1 = 1 :=
      (MonoidHom.mem_ker).1 x.2
    change Multiplicative.ofAdd (chapter09InfiniteLogVector x.1) = 1 at hx
    exact congrArg Multiplicative.toAdd hx
  have hreal (x : chapter09InfiniteLogKernel K)
      (w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}) :
      ‖((rmap w ((MulEquiv.piUnits x.1) w.1) : ℝˣ) : ℝ)‖ = 1 := by
    have hx := congrFun (hlog x) w.1
    change Real.log
      (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1) ^ w.1.mult :
        Chapter09PositiveReal) : ℝ≥0) : ℝ) = 0 at hx
    rw [w.2.mult_eq_one, pow_one] at hx
    have hpos : 0 < (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1 :
        w.1.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
    have hnorm :
        ‖((rmap w ((MulEquiv.piUnits x.1) w.1) : ℝˣ) : ℝ)‖ =
          (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1 :
            w.1.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) := by
      change ‖(NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal w.2)
          ((MulEquiv.piUnits x.1) w.1 : w.1.Completion)‖ =
        ‖((MulEquiv.piUnits x.1) w.1 : w.1.Completion)‖
      have hd := (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal
        w.2).isometry_toFun.dist_eq (0 : w.1.Completion)
          ((MulEquiv.piUnits x.1) w.1 : w.1.Completion)
      have hzero :
          (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal w.2).toFun
              (0 : w.1.Completion) = 0 := by
        change NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal w.2 0 = 0
        simp
      rw [hzero] at hd
      simpa [dist_eq_norm, chapter09NormUnit] using hd
    rw [hnorm]
    exact Real.eq_one_of_pos_of_log_eq_zero hpos hx
  have hcomplex (x : chapter09InfiniteLogKernel K)
      (w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}) :
      ‖((cmap w ((MulEquiv.piUnits x.1) w.1) : ℂˣ) : ℂ)‖ = 1 := by
    have hx := congrFun (hlog x) w.1
    change Real.log
      (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1) ^ w.1.mult :
        Chapter09PositiveReal) : ℝ≥0) : ℝ) = 0 at hx
    rw [w.2.mult_eq_two] at hx
    have hpow :
        (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1) ^ (2 : ℕ) :
          Chapter09PositiveReal) : ℝ≥0) : ℝ) =
          (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1 :
            w.1.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) ^ (2 : ℕ) := by
      simp
    rw [hpow] at hx
    have hpos : 0 < (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1 :
        w.1.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
    have hlogbase :
        Real.log
          (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1 :
            w.1.Completionˣ) : ℝ≥0) : ℝ)) = 0 := by
      rw [Real.log_pow] at hx
      exact (mul_eq_zero.mp hx).resolve_left (by norm_num)
    have hbase :
        (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1 :
          w.1.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero hpos hlogbase
    have hnorm :
        ‖((cmap w ((MulEquiv.piUnits x.1) w.1) : ℂˣ) : ℂ)‖ =
          (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1 :
            w.1.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) := by
      change ‖(NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.2)
          ((MulEquiv.piUnits x.1) w.1 : w.1.Completion)‖ =
        ‖((MulEquiv.piUnits x.1) w.1 : w.1.Completion)‖
      have hd := (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        w.2).isometry_toFun.dist_eq (0 : w.1.Completion)
          ((MulEquiv.piUnits x.1) w.1 : w.1.Completion)
      have hzero :
          (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.2).toFun
              (0 : w.1.Completion) = 0 := by
        change NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2 0 = 0
        simp
      rw [hzero] at hd
      simpa [dist_eq_norm, chapter09NormUnit] using hd
    rw [hnorm, hbase]
  let e0 :
      (Chapter09InfiniteAdele K)ˣ ≃*
        (NumberField.mixedEmbedding.mixedSpace K)ˣ :=
    Units.mapEquiv (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).toMulEquiv
  let e1 :
      (Chapter09InfiniteAdele K)ˣ ≃*
        ((∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}, ℝ)ˣ ×
          (∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}, ℂ)ˣ) :=
    e0.trans MulEquiv.prodUnits
  let pR :
      (∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}, ℝ)ˣ ≃*
        ∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}, ℝˣ :=
    MulEquiv.piUnits
  let pC :
      (∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}, ℂ)ˣ ≃*
        ∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}, ℂˣ :=
    MulEquiv.piUnits
  let e2 :
      (Chapter09InfiniteAdele K)ˣ ≃*
        ((∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}, ℝˣ) ×
          (∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}, ℂˣ)) :=
    e1.trans (MulEquiv.prodCongr pR pC)
  have hreal' (x : chapter09InfiniteLogKernel K)
      (w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}) :
      ‖(((e2 x.1).1 w : ℝˣ) : ℝ)‖ = 1 := by
    change ‖((rmap w ((MulEquiv.piUnits x.1) w.1) : ℝˣ) : ℝ)‖ = 1
    exact hreal x w
  have hcomplex' (x : chapter09InfiniteLogKernel K)
      (w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}) :
      ‖(((e2 x.1).2 w : ℂˣ) : ℂ)‖ = 1 := by
    change ‖((cmap w ((MulEquiv.piUnits x.1) w.1) : ℂˣ) : ℂ)‖ = 1
    exact hcomplex x w
  let f : chapter09InfiniteLogKernel K →*
      Chapter09ArchimedeanPhaseModel K :=
    { toFun := fun x =>
        ((fun w => ⟨(e2 x.1).1 w, hreal' x w⟩),
          (fun w => ⟨(e2 x.1).2 w, hcomplex' x w⟩))
      map_one' := by
        apply Prod.ext <;> funext w <;> apply Subtype.ext <;> simp
      map_mul' := by
        intro x y
        apply Prod.ext <;> funext w <;> apply Subtype.ext <;> simp }
  let g0 : Chapter09ArchimedeanPhaseModel K → (Chapter09InfiniteAdele K)ˣ :=
    fun z => e2.symm
      ((fun w => (z.1 w : ℝˣ)), (fun w => (z.2 w : ℂˣ)))
  have hcoordR (z : Chapter09ArchimedeanPhaseModel K)
      (w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}) :
      rmap w ((MulEquiv.piUnits (g0 z)) w.1) = z.1 w := by
    have h := congrFun (congrArg Prod.fst (e2.apply_symm_apply
      ((fun w => (z.1 w : ℝˣ)), (fun w => (z.2 w : ℂˣ))))) w
    change rmap w ((MulEquiv.piUnits (g0 z)) w.1) = z.1 w at h
    exact h
  have hcoordC (z : Chapter09ArchimedeanPhaseModel K)
      (w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}) :
      cmap w ((MulEquiv.piUnits (g0 z)) w.1) = z.2 w := by
    have h := congrFun (congrArg Prod.snd (e2.apply_symm_apply
      ((fun w => (z.1 w : ℝˣ)), (fun w => (z.2 w : ℂˣ))))) w
    change cmap w ((MulEquiv.piUnits (g0 z)) w.1) = z.2 w at h
    exact h
  have hglog (z : Chapter09ArchimedeanPhaseModel K) :
      chapter09InfiniteLogVector (g0 z) = 0 := by
    funext v
    obtain hv | hv := v.isReal_or_isComplex
    · let w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w} := ⟨v, hv⟩
      have hmap :
          ‖((rmap w ((MulEquiv.piUnits (g0 z)) v) : ℝˣ) : ℝ)‖ =
            ‖((MulEquiv.piUnits (g0 z)) v : v.Completion)‖ := by
        change ‖(NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal w.2)
            ((MulEquiv.piUnits (g0 z)) v : v.Completion)‖ =
          ‖((MulEquiv.piUnits (g0 z)) v : v.Completion)‖
        have hd := (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal
          w.2).isometry_toFun.dist_eq (0 : v.Completion)
            ((MulEquiv.piUnits (g0 z)) v : v.Completion)
        have hzero :
            (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal w.2).toFun
                (0 : v.Completion) = 0 := by
          change NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal w.2 0 = 0
          simp
        rw [hzero] at hd
        simpa [dist_eq_norm] using hd
      have hnorm : ‖((MulEquiv.piUnits (g0 z)) v : v.Completion)‖ = 1 := by
        calc
          ‖((MulEquiv.piUnits (g0 z)) v : v.Completion)‖ =
              ‖((rmap w ((MulEquiv.piUnits (g0 z)) v) : ℝˣ) : ℝ)‖ := hmap.symm
          _ = ‖((z.1 w : ℝˣ) : ℝ)‖ := by rw [hcoordR z w]
          _ = 1 := (z.1 w).property
      change Real.log
        (((chapter09NormUnit ((MulEquiv.piUnits (g0 z)) v) ^ v.mult :
          Chapter09PositiveReal) : ℝ≥0) : ℝ) = 0
      rw [hv.mult_eq_one, pow_one]
      have hbase :
          (((chapter09NormUnit ((MulEquiv.piUnits (g0 z)) v :
            v.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) = 1 := by
        simpa [chapter09NormUnit] using hnorm
      rw [hbase, Real.log_one]
    · let w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w} := ⟨v, hv⟩
      have hmap :
          ‖((cmap w ((MulEquiv.piUnits (g0 z)) v) : ℂˣ) : ℂ)‖ =
            ‖((MulEquiv.piUnits (g0 z)) v : v.Completion)‖ := by
        change ‖(NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.2)
            ((MulEquiv.piUnits (g0 z)) v : v.Completion)‖ =
          ‖((MulEquiv.piUnits (g0 z)) v : v.Completion)‖
        have hd := (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          w.2).isometry_toFun.dist_eq (0 : v.Completion)
            ((MulEquiv.piUnits (g0 z)) v : v.Completion)
        have hzero :
            (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.2).toFun
                (0 : v.Completion) = 0 := by
          change NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2 0 = 0
          simp
        rw [hzero] at hd
        simpa [dist_eq_norm] using hd
      have hnorm : ‖((MulEquiv.piUnits (g0 z)) v : v.Completion)‖ = 1 := by
        calc
          ‖((MulEquiv.piUnits (g0 z)) v : v.Completion)‖ =
              ‖((cmap w ((MulEquiv.piUnits (g0 z)) v) : ℂˣ) : ℂ)‖ := hmap.symm
          _ = ‖((z.2 w : ℂˣ) : ℂ)‖ := by rw [hcoordC z w]
          _ = 1 := (z.2 w).property
      change Real.log
        (((chapter09NormUnit ((MulEquiv.piUnits (g0 z)) v) ^ v.mult :
          Chapter09PositiveReal) : ℝ≥0) : ℝ) = 0
      rw [hv.mult_eq_two]
      have hbase :
          (((chapter09NormUnit ((MulEquiv.piUnits (g0 z)) v :
            v.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) = 1 := by
        simpa [chapter09NormUnit] using hnorm
      have hpow :
          (((chapter09NormUnit ((MulEquiv.piUnits (g0 z)) v :
            v.Completionˣ) ^ (2 : ℕ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) =
            (((chapter09NormUnit ((MulEquiv.piUnits (g0 z)) v :
              v.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) ^ (2 : ℕ) := by
        simp
      rw [hpow, hbase]
      norm_num
  let g : Chapter09ArchimedeanPhaseModel K →*
      chapter09InfiniteLogKernel K :=
    { toFun := fun z => ⟨g0 z, hglog z⟩
      map_one' := by
        apply Subtype.ext
        change e2.symm ((fun _ => 1), (fun _ => 1)) = 1
        rw [← e2.symm.map_one]
        congr 1
      map_mul' := by
        intro z z'
        apply Subtype.ext
        change e2.symm
            ((fun w => ((z.1 w : ℝˣ) * (z'.1 w : ℝˣ))),
              (fun w => ((z.2 w : ℂˣ) * (z'.2 w : ℂˣ)))) =
          e2.symm ((fun w => (z.1 w : ℝˣ)), (fun w => (z.2 w : ℂˣ))) *
            e2.symm ((fun w => (z'.1 w : ℝˣ)), (fun w => (z'.2 w : ℂˣ)))
        have hprod :
            ((fun w => ((z.1 w : ℝˣ) * (z'.1 w : ℝˣ))),
              (fun w => ((z.2 w : ℂˣ) * (z'.2 w : ℂˣ)))) =
            ((fun w => (z.1 w : ℝˣ)), (fun w => (z.2 w : ℂˣ))) *
              ((fun w => (z'.1 w : ℝˣ)), (fun w => (z'.2 w : ℂˣ))) := by
          ext w <;> rfl
        rw [hprod, e2.symm.map_mul] }
  let e : chapter09InfiniteLogKernel K ≃*
      Chapter09ArchimedeanPhaseModel K :=
    { toFun := f
      invFun := g
      left_inv := by
        intro x
        apply Subtype.ext
        apply e2.injective
        simp [f, g, g0]
      right_inv := by
        intro z
        apply Prod.ext
        · funext w
          apply Subtype.ext
          have h := congrFun (congrArg Prod.fst (e2.apply_symm_apply
            ((fun w => (z.1 w : ℝˣ)), (fun w => (z.2 w : ℂˣ))))) w
          change (e2 (g0 z)).1 w = z.1 w
          exact h
        · funext w
          apply Subtype.ext
          have h := congrFun (congrArg Prod.snd (e2.apply_symm_apply
            ((fun w => (z.1 w : ℝˣ)), (fun w => (z.2 w : ℂˣ))))) w
          change (e2 (g0 z)).2 w = z.2 w
          exact h
      map_mul' := by
        intro x y
        exact f.map_mul x y }
  exact ⟨e⟩

/-! The algebraic phase identification is also an identification of the
subgroup topologies; this is the form needed to transfer compactness. -/
theorem chapter09_infinite_log_kernel_continuous_equiv_phase_model
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (chapter09InfiniteLogKernel K ≃ₜ*
      Chapter09ArchimedeanPhaseModel K) := by
  classical
  let rmap : ∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w},
      w.1.Completionˣ →* ℝˣ :=
    fun w => Units.map
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal w.2).toMonoidHom
  let cmap : ∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w},
      w.1.Completionˣ →* ℂˣ :=
    fun w => Units.map
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2).toMonoidHom
  let hbase :
      Chapter09InfiniteAdele K ≃ₜ NumberField.mixedEmbedding.mixedSpace K :=
    (Homeomorph.piEquivPiSubtypeProd
      (fun (v : InfinitePlace K) => NumberField.InfinitePlace.IsReal v)
      (fun (v : InfinitePlace K) => v.Completion)).trans
      (Homeomorph.prodCongr
        (Homeomorph.piCongrRight
          (fun w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w} =>
            (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal
              w.2).toHomeomorph))
        ((Homeomorph.piCongrRight
          (fun w : {w : InfinitePlace K //
              ¬ NumberField.InfinitePlace.IsReal w} =>
          (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex
              (NumberField.InfinitePlace.not_isReal_iff_isComplex.1 w.2)).toHomeomorph)).trans
          (Homeomorph.piCongrLeft
            (Y := fun _ : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w} => ℂ)
            (Equiv.subtypeEquivRight
              (fun _ => NumberField.InfinitePlace.not_isReal_iff_isComplex)))))
  let ce :
      Chapter09InfiniteAdele K ≃ₜ* NumberField.mixedEmbedding.mixedSpace K :=
    ContinuousMulEquiv.mk
      (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).toMulEquiv
      hbase.continuous hbase.symm.continuous
  let ce0 : (Chapter09InfiniteAdele K)ˣ ≃ₜ*
      (NumberField.mixedEmbedding.mixedSpace K)ˣ :=
    Units.mapContinuousMulEquiv ce
  let cpiR :
      (∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}, ℝ)ˣ ≃ₜ*
        ∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}, ℝˣ :=
    ContinuousMulEquiv.piUnits
  let cpiC :
      (∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}, ℂ)ˣ ≃ₜ*
        ∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}, ℂˣ :=
    ContinuousMulEquiv.piUnits
  let cprod0 :
      (NumberField.mixedEmbedding.mixedSpace K)ˣ ≃ₜ*
        ((∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}, ℝ)ˣ ×
          (∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}, ℂ)ˣ) :=
    ContinuousMulEquiv.mk MulEquiv.prodUnits
      (Homeomorph.prodUnits :
        (NumberField.mixedEmbedding.mixedSpace K)ˣ ≃ₜ
          ((∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}, ℝ)ˣ ×
            (∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}, ℂ)ˣ)).continuous
      (Homeomorph.prodUnits.symm :
        ((∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}, ℝ)ˣ ×
            (∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}, ℂ)ˣ) ≃ₜ
          (NumberField.mixedEmbedding.mixedSpace K)ˣ).continuous
  let cprod1 :
      ((∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}, ℝ)ˣ ×
        (∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}, ℂ)ˣ) ≃ₜ*
        ((∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}, ℝˣ) ×
          (∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}, ℂˣ)) :=
    ContinuousMulEquiv.mk
      (MulEquiv.prodCongr
        (MulEquiv.piUnits :
          (∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}, ℝ)ˣ ≃*
            ∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}, ℝˣ)
        (MulEquiv.piUnits :
          (∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}, ℂ)ˣ ≃*
            ∀ w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}, ℂˣ))
      ((cpiR.continuous.comp continuous_fst).prodMk
        (cpiC.continuous.comp continuous_snd))
      ((cpiR.symm.continuous.comp continuous_fst).prodMk
        (cpiC.symm.continuous.comp continuous_snd))
  let cprod := ce0.trans cprod0 |>.trans cprod1
  have hlog (x : chapter09InfiniteLogKernel K) :
      chapter09InfiniteLogVector x.1 = 0 := by
    have hx : chapter09InfiniteLogMap K x.1 = 1 :=
      (MonoidHom.mem_ker).1 x.2
    change Multiplicative.ofAdd (chapter09InfiniteLogVector x.1) = 1 at hx
    exact congrArg Multiplicative.toAdd hx
  have hreal (x : chapter09InfiniteLogKernel K)
      (w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}) :
      ‖((rmap w ((MulEquiv.piUnits x.1) w.1) : ℝˣ) : ℝ)‖ = 1 := by
    have hx := congrFun (hlog x) w.1
    change Real.log
      (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1) ^ w.1.mult :
        Chapter09PositiveReal) : ℝ≥0) : ℝ) = 0 at hx
    rw [w.2.mult_eq_one, pow_one] at hx
    have hpos : 0 < (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1 :
        w.1.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
    have hnorm :
        ‖((rmap w ((MulEquiv.piUnits x.1) w.1) : ℝˣ) : ℝ)‖ =
          (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1 :
            w.1.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) := by
      change ‖(NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal w.2)
          ((MulEquiv.piUnits x.1) w.1 : w.1.Completion)‖ =
        ‖((MulEquiv.piUnits x.1) w.1 : w.1.Completion)‖
      have hd := (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal
        w.2).isometry_toFun.dist_eq (0 : w.1.Completion)
          ((MulEquiv.piUnits x.1) w.1 : w.1.Completion)
      have hzero :
          (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal w.2).toFun
              (0 : w.1.Completion) = 0 := by
        change NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal w.2 0 = 0
        simp
      rw [hzero] at hd
      simpa [dist_eq_norm, chapter09NormUnit] using hd
    rw [hnorm]
    exact Real.eq_one_of_pos_of_log_eq_zero hpos hx
  have hcomplex (x : chapter09InfiniteLogKernel K)
      (w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}) :
      ‖((cmap w ((MulEquiv.piUnits x.1) w.1) : ℂˣ) : ℂ)‖ = 1 := by
    have hx := congrFun (hlog x) w.1
    change Real.log
      (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1) ^ w.1.mult :
        Chapter09PositiveReal) : ℝ≥0) : ℝ) = 0 at hx
    rw [w.2.mult_eq_two] at hx
    have hpow :
        (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1) ^ (2 : ℕ) :
          Chapter09PositiveReal) : ℝ≥0) : ℝ) =
          (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1 :
            w.1.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) ^ (2 : ℕ) := by
      simp
    rw [hpow] at hx
    have hpos : 0 < (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1 :
        w.1.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
    have hlogbase :
        Real.log
          (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1 :
            w.1.Completionˣ) : ℝ≥0) : ℝ)) = 0 := by
      rw [Real.log_pow] at hx
      exact (mul_eq_zero.mp hx).resolve_left (by norm_num)
    have hbase :
        (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1 :
          w.1.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero hpos hlogbase
    have hnorm :
        ‖((cmap w ((MulEquiv.piUnits x.1) w.1) : ℂˣ) : ℂ)‖ =
          (((chapter09NormUnit ((MulEquiv.piUnits x.1) w.1 :
            w.1.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) := by
      change ‖(NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.2)
          ((MulEquiv.piUnits x.1) w.1 : w.1.Completion)‖ =
        ‖((MulEquiv.piUnits x.1) w.1 : w.1.Completion)‖
      have hd := (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        w.2).isometry_toFun.dist_eq (0 : w.1.Completion)
          ((MulEquiv.piUnits x.1) w.1 : w.1.Completion)
      have hzero :
          (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.2).toFun
              (0 : w.1.Completion) = 0 := by
        change NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2 0 = 0
        simp
      rw [hzero] at hd
      simpa [dist_eq_norm, chapter09NormUnit] using hd
    rw [hnorm, hbase]
  have hreal' (x : chapter09InfiniteLogKernel K)
      (w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}) :
      ‖(((cprod x.1).1 w : ℝˣ) : ℝ)‖ = 1 := by
    change ‖((rmap w ((MulEquiv.piUnits x.1) w.1) : ℝˣ) : ℝ)‖ = 1
    exact hreal x w
  have hcomplex' (x : chapter09InfiniteLogKernel K)
      (w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}) :
      ‖(((cprod x.1).2 w : ℂˣ) : ℂ)‖ = 1 := by
    change ‖((cmap w ((MulEquiv.piUnits x.1) w.1) : ℂˣ) : ℂ)‖ = 1
    exact hcomplex x w
  let f : chapter09InfiniteLogKernel K →*
      Chapter09ArchimedeanPhaseModel K :=
    { toFun := fun x =>
        ((fun w => ⟨(cprod x.1).1 w, hreal' x w⟩),
          (fun w => ⟨(cprod x.1).2 w, hcomplex' x w⟩))
      map_one' := by
        apply Prod.ext <;> funext w <;> apply Subtype.ext <;> simp
      map_mul' := by
        intro x y
        apply Prod.ext <;> funext w <;> apply Subtype.ext <;> simp }
  let g0 : Chapter09ArchimedeanPhaseModel K → (Chapter09InfiniteAdele K)ˣ :=
    fun z => cprod.symm
      ((fun w => (z.1 w : ℝˣ)), (fun w => (z.2 w : ℂˣ)))
  have hcoordR (z : Chapter09ArchimedeanPhaseModel K)
      (w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w}) :
      rmap w ((MulEquiv.piUnits (g0 z)) w.1) = z.1 w := by
    have h := congrFun (congrArg Prod.fst (cprod.apply_symm_apply
      ((fun w => (z.1 w : ℝˣ)), (fun w => (z.2 w : ℂˣ))))) w
    change rmap w ((MulEquiv.piUnits (g0 z)) w.1) = z.1 w at h
    exact h
  have hcoordC (z : Chapter09ArchimedeanPhaseModel K)
      (w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w}) :
      cmap w ((MulEquiv.piUnits (g0 z)) w.1) = z.2 w := by
    have h := congrFun (congrArg Prod.snd (cprod.apply_symm_apply
      ((fun w => (z.1 w : ℝˣ)), (fun w => (z.2 w : ℂˣ))))) w
    change cmap w ((MulEquiv.piUnits (g0 z)) w.1) = z.2 w at h
    exact h
  have hglog (z : Chapter09ArchimedeanPhaseModel K) :
      chapter09InfiniteLogVector (g0 z) = 0 := by
    funext v
    obtain hv | hv := v.isReal_or_isComplex
    · let w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w} := ⟨v, hv⟩
      have hmap :
          ‖((rmap w ((MulEquiv.piUnits (g0 z)) v) : ℝˣ) : ℝ)‖ =
            ‖((MulEquiv.piUnits (g0 z)) v : v.Completion)‖ := by
        change ‖(NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal w.2)
            ((MulEquiv.piUnits (g0 z)) v : v.Completion)‖ =
          ‖((MulEquiv.piUnits (g0 z)) v : v.Completion)‖
        have hd := (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal
          w.2).isometry_toFun.dist_eq (0 : v.Completion)
            ((MulEquiv.piUnits (g0 z)) v : v.Completion)
        have hzero :
            (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal w.2).toFun
                (0 : v.Completion) = 0 := by
          change NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal w.2 0 = 0
          simp
        rw [hzero] at hd
        simpa [dist_eq_norm] using hd
      have hnorm : ‖((MulEquiv.piUnits (g0 z)) v : v.Completion)‖ = 1 := by
        calc
          ‖((MulEquiv.piUnits (g0 z)) v : v.Completion)‖ =
              ‖((rmap w ((MulEquiv.piUnits (g0 z)) v) : ℝˣ) : ℝ)‖ := hmap.symm
          _ = ‖((z.1 w : ℝˣ) : ℝ)‖ := by rw [hcoordR z w]
          _ = 1 := (z.1 w).property
      change Real.log
        (((chapter09NormUnit ((MulEquiv.piUnits (g0 z)) v) ^ v.mult :
          Chapter09PositiveReal) : ℝ≥0) : ℝ) = 0
      rw [hv.mult_eq_one, pow_one]
      have hbase :
          (((chapter09NormUnit ((MulEquiv.piUnits (g0 z)) v :
            v.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) = 1 := by
        simpa [chapter09NormUnit] using hnorm
      rw [hbase, Real.log_one]
    · let w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w} := ⟨v, hv⟩
      have hmap :
          ‖((cmap w ((MulEquiv.piUnits (g0 z)) v) : ℂˣ) : ℂ)‖ =
            ‖((MulEquiv.piUnits (g0 z)) v : v.Completion)‖ := by
        change ‖(NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.2)
            ((MulEquiv.piUnits (g0 z)) v : v.Completion)‖ =
          ‖((MulEquiv.piUnits (g0 z)) v : v.Completion)‖
        have hd := (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          w.2).isometry_toFun.dist_eq (0 : v.Completion)
            ((MulEquiv.piUnits (g0 z)) v : v.Completion)
        have hzero :
            (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.2).toFun
                (0 : v.Completion) = 0 := by
          change NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2 0 = 0
          simp
        rw [hzero] at hd
        simpa [dist_eq_norm] using hd
      have hnorm : ‖((MulEquiv.piUnits (g0 z)) v : v.Completion)‖ = 1 := by
        calc
          ‖((MulEquiv.piUnits (g0 z)) v : v.Completion)‖ =
              ‖((cmap w ((MulEquiv.piUnits (g0 z)) v) : ℂˣ) : ℂ)‖ := hmap.symm
          _ = ‖((z.2 w : ℂˣ) : ℂ)‖ := by rw [hcoordC z w]
          _ = 1 := (z.2 w).property
      change Real.log
        (((chapter09NormUnit ((MulEquiv.piUnits (g0 z)) v) ^ v.mult :
          Chapter09PositiveReal) : ℝ≥0) : ℝ) = 0
      rw [hv.mult_eq_two]
      have hbase :
          (((chapter09NormUnit ((MulEquiv.piUnits (g0 z)) v :
            v.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) = 1 := by
        simpa [chapter09NormUnit] using hnorm
      have hpow :
          (((chapter09NormUnit ((MulEquiv.piUnits (g0 z)) v :
            v.Completionˣ) ^ (2 : ℕ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) =
            (((chapter09NormUnit ((MulEquiv.piUnits (g0 z)) v :
              v.Completionˣ) : Chapter09PositiveReal) : ℝ≥0) : ℝ) ^ (2 : ℕ) := by
        simp
      rw [hpow, hbase]
      norm_num
  let g : Chapter09ArchimedeanPhaseModel K →*
      chapter09InfiniteLogKernel K :=
    { toFun := fun z => ⟨g0 z, hglog z⟩
      map_one' := by
        apply Subtype.ext
        change cprod.symm ((fun _ => 1), (fun _ => 1)) = 1
        rw [← cprod.symm.map_one]
        congr 1
      map_mul' := by
        intro z z'
        apply Subtype.ext
        change cprod.symm
            ((fun w => ((z.1 w : ℝˣ) * (z'.1 w : ℝˣ))),
              (fun w => ((z.2 w : ℂˣ) * (z'.2 w : ℂˣ)))) =
          cprod.symm ((fun w => (z.1 w : ℝˣ)), (fun w => (z.2 w : ℂˣ))) *
            cprod.symm ((fun w => (z'.1 w : ℝˣ)), (fun w => (z'.2 w : ℂˣ)))
        have hprod :
            ((fun w => ((z.1 w : ℝˣ) * (z'.1 w : ℝˣ))),
              (fun w => ((z.2 w : ℂˣ) * (z'.2 w : ℂˣ)))) =
            ((fun w => (z.1 w : ℝˣ)), (fun w => (z.2 w : ℂˣ))) *
              ((fun w => (z'.1 w : ℝˣ)), (fun w => (z'.2 w : ℂˣ))) := by
          ext w <;> rfl
        rw [hprod]
        exact cprod.symm.toMulEquiv.map_mul _ _ }
  have hf_cont : Continuous (f : chapter09InfiniteLogKernel K →
      Chapter09ArchimedeanPhaseModel K) := by
    have hc1 : Continuous (fun x : chapter09InfiniteLogKernel K =>
        (cprod x.1).1) :=
      cprod.continuous.comp continuous_subtype_val |>.fst
    have hc2 : Continuous (fun x : chapter09InfiniteLogKernel K =>
        (cprod x.1).2) :=
      cprod.continuous.comp continuous_subtype_val |>.snd
    have hR : Continuous (fun x : chapter09InfiniteLogKernel K =>
        (fun w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w} =>
          (⟨(cprod x.1).1 w, hreal' x w⟩ : chapter09RealSignGroup))) := by
      apply continuous_pi
      intro w
      exact ((continuous_apply w).comp hc1).subtype_mk (fun x => hreal' x w)
    have hC : Continuous (fun x : chapter09InfiniteLogKernel K =>
        (fun w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w} =>
          (⟨(cprod x.1).2 w, hcomplex' x w⟩ : chapter09ComplexUnitCircle))) := by
      apply continuous_pi
      intro w
      exact ((continuous_apply w).comp hc2).subtype_mk (fun x => hcomplex' x w)
    change Continuous (fun x : chapter09InfiniteLogKernel K =>
      ((fun w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w} =>
          (⟨(cprod x.1).1 w, hreal' x w⟩ : chapter09RealSignGroup)),
        (fun w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w} =>
          (⟨(cprod x.1).2 w, hcomplex' x w⟩ : chapter09ComplexUnitCircle))))
    exact hR.prodMk hC
  have hg0_cont : Continuous g0 := by
    have hR : Continuous (fun z : Chapter09ArchimedeanPhaseModel K =>
        fun w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w} =>
          (z.1 w : ℝˣ)) := by
      apply continuous_pi
      intro w
      exact continuous_subtype_val.comp ((continuous_apply w).comp continuous_fst)
    have hC : Continuous (fun z : Chapter09ArchimedeanPhaseModel K =>
        fun w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w} =>
          (z.2 w : ℂˣ)) := by
      apply continuous_pi
      intro w
      exact continuous_subtype_val.comp ((continuous_apply w).comp continuous_snd)
    change Continuous (fun z : Chapter09ArchimedeanPhaseModel K =>
      cprod.symm
        ((fun w : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w} =>
            (z.1 w : ℝˣ)),
          (fun w : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w} =>
            (z.2 w : ℂˣ))))
    exact cprod.symm.continuous.comp (hR.prodMk hC)
  have hg_cont : Continuous (g : Chapter09ArchimedeanPhaseModel K →
      chapter09InfiniteLogKernel K) := by
    change Continuous (fun z => (⟨g0 z, hglog z⟩ : chapter09InfiniteLogKernel K))
    exact hg0_cont.subtype_mk (fun z => hglog z)
  let e : chapter09InfiniteLogKernel K ≃*
      Chapter09ArchimedeanPhaseModel K :=
    { toFun := f
      invFun := g
      left_inv := by
        intro x
        apply Subtype.ext
        apply cprod.injective
        simp [f, g, g0]
      right_inv := by
        intro z
        apply Prod.ext
        · funext w
          apply Subtype.ext
          have h := congrFun (congrArg Prod.fst (cprod.apply_symm_apply
            ((fun w => (z.1 w : ℝˣ)), (fun w => (z.2 w : ℂˣ))))) w
          change (cprod (g0 z)).1 w = z.1 w
          exact h
        · funext w
          apply Subtype.ext
          have h := congrFun (congrArg Prod.snd (cprod.apply_symm_apply
            ((fun w => (z.1 w : ℝˣ)), (fun w => (z.2 w : ℂˣ))))) w
          change (cprod (g0 z)).2 w = z.2 w
          exact h
      map_mul' := by
        intro x y
        exact f.map_mul x y }
  exact ⟨ContinuousMulEquiv.mk e hf_cont hg_cont⟩

theorem chapter09_infinite_log_kernel_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (chapter09InfiniteLogKernel K)) := by
  classical
  have hunitSphere (F : Type) [NormedField F] [ProperSpace F] :
      IsCompact {u : Fˣ | ‖(u : F)‖ = 1} := by
    have hS : IsCompact (Metric.sphere (0 : F) 1) := isCompact_sphere _ _
    have hOp : IsCompact (MulOpposite.op '' Metric.sphere (0 : F) 1) :=
      hS.image MulOpposite.continuous_op
    have hprod : IsCompact
        (Metric.sphere (0 : F) 1 ×ˢ
          (MulOpposite.op '' Metric.sphere (0 : F) 1)) :=
      hS.prod hOp
    have hpre := Units.isClosedEmbedding_embedProduct.isCompact_preimage hprod
    have hEq :
        (Units.embedProduct F) ⁻¹'
            (Metric.sphere (0 : F) 1 ×ˢ
              (MulOpposite.op '' Metric.sphere (0 : F) 1)) =
          {u : Fˣ | ‖(u : F)‖ = 1} := by
      ext u
      constructor
      · intro hu
        have hu1 : (u : F) ∈ Metric.sphere (0 : F) 1 := hu.1
        simpa [Metric.mem_sphere, dist_zero_right, dist_eq_norm] using hu1
      · intro hu
        change ‖(u : F)‖ = 1 at hu
        have hu1 : (u : F) ∈ Metric.sphere (0 : F) 1 := by
          simpa [Metric.mem_sphere, dist_zero_right, dist_eq_norm] using hu
        have huinv : (u : F)⁻¹ ∈ Metric.sphere (0 : F) 1 := by
          simpa [Metric.mem_sphere, dist_zero_right, dist_eq_norm, norm_inv] using hu
        change Units.embedProduct F u ∈
          Metric.sphere (0 : F) 1 ×ˢ
            (MulOpposite.op '' Metric.sphere (0 : F) 1)
        rw [Units.embedProduct_apply]
        refine ⟨hu1, ?_⟩
        refine ⟨(u : F)⁻¹, huinv, ?_⟩
        simp
    rw [hEq] at hpre
    exact hpre
  have hR : IsCompact {u : ℝˣ | ‖(u : ℝ)‖ = 1} := hunitSphere ℝ
  have hC : IsCompact {u : ℂˣ | ‖(u : ℂ)‖ = 1} := hunitSphere ℂ
  have hsR : IsCompact (Set.univ : Set chapter09RealSignGroup) := by
    rw [Subtype.isCompact_iff]
    simpa [chapter09RealSignGroup] using hR
  have hsC : IsCompact (Set.univ : Set chapter09ComplexUnitCircle) := by
    rw [Subtype.isCompact_iff]
    simpa [chapter09ComplexUnitCircle] using hC
  have hfR : IsCompact (Set.univ :
      Set ({w : InfinitePlace K // NumberField.InfinitePlace.IsReal w} →
        chapter09RealSignGroup)) := by
    simpa using (isCompact_univ_pi
      (fun _ : {w : InfinitePlace K // NumberField.InfinitePlace.IsReal w} => hsR))
  have hfC : IsCompact (Set.univ :
      Set ({w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w} →
        chapter09ComplexUnitCircle)) := by
    simpa using (isCompact_univ_pi
      (fun _ : {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w} => hsC))
  have hphase : IsCompact (Set.univ : Set (Chapter09ArchimedeanPhaseModel K)) := by
    simpa using hfR.prod hfC
  let e := Classical.choice
    (chapter09_infinite_log_kernel_continuous_equiv_phase_model K)
  have himage := hphase.image e.symm.continuous
  simpa [Set.image_univ] using himage

def chapter09GlobalUnitLogEmbeddingRaw
    (K : Type*) [Field K] [NumberField K] :
    Additive ((𝓞 K)ˣ) →+ (InfinitePlace K → ℝ) where
  toFun u := chapter09InfiniteLogVector (chapter09InfiniteUnitEmbedding K u.toMul)
  map_zero' := by
    change chapter09InfiniteLogVector (chapter09InfiniteUnitEmbedding K 1) = 0
    exact congrArg (fun z : Multiplicative (InfinitePlace K → ℝ) => z)
      ((chapter09InfiniteLogMap K).map_one)
  map_add' u v := by
    rw [toMul_add, (chapter09InfiniteUnitEmbedding K).map_mul]
    have h := (chapter09InfiniteLogMap K).map_mul
      (chapter09InfiniteUnitEmbedding K u.toMul)
      (chapter09InfiniteUnitEmbedding K v.toMul)
    exact congrArg (fun z : Multiplicative (InfinitePlace K → ℝ) => z) h

def chapter09GlobalUnitLogEmbedding
    (K : Type*) [Field K] [NumberField K] :
    Additive ((𝓞 K)ˣ) →+ chapter09LogHyperplane K where
  toFun u := ⟨chapter09GlobalUnitLogEmbeddingRaw K u, by
    rw [chapter09LogHyperplane_mem_iff]
    change (∑ v : InfinitePlace K,
      Real.log ((((chapter09NormUnit
        ((MulEquiv.piUnits (chapter09InfiniteUnitEmbedding K u.toMul)) v) ^ v.mult :
          Chapter09PositiveReal) : ℝ≥0) : ℝ))) = 0
    have hmodule := (chapter09ArchimedeanUnitEmbedding K u.toMul).property
    change chapter09InfiniteIdeleModule
      (chapter09InfiniteUnitEmbedding K u.toMul) = 1 at hmodule
    have hprod :
        (∏ v : InfinitePlace K,
          ((((chapter09NormUnit
            ((MulEquiv.piUnits (chapter09InfiniteUnitEmbedding K u.toMul)) v) ^ v.mult :
              Chapter09PositiveReal) : ℝ≥0) : ℝ))) = 1 := by
      have h := congrArg (fun z : Chapter09PositiveReal => ((z : ℝ≥0) : ℝ)) hmodule
      simpa [chapter09InfiniteIdeleModule] using h
    rw [← Real.log_prod]
    · rw [hprod]
      simp
    · intro v hv
      exact_mod_cast Units.ne_zero
        (chapter09NormUnit
          ((MulEquiv.piUnits (chapter09InfiniteUnitEmbedding K u.toMul)) v) ^ v.mult)
  ⟩
  map_zero' := by
    apply Subtype.ext
    exact (chapter09GlobalUnitLogEmbeddingRaw K).map_zero
  map_add' u v := by
    apply Subtype.ext
    exact (chapter09GlobalUnitLogEmbeddingRaw K).map_add u v

theorem chapter09_global_unit_log_lies_in_hyperplane
    {K : Type*} [Field K] [NumberField K]
    (u : (𝓞 K)ˣ) :
    chapter09GlobalUnitLogEmbeddingRaw K (Additive.ofMul u) ∈
      chapter09LogHyperplane K := by
  exact (chapter09GlobalUnitLogEmbedding K (Additive.ofMul u)).property

theorem chapter09_global_unit_log_kernel
    (K : Type*) [Field K] [NumberField K] :
    (chapter09GlobalUnitLogEmbeddingRaw K).ker =
      (NumberField.Units.torsion K).toAddSubgroup := by
  ext u
  constructor
  · intro hu
    change chapter09GlobalUnitLogEmbeddingRaw K u = 0 at hu
    have hlog : NumberField.Units.logEmbedding K u = 0 := by
      funext w
      have hfactor :
          ‖(↑(MulEquiv.piUnits
              (chapter09InfiniteUnitEmbedding K u.toMul) w.1) :
            w.1.Completion)‖ = w.1 (u.toMul : K) := by
        change ‖((u.toMul : K) : w.1.Completion)‖ = w.1 (u.toMul : K)
        rw [← (WithAbs.equiv w.1.1).apply_symm_apply (u.toMul : K),
          NumberField.InfinitePlace.Completion.norm_coe]
        rfl
      have hcoord := congrFun hu w.1
      change Real.log
        (((chapter09NormUnit ((MulEquiv.piUnits
          (chapter09InfiniteUnitEmbedding K u.toMul)) w.1) ^ w.1.mult :
            Chapter09PositiveReal) : ℝ≥0) : ℝ) = 0 at hcoord
      have hpow :
          (((chapter09NormUnit ((MulEquiv.piUnits
            (chapter09InfiniteUnitEmbedding K u.toMul)) w.1) ^ w.1.mult :
              Chapter09PositiveReal) : ℝ≥0) : ℝ) =
            (w.1 (u.toMul : K)) ^ w.1.mult := by
        change ‖(↑((MulEquiv.piUnits
            (chapter09InfiniteUnitEmbedding K u.toMul)) w.1) :
          w.1.Completion)‖ ^ w.1.mult =
            (w.1 (u.toMul : K)) ^ w.1.mult
        rw [hfactor]
      rw [hpow, Real.log_pow] at hcoord
      change (w.1.mult : ℝ) * Real.log (w.1 (u.toMul : K)) = 0
      exact hcoord
    have ht :=
      (NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff
        (K := K)).1 hlog
    change u.toMul ∈ NumberField.Units.torsion K
    exact ht
  · intro hu
    change chapter09GlobalUnitLogEmbeddingRaw K u = 0
    have htorsion : u.toMul ∈ NumberField.Units.torsion K := by
      exact hu
    have hplaces : ∀ v : InfinitePlace K, v (u.toMul : K) = 1 :=
      (NumberField.Units.mem_torsion K).1 htorsion
    funext v
    have hfactor :
        ‖(↑(MulEquiv.piUnits
            (chapter09InfiniteUnitEmbedding K u.toMul) v) :
          v.Completion)‖ = v (u.toMul : K) := by
      change ‖((u.toMul : K) : v.Completion)‖ = v (u.toMul : K)
      rw [← (WithAbs.equiv v.1).apply_symm_apply (u.toMul : K),
        NumberField.InfinitePlace.Completion.norm_coe]
      rfl
    change Real.log
      (((chapter09NormUnit ((MulEquiv.piUnits
        (chapter09InfiniteUnitEmbedding K u.toMul)) v) ^ v.mult :
          Chapter09PositiveReal) : ℝ≥0) : ℝ) = 0
    have hpow :
        (((chapter09NormUnit ((MulEquiv.piUnits
          (chapter09InfiniteUnitEmbedding K u.toMul)) v) ^ v.mult :
            Chapter09PositiveReal) : ℝ≥0) : ℝ) =
          (v (u.toMul : K)) ^ v.mult := by
      change ‖(↑((MulEquiv.piUnits
          (chapter09InfiniteUnitEmbedding K u.toMul)) v) :
        v.Completion)‖ ^ v.mult = (v (u.toMul : K)) ^ v.mult
      rw [hfactor]
    rw [hpow, hplaces v, one_pow, Real.log_one]

def chapter09UnitLogLattice
    (K : Type*) [Field K] [NumberField K] :
    Submodule ℤ (chapter09LogHyperplane K) :=
  Submodule.map (chapter09GlobalUnitLogEmbedding K).toIntLinearMap ⊤

theorem chapter09UnitLogLattice_mem_iff
    {K : Type*} [Field K] [NumberField K]
    {t : chapter09LogHyperplane K} :
    t ∈ chapter09UnitLogLattice K ↔
      ∃ u : Additive ((𝓞 K)ˣ), chapter09GlobalUnitLogEmbedding K u = t := by
  rw [chapter09UnitLogLattice, Submodule.mem_map]
  simp

theorem chapter09UnitLogLattice_discrete
    (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (chapter09UnitLogLattice K) := by
  classical
  let p :
      chapter09LogHyperplane K →
        NumberField.Units.dirichletUnitTheorem.logSpace K :=
    fun t w => t.1 w.1
  have hp (u : Additive ((𝓞 K)ˣ)) :
      p (chapter09GlobalUnitLogEmbedding K u) =
        NumberField.Units.logEmbedding K u := by
    funext w
    change Real.log
      (((chapter09NormUnit ((MulEquiv.piUnits
        (chapter09InfiniteUnitEmbedding K u.toMul)) w.1) ^ w.1.mult :
          Chapter09PositiveReal) : ℝ≥0) : ℝ) =
      (w.1.mult : ℝ) * Real.log (w.1 (u.toMul : K))
    have hfactor :
        ‖(↑(MulEquiv.piUnits
            (chapter09InfiniteUnitEmbedding K u.toMul) w.1) :
          w.1.Completion)‖ = w.1 (u.toMul : K) := by
      change ‖((u.toMul : K) : w.1.Completion)‖ = w.1 (u.toMul : K)
      rw [← (WithAbs.equiv w.1.1).apply_symm_apply (u.toMul : K),
        NumberField.InfinitePlace.Completion.norm_coe]
      rfl
    have hpow :
        (((chapter09NormUnit ((MulEquiv.piUnits
          (chapter09InfiniteUnitEmbedding K u.toMul)) w.1) ^ w.1.mult :
            Chapter09PositiveReal) : ℝ≥0) : ℝ) =
          (w.1 (u.toMul : K)) ^ w.1.mult := by
      change ‖(↑((MulEquiv.piUnits
          (chapter09InfiniteUnitEmbedding K u.toMul)) w.1) :
        w.1.Completion)‖ ^ w.1.mult =
          (w.1 (u.toMul : K)) ^ w.1.mult
      rw [hfactor]
    rw [hpow, Real.log_pow]
  have hp_inj : Function.Injective p := by
    intro x y h
    apply Subtype.ext
    funext v
    by_cases hv : v = NumberField.Units.dirichletUnitTheorem.w₀ (K := K)
    · subst v
      have hx := x.property
      have hy := y.property
      change (∑ v : InfinitePlace K, x.1 v) = 0 at hx
      change (∑ v : InfinitePlace K, y.1 v) = 0 at hy
      rw [Fintype.sum_eq_add_sum_subtype_ne _
        (NumberField.Units.dirichletUnitTheorem.w₀ (K := K))] at hx hy
      have hsum :
          (∑ w : {w : InfinitePlace K //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀ (K := K)}, x.1 w.1) =
            ∑ w : {w : InfinitePlace K //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀ (K := K)}, y.1 w.1 := by
        apply Finset.sum_congr rfl
        intro w hw
        have hw' := congrFun h w
        change x.1 w.1 = y.1 w.1 at hw'
        exact hw'
      linarith
    · have hv' := congrFun h
        (⟨v, hv⟩ :
          {w : InfinitePlace K //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀ (K := K)})
      change x.1 v = y.1 v at hv'
      exact hv'
  have hfinite :
      ((chapter09UnitLogLattice K : Set (chapter09LogHyperplane K)) ∩
        Metric.closedBall 0 1).Finite := by
    refine Set.Finite.of_finite_image (f := p) ?_ hp_inj.injOn
    refine (NumberField.Units.dirichletUnitTheorem.unitLattice_inter_ball_finite K 1).subset ?_
    rintro _ ⟨t, ⟨htL, htB⟩, rfl⟩
    have htmem := (chapter09UnitLogLattice_mem_iff).1 htL
    obtain ⟨u, hu⟩ := htmem
    have hunit : p t ∈ NumberField.Units.unitLattice K := by
      rw [← hu, hp]
      exact ⟨u, trivial, rfl⟩
    refine ⟨hunit, ?_⟩
    rw [mem_closedBall_zero_iff] at htB ⊢
    change (↑(Finset.univ.sup
      (fun w : {w : InfinitePlace K //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀ (K := K)} =>
        ‖t.1 w.1‖₊) : ℝ≥0) : ℝ) ≤ 1
    have hs :
        Finset.univ.sup
            (fun w : {w : InfinitePlace K //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀ (K := K)} =>
              ‖t.1 w.1‖₊) ≤ (1 : ℝ≥0) := by
      refine Finset.sup_le ?_
      intro w hw
      exact_mod_cast (norm_le_pi_norm t.1 w.1).trans htB
    exact_mod_cast hs
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine isOpen_singleton_of_finite_mem_nhds 0
    (s := Metric.closedBall 0 1) ?_ ?_
  · exact Metric.closedBall_mem_nhds _ (by simp)
  · refine Set.Finite.of_finite_image ?_
      (Set.injOn_of_injective Subtype.val_injective)
    convert! hfinite
    ext x
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Subtype.mem x, hx⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨⟨x, hx1⟩, hx2, rfl⟩

attribute [instance] chapter09UnitLogLattice_discrete

theorem chapter09UnitLogLattice_span_eq_top
    (K : Type*) [Field K] [NumberField K] :
    Submodule.span ℝ (chapter09UnitLogLattice K : Set (chapter09LogHyperplane K)) = ⊤ := by
  classical
  let pLin :
      chapter09LogHyperplane K →ₗ[ℝ]
        NumberField.Units.dirichletUnitTheorem.logSpace K :=
    { toFun := fun t w => t.1 w.1
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c x
        rfl }
  have hp (u : Additive ((𝓞 K)ˣ)) :
      pLin (chapter09GlobalUnitLogEmbedding K u) =
        NumberField.Units.logEmbedding K u := by
    funext w
    change Real.log
      (((chapter09NormUnit ((MulEquiv.piUnits
        (chapter09InfiniteUnitEmbedding K u.toMul)) w.1) ^ w.1.mult :
          Chapter09PositiveReal) : ℝ≥0) : ℝ) =
      (w.1.mult : ℝ) * Real.log (w.1 (u.toMul : K))
    have hfactor :
        ‖(↑(MulEquiv.piUnits
            (chapter09InfiniteUnitEmbedding K u.toMul) w.1) :
          w.1.Completion)‖ = w.1 (u.toMul : K) := by
      change ‖((u.toMul : K) : w.1.Completion)‖ = w.1 (u.toMul : K)
      rw [← (WithAbs.equiv w.1.1).apply_symm_apply (u.toMul : K),
        NumberField.InfinitePlace.Completion.norm_coe]
      rfl
    have hpow :
        (((chapter09NormUnit ((MulEquiv.piUnits
          (chapter09InfiniteUnitEmbedding K u.toMul)) w.1) ^ w.1.mult :
            Chapter09PositiveReal) : ℝ≥0) : ℝ) =
          (w.1 (u.toMul : K)) ^ w.1.mult := by
      change ‖(↑((MulEquiv.piUnits
          (chapter09InfiniteUnitEmbedding K u.toMul)) w.1) :
        w.1.Completion)‖ ^ w.1.mult =
          (w.1 (u.toMul : K)) ^ w.1.mult
      rw [hfactor]
    rw [hpow, Real.log_pow]
  have himage :
      pLin '' (chapter09UnitLogLattice K : Set (chapter09LogHyperplane K)) =
        Set.range (NumberField.Units.logEmbedding K) := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨u, hu⟩ := (chapter09UnitLogLattice_mem_iff).1 ht
      exact ⟨u, by rw [← hu, hp]⟩
    · rintro ⟨u, rfl⟩
      refine ⟨chapter09GlobalUnitLogEmbedding K u, ?_, hp u⟩
      exact (chapter09UnitLogLattice_mem_iff).2 ⟨u, rfl⟩
  have hle :
      (NumberField.Units.unitLattice K : Set
          (NumberField.Units.dirichletUnitTheorem.logSpace K)) ⊆
        Submodule.span ℝ (Set.range (NumberField.Units.logEmbedding K)) := by
    intro y hy
    change y ∈ Submodule.map (NumberField.Units.logEmbedding K).toIntLinearMap ⊤ at hy
    change ∃ u : Additive ((𝓞 K)ˣ),
      u ∈ (⊤ : Submodule ℤ (Additive ((𝓞 K)ˣ))) ∧
        NumberField.Units.logEmbedding K u = y at hy
    obtain ⟨u, hu, huy⟩ := hy
    rw [← huy]
    exact (Submodule.subset_span (R := ℝ)) ⟨u, rfl⟩
  have hspan_range :
      Submodule.span ℝ (Set.range (NumberField.Units.logEmbedding K)) = ⊤ := by
    apply le_antisymm le_top
    rw [← NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top K]
    exact Submodule.span_le.2 hle
  have hmapspan :
      (Submodule.span ℝ (chapter09UnitLogLattice K :
        Set (chapter09LogHyperplane K))).map pLin = ⊤ := by
    rw [Submodule.map_span, himage, hspan_range]
  have hpinj : Function.Injective pLin := by
    intro x y h
    apply Subtype.ext
    funext v
    by_cases hv : v = NumberField.Units.dirichletUnitTheorem.w₀ (K := K)
    · subst v
      have hx := x.property
      have hy := y.property
      change (∑ v : InfinitePlace K, x.1 v) = 0 at hx
      change (∑ v : InfinitePlace K, y.1 v) = 0 at hy
      rw [Fintype.sum_eq_add_sum_subtype_ne _
        (NumberField.Units.dirichletUnitTheorem.w₀ (K := K))] at hx hy
      have hsum :
          (∑ w : {w : InfinitePlace K //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀ (K := K)}, x.1 w.1) =
            ∑ w : {w : InfinitePlace K //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀ (K := K)}, y.1 w.1 := by
        apply Finset.sum_congr rfl
        intro w hw
        have hw' := congrFun h w
        change x.1 w.1 = y.1 w.1 at hw'
        exact hw'
      linarith
    · have hv' := congrFun h
        (⟨v, hv⟩ :
          {w : InfinitePlace K //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀ (K := K)})
      change x.1 v = y.1 v at hv'
      exact hv'
  apply le_antisymm le_top
  intro t ht
  have hmem :
      pLin t ∈
        (Submodule.span ℝ (chapter09UnitLogLattice K :
          Set (chapter09LogHyperplane K))).map pLin := by
    rw [hmapspan]
    trivial
  change ∃ s, s ∈
      Submodule.span ℝ (chapter09UnitLogLattice K :
        Set (chapter09LogHyperplane K)) ∧ pLin s = pLin t at hmem
  obtain ⟨s, hs, hst⟩ := hmem
  have hst' : s = t := hpinj hst
  simpa [hst'] using hs

theorem chapter09UnitLogLattice_is_full_lattice
    (K : Type*) [Field K] [NumberField K] :
    IsZLattice ℝ (chapter09UnitLogLattice K) := by
  exact ⟨chapter09UnitLogLattice_span_eq_top K⟩

/- This is the bounded fundamental-region interface extracted from the
Minkowski argument: every logarithmic vector is reduced by a global unit into
one fixed bounded, hence compact, region. -/
theorem chapter09_unit_log_reduction
    (K : Type*) [Field K] [NumberField K] :
    ∃ B : Set (chapter09LogHyperplane K), IsCompact B ∧
      ∀ t : chapter09LogHyperplane K, ∃ u : Additive ((𝓞 K)ˣ),
        t - chapter09GlobalUnitLogEmbedding K u ∈ B := by
  classical
  let _ : IsZLattice ℝ (chapter09UnitLogLattice K) :=
    chapter09UnitLogLattice_is_full_lattice K
  have hfree := ZLattice.module_free ℝ (chapter09UnitLogLattice K)
  let b := Module.Free.chooseBasis ℤ (chapter09UnitLogLattice K)
  let e := b.ofZLatticeBasis ℝ
  refine ⟨(e.parallelepiped : Set (chapter09LogHyperplane K)),
    e.parallelepiped.isCompact, ?_⟩
  intro t
  let x' : chapter09UnitLogLattice K :=
    b.repr.symm (Finsupp.equivFunOnFinite.symm
      fun i ↦ ⌊e.repr t i⌋)
  obtain ⟨u, hu⟩ := (chapter09UnitLogLattice_mem_iff).1 x'.property
  refine ⟨u, ?_⟩
  rw [hu]
  change t + (-(x' : chapter09LogHyperplane K)) ∈
    (e.parallelepiped : Set (chapter09LogHyperplane K))
  simp [parallelepiped_basis_eq, x', e, Int.floor_le,
    Int.lt_floor_add_one, le_of_lt, add_comm (1 : ℝ)]

theorem chapter09_unit_log_lattice_is_discrete_and_cocompact
    (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (chapter09UnitLogLattice K) ∧
      ∃ B : Set (chapter09LogHyperplane K), IsCompact B ∧
        ∀ t : chapter09LogHyperplane K, ∃ u : Additive ((𝓞 K)ˣ),
          t - chapter09GlobalUnitLogEmbedding K u ∈ B := by
  exact ⟨chapter09UnitLogLattice_discrete K, chapter09_unit_log_reduction K⟩

theorem chapter09_unit_rank_eq_card_infinite_places_sub_one
    (K : Type*) [Field K] [NumberField K] :
    NumberField.Units.rank K = Fintype.card (InfinitePlace K) - 1 := by
  rfl

/- The structure theorem in the source is intentionally noncanonical. -/
theorem chapter09_dirichlet_unit_theorem
    (K : Type*) [Field K] [NumberField K] :
    Nonempty ((𝓞 K)ˣ ≃*
      (NumberField.Units.torsion K) ×
        Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) := by
  let f :
      (NumberField.Units.torsion K) ×
          Multiplicative (Fin (NumberField.Units.rank K) → ℤ) →*
        (𝓞 K)ˣ :=
    { toFun := fun z => z.1 * ∏ i, (NumberField.Units.fundSystem K i) ^
        (Multiplicative.toAdd z.2 i)
      map_one' := by
        apply Units.ext
        simp
      map_mul' := by
        intro z w
        apply Units.ext
        simp only [Units.val_mul, Prod.fst_mul, Prod.snd_mul]
        change (↑((z.1 : (𝓞 K)ˣ) * (w.1 : (𝓞 K)ˣ)) : 𝓞 K) *
              (↑(∏ i, (NumberField.Units.fundSystem K i) ^
                ((Multiplicative.toAdd z.2 + Multiplicative.toAdd w.2) i)) : 𝓞 K) =
          (((z.1 : (𝓞 K)ˣ) : 𝓞 K) *
              (↑(∏ i, (NumberField.Units.fundSystem K i) ^
                (Multiplicative.toAdd z.2 i)) : 𝓞 K)) *
            (((w.1 : (𝓞 K)ˣ) : 𝓞 K) *
              (↑(∏ i, (NumberField.Units.fundSystem K i) ^
                (Multiplicative.toAdd w.2 i)) : 𝓞 K))
        have hprodU :
            ∏ i, (NumberField.Units.fundSystem K i) ^
                ((Multiplicative.toAdd z.2 + Multiplicative.toAdd w.2) i) =
              (∏ i, (NumberField.Units.fundSystem K i) ^
                (Multiplicative.toAdd z.2 i)) *
                ∏ i, (NumberField.Units.fundSystem K i) ^
                  (Multiplicative.toAdd w.2 i) := by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro i hi
          simp only [Pi.add_apply]
          rw [zpow_add]
        rw [hprodU]
        simp only [Units.val_mul]
        ac_rfl }
  have hfbij : Function.Bijective f := by
    constructor
    · intro z w hzw
      have hzrep :
          f z = (z.1 : (𝓞 K)ˣ) * ∏ i, (NumberField.Units.fundSystem K i) ^
            (Multiplicative.toAdd z.2 i) := by
        rfl
      have hwrep :
          f z = (w.1 : (𝓞 K)ˣ) * ∏ i, (NumberField.Units.fundSystem K i) ^
            (Multiplicative.toAdd w.2 i) := by
        rw [hzw]
        rfl
      have hu :=
        (NumberField.Units.exist_unique_eq_mul_prod K
          (f z)).unique
          hzrep hwrep
      apply Prod.ext
      · exact congrArg Prod.fst hu
      · apply Multiplicative.ext
        exact congrArg (fun q => q.2) hu
    · intro x
      rcases
          (NumberField.Units.exist_unique_eq_mul_prod K x) with
        ⟨z, hz, huniq⟩
      refine ⟨⟨z.1, Multiplicative.ofAdd z.2⟩, ?_⟩
      exact hz.symm
  exact ⟨(MulEquiv.ofBijective f hfbij).symm⟩

theorem chapter09_dirichlet_unit_theorem_kernel_finite
    (K : Type*) [Field K] [NumberField K] :
    Finite (NumberField.Units.torsion K) := by
  infer_instance

end

end LastLib.Book04AdelesAndIdeles.Chapter09
