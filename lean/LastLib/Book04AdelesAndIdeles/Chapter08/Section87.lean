import LastLib.Book04AdelesAndIdeles.Chapter08.Section82
import LastLib.Book04AdelesAndIdeles.Chapter06.Dependencies
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

namespace LastLib.Book04AdelesAndIdeles.Chapter08

noncomputable section

open scoped BigOperators NNReal nonZeroDivisors RestrictedProduct
open IsDedekindDomain

/-! ## 8.7 Divisor sequence in one view -/

def chapter08GlobalUnitEmbedding (K : Type*) [Field K] [NumberField K] :
    (Chapter08Integers K)ˣ →* Kˣ :=
  Units.map (algebraMap (Chapter08Integers K) K)

def chapter08PrincipalIdealGroup (K : Type*) [Field K] [NumberField K] :=
  (toPrincipalIdeal (Chapter08Integers K) K).range

def chapter08PrincipalIdealMap (K : Type*) [Field K] [NumberField K] :
    Kˣ →* chapter08PrincipalIdealGroup K where
  toFun := fun a => ⟨toPrincipalIdeal (Chapter08Integers K) K a,
    MonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' := by
    intro x y
    apply Subtype.ext
    simp

def chapter08GlobalUnitToPrincipalIdeal (K : Type*) [Field K] [NumberField K] :
    (Chapter08Integers K)ˣ →* chapter08PrincipalIdealGroup K :=
  (chapter08PrincipalIdealMap K).comp (chapter08GlobalUnitEmbedding K)

theorem chapter08_global_unit_kernel_principal_ideal
    (K : Type*) [Field K] [NumberField K] :
    MonoidHom.ker (chapter08PrincipalIdealMap K) =
      MonoidHom.range (chapter08GlobalUnitEmbedding K) := by
  ext a
  constructor
  · intro ha
    have ha' : toPrincipalIdeal (Chapter08Integers K) K a = 1 := by
      exact congrArg (fun z : chapter08PrincipalIdealGroup K =>
        (z : Chapter08IdealGroup K)) ha
    have hspan : Submodule.span (Chapter08Integers K) {(a : K)} = 1 := by
      have hcoe := congrArg (fun I : Chapter08IdealGroup K =>
        ((I : Chapter08FractionalIdeal K) : Submodule (Chapter08Integers K) K)) ha'
      simpa [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton] using hcoe
    obtain ⟨u, hu⟩ := (Submodule.span_singleton_eq_one_iff).1 hspan
    refine ⟨u, ?_⟩
    apply Units.ext
    simpa [chapter08GlobalUnitEmbedding] using hu.symm
  · rintro ⟨u, rfl⟩
    change chapter08PrincipalIdealMap K (chapter08GlobalUnitEmbedding K u) = 1
    apply Subtype.ext
    apply Units.ext
    apply FractionalIdeal.coeToSubmodule_injective
    have hspan : Submodule.span (Chapter08Integers K)
        {((algebraMap (Chapter08Integers K) K) (u : Chapter08Integers K))} = 1 :=
      (Submodule.span_singleton_eq_one_iff).2 ⟨u, rfl⟩
    simpa [chapter08PrincipalIdealMap, chapter08GlobalUnitEmbedding,
      coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton] using hspan

theorem chapter08_global_divisor_short_exact
    (K : Type*) [Field K] [NumberField K] :
    chapter08IsShortExact (chapter08GlobalUnitEmbedding K)
      (chapter08PrincipalIdealMap K) := by
  refine ⟨Units.map_injective (algebraMap_injective_of_field_isFractionRing
      (Chapter08Integers K) K K K), ?_, ?_⟩
  · rw [chapter08IsExact, chapter08_global_unit_kernel_principal_ideal]
  · rintro ⟨I, ⟨a, ha⟩⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha

theorem chapter08_divisor_diagram_commutes
    {K : Type*} [Field K] [NumberField K]
    (u : (Chapter08Integers K)ˣ) :
    chapter08FiniteIdeleIdealMap K
        (chapter08FinitePrincipalIdele (chapter08GlobalUnitEmbedding K u)) =
      toPrincipalIdeal (Chapter08Integers K) K (chapter08GlobalUnitEmbedding K u) := by
  exact chapter08_finite_idele_ideal_principal _

theorem chapter08_finite_divisor_square_commutes
    (K : Type*) [Field K] [NumberField K] :
    (chapter08FiniteIdeleIdealMap K).comp (chapter08FinitePrincipalIdeleHom K) =
      toPrincipalIdeal (Chapter08Integers K) K := by
  apply MonoidHom.ext
  intro a
  exact chapter08_finite_idele_ideal_principal a

theorem chapter08_divisor_quotient_is_class_group
    (K : Type*) [Field K] [NumberField K] :
    Nonempty
      ((Chapter08IdealGroup K ⧸
        (toPrincipalIdeal (Chapter08Integers K) K).range) ≃*
        Chapter08OrdinaryClassGroup K) := by
  exact ⟨(ClassGroup.equiv K).symm⟩

/-! Finite divisors are the finitely supported valuation vectors. -/

def chapter08PrincipalDivisor {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) : Chapter08FiniteDivisors K :=
  chapter08FiniteIdeleOrderFinsupp (chapter08FinitePrincipalIdele a)

@[simp]
theorem chapter08PrincipalDivisor_apply
    {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) (v : HeightOneSpectrum (Chapter08Integers K)) :
    chapter08PrincipalDivisor a v =
      FractionalIdeal.count K v
        (toPrincipalIdeal (Chapter08Integers K) K a : Chapter08FractionalIdeal K) := by
  rw [chapter08PrincipalDivisor, chapter08FiniteIdeleOrderFinsupp_apply,
    ← chapter08_finite_idele_ideal_count (x := chapter08FinitePrincipalIdele a) v,
    chapter08_finite_idele_ideal_principal]

def chapter08PrincipalDivisorHom (K : Type*) [Field K] [NumberField K] :
    Kˣ →* Multiplicative (Chapter08FiniteDivisors K) where
  toFun := fun a => Multiplicative.ofAdd (chapter08PrincipalDivisor a)
  map_one' := by
    apply Multiplicative.ext
    ext v
    change chapter08FiniteIdeleOrder
        (chapter08FinitePrincipalIdele (1 : Kˣ)) v = 0
    apply (chapter08_local_order_eq_zero_iff_valued_eq_one v _
      (chapter08_finite_idele_component_ne_zero
        (chapter08FinitePrincipalIdele (1 : Kˣ)) v)).2
    exact Valuation.map_one _
  map_mul' := by
    intro x y
    apply Multiplicative.ext
    ext v
    change chapter08FiniteIdeleOrder
        (chapter08FinitePrincipalIdele (x * y)) v =
      chapter08FiniteIdeleOrder (chapter08FinitePrincipalIdele x) v +
        chapter08FiniteIdeleOrder (chapter08FinitePrincipalIdele y) v
    rw [← chapter08FinitePrincipalIdeleHom_apply,
      ← chapter08FinitePrincipalIdeleHom_apply,
      ← chapter08FinitePrincipalIdeleHom_apply,
      map_mul, chapter08_finite_idele_order_mul]

abbrev Chapter08DivisorClassGroup (K : Type*) [Field K] [NumberField K] :=
  Multiplicative (Chapter08FiniteDivisors K) ⧸
    MonoidHom.range (chapter08PrincipalDivisorHom K)

noncomputable def chapter08DivisorToIdeal
    {K : Type*} [Field K] [NumberField K]
    (d : Chapter08FiniteDivisors K) : Chapter08IdealGroup K :=
  Units.mk0
    (d.prod (fun v n => (v.asIdeal : Chapter08FractionalIdeal K) ^ n)) (by
      classical
      rw [Finsupp.prod_ne_zero_iff]
      intro v hv
      exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))

def chapter08DivisorToIdealHom (K : Type*) [Field K] [NumberField K] :
    Multiplicative (Chapter08FiniteDivisors K) →* Chapter08IdealGroup K where
  toFun := fun d => chapter08DivisorToIdeal (Multiplicative.toAdd d)
  map_one' := by
    apply Units.ext
    change (0 : Chapter08FiniteDivisors K).prod
        (fun v n => (v.asIdeal : Chapter08FractionalIdeal K) ^ n) = 1
    exact Finsupp.prod_zero_index
  map_mul' := by
    intro x y
    apply Units.ext
    change (Multiplicative.toAdd x + Multiplicative.toAdd y).prod
        (fun v n => (v.asIdeal : Chapter08FractionalIdeal K) ^ n) = _
    rw [Finsupp.prod_add_index'
      (h_zero := fun v => zpow_zero _)
      (h_add := fun v m n =>
        zpow_add₀ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot) m n)]
    rfl

theorem chapter08_divisor_to_ideal_principal
    {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) :
    chapter08DivisorToIdealHom K (chapter08PrincipalDivisorHom K a) =
      toPrincipalIdeal (Chapter08Integers K) K a := by
  apply Units.ext
  change chapter08FiniteIdeleFractionalIdeal
      (chapter08FinitePrincipalIdele a) = _
  exact congrArg Units.val (chapter08_finite_idele_ideal_principal a)

/-! The canonical additive Haar character sees the same local factors as the
idele module: weighted archimedean norms and the normalized finite-place
factors.  This pointwise bridge is kept in the earlier chapter so later
measure-theoretic sections need not duplicate the valuation bookkeeping. -/

theorem chapter08_adele_unit_distrib_haar_char_apply
    (K : Type*) [Field K] [NumberField K]
    [LocallyCompactSpace (NumberField.AdeleRing (Chapter08Integers K) K)]
    (x : (NumberField.AdeleRing (Chapter08Integers K) K)ˣ) :
    MeasureTheory.distribHaarChar
        (G := (NumberField.AdeleRing (Chapter08Integers K) K)ˣ)
        (A := NumberField.AdeleRing (Chapter08Integers K) K) x =
      (∏ v : NumberField.InfinitePlace K,
        ‖((MulEquiv.piUnits (MulEquiv.prodUnits x).1) v : v.Completion)‖₊ ^ v.mult) *
        (∏ᶠ v : HeightOneSpectrum (Chapter08Integers K),
          (Ideal.absNorm v.asIdeal : ℝ≥0) ^
            (-chapter08LocalOrder v
              ((RestrictedProduct.unitsEquiv
                (fun v : HeightOneSpectrum (Chapter08Integers K) =>
                  v.adicCompletion K) (MulEquiv.prodUnits x).2) v :
                v.adicCompletion K))) := by
  have hlocal : ∀ (v : HeightOneSpectrum (Chapter08Integers K))
      (y : v.adicCompletion K),
      LastLib.Book04AdelesAndIdeles.Chapter06.chapter06StandardNumberFieldLocalOrder v y =
        chapter08LocalOrder v y := by
    intro v y
    rfl
  simpa [LastLib.Book04AdelesAndIdeles.Chapter06.chapter06StandardNumberFieldInfiniteHaarFactor,
    LastLib.Book04AdelesAndIdeles.Chapter06.chapter06StandardNumberFieldFiniteHaarFactor,
    hlocal] using
    (LastLib.Book04AdelesAndIdeles.Chapter06.chapter06_standard_number_field_adele_unit_distrib_haar_char_apply
      K x)

def chapter08DivisorClassMap (K : Type*) [Field K] [NumberField K] :
    Chapter08DivisorClassGroup K →* Chapter08OrdinaryClassGroup K :=
  QuotientGroup.lift (MonoidHom.range (chapter08PrincipalDivisorHom K))
    ((ClassGroup.mk K).comp (chapter08DivisorToIdealHom K)) (by
      intro x hx
      rcases hx with ⟨a, rfl⟩
      change ClassGroup.mk K
        (chapter08DivisorToIdealHom K (chapter08PrincipalDivisorHom K a)) = 1
      rw [chapter08_divisor_to_ideal_principal]
      apply (ClassGroup.mk_eq_one_iff).2
      refine ⟨(a : K), ?_⟩
      simp [coe_toPrincipalIdeal])

theorem chapter08_divisor_class_map_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter08DivisorClassMap K) := by
  intro c
  obtain ⟨q, rfl⟩ := (ClassGroup.equiv K).symm.surjective c
  obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective
    ((toPrincipalIdeal (Chapter08Integers K) K).range) q
  obtain ⟨x, hx⟩ := chapter08_finite_idele_ideal_surjective K I
  let d := chapter08FiniteIdeleOrderFinsupp x
  have hdi : chapter08DivisorToIdealHom K (Multiplicative.ofAdd d) =
      chapter08FiniteIdeleIdealMap K x := by
    apply Units.ext
    change d.prod (fun v n => (v.asIdeal : Chapter08FractionalIdeal K) ^ n) =
      chapter08FiniteIdeleFractionalIdeal x
    rfl
  refine ⟨QuotientGroup.mk'
      (MonoidHom.range (chapter08PrincipalDivisorHom K))
      (Multiplicative.ofAdd d), ?_⟩
  apply (ClassGroup.equiv K).injective
  simp [chapter08DivisorClassMap, hdi, hx]
  rfl

theorem chapter08_divisor_class_map_kernel
    (K : Type*) [Field K] [NumberField K] :
    MonoidHom.ker (chapter08DivisorClassMap K) = ⊥ := by
  apply (MonoidHom.ker_eq_bot_iff _).2
  intro q₁ q₂ hq
  obtain ⟨d₁, rfl⟩ := QuotientGroup.mk'_surjective
    (MonoidHom.range (chapter08PrincipalDivisorHom K)) q₁
  obtain ⟨d₂, rfl⟩ := QuotientGroup.mk'_surjective
    (MonoidHom.range (chapter08PrincipalDivisorHom K)) q₂
  have hclass : ClassGroup.mk K (chapter08DivisorToIdealHom K d₁) =
      ClassGroup.mk K (chapter08DivisorToIdealHom K d₂) := by
    simpa [chapter08DivisorClassMap] using hq
  have hq := ((ClassGroup.equiv K).injective.eq_iff).mpr hclass
  have hq' : QuotientGroup.mk' (toPrincipalIdeal (Chapter08Integers K) K).range
        (chapter08DivisorToIdealHom K d₁) =
      QuotientGroup.mk' (toPrincipalIdeal (Chapter08Integers K) K).range
        (chapter08DivisorToIdealHom K d₂) := by
    rw [ClassGroup.equiv_mk, ClassGroup.equiv_mk] at hq
    rw [FractionalIdeal.canonicalEquiv_self] at hq
    convert hq using 1 <;> rfl
  rw [QuotientGroup.mk'_eq_mk'] at hq'
  obtain ⟨z, hz, hzprod⟩ := hq'
  rcases hz with ⟨a, rfl⟩
  have ha : chapter08DivisorToIdealHom K d₁ *
      toPrincipalIdeal (Chapter08Integers K) K a =
      chapter08DivisorToIdealHom K d₂ := hzprod
  have hd : Multiplicative.toAdd d₁ + chapter08PrincipalDivisor a =
      Multiplicative.toAdd d₂ := by
    ext v
    have hc := congrArg (fun I : Chapter08IdealGroup K =>
      FractionalIdeal.count K v (I : Chapter08FractionalIdeal K)) ha
    have hc₁ : FractionalIdeal.count K v
        (chapter08DivisorToIdealHom K d₁ : Chapter08FractionalIdeal K) =
        Multiplicative.toAdd d₁ v := by
      change FractionalIdeal.count K v
          ((Multiplicative.toAdd d₁).prod
            (fun v n => (v.asIdeal : Chapter08FractionalIdeal K) ^ n)) = _
      exact FractionalIdeal.count_finsuppProd K v _
    have hc₂ : FractionalIdeal.count K v
        (chapter08DivisorToIdealHom K d₂ : Chapter08FractionalIdeal K) =
        Multiplicative.toAdd d₂ v := by
      change FractionalIdeal.count K v
          ((Multiplicative.toAdd d₂).prod
            (fun v n => (v.asIdeal : Chapter08FractionalIdeal K) ^ n)) = _
      exact FractionalIdeal.count_finsuppProd K v _
    simp only [Units.val_mul] at hc
    rw [FractionalIdeal.count_mul K v (Units.ne_zero _) (Units.ne_zero _),
      hc₁, ← chapter08PrincipalDivisor_apply, hc₂] at hc
    exact hc
  rw [QuotientGroup.mk'_eq_mk']
  refine ⟨chapter08PrincipalDivisorHom K a, ⟨a, rfl⟩, ?_⟩
  exact Multiplicative.toAdd.injective (by
    simpa [chapter08PrincipalDivisorHom] using hd)

noncomputable def chapter08DivisorClassGroupEquivClassGroup
    (K : Type*) [Field K] [NumberField K] :
    Chapter08DivisorClassGroup K ≃* Chapter08OrdinaryClassGroup K :=
  MulEquiv.ofBijective (chapter08DivisorClassMap K)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (chapter08_divisor_class_map_kernel K),
      chapter08_divisor_class_map_surjective K⟩

/-! Adding archimedean real coefficients records the degree balance that the ideal map alone omits. -/

def chapter08ArchimedeanDivisorCoefficient
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08InfiniteIdeles K)
    (w : NumberField.InfinitePlace K) : ℝ :=
  -Real.log (‖x.1 w‖ ^ w.mult)

def chapter08ExtendedDivisorDegree
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08Ideles K) : ℝ :=
  Real.log (chapter08IdealNorm (chapter08FiniteIdeleIdealMap K x.2) : ℝ) +
    ∑ w : NumberField.InfinitePlace K,
      chapter08ArchimedeanDivisorCoefficient x.1 w

/- Local dependency guess for the later fixup pass: the earlier product-formula API identifies the
normalization of the finite ideal norm with the weighted archimedean norm used here. -/

theorem chapter08_extended_divisor_degree_principal_zero
    {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) :
    chapter08ExtendedDivisorDegree (chapter08PrincipalIdeleHom K a) = 0 := by
  change chapter08ExtendedDivisorDegree
    (chapter08InfinitePrincipalIdele a, chapter08FinitePrincipalIdele a) = 0
  unfold chapter08ExtendedDivisorDegree chapter08ArchimedeanDivisorCoefficient
  rw [chapter08_finite_idele_ideal_principal]
  simp [chapter08IdealNorm, chapter08InfinitePrincipalIdele, coe_toPrincipalIdeal]
  have hprod := NumberField.InfinitePlace.prod_eq_abs_norm (a : K)
  have hnonzero : ∀ w : NumberField.InfinitePlace K,
      ‖(chapter08InfinitePrincipalIdele a : Chapter08InfiniteIdeles K).1 w‖ ^ w.mult ≠ 0 := by
    intro w
    apply pow_ne_zero
    apply norm_ne_zero_iff.mpr
    intro hz
    have hmul := congr_fun (chapter08InfinitePrincipalIdele a).val_inv w
    change (chapter08InfinitePrincipalIdele a).1 w *
        (chapter08InfinitePrincipalIdele a).inv w = 1 at hmul
    rw [hz, zero_mul] at hmul
    exact zero_ne_one hmul
  have hprod' :
      (∏ w : NumberField.InfinitePlace K,
        ‖(chapter08InfinitePrincipalIdele a : Chapter08InfiniteIdeles K).1 w‖ ^ w.mult) =
        (|(Algebra.norm ℚ (a : K))| : ℝ) := by
    have hfactor : ∀ w : NumberField.InfinitePlace K,
        ‖(chapter08InfinitePrincipalIdele a : Chapter08InfiniteIdeles K).1 w‖ ^ w.mult =
          w (a : K) ^ w.mult := by
      intro w
      change ‖((a : K) : w.Completion)‖ ^ w.mult = w (a : K) ^ w.mult
      rw [← (WithAbs.equiv w.1).apply_symm_apply (a : K),
        NumberField.InfinitePlace.Completion.norm_coe]
      rfl
    have hprod_real :
        (∏ w : NumberField.InfinitePlace K, w (a : K) ^ w.mult) =
          |(Algebra.norm ℚ (a : K) : ℝ)| := by
      simpa only [Rat.cast_abs] using hprod
    calc
      (∏ w : NumberField.InfinitePlace K,
          ‖(chapter08InfinitePrincipalIdele a : Chapter08InfiniteIdeles K).1 w‖ ^ w.mult) =
          ∏ w : NumberField.InfinitePlace K, w (a : K) ^ w.mult := by
        apply Finset.prod_congr rfl
        intro w hw
        exact hfactor w
      _ = |(Algebra.norm ℚ (a : K) : ℝ)| := hprod_real
  have hsum :
      ∑ w : NumberField.InfinitePlace K,
        Real.log (‖(chapter08InfinitePrincipalIdele a : Chapter08InfiniteIdeles K).1 w‖ ^ w.mult) =
        Real.log (|(Algebra.norm ℚ (a : K))| : ℝ) := by
    rw [← hprod']
    exact (Real.log_prod (fun w _ => hnonzero w)).symm
  have hsum' :
      ∑ w : NumberField.InfinitePlace K,
        (w.mult : ℝ) * Real.log
          ‖(chapter08InfinitePrincipalIdele a : Chapter08InfiniteIdeles K).1 w‖ =
        Real.log (|(Algebra.norm ℚ (a : K))| : ℝ) := by
    simpa only [Real.log_pow] using hsum
  rw [← Real.log_abs]
  have hzero : Real.log (|(Algebra.norm ℚ (a : K))| : ℝ) -
      ∑ w : NumberField.InfinitePlace K,
        (w.mult : ℝ) * Real.log
          ‖(chapter08InfinitePrincipalIdele a : Chapter08InfiniteIdeles K).1 w‖ = 0 := by
    rw [hsum']
    ring
  have hnorm : ∀ w : NumberField.InfinitePlace K,
      ‖(chapter08InfinitePrincipalIdele a : Chapter08InfiniteIdeles K).1 w‖ =
        ‖WithAbs.toAbs w.1 (a : K)‖ := by
    intro w
    change ‖(WithAbs.toAbs w.1 (a : K) : w.Completion)‖ =
      ‖WithAbs.toAbs w.1 (a : K)‖
    rw [NumberField.InfinitePlace.Completion.norm_coe,
      WithAbs.norm_eq_apply_ofAbs]
    rfl
  have hsumNorm :
      (∑ w : NumberField.InfinitePlace K,
        (w.mult : ℝ) * Real.log ‖WithAbs.toAbs w.1 (a : K)‖) =
      ∑ w : NumberField.InfinitePlace K,
        (w.mult : ℝ) * Real.log
          ‖(chapter08InfinitePrincipalIdele a : Chapter08InfiniteIdeles K).1 w‖ := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [hnorm]
  rw [hsumNorm]
  simpa only [sub_eq_add_neg] using hzero

theorem chapter08_extended_divisor_degree_has_finite_log_term
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08Ideles K) :
    chapter08ExtendedDivisorDegree x =
      chapter08FiniteDegreeContribution x.2 +
        ∑ w : NumberField.InfinitePlace K,
          chapter08ArchimedeanDivisorCoefficient x.1 w := by
  rfl

end

end LastLib.Book04AdelesAndIdeles.Chapter08
