import LastLib.Book04AdelesAndIdeles.Chapter08.Dependencies
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.Section04LocalizationsOfDedekindDomains
import Mathlib.Topology.Algebra.Group.Units

namespace LastLib.Book04AdelesAndIdeles.Chapter08

noncomputable section

open scoped BigOperators nonZeroDivisors RestrictedProduct WithZero
open Filter IsDedekindDomain

/-! ## 8.1 From local valuations to a fractional ideal -/

def chapter08FiniteIdeleComponent {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) : v.adicCompletion K :=
  (x.1 v)

theorem chapter08_finite_idele_component_ne_zero
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) :
    chapter08FiniteIdeleComponent x v ≠ 0 := by
  exact (IsDedekindDomain.FiniteAdeleRing.isUnit_iff.mp x.isUnit).1 v

/- Mathlib's multiplicative valuation is `exp (-ord)`, so negating its additive exponent recovers
the ideal-theoretic order.  The zero case is only a harmless totalization; all uses coming from
finite ideles have nonzero local components. -/
def chapter08LocalOrder {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (Chapter08Integers K))
    (x : v.adicCompletion K) : ℤ :=
  if hx : (Valued.v x : ℤᵐ⁰) = 0 then
    0
  else
    -((WithZero.unzero hx).toAdd)

def chapter08FiniteIdeleOrder {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) : ℤ :=
  chapter08LocalOrder v (chapter08FiniteIdeleComponent x v)

theorem chapter08_local_order_eq_zero_iff_valued_eq_one
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (Chapter08Integers K))
    (x : v.adicCompletion K) (hx : x ≠ 0) :
    chapter08LocalOrder v x = 0 ↔ (Valued.v x : ℤᵐ⁰) = 1 := by
  have hxv : (Valued.v x : ℤᵐ⁰) ≠ 0 := by simpa using hx
  rw [chapter08LocalOrder, dif_neg hxv]
  constructor
  · intro h
    have h' := (WithZero.toAdd_unzero_eq_iff hxv (0 : ℤ)).1 (neg_eq_zero.mp h)
    simpa only [ofAdd_zero, WithZero.coe_one] using h'
  · intro h
    exact neg_eq_zero.mpr <| (WithZero.toAdd_unzero_eq_iff hxv (0 : ℤ)).2 <|
      by simpa only [ofAdd_zero, WithZero.coe_one] using h

theorem chapter08_finite_idele_order_eventually_eq_zero
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    ∀ᶠ v : HeightOneSpectrum (Chapter08Integers K) in Filter.cofinite,
      chapter08FiniteIdeleOrder x v = 0 := by
  filter_upwards [IsDedekindDomain.FiniteAdeleRing.unitsEquiv_finite_valued_eq_one x] with v hv
  change chapter08LocalOrder v (chapter08FiniteIdeleComponent x v) = 0
  apply (chapter08_local_order_eq_zero_iff_valued_eq_one v _
    (chapter08_finite_idele_component_ne_zero x v)).2
  change Valued.v (chapter08FiniteIdeleComponent x v) = 1
  have heq :
      (↑((RestrictedProduct.unitsEquiv (HeightOneSpectrum.adicCompletion K) x) v) :
        v.adicCompletion K) = chapter08FiniteIdeleComponent x v :=
    RestrictedProduct.unitsEquiv_apply v x
  rw [← heq]
  exact hv

def chapter08FiniteIdeleOrderFinsupp {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : Chapter08FiniteDivisors K :=
  Finsupp.mk (chapter08_finite_idele_order_eventually_eq_zero x).toFinset
    (chapter08FiniteIdeleOrder x)
    (fun _ => (chapter08_finite_idele_order_eventually_eq_zero x).mem_toFinset)

@[simp]
theorem chapter08FiniteIdeleOrderFinsupp_apply {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) :
    chapter08FiniteIdeleOrderFinsupp x v = chapter08FiniteIdeleOrder x v := by
  rfl

theorem chapter08_finite_idele_order_mul
    {K : Type*} [Field K] [NumberField K]
    (x y : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) :
    chapter08FiniteIdeleOrder (x * y) v =
      chapter08FiniteIdeleOrder x v + chapter08FiniteIdeleOrder y v := by
  have local_mul : ∀ (a b : v.adicCompletion K), a ≠ 0 → b ≠ 0 →
      chapter08LocalOrder v (a * b) =
        chapter08LocalOrder v a + chapter08LocalOrder v b := by
    intro a b ha hb
    have hav : (Valued.v a : ℤᵐ⁰) ≠ 0 := by simpa using ha
    have hbv : (Valued.v b : ℤᵐ⁰) ≠ 0 := by simpa using hb
    have hmul : Valued.v (a * b) = Valued.v a * Valued.v b :=
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).map_mul a b
    have habv : (Valued.v (a * b) : ℤᵐ⁰) ≠ 0 := by
      rw [hmul]
      exact mul_ne_zero hav hbv
    unfold chapter08LocalOrder
    rw [dif_neg habv, dif_neg hav, dif_neg hbv]
    have hu : WithZero.unzero habv =
        WithZero.unzero hav * WithZero.unzero hbv := by
      rw [← WithZero.coe_inj, WithZero.coe_unzero, WithZero.coe_mul,
        WithZero.coe_unzero, WithZero.coe_unzero]
      exact hmul
    rw [hu, toAdd_mul]
    ring
  change chapter08LocalOrder v
    (chapter08FiniteIdeleComponent x v * chapter08FiniteIdeleComponent y v) = _
  exact local_mul _ _ (chapter08_finite_idele_component_ne_zero x v)
    (chapter08_finite_idele_component_ne_zero y v)

theorem chapter08_finite_idele_order_inv
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) :
    chapter08FiniteIdeleOrder x⁻¹ v = -chapter08FiniteIdeleOrder x v := by
  have hone : chapter08FiniteIdeleOrder (1 : Chapter08FiniteIdeles K) v = 0 := by
    apply (chapter08_local_order_eq_zero_iff_valued_eq_one v _
      (chapter08_finite_idele_component_ne_zero (1 : Chapter08FiniteIdeles K) v)).2
    change Valued.v (1 : v.adicCompletion K) = 1
    exact Valuation.map_one _
  have hmul := chapter08_finite_idele_order_mul x x⁻¹ v
  have hzero : 0 = chapter08FiniteIdeleOrder x v +
      chapter08FiniteIdeleOrder x⁻¹ v := by
    simpa [hone] using hmul
  linarith

theorem chapter08_finite_idele_order_eq_zero_iff_local_unit
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) :
    chapter08FiniteIdeleOrder x v = 0 ↔
      (Valued.v (chapter08FiniteIdeleComponent x v) : ℤᵐ⁰) = 1 := by
  exact chapter08_local_order_eq_zero_iff_valued_eq_one v _
    (chapter08_finite_idele_component_ne_zero x v)

/-! The divisor-to-ideal construction is the finite Euler product of prime ideals. -/

noncomputable def chapter08FiniteIdeleFractionalIdeal
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : Chapter08FractionalIdeal K :=
  (chapter08FiniteIdeleOrderFinsupp x).prod
    (fun v n => (v.asIdeal : Chapter08FractionalIdeal K) ^ n)

theorem chapter08_finite_idele_fractionalIdeal_ne_zero
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    chapter08FiniteIdeleFractionalIdeal x ≠ 0 := by
  classical
  unfold chapter08FiniteIdeleFractionalIdeal
  rw [Finsupp.prod_ne_zero_iff]
  intro v hv
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

noncomputable def chapter08FiniteIdeleIdeal
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : Chapter08IdealGroup K :=
  Units.mk0 (chapter08FiniteIdeleFractionalIdeal x)
    (chapter08_finite_idele_fractionalIdeal_ne_zero x)

noncomputable def chapter08FiniteIdeleIdealMap
    (K : Type*) [Field K] [NumberField K] :
    Chapter08FiniteIdeles K →* Chapter08IdealGroup K where
  toFun := chapter08FiniteIdeleIdeal
  map_one' := by
    apply Units.ext
    change chapter08FiniteIdeleFractionalIdeal (1 : Chapter08FiniteIdeles K) = 1
    classical
    have hord : chapter08FiniteIdeleOrderFinsupp (1 : Chapter08FiniteIdeles K) = 0 := by
      ext v
      rw [chapter08FiniteIdeleOrderFinsupp_apply]
      apply (chapter08_local_order_eq_zero_iff_valued_eq_one v _
        (chapter08_finite_idele_component_ne_zero (1 : Chapter08FiniteIdeles K) v)).2
      change Valued.v (1 : v.adicCompletion K) = 1
      exact Valuation.map_one _
    rw [chapter08FiniteIdeleFractionalIdeal, hord, Finsupp.prod_zero_index]
  map_mul' := by
    intro x y
    apply Units.ext
    change chapter08FiniteIdeleFractionalIdeal (x * y) =
      chapter08FiniteIdeleFractionalIdeal x * chapter08FiniteIdeleFractionalIdeal y
    have hord : chapter08FiniteIdeleOrderFinsupp (x * y) =
        chapter08FiniteIdeleOrderFinsupp x + chapter08FiniteIdeleOrderFinsupp y := by
      ext v
      change chapter08FiniteIdeleOrder (x * y) v =
        chapter08FiniteIdeleOrder x v + chapter08FiniteIdeleOrder y v
      exact chapter08_finite_idele_order_mul x y v
    change (chapter08FiniteIdeleOrderFinsupp (x * y)).prod
        (fun v n => (v.asIdeal : Chapter08FractionalIdeal K) ^ n) = _
    rw [hord]
    change (chapter08FiniteIdeleOrderFinsupp x + chapter08FiniteIdeleOrderFinsupp y).prod
        (fun v n => (v.asIdeal : Chapter08FractionalIdeal K) ^ n) =
      (chapter08FiniteIdeleOrderFinsupp x).prod
          (fun v n => (v.asIdeal : Chapter08FractionalIdeal K) ^ n) *
        (chapter08FiniteIdeleOrderFinsupp y).prod
          (fun v n => (v.asIdeal : Chapter08FractionalIdeal K) ^ n)
    rw [Finsupp.prod_add_index']
    · simp
    · intro v m n
      exact zpow_add₀ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot) m n

theorem chapter08FiniteIdeleIdealMap_apply
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    chapter08FiniteIdeleIdealMap K x = chapter08FiniteIdeleIdeal x :=
  rfl

theorem chapter08_finite_idele_ideal_count
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) :
    FractionalIdeal.count K v
        (chapter08FiniteIdeleIdealMap K x : Chapter08FractionalIdeal K) =
      chapter08FiniteIdeleOrder x v := by
  change FractionalIdeal.count K v
      ((chapter08FiniteIdeleOrderFinsupp x).prod
        (fun v n => (v.asIdeal : Chapter08FractionalIdeal K) ^ n)) =
      chapter08FiniteIdeleOrderFinsupp x v
  rw [FractionalIdeal.count_finsuppProd]

def chapter08FiniteIntegralUnits {K : Type*} [Field K] [NumberField K] :
    Subgroup (Chapter08FiniteIdeles K) where
  carrier := {x | ∀ v, chapter08FiniteIdeleOrder x v = 0}
  one_mem' := by
    intro v
    apply (chapter08_local_order_eq_zero_iff_valued_eq_one v _
      (chapter08_finite_idele_component_ne_zero (1 : Chapter08FiniteIdeles K) v)).2
    change Valued.v (1 : v.adicCompletion K) = 1
    exact Valuation.map_one _
  mul_mem' := by
    intro x y hx hy v
    rw [chapter08_finite_idele_order_mul, hx v, hy v, add_zero]
  inv_mem' := by
    intro x hx v
    rw [chapter08_finite_idele_order_inv, hx v, neg_zero]

theorem chapter08_mem_finiteIntegralUnits_iff
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    x ∈ chapter08FiniteIntegralUnits ↔
      ∀ v, chapter08FiniteIdeleOrder x v = 0 :=
  Iff.rfl

theorem chapter08_finite_integral_unit_iff_local_valued_eq_one
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    x ∈ chapter08FiniteIntegralUnits ↔
      ∀ v, (Valued.v (chapter08FiniteIdeleComponent x v) : ℤᵐ⁰) = 1 := by
  simp only [chapter08_mem_finiteIntegralUnits_iff]
  exact forall_congr' fun v =>
    chapter08_finite_idele_order_eq_zero_iff_local_unit x v

theorem chapter08_finite_idele_ideal_kernel
    {K : Type*} [Field K] [NumberField K] :
    MonoidHom.ker (chapter08FiniteIdeleIdealMap K) = chapter08FiniteIntegralUnits := by
  ext x
  rw [MonoidHom.mem_ker, chapter08_mem_finiteIntegralUnits_iff]
  constructor
  · intro hx v
    have hc := chapter08_finite_idele_ideal_count x v
    rw [hx] at hc
    change FractionalIdeal.count K v (1 : Chapter08FractionalIdeal K) =
      chapter08FiniteIdeleOrder x v at hc
    rw [FractionalIdeal.count_one] at hc
    exact hc.symm
  · intro hx
    apply Units.ext
    change chapter08FiniteIdeleFractionalIdeal x = 1
    have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization' K
      (I := chapter08FiniteIdeleFractionalIdeal x)
      (chapter08_finite_idele_fractionalIdeal_ne_zero x)
    calc
      chapter08FiniteIdeleFractionalIdeal x =
          ∏ᶠ v : HeightOneSpectrum (Chapter08Integers K),
            (v.asIdeal : Chapter08FractionalIdeal K) ^
              (FractionalIdeal.count K v (chapter08FiniteIdeleFractionalIdeal x)) :=
        hfac.symm
      _ = 1 := by
        have hcount : ∀ v : HeightOneSpectrum (Chapter08Integers K),
            FractionalIdeal.count K v (chapter08FiniteIdeleFractionalIdeal x) = 0 := by
          intro v
          have hc := chapter08_finite_idele_ideal_count x v
          change FractionalIdeal.count K v (chapter08FiniteIdeleFractionalIdeal x) =
            chapter08FiniteIdeleOrder x v at hc
          exact hc.trans (hx v)
        simp_rw [hcount, zpow_zero]
        exact finprod_one

theorem chapter08_finite_idele_ideal_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter08FiniteIdeleIdealMap K) := by
  classical
  intro I
  let hI : (I : Chapter08FractionalIdeal K) ≠ 0 := by
    exact Units.ne_zero I
  let d : Chapter08FiniteDivisors K :=
    Finsupp.mk (FractionalIdeal.finite_factors (I : Chapter08FractionalIdeal K)).toFinset
      (fun v => FractionalIdeal.count K v (I : Chapter08FractionalIdeal K))
      (fun _ => (FractionalIdeal.finite_factors (I : Chapter08FractionalIdeal K)).mem_toFinset)
  let localUnit : ∀ v : HeightOneSpectrum (Chapter08Integers K),
      (v.adicCompletion K)ˣ := fun v =>
    Units.mk0
      (Classical.choose
        (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
          K v (WithZero.exp (-d v)))) (by
        have hval := Classical.choose_spec
          (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
            K v (WithZero.exp (-d v)))
        intro hz
        rw [hz, map_zero] at hval
        exact WithZero.exp_ne_zero hval.symm)
  have hlocal : ∀ v : HeightOneSpectrum (Chapter08Integers K),
      Valued.v (localUnit v : v.adicCompletion K) = WithZero.exp (-d v) := by
    intro v
    change Valued.v (Classical.choose
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
        K v (WithZero.exp (-d v)))) = WithZero.exp (-d v)
    exact Classical.choose_spec
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
        K v (WithZero.exp (-d v)))
  have hdzero : ∀ᶠ v : HeightOneSpectrum (Chapter08Integers K) in Filter.cofinite,
      d v = 0 := by
    rw [Filter.eventually_cofinite]
    have hsupp : {v | ¬d v = 0} = (d.support : Set _) := by
      ext v
      simp [Finsupp.mem_support_iff]
    rw [hsupp]
    exact d.support.finite_toSet
  have hunit : ∀ᶠ v : HeightOneSpectrum (Chapter08Integers K) in Filter.cofinite,
      localUnit v ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
    filter_upwards [hdzero] with v hv
    apply (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).2
    rw [hlocal v, hv]
    exact WithZero.exp_zero
  let x : Chapter08FiniteIdeles K :=
    RestrictedProduct.mkUnit (fun v => localUnit v) hunit
  have hx : chapter08FiniteIdeleOrderFinsupp x = d := by
    ext v
    rw [chapter08FiniteIdeleOrderFinsupp_apply]
    change chapter08LocalOrder v (localUnit v : v.adicCompletion K) = d v
    unfold chapter08LocalOrder
    rw [hlocal v, dif_neg WithZero.exp_ne_zero,
      WithZero.toAdd_unzero_eq_log, WithZero.log_exp]
    ring
  refine ⟨x, ?_⟩
  apply Units.ext
  change chapter08FiniteIdeleFractionalIdeal x = (I : Chapter08FractionalIdeal K)
  rw [chapter08FiniteIdeleFractionalIdeal, hx]
  have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI
  rw [← hfac]
  rw [finprod_eq_finsetProd_of_mulSupport_subset
    (s := (FractionalIdeal.finite_factors (I : Chapter08FractionalIdeal K)).toFinset)]
  · rfl
  · rw [(FractionalIdeal.finite_factors (I : Chapter08FractionalIdeal K)).coe_toFinset]
    intro v hv h
    rw [Function.mem_mulSupport] at hv
    rw [h, zpow_zero] at hv
    exact hv rfl

theorem chapter08_finite_idele_ideal_short_exact
    (K : Type*) [Field K] [NumberField K] :
    chapter08IsShortExact (chapter08FiniteIntegralUnits (K := K)).subtype
      (chapter08FiniteIdeleIdealMap K) := by
  refine ⟨?_, ?_, chapter08_finite_idele_ideal_surjective K⟩
  exact (chapter08FiniteIntegralUnits (K := K)).subtype_injective
  rw [chapter08IsExact, Subgroup.range_subtype,
    chapter08_finite_idele_ideal_kernel]

/-! The sign convention is the book's convention: the exponent is `+ ord_v`. -/

def chapter08IdealNorm {K : Type*} [Field K] [NumberField K]
    (I : Chapter08IdealGroup K) : ℚ :=
  FractionalIdeal.absNorm (I : Chapter08FractionalIdeal K)

def chapter08FiniteIdeleNorm {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : ℚ :=
  ∏ᶠ v : HeightOneSpectrum (Chapter08Integers K),
    (Ideal.absNorm v.asIdeal : ℚ) ^ (-chapter08FiniteIdeleOrder x v)

theorem chapter08_finite_idele_norm_product_formula
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    chapter08FiniteIdeleNorm x =
      (chapter08IdealNorm (chapter08FiniteIdeleIdealMap K x))⁻¹ := by
  classical
  unfold chapter08FiniteIdeleNorm chapter08IdealNorm
  let I : Chapter08FractionalIdeal K := chapter08FiniteIdeleFractionalIdeal x
  have hI : I ≠ 0 := chapter08_finite_idele_fractionalIdeal_ne_zero x
  have hfinite : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (Chapter08Integers K) =>
        (v.asIdeal : Chapter08FractionalIdeal K) ^ FractionalIdeal.count K v I) := by
    rw [Function.HasFiniteMulSupport]
    refine (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)).subset ?_
    intro v hv
    rw [Function.mem_mulSupport] at hv
    intro hzero
    apply hv
    simp [hzero]
  have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI
  have hmap :
      FractionalIdeal.absNorm (∏ᶠ v : HeightOneSpectrum (Chapter08Integers K),
        (v.asIdeal : Chapter08FractionalIdeal K) ^ FractionalIdeal.count K v I) =
        ∏ᶠ v : HeightOneSpectrum (Chapter08Integers K),
          FractionalIdeal.absNorm
            ((v.asIdeal : Chapter08FractionalIdeal K) ^ FractionalIdeal.count K v I) :=
    ((FractionalIdeal.absNorm (R := Chapter08Integers K) (K := K)).toMonoidHom).map_finprod
      hfinite
  have hcount : ∀ v : HeightOneSpectrum (Chapter08Integers K),
      FractionalIdeal.count K v I = chapter08FiniteIdeleOrder x v := by
    intro v
    change FractionalIdeal.count K v (chapter08FiniteIdeleFractionalIdeal x) = _
    exact chapter08_finite_idele_ideal_count x v
  calc
    ∏ᶠ v : HeightOneSpectrum (Chapter08Integers K),
        (Ideal.absNorm v.asIdeal : ℚ) ^ (-chapter08FiniteIdeleOrder x v) =
      (∏ᶠ v : HeightOneSpectrum (Chapter08Integers K),
        FractionalIdeal.absNorm
          ((v.asIdeal : Chapter08FractionalIdeal K) ^ FractionalIdeal.count K v I))⁻¹ := by
      simp_rw [zpow_neg]
      rw [finprod_inv_distrib]
      apply congrArg Inv.inv
      apply finprod_congr
      intro v
      rw [map_zpow₀,
        FractionalIdeal.coeIdeal_absNorm, hcount]
    _ = (FractionalIdeal.absNorm I)⁻¹ := by
      rw [← hmap, hfac]
    _ = (FractionalIdeal.absNorm
        (chapter08FiniteIdeleFractionalIdeal x))⁻¹ := by
      rfl

def chapter08FiniteDegreeContribution {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : ℝ :=
  Real.log (chapter08IdealNorm (chapter08FiniteIdeleIdealMap K x) : ℝ)

theorem chapter08_finite_degree_contribution_eq_log_norm
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    chapter08FiniteDegreeContribution x =
      Real.log (chapter08IdealNorm (chapter08FiniteIdeleIdealMap K x) : ℝ) :=
  rfl

/-! Surjectivity is realized by local uniformizers at a finite set of places. -/

theorem chapter08_finite_idele_order_finsupp_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter08FiniteIdeleOrderFinsupp (K := K)) := by
  classical
  intro d
  let localUnit : ∀ v : HeightOneSpectrum (Chapter08Integers K),
      (v.adicCompletion K)ˣ := fun v =>
    Units.mk0
      (Classical.choose
        (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
          K v (WithZero.exp (-d v)))) (by
        have hval := Classical.choose_spec
          (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
            K v (WithZero.exp (-d v)))
        intro hz
        rw [hz, map_zero] at hval
        exact WithZero.exp_ne_zero hval.symm)
  have hlocal : ∀ v : HeightOneSpectrum (Chapter08Integers K),
      Valued.v (localUnit v : v.adicCompletion K) = WithZero.exp (-d v) := by
    intro v
    change Valued.v (Classical.choose
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
        K v (WithZero.exp (-d v)))) = WithZero.exp (-d v)
    exact Classical.choose_spec
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
        K v (WithZero.exp (-d v)))
  have hdzero : ∀ᶠ v : HeightOneSpectrum (Chapter08Integers K) in Filter.cofinite,
      d v = 0 := by
    rw [Filter.eventually_cofinite]
    have hsupp : {v | ¬d v = 0} = (d.support : Set _) := by
      ext v
      simp [Finsupp.mem_support_iff]
    rw [hsupp]
    exact d.support.finite_toSet
  have hunit : ∀ᶠ v : HeightOneSpectrum (Chapter08Integers K) in Filter.cofinite,
      localUnit v ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
    filter_upwards [hdzero] with v hv
    apply (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).2
    rw [hlocal v, hv]
    exact WithZero.exp_zero
  let z : Chapter08FiniteIdeles K :=
    RestrictedProduct.mkUnit (fun v => localUnit v) hunit
  refine ⟨z, ?_⟩
  ext v
  rw [chapter08FiniteIdeleOrderFinsupp_apply]
  change chapter08LocalOrder v (localUnit v : v.adicCompletion K) = d v
  unfold chapter08LocalOrder
  rw [hlocal v, dif_neg WithZero.exp_ne_zero,
    WithZero.toAdd_unzero_eq_log, WithZero.log_exp]
  ring

theorem chapter08_finite_idele_ideal_realizes_divisor
    (K : Type*) [Field K] [NumberField K]
    (d : Chapter08FiniteDivisors K) :
    ∃ x : Chapter08FiniteIdeles K,
      chapter08FiniteIdeleOrderFinsupp x = d := by
  exact chapter08_finite_idele_order_finsupp_surjective K d

def chapter08FinitePrincipalIdele {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) : Chapter08FiniteIdeles K :=
  IsDedekindDomain.FiniteAdeleRing.unitEmbedding (Chapter08Integers K) K a

def chapter08FinitePrincipalIdeleHom (K : Type*) [Field K] [NumberField K] :
    Kˣ →* Chapter08FiniteIdeles K :=
  IsDedekindDomain.FiniteAdeleRing.unitEmbedding (Chapter08Integers K) K

theorem chapter08FinitePrincipalIdeleHom_apply
    {K : Type*} [Field K] [NumberField K] (a : Kˣ) :
    chapter08FinitePrincipalIdeleHom K a = chapter08FinitePrincipalIdele a :=
  rfl

theorem chapter08_finite_idele_ideal_principal
    {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) :
    chapter08FiniteIdeleIdealMap K (chapter08FinitePrincipalIdele a) =
      toPrincipalIdeal (Chapter08Integers K) K a := by
  apply Units.ext
  rw [chapter08FiniteIdeleIdealMap_apply]
  simp only [chapter08FiniteIdeleIdeal, chapter08FiniteIdeleFractionalIdeal,
    Units.val_mk0, coe_toPrincipalIdeal]
  have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization'
    K (I := FractionalIdeal.spanSingleton (Chapter08Integers K)⁰ (a : K)) (by
      exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr a.ne_zero)
  have hcount : ∀ v : HeightOneSpectrum (Chapter08Integers K),
      FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (Chapter08Integers K)⁰ (a : K)) =
        chapter08FiniteIdeleOrderFinsupp (chapter08FinitePrincipalIdele a) v := by
    intro v
    rw [chapter08FiniteIdeleOrderFinsupp_apply]
    change FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (Chapter08Integers K)⁰ (a : K)) =
      chapter08LocalOrder v (a : v.adicCompletion K)
    unfold chapter08LocalOrder
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
        v a.ne_zero]
    rw [dif_neg WithZero.exp_ne_zero, WithZero.toAdd_unzero_eq_log,
      WithZero.log_exp]
    simp [LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent]
  have hfinite := chapter08_finite_idele_order_eventually_eq_zero
    (chapter08FinitePrincipalIdele a)
  rw [← hfac]
  simp_rw [hcount]
  rw [finprod_eq_finsetProd_of_mulSupport_subset
    (s := hfinite.toFinset)]
  · rfl
  · rw [hfinite.coe_toFinset]
    intro v hv h
    rw [Function.mem_mulSupport] at hv
    have horder : chapter08FiniteIdeleOrderFinsupp
        (chapter08FinitePrincipalIdele a) v = 0 := by
      rw [chapter08FiniteIdeleOrderFinsupp_apply]
      exact h
    rw [horder, zpow_zero] at hv
    exact hv rfl

/-! The opposite convention used in some references is obtained by inversion. -/

def chapter08OppositeFiniteIdeleIdealMap
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : Chapter08IdealGroup K :=
  (chapter08FiniteIdeleIdealMap K x)⁻¹

theorem chapter08_opposite_finite_idele_ideal_count
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (v : HeightOneSpectrum (Chapter08Integers K)) :
    FractionalIdeal.count K v
        (chapter08OppositeFiniteIdeleIdealMap x : Chapter08FractionalIdeal K) =
      -chapter08FiniteIdeleOrder x v := by
  change FractionalIdeal.count K v
      ((chapter08FiniteIdeleIdealMap K x : Chapter08FractionalIdeal K)⁻¹) = _
  rw [FractionalIdeal.count_inv, chapter08_finite_idele_ideal_count]

theorem chapter08_finite_idele_realization_need_not_be_global_principal
    (K : Type*) [Field K] [NumberField K]
    {I : Chapter08IdealGroup K}
    (hI : ClassGroup.mk K I ≠ 1) :
    ∀ a : Kˣ, chapter08FiniteIdeleIdealMap K
      (chapter08FinitePrincipalIdele a) ≠ I := by
  intro a ha
  apply hI
  rw [← ha, chapter08_finite_idele_ideal_principal]
  apply (ClassGroup.mk_eq_one_iff).2
  refine ⟨(a : K), ?_⟩
  simp [coe_toPrincipalIdeal]

/-! Topological assertions are stated with the source's graph topology and discrete target. -/

theorem chapter08_finite_idele_ideal_continuous
    (K : Type*) [Field K] [NumberField K] :
    letI : TopologicalSpace (Chapter08FiniteIdeles K) :=
      chapter08FiniteIdeleGraphTopology K
    letI : TopologicalSpace (Chapter08IdealGroup K) := ⊥
    Continuous (chapter08FiniteIdeleIdealMap K) := by
  have hkernel : @IsOpen (Chapter08FiniteIdeles K)
      (chapter08FiniteIdeleGraphTopology K)
      (chapter08FiniteIntegralUnits (K := K) : Set (Chapter08FiniteIdeles K)) := by
    let B : ∀ v : HeightOneSpectrum (Chapter08Integers K),
        Set ((v.adicCompletion K)ˣ) :=
      fun v => (Submonoid.ofClass (v.adicCompletionIntegers K)).units
    let U : Set (Πʳ v : HeightOneSpectrum (Chapter08Integers K),
        [(v.adicCompletion K)ˣ, B v]) :=
      {z | ∀ v, z v ∈ B v}
    have hB : ∀ v : HeightOneSpectrum (Chapter08Integers K), IsOpen (B v) := by
      intro v
      exact Submonoid.isOpen_units
        (Valued.isOpen_valuationSubring (v.adicCompletion K))
    have hU : IsOpen U := RestrictedProduct.isOpen_forall_mem hB
    have heq :
        (chapter08FiniteIntegralUnits (K := K) : Set (Chapter08FiniteIdeles K)) =
          (RestrictedProduct.unitsEquiv
            (𝓕 := Filter.cofinite)
            (B := fun v : HeightOneSpectrum (Chapter08Integers K) =>
              v.adicCompletionIntegers K)
            (fun v : HeightOneSpectrum (Chapter08Integers K) =>
              v.adicCompletion K)) ⁻¹' U := by
      ext z
      constructor
      · intro hz v
        change (RestrictedProduct.unitsEquiv
          (𝓕 := Filter.cofinite)
          (B := fun v : HeightOneSpectrum (Chapter08Integers K) =>
            v.adicCompletionIntegers K)
          (fun v : HeightOneSpectrum (Chapter08Integers K) =>
            v.adicCompletion K) z v) ∈ (v.adicCompletionIntegers K).units
        apply IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.2
        have he := RestrictedProduct.unitsEquiv_apply
          (R := fun v : HeightOneSpectrum (Chapter08Integers K) =>
            v.adicCompletion K) v z
        rw [he]
        change Valued.v (chapter08FiniteIdeleComponent z v) = 1
        exact (chapter08_finite_integral_unit_iff_local_valued_eq_one z).1 hz v
      · intro hz
        refine (chapter08_finite_integral_unit_iff_local_valued_eq_one z).2 ?_
        intro v
        have hv := hz v
        change (RestrictedProduct.unitsEquiv
          (𝓕 := Filter.cofinite)
          (B := fun v : HeightOneSpectrum (Chapter08Integers K) =>
            v.adicCompletionIntegers K)
          (fun v : HeightOneSpectrum (Chapter08Integers K) =>
            v.adicCompletion K) z v) ∈ (v.adicCompletionIntegers K).units at hv
        have hval :=
          IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.1 hv
        have he := RestrictedProduct.unitsEquiv_apply
          (R := fun v : HeightOneSpectrum (Chapter08Integers K) =>
            v.adicCompletion K) v z
        rw [he] at hval
        change Valued.v (chapter08FiniteIdeleComponent z v) = 1 at hval
        exact hval
    rw [heq]
    exact isOpen_induced hU
  have hdisc : @DiscreteTopology (Chapter08IdealGroup K) ⊥ :=
    discreteTopology_bot _
  have hgroup : @IsTopologicalGroup (Chapter08FiniteIdeles K)
      (chapter08FiniteIdeleGraphTopology K) Units.instGroup :=
    letI : Fact (∀ v : HeightOneSpectrum (Chapter08Integers K),
        IsOpen ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
          Set ((v.adicCompletion K)ˣ))) := ⟨by
      intro v
      exact Submonoid.isOpen_units
        (Valued.isOpen_valuationSubring (v.adicCompletion K))⟩
    topologicalGroup_induced
      (RestrictedProduct.unitsEquiv
        (𝓕 := Filter.cofinite)
        (B := fun v : HeightOneSpectrum (Chapter08Integers K) =>
          v.adicCompletionIntegers K)
        (fun v : HeightOneSpectrum (Chapter08Integers K) =>
          v.adicCompletion K))
  have hsep : @SeparatelyContinuousMul (Chapter08FiniteIdeles K)
      (chapter08FiniteIdeleGraphTopology K) _ :=
    letI : @ContinuousMul (Chapter08FiniteIdeles K)
        (chapter08FiniteIdeleGraphTopology K) _ := hgroup.toContinuousMul
    inferInstance
  apply (@continuous_discrete_rng (Chapter08IdealGroup K) (Chapter08FiniteIdeles K)
    (chapter08FiniteIdeleGraphTopology K) ⊥ hdisc
    (chapter08FiniteIdeleIdealMap K)).2
  intro I
  obtain ⟨x, hx⟩ := chapter08_finite_idele_ideal_surjective K I
  have hpre : (chapter08FiniteIdeleIdealMap K) ⁻¹' ({I} : Set (Chapter08IdealGroup K)) =
      (fun z : Chapter08FiniteIdeles K => x * z) ''
        (MonoidHom.ker (chapter08FiniteIdeleIdealMap K) : Set (Chapter08FiniteIdeles K)) := by
    ext y
    constructor
    · intro hy
      change chapter08FiniteIdeleIdealMap K y = I at hy
      have hmem : x⁻¹ * y ∈ MonoidHom.ker (chapter08FiniteIdeleIdealMap K) := by
        rw [MonoidHom.mem_ker]
        simp [map_mul, hx, hy]
      exact ⟨x⁻¹ * y, hmem, by simp⟩
    · rintro ⟨z, hz, rfl⟩
      change chapter08FiniteIdeleIdealMap K (x * z) = I
      rw [map_mul, hx, MonoidHom.mem_ker.mp hz, mul_one]
  rw [chapter08_finite_idele_ideal_kernel] at hpre
  rw [hpre]
  exact @isOpenMap_mul_left (Chapter08FiniteIdeles K)
    (chapter08FiniteIdeleGraphTopology K) Units.instGroup hsep x _ hkernel

theorem chapter08_finite_idele_ideal_isOpenMap
    (K : Type*) [Field K] [NumberField K] :
    letI : TopologicalSpace (Chapter08FiniteIdeles K) :=
      chapter08FiniteIdeleGraphTopology K
    letI : TopologicalSpace (Chapter08IdealGroup K) := ⊥
    IsOpenMap (chapter08FiniteIdeleIdealMap K) := by
  have hdisc : @DiscreteTopology (Chapter08IdealGroup K) ⊥ :=
    discreteTopology_bot _
  intro s hs
  exact @isOpen_discrete (Chapter08IdealGroup K) ⊥ hdisc (chapter08FiniteIdeleIdealMap K '' s)

theorem chapter08_ideal_group_has_discrete_topology
    (K : Type*) [Field K] [NumberField K] :
    @DiscreteTopology (Chapter08IdealGroup K) ⊥ := by
  exact discreteTopology_bot _

end

end LastLib.Book04AdelesAndIdeles.Chapter08
