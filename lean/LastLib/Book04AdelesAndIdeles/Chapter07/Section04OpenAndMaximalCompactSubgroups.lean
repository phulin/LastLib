import LastLib.Book04AdelesAndIdeles.Chapter07.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter07.Section03AdditiveAndMultiplicativeInformation
import Mathlib.Topology.Algebra.IsOpenUnits

namespace LastLib.Book04AdelesAndIdeles.Chapter07

noncomputable section

open Set Filter Topology WithZeroTopology
open scoped BigOperators DirectSum RestrictedProduct WithZero

/-! # 7.4 Open and maximal compact subgroups -/

/-- Data expressing the discrete-valued local structure used in the local decomposition. -/
structure Chapter07LocalOrderDecompositionData
    (G : Type*) [CommGroup G] [TopologicalSpace G] where
  integralUnits : Subgroup G
  order : G → ℤ
  order_one : order 1 = 0
  order_mul : ∀ x y, order (x * y) = order x + order y
  uniformizer : G
  order_uniformizer : order uniformizer = 1
  kernel_order : {x | order x = 0} = integralUnits
  order_continuous : Continuous order
  integralUnits_open : IsOpen (integralUnits : Set G)
  integralUnits_compact : IsCompact (integralUnits : Set G)
  order_surjective : Function.Surjective order

/-- The local order coset of integer `n`. -/
def chapter07LocalOrderCoset
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (D : Chapter07LocalOrderDecompositionData G) (n : ℤ) : Set G :=
  {x | D.order x = n}

theorem chapter07_local_order_coset_eq_uniformizer_power_mul_units
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (D : Chapter07LocalOrderDecompositionData G) (n : ℤ) :
    chapter07LocalOrderCoset D n =
      {x | ∃ u : G, u ∈ D.integralUnits ∧ x = D.uniformizer ^ n * u} := by
  have hpow : ∀ m : ℤ, D.order (D.uniformizer ^ m) = m := by
    intro m
    let F : G →* Multiplicative ℤ :=
      { toFun := fun x => Multiplicative.ofAdd (D.order x)
        map_one' := by simp [D.order_one]
        map_mul' := by
          intro x y
          simp [D.order_mul] }
    have h := congrArg Multiplicative.toAdd (map_zpow F D.uniformizer m)
    simpa [F, D.order_uniformizer] using h
  ext x
  constructor
  · intro hx
    have hxorder : D.order x = n := hx
    refine ⟨D.uniformizer ^ (-n) * x, ?_, ?_⟩
    · have hzero : D.order (D.uniformizer ^ (-n) * x) = 0 := by
        rw [D.order_mul, hpow, hxorder]
        abel
      have hmem : D.uniformizer ^ (-n) * x ∈
          ({y : G | D.order y = 0} : Set G) := hzero
      rw [D.kernel_order] at hmem
      exact hmem
    · rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  · rintro ⟨u, hu, rfl⟩
    change D.order (D.uniformizer ^ n * u) = n
    have hu0 : D.order u = 0 := by
      have humem : u ∈ ({y : G | D.order y = 0} : Set G) := by
        rw [D.kernel_order]
        exact hu
      exact humem
    rw [D.order_mul, hpow, hu0, add_zero]

theorem chapter07_local_order_coset_open
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (D : Chapter07LocalOrderDecompositionData G) (n : ℤ) :
    IsOpen (chapter07LocalOrderCoset D n) := by
  change IsOpen (D.order ⁻¹' ({n} : Set ℤ))
  apply D.order_continuous.isOpen_preimage
  exact (discreteTopology_iff_isOpen_singleton.mp (inferInstance : DiscreteTopology ℤ)) n

theorem chapter07_local_order_continuous
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (D : Chapter07LocalOrderDecompositionData G) :
    Continuous D.order :=
  D.order_continuous

theorem chapter07_local_order_cosets_cover
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (D : Chapter07LocalOrderDecompositionData G) :
    (⋃ n : ℤ, chapter07LocalOrderCoset D n) = Set.univ := by
  ext x
  simp [chapter07LocalOrderCoset]

theorem chapter07_local_order_cosets_pairwise_disjoint
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (D : Chapter07LocalOrderDecompositionData G) :
    Pairwise (fun m n : ℤ =>
      Disjoint (chapter07LocalOrderCoset D m) (chapter07LocalOrderCoset D n)) := by
  intro m n hmn
  rw [Set.disjoint_left]
  intro x hxm hxn
  exact hmn (by
    calc
      m = D.order x := by simpa [chapter07LocalOrderCoset] using hxm.symm
      _ = n := by simpa [chapter07LocalOrderCoset] using hxn)

theorem chapter07_finite_local_order_continuous
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :
    Continuous (chapter07LocalOrder R K v) := by
  apply (continuous_discrete_rng (f := chapter07LocalOrder R K v)).2
  intro n
  have hval : Continuous (fun u : (chapter07LocalField R K v)ˣ =>
      (u : chapter07LocalField R K v)) :=
    Units.continuous_val
  have hv : Continuous (fun u : (chapter07LocalField R K v)ˣ =>
      Valued.v (u : chapter07LocalField R K v)) :=
    (Valued.continuous_valuation_of_surjective
      (v.valuedAdicCompletion_surjective K)).comp hval
  have hset :
      (chapter07LocalOrder R K v ⁻¹' ({n} : Set ℤ)) =
        (fun u : (chapter07LocalField R K v)ˣ =>
          Valued.v (u : chapter07LocalField R K v)) ⁻¹'
          ({WithZero.exp (-n)} : Set (WithZero (Multiplicative ℤ))) := by
    ext u
    have hu : Valued.v (u : chapter07LocalField R K v) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (by simp)
    constructor
    · intro huorder
      have hlog : WithZero.log (Valued.v (u : chapter07LocalField R K v)) = -n := by
        have := congrArg Neg.neg huorder
        simpa [chapter07LocalOrder] using this
      have := congrArg WithZero.exp hlog
      simpa [WithZero.exp_log hu] using this
    · intro huv
      have hlog : WithZero.log (Valued.v (u : chapter07LocalField R K v)) = -n := by
        have := congrArg WithZero.log huv
        simpa using this
      simp [chapter07LocalOrder, hlog]
  rw [hset]
  apply hv.isOpen_preimage
  apply WithZeroTopology.isOpen_iff.mpr
  left
  change (0 : WithZero (Multiplicative ℤ)) ≠ WithZero.exp (-n)
  exact (WithZero.exp_ne_zero :
    WithZero.exp (-n) ≠ (0 : WithZero (Multiplicative ℤ))).symm

theorem chapter07_finite_local_order_surjective
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :
    Function.Surjective (chapter07LocalOrder R K v) := by
  exact chapter07LocalOrder_surjective R K v

theorem chapter07_finite_local_order_kernel
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :
    {u | chapter07LocalOrder R K v u = 0} =
      chapter07LocalIntegralUnitSubgroup R K v := by
  ext u
  exact chapter07LocalOrder_eq_zero_iff_mem_localIntegralUnitSubgroup R K v u

theorem chapter07_finite_local_order_coset_open
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) (n : ℤ) :
    IsOpen {u : (chapter07LocalField R K v)ˣ |
      chapter07LocalOrder R K v u = n} := by
  change IsOpen ((chapter07LocalOrder R K v) ⁻¹' ({n} : Set ℤ))
  exact (chapter07_finite_local_order_continuous R K v).isOpen_preimage
    ({n} : Set ℤ)
    ((discreteTopology_iff_isOpen_singleton.mp (inferInstance : DiscreteTopology ℤ)) n)

theorem chapter07_finite_local_order_cosets_cover
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :
    (⋃ n : ℤ, {u : (chapter07LocalField R K v)ˣ |
      chapter07LocalOrder R K v u = n}) = Set.univ := by
  ext u
  simp

theorem chapter07_finite_local_order_cosets_pairwise_disjoint
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :
    Pairwise (fun m n : ℤ =>
      Disjoint
        {u : (chapter07LocalField R K v)ˣ |
          chapter07LocalOrder R K v u = m}
        {u : (chapter07LocalField R K v)ˣ |
          chapter07LocalOrder R K v u = n}) := by
  intro m n hmn
  exact Set.disjoint_left.2 (fun u hum hun =>
    hmn (by simpa using hum.symm.trans hun))

theorem chapter07_finite_local_idele_coset_decomposition
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) (π : (chapter07LocalField R K v)ˣ)
    (hπ : chapter07LocalOrder R K v π = 1) :
    ∀ x : (chapter07LocalField R K v)ˣ, ∃ n : ℤ, ∃ u : (chapter07LocalField R K v)ˣ,
      u ∈ chapter07LocalIntegralUnitSubgroup R K v ∧
        x = π ^ n * u := by
  intro x
  let F : (chapter07LocalField R K v)ˣ →* Multiplicative ℤ :=
    { toFun := fun y => Multiplicative.ofAdd (chapter07LocalOrder R K v y)
      map_one' := by
        simp [chapter07LocalOrder_apply_one]
      map_mul' := by
        intro y z
        simp [chapter07LocalOrder_mul] }
  have hpow : ∀ m : ℤ,
      chapter07LocalOrder R K v (π ^ m) = m := by
    intro m
    have h := congrArg Multiplicative.toAdd (map_zpow F π m)
    simpa [F, hπ] using h
  refine ⟨chapter07LocalOrder R K v x,
    π ^ (-(chapter07LocalOrder R K v x)) * x, ?_, ?_⟩
  · apply (chapter07LocalOrder_eq_zero_iff_mem_localIntegralUnitSubgroup R K v
      (π ^ (-(chapter07LocalOrder R K v x)) * x)).1
    rw [chapter07LocalOrder_mul, hpow]
    have hx := chapter07LocalOrder R K v x
    abel
  · rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]

/-- The homomorphism in the global finite exact sequence is the finite order map. -/
def chapter07FiniteIntegralUnitInclusion
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    chapter07FiniteIntegralUnitSubgroup R K →*
      chapter07FiniteIdeleGroup R K :=
  (chapter07FiniteIntegralUnitSubgroup R K).subtype

theorem chapter07_finite_order_kernel
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    (chapter07FiniteOrderHom R K).ker =
      (chapter07FiniteIntegralUnitInclusion R K).range := by
  ext x
  constructor
  · intro hx
    have hx' : chapter07FiniteOrderValue R K x = 0 := by
      simpa [chapter07FiniteOrderValue] using hx
    have hmem : x ∈ chapter07FiniteIntegralUnitSubgroup R K :=
      (chapter07_finite_order_value_eq_zero_iff R K x).1 hx'
    exact ⟨⟨x, hmem⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    change chapter07FiniteOrderHom R K (y : chapter07FiniteIdeleGroup R K) = 1
    have hzero : chapter07FiniteOrderValue R K (y : chapter07FiniteIdeleGroup R K) = 0 :=
      (chapter07_finite_order_value_eq_zero_iff R K (y : chapter07FiniteIdeleGroup R K)).2 y.property
    simpa [chapter07FiniteOrderValue] using hzero

theorem chapter07_finite_order_exact_sequence
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Function.MulExact (chapter07FiniteIntegralUnitInclusion R K)
      (chapter07FiniteOrderHom R K) := by
  apply MonoidHom.mulExact_of_comp_of_mem_range
  · ext x v
    have hzero : chapter07FiniteOrderValue R K
        (x : chapter07FiniteIdeleGroup R K) = 0 :=
      (chapter07_finite_order_value_eq_zero_iff R K
        (x : chapter07FiniteIdeleGroup R K)).2 x.property
    have hhom : chapter07FiniteOrderHom R K
        (x : chapter07FiniteIdeleGroup R K) = 1 := by
      simpa [chapter07FiniteOrderValue] using hzero
    exact congrArg (fun d : Multiplicative (chapter07FiniteDivisorGroup R) => d v) hhom
  · intro x hx
    have hx' : x ∈ (chapter07FiniteOrderHom R K).ker := hx
    rw [chapter07_finite_order_kernel R K] at hx'
    exact hx'

/-- The direct sum is equipped with the discrete topology when it is used as the quotient in the
finite exact sequence. -/
@[instance_reducible] def chapter07FiniteDivisorDiscreteTopology
    (R : Type*) [CommRing R] [IsDedekindDomain R] :
    TopologicalSpace (chapter07FiniteDivisorGroup R) :=
  ⊥

theorem chapter07_finite_order_continuous
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
      @Continuous (chapter07FiniteIdeleGroup R K)
      (Multiplicative (chapter07FiniteDivisorGroup R))
      inferInstance (chapter07FiniteDivisorDiscreteTopology R)
      (chapter07FiniteOrderHom R K) := by
  classical
  rw [chapter07_finiteIdele_restrictedProduct_topology R K]
  let G : chapter07FiniteIdeleRestrictedProduct R K →
      Multiplicative (chapter07FiniteDivisorGroup R) := fun y =>
    Multiplicative.ofAdd <|
      chapter07FiniteOrderVector
        (fun v : chapter07FinitePlace R => (chapter07LocalField R K v)ˣ)
        (fun v : chapter07FinitePlace R =>
          (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units)
        (fun v : chapter07FinitePlace R => chapter07LocalOrder R K v) y
  have hdisc : @DiscreteTopology (Multiplicative (chapter07FiniteDivisorGroup R))
      (chapter07FiniteDivisorDiscreteTopology R) :=
    discreteTopology_bot _
  have hG : @Continuous (chapter07FiniteIdeleRestrictedProduct R K)
      (Multiplicative (chapter07FiniteDivisorGroup R))
      (inferInstance : TopologicalSpace (chapter07FiniteIdeleRestrictedProduct R K))
      (chapter07FiniteDivisorDiscreteTopology R) G := by
    apply (@continuous_discrete_rng
      (Multiplicative (chapter07FiniteDivisorGroup R))
      (chapter07FiniteIdeleRestrictedProduct R K)
      (inferInstance : TopologicalSpace (chapter07FiniteIdeleRestrictedProduct R K))
      (chapter07FiniteDivisorDiscreteTopology R) hdisc).mpr
    intro d
    let S : Set (chapter07FinitePlace R) :=
      (Multiplicative.toAdd d).support
    let U : (v : chapter07FinitePlace R) →
        Set ((chapter07LocalField R K v)ˣ) := fun v =>
      {u | chapter07LocalOrder R K v u = (Multiplicative.toAdd d) v}
    have hS : S.Finite := (Multiplicative.toAdd d).support.finite_toSet
    have hU : ∀ v, IsOpen (U v) := by
      intro v
      change IsOpen (chapter07LocalOrder R K v ⁻¹'
        ({(Multiplicative.toAdd d) v} : Set ℤ))
      apply (chapter07_finite_local_order_continuous R K v).isOpen_preimage
      exact (discreteTopology_iff_isOpen_singleton.mp
        (inferInstance : DiscreteTopology ℤ)) _
    have hA : ∀ v : chapter07FinitePlace R,
        IsOpen ((Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units :
          Set ((chapter07LocalField R K v)ˣ)) := by
      intro v
      have hlocal : IsOpen (chapter07LocalIntegerRing R K v :
          Set (chapter07LocalField R K v)) := by
        exact Valued.isOpen_valuationSubring _
      exact Submonoid.isOpen_units hlocal
    have hopen := chapter07_restrictedProduct_basicOpen_isOpen_shared
      (fun v : chapter07FinitePlace R => (chapter07LocalField R K v)ˣ)
      (fun v : chapter07FinitePlace R =>
        (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units)
      S hS U hU hA
    have heq : G ⁻¹' ({d} : Set (Multiplicative (chapter07FiniteDivisorGroup R))) =
        chapter07RestrictedProductBasicOpenShared
          (fun v : chapter07FinitePlace R => (chapter07LocalField R K v)ˣ)
          (fun v : chapter07FinitePlace R =>
            (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units)
          S U := by
      ext y
      constructor
      · intro hy
        constructor
        · intro v hv
          have hvec := congrArg Multiplicative.toAdd hy
          have hval := congrArg (fun z : chapter07FiniteDivisorGroup R => z v) hvec
          by_cases hmem : y v ∈
              (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units
          · have hz : chapter07LocalOrder R K v (y v) = 0 :=
              chapter07LocalOrder_eq_zero_on_integral_units R K v (y v) hmem
            have hdzero : (Multiplicative.toAdd d) v = 0 := by
              have hdzero' : 0 = (Multiplicative.toAdd d) v := by
                simpa [G, chapter07FiniteOrderVector_apply, hmem] using hval
              exact hdzero'.symm
            change chapter07LocalOrder R K v (y v) =
              (Multiplicative.toAdd d) v
            rw [hz, hdzero]
          · have huv : chapter07LocalOrder R K v (y v) =
                (Multiplicative.toAdd d) v := by
              simpa [G, chapter07FiniteOrderVector_apply, hmem] using hval
            change chapter07LocalOrder R K v (y v) =
              (Multiplicative.toAdd d) v
            exact huv
        · intro v hv
          change y v ∈
            (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units
          by_contra hmem
          have hvec := congrArg Multiplicative.toAdd hy
          have hval := congrArg (fun z : chapter07FiniteDivisorGroup R => z v) hvec
          have hzero : (Multiplicative.toAdd d) v = 0 := by
            exact Finsupp.notMem_support_iff.mp hv
          have hord : chapter07LocalOrder R K v (y v) = 0 := by
            simpa [G, chapter07FiniteOrderVector_apply, hmem, hzero] using hval
          exact hmem ((chapter07LocalOrder_eq_zero_iff_mem_localIntegralUnitSubgroup
            R K v (y v)).1 hord)
      · intro hy
        apply congrArg Multiplicative.ofAdd ?_
        ext v
        by_cases hv : v ∈ S
        · have huv : chapter07LocalOrder R K v (y v) =
              (Multiplicative.toAdd d) v := hy.1 v hv
          rw [chapter07FiniteOrderVector_apply]
          change (if y v ∉
              (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units then
              chapter07LocalOrder R K v (y v) else 0) =
            (Multiplicative.toAdd d) v
          by_cases hmem : y v ∈
              (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units
          · have hz : chapter07LocalOrder R K v (y v) = 0 :=
              chapter07LocalOrder_eq_zero_on_integral_units R K v (y v) hmem
            have hzero : (Multiplicative.toAdd d) v = 0 := by
              rw [← huv, hz]
            rw [if_neg (by simp [hmem])]
            change 0 = (Multiplicative.toAdd d) v
            exact hzero.symm
          · rw [if_pos hmem]
            exact huv
        · have hmem := hy.2 v hv
          change y v ∈
            (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units at hmem
          have hzero : (Multiplicative.toAdd d) v = 0 := by
            exact Finsupp.notMem_support_iff.mp hv
          rw [chapter07FiniteOrderVector_apply]
          change (if y v ∉
              (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units then
              chapter07LocalOrder R K v (y v) else 0) =
            (Multiplicative.toAdd d) v
          rw [if_neg (by simp [hmem])]
          exact hzero.symm
    rw [heq]
    exact hopen
  have hcomp : @Continuous (chapter07FiniteIdeleGroup R K)
      (Multiplicative (chapter07FiniteDivisorGroup R))
      (TopologicalSpace.induced (chapter07FiniteIdeleEquiv R K)
        (inferInstance : TopologicalSpace (chapter07FiniteIdeleRestrictedProduct R K)))
      (chapter07FiniteDivisorDiscreteTopology R)
      (G ∘ chapter07FiniteIdeleEquiv R K) := by
    exact @Continuous.comp
      (chapter07FiniteIdeleGroup R K)
      (chapter07FiniteIdeleRestrictedProduct R K)
      (Multiplicative (chapter07FiniteDivisorGroup R))
      (TopologicalSpace.induced (chapter07FiniteIdeleEquiv R K)
        (inferInstance : TopologicalSpace (chapter07FiniteIdeleRestrictedProduct R K)))
      (inferInstance : TopologicalSpace (chapter07FiniteIdeleRestrictedProduct R K))
      (chapter07FiniteDivisorDiscreteTopology R)
      (chapter07FiniteIdeleEquiv R K)
      G hG
      (continuous_induced_dom :
        @Continuous (chapter07FiniteIdeleGroup R K)
          (chapter07FiniteIdeleRestrictedProduct R K)
          (TopologicalSpace.induced (chapter07FiniteIdeleEquiv R K)
            (inferInstance : TopologicalSpace (chapter07FiniteIdeleRestrictedProduct R K)))
          (inferInstance : TopologicalSpace (chapter07FiniteIdeleRestrictedProduct R K))
          (chapter07FiniteIdeleEquiv R K))
  simpa [G, chapter07FiniteOrderHom, Function.comp_def] using hcomp

theorem chapter07_finite_order_surjective
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Function.Surjective (chapter07FiniteOrderHom R K) := by
  intro d
  obtain ⟨x, hx⟩ :=
    chapter07_finite_order_value_surjective R K (Multiplicative.toAdd d)
  refine ⟨x, ?_⟩
  exact congrArg Multiplicative.ofAdd hx

noncomputable def chapter07FiniteOrderQuotientEquiv
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    (chapter07FiniteIdeleGroup R K ⧸ chapter07FiniteIntegralUnitSubgroup R K) ≃*
      Multiplicative (chapter07FiniteDivisorGroup R) := by
  let hker : (chapter07FiniteOrderHom R K).ker =
      chapter07FiniteIntegralUnitSubgroup R K := by
    rw [chapter07_finite_order_kernel R K]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  exact
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (chapter07FiniteOrderHom R K)
        (chapter07_finite_order_surjective R K))

theorem chapter07_finite_order_quotient_is_discrete_topologically
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    DiscreteTopology
      (chapter07FiniteIdeleGroup R K ⧸ chapter07FiniteIntegralUnitSubgroup R K) := by
  have hA : ∀ v : chapter07FinitePlace R,
      IsOpen (chapter07LocalIntegralUnitSubgroup R K v :
        Set ((chapter07LocalField R K v)ˣ)) := by
    intro v
    have hlocal : IsOpen (chapter07LocalIntegerRing R K v :
        Set (chapter07LocalField R K v)) := by
      exact Valued.isOpen_valuationSubring _
    exact Submonoid.isOpen_units hlocal
  let B := chapter07RestrictedProductBasicOpenShared
    (fun v : chapter07FinitePlace R => (chapter07LocalField R K v)ˣ)
    (fun v : chapter07FinitePlace R => chapter07LocalIntegralUnitSubgroup R K v)
    (∅ : Set (chapter07FinitePlace R))
    (fun _ => Set.univ)
  have hB : IsOpen B := by
    exact chapter07_restrictedProduct_basicOpen_isOpen_shared
      (fun v : chapter07FinitePlace R => (chapter07LocalField R K v)ˣ)
      (fun v : chapter07FinitePlace R => chapter07LocalIntegralUnitSubgroup R K v)
      ∅ Set.finite_empty (fun _ => Set.univ) (fun _ => isOpen_univ) hA
  have hpre : (chapter07FiniteIdeleEquiv R K) ⁻¹' B =
      (chapter07FiniteIntegralUnitSubgroup R K :
        Set (chapter07FiniteIdeleGroup R K)) := by
    ext x
    simp [B, chapter07RestrictedProductBasicOpenShared,
      chapter07FiniteIntegralUnitSubgroup]
  have hopen : IsOpen (chapter07FiniteIntegralUnitSubgroup R K :
      Set (chapter07FiniteIdeleGroup R K)) := by
    have htop : IsOpen[TopologicalSpace.induced
        (chapter07FiniteIdeleEquiv R K) inferInstance]
        ((chapter07FiniteIdeleEquiv R K) ⁻¹' B) :=
      isOpen_induced_iff.mpr ⟨B, hB, rfl⟩
    rw [hpre] at htop
    rw [← chapter07_finiteIdele_restrictedProduct_topology R K] at htop
    exact htop
  exact QuotientGroup.discreteTopology hopen

theorem chapter07_finite_divisor_group_is_discrete
    (R : Type*) [CommRing R] [IsDedekindDomain R] :
    @DiscreteTopology (chapter07FiniteDivisorGroup R)
      (chapter07FiniteDivisorDiscreteTopology R) := by
  exact discreteTopology_bot _

theorem chapter07_finite_order_quotient_is_discrete
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    DiscreteTopology
      (chapter07FiniteIdeleGroup R K ⧸ chapter07FiniteIntegralUnitSubgroup R K) := by
  exact chapter07_finite_order_quotient_is_discrete_topologically R K

/-- A choice of local uniformizers gives a noncanonical section of the finite order map. -/
structure Chapter07UniformizerChoice
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] where
  uniformizer : ∀ v : chapter07FinitePlace R, (chapter07LocalField R K v)ˣ
  order_uniformizer : ∀ v, chapter07LocalOrder R K v (uniformizer v) = 1

theorem chapter07_uniformizer_choice_exists
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Nonempty (Chapter07UniformizerChoice R K) := by
  classical
  let u : ∀ v : chapter07FinitePlace R, (chapter07LocalField R K v)ˣ :=
    fun v => Classical.choose (chapter07LocalOrder_surjective R K v 1)
  exact ⟨⟨u, fun v => Classical.choose_spec (chapter07LocalOrder_surjective R K v 1)⟩⟩

noncomputable def chapter07FiniteOrderSection
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (c : Chapter07UniformizerChoice R K) :
    Multiplicative (chapter07FiniteDivisorGroup R) →*
      chapter07FiniteIdeleGroup R K :=
  { toFun := fun d =>
      (chapter07FiniteIdeleEquiv R K).symm
        (RestrictedProduct.mk
          (fun v : chapter07FinitePlace R =>
            c.uniformizer v ^ (Multiplicative.toAdd d) v)
          (by
            filter_upwards [d.support.finite_toSet.compl_mem_cofinite] with v hv
            have hdv : Multiplicative.toAdd d v = 0 :=
              Finsupp.notMem_support_iff.mp hv
            rw [hdv, zpow_zero]
            exact (chapter07LocalIntegralUnitSubgroup R K v).one_mem))
    map_one' := by
      apply (chapter07FiniteIdeleEquiv R K).injective
      ext v
      simp
    map_mul' := by
      intro d e
      apply (chapter07FiniteIdeleEquiv R K).injective
      simp [map_mul]
      ext v
      change (↑(c.uniformizer v ^ ((Multiplicative.toAdd d) v +
        (Multiplicative.toAdd e) v)) : chapter07LocalField R K v).toCompletion =
        (↑(c.uniformizer v ^ (Multiplicative.toAdd d) v) :
          chapter07LocalField R K v).toCompletion *
        (↑(c.uniformizer v ^ (Multiplicative.toAdd e) v) :
          chapter07LocalField R K v).toCompletion
      have hz : c.uniformizer v ^ ((Multiplicative.toAdd d) v +
          (Multiplicative.toAdd e) v) =
          c.uniformizer v ^ (Multiplicative.toAdd d) v *
            c.uniformizer v ^ (Multiplicative.toAdd e) v := by
        rw [zpow_add]
      simpa using congrArg
        (fun u : (chapter07LocalField R K v)ˣ =>
          (u : chapter07LocalField R K v).toCompletion) hz }

theorem chapter07_finite_order_section_right_inverse
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (c : Chapter07UniformizerChoice R K) :
    (chapter07FiniteOrderHom R K).comp (chapter07FiniteOrderSection R K c) =
      MonoidHom.id (Multiplicative (chapter07FiniteDivisorGroup R)) := by
  classical
  apply MonoidHom.ext
  intro d
  change chapter07FiniteOrderHom R K (chapter07FiniteOrderSection R K c d) = d
  change Multiplicative.toAdd
      (chapter07FiniteOrderHom R K (chapter07FiniteOrderSection R K c d)) =
    Multiplicative.toAdd d
  ext v
  rw [chapter07FiniteOrderHom_apply]
  change (if c.uniformizer v ^ (Multiplicative.toAdd d) v ∈
      chapter07LocalIntegralUnitSubgroup R K v then 0
    else chapter07LocalOrder R K v
      (c.uniformizer v ^ (Multiplicative.toAdd d) v)) = (Multiplicative.toAdd d) v
  let F : (chapter07LocalField R K v)ˣ →* Multiplicative ℤ :=
    { toFun := fun y => Multiplicative.ofAdd (chapter07LocalOrder R K v y)
      map_one' := by simp [chapter07LocalOrder_apply_one]
      map_mul' := by
        intro y z
        simp [chapter07LocalOrder_mul] }
  have hpow : ∀ m : ℤ,
      chapter07LocalOrder R K v (c.uniformizer v ^ m) = m := by
    intro m
    have h := congrArg Multiplicative.toAdd
      (map_zpow F (c.uniformizer v) m)
    simpa [F, c.order_uniformizer] using h
  by_cases hd : (Multiplicative.toAdd d) v = 0
  · rw [hd, zpow_zero]
    simp
  · have hnot : ¬ c.uniformizer v ^ (Multiplicative.toAdd d) v ∈
        chapter07LocalIntegralUnitSubgroup R K v := by
      intro hm
      have hz := (chapter07LocalOrder_eq_zero_iff_mem_localIntegralUnitSubgroup R K v
        (c.uniformizer v ^ (Multiplicative.toAdd d) v)).2 hm
      rw [hpow] at hz
      exact hd hz
    simp [hnot, hpow]

theorem chapter07_finite_order_section_continuous
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (c : Chapter07UniformizerChoice R K) :
      @Continuous (Multiplicative (chapter07FiniteDivisorGroup R))
      (chapter07FiniteIdeleGroup R K)
      (chapter07FiniteDivisorDiscreteTopology R) inferInstance
      (chapter07FiniteOrderSection R K c) := by
  change Continuous[⊥, inferInstance] (chapter07FiniteOrderSection R K c)
  exact continuous_bot

theorem chapter07_finite_order_splitting_is_noncanonical
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    ∀ c : Chapter07UniformizerChoice R K,
      Function.RightInverse (chapter07FiniteOrderSection R K c)
        (chapter07FiniteOrderHom R K) := by
  intro c d
  exact congrArg (fun f : Multiplicative (chapter07FiniteDivisorGroup R) →*
      Multiplicative (chapter07FiniteDivisorGroup R) => f d)
    (chapter07_finite_order_section_right_inverse R K c)

/-! ### Maximal compact subgroups -/

def chapter07RealMaximalCompact : Subgroup ℝˣ where
  carrier := {u | (u : ℝ) = 1 ∨ (u : ℝ) = -1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change (u : ℝ) = 1 ∨ (u : ℝ) = -1 at hu
    change (v : ℝ) = 1 ∨ (v : ℝ) = -1 at hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    all_goals
      change (↑(u * v) : ℝ) = 1 ∨ (↑(u * v) : ℝ) = -1
      simp [hu, hv]
  inv_mem' := by
    intro u hu
    change (u : ℝ) = 1 ∨ (u : ℝ) = -1 at hu
    rcases hu with hu | hu
    all_goals
      change (↑(u⁻¹) : ℝ) = 1 ∨ (↑(u⁻¹) : ℝ) = -1
      simp [hu]

def chapter07ComplexMaximalCompact : Subgroup ℂˣ where
  carrier := {u | ‖(u : ℂ)‖ = 1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change ‖(u : ℂ)‖ = 1 at hu
    change ‖(v : ℂ)‖ = 1 at hv
    change ‖(↑(u * v) : ℂ)‖ = 1
    change ‖(u : ℂ) * (v : ℂ)‖ = 1
    simp [hu, hv]
  inv_mem' := by
    intro u hu
    change ‖(u : ℂ)‖ = 1 at hu
    change ‖(↑(u⁻¹) : ℂ)‖ = 1
    simp [Units.val_inv_eq_inv_val, norm_inv, hu]

private theorem chapter07_compact_units_norm_eq_one
    (𝕜 : Type*) [NormedField 𝕜] (L : Subgroup 𝕜ˣ)
    (hL : IsCompact (L : Set 𝕜ˣ)) (u : 𝕜ˣ) (hu : u ∈ L) :
    ‖(u : 𝕜)‖ = 1 := by
  let f : 𝕜ˣ → ℝ := fun x => ‖(x : 𝕜)‖
  have hf : Continuous f := continuous_norm.comp Units.continuous_val
  obtain ⟨M, hM⟩ := (hL.image hf).bddAbove
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hinv : 1 < f u⁻¹ := by
      change 1 < ‖((u⁻¹ : 𝕜ˣ) : 𝕜)‖
      rw [Units.val_inv_eq_inv_val, norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.mpr (Units.ne_zero u))).2 hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hinv
    have hle : f (u⁻¹ ^ n) ≤ M :=
      hM ⟨u⁻¹ ^ n, L.pow_mem (L.inv_mem hu) n, rfl⟩
    have hle' : f u⁻¹ ^ n ≤ M := by
      simpa [f, norm_pow] using hle
    exact (not_lt_of_ge hle') hn
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hgt
    have hle : f (u ^ n) ≤ M :=
      hM ⟨u ^ n, L.pow_mem hu n, rfl⟩
    have hle' : f u ^ n ≤ M := by
      simpa [f, norm_pow] using hle
    exact (not_lt_of_ge hle') hn

theorem chapter07_real_maximal_compact_unique :
    chapter07UniqueMaximalCompactSubgroup ℝˣ chapter07RealMaximalCompact := by
  refine ⟨?_, ?_⟩
  · have hset : (chapter07RealMaximalCompact : Set ℝˣ) = {1, (-1 : ℝˣ)} := by
      ext u
      constructor
      · intro hu
        change (u : ℝ) = 1 ∨ (u : ℝ) = -1 at hu
        rcases hu with hu | hu
        · left
          exact Units.ext hu
        · right
          exact Units.ext hu
      · intro hu
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl <;>
          simp [chapter07RealMaximalCompact]
    rw [hset]
    have hfin : ({1, (-1 : ℝˣ)} : Set ℝˣ).Finite := by simp
    exact hfin.isCompact
  · intro L hL u hu
    change (u : ℝ) = 1 ∨ (u : ℝ) = -1
    have hnorm : ‖(u : ℝ)‖ = 1 :=
      chapter07_compact_units_norm_eq_one ℝ L hL u hu
    rw [Real.norm_eq_abs] at hnorm
    exact eq_or_eq_neg_of_abs_eq hnorm

theorem chapter07_complex_maximal_compact_unique :
    chapter07UniqueMaximalCompactSubgroup ℂˣ chapter07ComplexMaximalCompact := by
  refine ⟨?_, ?_⟩
  · have hset : (chapter07ComplexMaximalCompact : Set ℂˣ) =
        {u : ℂˣ | ‖(u : ℂ)‖ = 1} := by
      rfl
    rw [hset]
    let S : Set (ℂ × ℂᵐᵒᵖ) :=
      Metric.sphere (0 : ℂ) 1 ×ˢ
        (MulOpposite.op '' Metric.sphere (0 : ℂ) 1)
    have hS : IsCompact S := by
      exact (isCompact_sphere (0 : ℂ) 1).prod
        ((isCompact_sphere (0 : ℂ) 1).image MulOpposite.continuous_op)
    have hpre : (Units.embedProduct ℂ) ⁻¹' S =
        ({u : ℂˣ | ‖(u : ℂ)‖ = 1} : Set ℂˣ) := by
      ext u
      simp only [S, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply,
        Metric.mem_sphere, dist_zero_right]
      change (‖(u : ℂ)‖ = 1 ∧
        MulOpposite.op ((u⁻¹ : ℂˣ) : ℂ) ∈
          MulOpposite.op '' Metric.sphere (0 : ℂ) 1) ↔ ‖(u : ℂ)‖ = 1
      constructor
      · rintro ⟨hu, _⟩
        exact hu
      · intro hu
        refine ⟨hu, ?_⟩
        refine ⟨((u⁻¹ : ℂˣ) : ℂ), ?_, rfl⟩
        simpa [Units.val_inv_eq_inv_val, norm_inv] using hu
    rw [← hpre]
    exact Units.isClosedEmbedding_embedProduct.isCompact_preimage hS
  · intro L hL u hu
    change ‖(u : ℂ)‖ = 1
    exact chapter07_compact_units_norm_eq_one ℂ L hL u hu

def chapter07FiniteLocalMaximalCompact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :
    Subgroup (chapter07LocalField R K v)ˣ :=
  chapter07LocalIntegralUnitSubgroup R K v

private theorem chapter07_finite_local_residueField_finite_local
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    (v : chapter07FinitePlace R) :
    Finite (IsLocalRing.ResidueField (chapter07LocalIntegerRing R K v)) := by
  let hfiniteQuotient : Finite (R ⧸ v.asIdeal) :=
    v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  let f : R →+* IsLocalRing.ResidueField (chapter07LocalIntegerRing R K v) :=
    (IsLocalRing.residue (chapter07LocalIntegerRing R K v)).comp
      (algebraMap R (chapter07LocalIntegerRing R K v))
  have hf : ∀ r : R, r ∈ v.asIdeal → f r = 0 := by
    intro r hr
    apply (IsLocalRing.residue_eq_zero_iff
      (R := ↥(chapter07LocalIntegerRing R K v))
      (algebraMap R (chapter07LocalIntegerRing R K v) r)).2
    rw [IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit (algebraMap R (chapter07LocalIntegerRing R K v) r)
    intro hunit
    have hval :=
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
        (K := K) (v := v)).1 hunit
    have hlt : Valued.v
        ((algebraMap R (chapter07LocalIntegerRing R K v) r :
          chapter07LocalIntegerRing R K v) : chapter07LocalField R K v) < 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
      rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
        (K := K) (v := v) (algebraMap R K r)]
      exact (v.valuation_lt_one_iff_mem (K := K) r).2 hr
    exact (ne_of_lt hlt) hval
  let g : R ⧸ v.asIdeal →+* IsLocalRing.ResidueField
      (chapter07LocalIntegerRing R K v) :=
    Ideal.Quotient.lift v.asIdeal f hf
  have hrep : ∀ x : chapter07LocalIntegerRing R K v, ∃ r : R,
      IsLocalRing.residue (chapter07LocalIntegerRing R K v)
          (algebraMap R (chapter07LocalIntegerRing R K v) r) =
        IsLocalRing.residue (chapter07LocalIntegerRing R K v) x := by
    intro x
    have hxval : Valued.v (x : chapter07LocalField R K v) ≤ 1 := x.property
    let U : Set (chapter07LocalField R K v) :=
      {z | Valued.v (z - (x : chapter07LocalField R K v)) < 1}
    have hUopen : IsOpen U := by
      change IsOpen ((fun z : chapter07LocalField R K v =>
        Valued.v (z - (x : chapter07LocalField R K v))) ⁻¹' Set.Iio 1)
      apply (WithZeroTopology.isOpen_Iio : IsOpen (Set.Iio (1 : ℤᵐ⁰))).preimage
      exact (Valued.continuous_valuation_of_surjective
        (v.valuedAdicCompletion_surjective K)).comp
        (continuous_id.sub continuous_const)
    have hxU : (x : chapter07LocalField R K v) ∈ U := by
      simp [U]
    obtain ⟨y, hy⟩ :=
      (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap
        (v := v) (K := K)).exists_mem_open hUopen ⟨x, hxU⟩
    have hyclose : Valued.v
        ((algebraMap K (chapter07LocalField R K v) y) - (x : chapter07LocalField R K v)) < 1 := hy
    have hmapK : algebraMap K (chapter07LocalField R K v) y =
        (y : chapter07LocalField R K v) := by
      rfl
    have hyval' : Valued.v (algebraMap K (chapter07LocalField R K v) y) ≤ 1 := by
      have hsum := (Valued.v : Valuation (chapter07LocalField R K v) ℤᵐ⁰).map_add
        ((algebraMap K (chapter07LocalField R K v) y) - (x : chapter07LocalField R K v))
        (x : chapter07LocalField R K v)
      rw [sub_add_cancel] at hsum
      exact (hsum.trans (max_le (le_of_lt hyclose) hxval))
    have hyval : v.valuation K y ≤ 1 := by
      rw [← IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe
        (K := K) (v := v) y]
      rw [hmapK] at hyval'
      exact hyval'
    obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer (K := K) hyval
      (1 : (ℤᵐ⁰)ˣ)
    have hmapR : algebraMap R (chapter07LocalField R K v) r =
        (algebraMap R K r : chapter07LocalField R K v) := by
      rfl
    have hsub : ((algebraMap R K r - y : K) : chapter07LocalField R K v) =
        (algebraMap R K r : chapter07LocalField R K v) -
          (y : chapter07LocalField R K v) := by
      apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
      change
        ((WithVal.toVal (v.valuation K) (algebraMap R K r - y) :
          WithVal (v.valuation K)) :
          UniformSpace.Completion (WithVal (v.valuation K))) =
          ((WithVal.toVal (v.valuation K) (algebraMap R K r) :
            WithVal (v.valuation K)) :
            UniformSpace.Completion (WithVal (v.valuation K))) -
            ((WithVal.toVal (v.valuation K) y : WithVal (v.valuation K)) :
              UniformSpace.Completion (WithVal (v.valuation K)))
      exact (UniformSpace.Completion.coeRingHom
        (α := WithVal (v.valuation K))).map_sub _ _
    have hrclose : Valued.v
        ((algebraMap R (chapter07LocalField R K v) r) -
          (algebraMap K (chapter07LocalField R K v) y)) < 1 := by
      have hr' : Valued.v
          (((algebraMap R K r - y : K) : chapter07LocalField R K v)) < 1 := by
        rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe
          (K := K) (v := v)]
        simpa using hr
      rw [hmapR, hmapK]
      rw [← hsub]
      exact hr'
    have harclose : Valued.v
        ((algebraMap R (chapter07LocalField R K v) r) -
          (x : chapter07LocalField R K v)) < 1 := by
      have hsum := (Valued.v : Valuation (chapter07LocalField R K v) ℤᵐ⁰).map_add
        ((algebraMap R (chapter07LocalField R K v) r) -
          (algebraMap K (chapter07LocalField R K v) y))
        ((algebraMap K (chapter07LocalField R K v) y) -
          (x : chapter07LocalField R K v))
      rw [sub_add_sub_cancel] at hsum
      exact (hsum.trans_lt (max_lt hrclose hyclose))
    have hmax : (algebraMap R (chapter07LocalIntegerRing R K v) r :
        chapter07LocalIntegerRing R K v) - x ∈
        IsLocalRing.maximalIdeal (chapter07LocalIntegerRing R K v) := by
      rw [IsLocalRing.mem_maximalIdeal]
      change ¬ IsUnit ((algebraMap R (chapter07LocalIntegerRing R K v) r :
        chapter07LocalIntegerRing R K v) - x)
      intro hunit
      have hval :=
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
          (K := K) (v := v)).1 hunit
      have hlt : Valued.v
          (((algebraMap R (chapter07LocalIntegerRing R K v) r :
            chapter07LocalIntegerRing R K v) - x) :
            chapter07LocalField R K v) < 1 := by
        simpa [hmapR] using harclose
      exact (ne_of_lt hlt) hval
    have hzero : IsLocalRing.residue (chapter07LocalIntegerRing R K v)
        ((algebraMap R (chapter07LocalIntegerRing R K v) r :
          chapter07LocalIntegerRing R K v) - x) = 0 :=
      (IsLocalRing.residue_eq_zero_iff
        (R := ↥(chapter07LocalIntegerRing R K v))
        ((algebraMap R (chapter07LocalIntegerRing R K v) r :
          chapter07LocalIntegerRing R K v) - x)).2 hmax
    refine ⟨r, ?_⟩
    exact sub_eq_zero.mp (by simpa using hzero)
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨x, rfl⟩ :=
      IsLocalRing.residue_surjective
        (R := ↥(chapter07LocalIntegerRing R K v)) z
    obtain ⟨r, hr⟩ := hrep x
    refine ⟨Ideal.Quotient.mk v.asIdeal r, ?_⟩
    simpa [g, f, IsLocalRing.residue_def] using hr
  exact Finite.of_surjective g hg

theorem chapter07_finite_local_maximal_compact_unique
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    (v : chapter07FinitePlace R) :
    chapter07UniqueMaximalCompactSubgroup (chapter07LocalField R K v)ˣ
      (chapter07FiniteLocalMaximalCompact R K v) := by
  let e : chapter07LocalIntegerRing R K v ≃+*
      Valued.integer (chapter07LocalField R K v) :=
    { toFun := fun x =>
        ⟨x, (Valuation.mem_valuationSubring_iff (Valued.v)
          (x : chapter07LocalField R K v)).1 x.property⟩
      invFun := fun x =>
        ⟨x, (Valuation.mem_valuationSubring_iff (Valued.v)
          (x : chapter07LocalField R K v)).2 x.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_mul' := by intro x y; rfl }
  let hcomplete : CompleteSpace (Valued.integer (chapter07LocalField R K v)) := by
    apply completeSpace_of_isComplete_univ
    rw [Subtype.isComplete_iff]
    convert (Valued.isClosed_valuationSubring (chapter07LocalField R K v)).isComplete using 1
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact (Valuation.mem_valuationSubring_iff (Valued.v)
        (y : chapter07LocalField R K v)).2 y.property
    · intro hx
      exact ⟨⟨x, (Valuation.mem_valuationSubring_iff (Valued.v)
          (x : chapter07LocalField R K v)).1 hx⟩,
        Set.mem_univ _, rfl⟩
  let hdvr : IsDiscreteValuationRing (Valued.integer (chapter07LocalField R K v)) :=
    { principal := (isPrincipalIdealRing_iff _).1
          (.of_surjective _ e.surjective)
      __ := e.isLocalRing
      not_a_field' := by
        obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt
          (bot_lt_iff_ne_bot.mpr <| IsDiscreteValuationRing.not_a_field
            (chapter07LocalIntegerRing R K v))
        rw [Submodule.ne_bot_iff]
        refine ⟨e a, ⟨?_, by simp only [ne_eq, EmbeddingLike.map_eq_zero_iff,
          ZeroMemClass.coe_eq_zero, ha, not_false_eq_true]⟩⟩
        rw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff e,
          ← IsLocalRing.mem_maximalIdeal]
        exact a.2 }
  let hfiniteO : Finite (IsLocalRing.ResidueField (chapter07LocalIntegerRing R K v)) :=
    chapter07_finite_local_residueField_finite_local R K v
  let hfiniteI : Finite (Valued.ResidueField (chapter07LocalField R K v)) := by
    exact @Finite.of_equiv _ _ hfiniteO (IsLocalRing.ResidueField.mapEquiv e).toEquiv
  let hcompactSpaceI : CompactSpace (Valued.integer (chapter07LocalField R K v)) :=
    (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
      (K := chapter07LocalField R K v) (Γ₀ := ℤᵐ⁰)).2
      ⟨hcomplete, hdvr, hfiniteI⟩
  have hcompactI : IsCompact (Valued.integer (chapter07LocalField R K v) :
    Set (chapter07LocalField R K v)) :=
    by
      convert ((isCompact_univ_iff.mpr hcompactSpaceI :
          IsCompact (Set.univ : Set (Valued.integer (chapter07LocalField R K v)))).image
          (continuous_subtype_val : Continuous
            (fun x : Valued.integer (chapter07LocalField R K v) =>
              (x : chapter07LocalField R K v)))) using 1
      ext x
      simp
  have hcompactO : IsCompact (chapter07LocalIntegerRing R K v :
      Set (chapter07LocalField R K v)) := by
    convert hcompactI using 1
    ext x
    constructor
    · intro hx
      exact (Valuation.mem_valuationSubring_iff (Valued.v) x).2 hx
    · intro hx
      exact (Valuation.mem_valuationSubring_iff (Valued.v) x).1 hx
  refine ⟨?_, ?_⟩
  · exact Submonoid.units_isCompact hcompactO
  · intro L hL u hu
    apply (chapter07LocalOrder_eq_zero_iff_mem_localIntegralUnitSubgroup R K v u).1
    have hcont : Continuous (chapter07LocalOrder R K v) :=
      chapter07_finite_local_order_continuous R K v
    have hcompact : IsCompact (chapter07LocalOrder R K v '' (L : Set _)) :=
      hL.image hcont
    obtain ⟨M, hM⟩ := hcompact.bddAbove
    have hpow (w : (chapter07LocalField R K v)ˣ) : ∀ n : ℕ,
        chapter07LocalOrder R K v (w ^ n) = (n : ℤ) * chapter07LocalOrder R K v w := by
      intro n
      induction n with
      | zero => simp [chapter07LocalOrder_apply_one]
      | succ n ih =>
          rw [pow_succ, chapter07LocalOrder_mul, ih]
          push_cast
          ring
    by_contra hzero
    have hpos : 0 < chapter07LocalOrder R K v u ∨
        chapter07LocalOrder R K v u < 0 := lt_or_gt_of_ne (Ne.symm hzero)
    rcases hpos with hpos | hneg
    · obtain ⟨n, hn⟩ := Archimedean.arch (M + 1) hpos
      have hle := hM ⟨u ^ n, L.pow_mem hu n, rfl⟩
      rw [hpow] at hle
      have hn' : M + 1 ≤ (n : ℤ) * chapter07LocalOrder R K v u := by
        simpa [nsmul_eq_mul] using hn
      omega
    · have hneg' : 0 < -chapter07LocalOrder R K v u := by linarith
      obtain ⟨n, hn⟩ := Archimedean.arch (M + 1) hneg'
      have hle := hM ⟨(u⁻¹) ^ n, L.pow_mem (L.inv_mem hu) n, rfl⟩
      rw [hpow, chapter07LocalOrder_inv] at hle
      have hn' : M + 1 ≤ (n : ℤ) * (-chapter07LocalOrder R K v u) := by
        simpa [nsmul_eq_mul] using hn
      omega

theorem chapter07_finite_integral_units_unique_maximal_compact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    chapter07UniqueMaximalCompactSubgroup (chapter07FiniteIdeleGroup R K)
      (chapter07FiniteIntegralUnitSubgroup R K) := by
  refine ⟨(chapter07_finiteIntegralUnits_compact_open R K).1, ?_⟩
  intro L hL u hu v
  let ev : chapter07FiniteIdeleGroup R K →*
      (chapter07LocalField R K v)ˣ :=
    { toFun := fun x => chapter07FiniteIdeleEquiv R K x v
      map_one' := by rfl
      map_mul' := by intro x y; rfl }
  have hev : Continuous ev := by
    have hval : Continuous (fun x : chapter07FiniteIdeleGroup R K =>
        (x : chapter07FiniteAdeleRing R K)) := Units.continuous_val
    have heval : Continuous (fun x : chapter07FiniteAdeleRing R K => x v) :=
      RestrictedProduct.continuous_eval
        (R := fun v : chapter07FinitePlace R => chapter07LocalField R K v)
        (A := fun v : chapter07FinitePlace R => chapter07LocalIntegerRing R K v) v
    have hcoord : Continuous (fun x : chapter07FiniteIdeleGroup R K =>
        ((ev x : (chapter07LocalField R K v)ˣ) : chapter07LocalField R K v)) := by
      change Continuous (fun x : chapter07FiniteIdeleGroup R K => x.1 v)
      exact heval.comp hval
    refine Units.continuous_iff.mpr ⟨hcoord, ?_⟩
    refine (hcoord.comp continuous_inv).congr ?_
    intro x
    change ((ev (x⁻¹) : (chapter07LocalField R K v)ˣ) : chapter07LocalField R K v) =
      ((ev x)⁻¹ : (chapter07LocalField R K v)ˣ)
    rw [map_inv]
  have hcompact : IsCompact (L.map ev : Set ((chapter07LocalField R K v)ˣ)) := by
    rw [Subgroup.coe_map]
    exact hL.image hev
  have hcontains := (chapter07_finite_local_maximal_compact_unique R K v).2
    (L.map ev) hcompact
  exact hcontains ⟨u, hu, rfl⟩

/-- The global product of the local maximal compact subgroups. -/
def chapter07GlobalMaximalCompact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Subgroup (chapter07IdeleGroup R K) where
  carrier := {x |
    (∀ v : NumberField.InfinitePlace K, ‖x.1.1 v‖ = 1) ∧
      ∀ v : chapter07FinitePlace R,
        Valued.v (x.1.2 v) = 1}
  one_mem' := by
    constructor
    · intro v
      change ‖(1 : v.Completion)‖ = 1
      simp
    · intro v
      change Valued.v (1 : chapter07LocalField R K v) = 1
      simp
  mul_mem' := by
    intro x y hx hy
    constructor
    · intro v
      change ‖x.1.1 v * y.1.1 v‖ = 1
      simp [hx.1 v, hy.1 v]
    · intro v
      change Valued.v (x.1.2 v * y.1.2 v) = 1
      simp [hx.2 v, hy.2 v]
  inv_mem' := by
    intro x hx
    constructor
    · intro v
      simp [chapter07_idele_inv_apply_infinite, norm_inv, hx.1 v]
    · intro v
      simp [chapter07_idele_inv_apply_finite, hx.2 v]

theorem chapter07_global_maximal_compact_is_compact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    IsCompact (chapter07GlobalMaximalCompact R K : Set (chapter07IdeleGroup R K)) := by
  let Hinf : Set (NumberField.InfiniteAdeleRing K)ˣ :=
    {x | ∀ v : NumberField.InfinitePlace K, ‖x.1 v‖ = 1}
  let P : Set (NumberField.InfiniteAdeleRing K) :=
    Set.univ.pi (fun v : NumberField.InfinitePlace K =>
      Metric.sphere (0 : v.Completion) 1)
  have hP : IsCompact P := by
    apply isCompact_univ_pi
    intro v
    rcases NumberField.InfinitePlace.isReal_or_isComplex v with hv | hv
    · let e := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv
      have he : e.symm (e 0) = (0 : v.Completion) := e.symm_apply_apply 0
      have hpre := e.preimage_sphere (e 0) 1
      rw [he] at hpre
      rw [← hpre]
      exact e.toHomeomorph.isCompact_preimage.mpr (isCompact_sphere (e 0) 1)
    · let e := NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv
      have he : e.symm (e 0) = (0 : v.Completion) := e.symm_apply_apply 0
      have hpre := e.preimage_sphere (e 0) 1
      rw [he] at hpre
      rw [← hpre]
      exact e.toHomeomorph.isCompact_preimage.mpr (isCompact_sphere (e 0) 1)
  let S : Set (NumberField.InfiniteAdeleRing K ×
      (NumberField.InfiniteAdeleRing K)ᵐᵒᵖ) :=
    P ×ˢ (MulOpposite.op '' P)
  have hS : IsCompact S := by
    exact hP.prod (hP.image MulOpposite.continuous_op)
  have hpre : (Units.embedProduct (NumberField.InfiniteAdeleRing K)) ⁻¹' S = Hinf := by
    ext x
    simp only [S, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply]
    constructor
    · intro hx
      change ∀ v : NumberField.InfinitePlace K, ‖x.1 v‖ = 1
      intro v
      have hv := hx.1 v (Set.mem_univ v)
      simpa [P, Metric.mem_sphere, dist_zero_right] using hv
    · intro hx
      constructor
      · intro v hv
        have := hx v
        simpa [P, Metric.mem_sphere, dist_zero_right] using this
      · refine ⟨((x⁻¹ : (NumberField.InfiniteAdeleRing K)ˣ) :
          NumberField.InfiniteAdeleRing K), ?_, rfl⟩
        intro v hv
        have hnorm : ‖x.1 v‖ = 1 := hx v
        change ((x⁻¹ : (NumberField.InfiniteAdeleRing K)ˣ) :
          NumberField.InfiniteAdeleRing K) v ∈
            Metric.sphere (0 : v.Completion) 1
        have hinv : ((x⁻¹ : (NumberField.InfiniteAdeleRing K)ˣ) :
            NumberField.InfiniteAdeleRing K) v = (x.1 v)⁻¹ := by
          have hfun := congrArg (fun f : NumberField.InfiniteAdeleRing K => f v)
            x.inv_val
          change ((x⁻¹ : (NumberField.InfiniteAdeleRing K)ˣ) :
            NumberField.InfiniteAdeleRing K) v * x.1 v = 1 at hfun
          exact eq_inv_of_mul_eq_one_left hfun
        rw [hinv]
        simp [norm_inv, hnorm]
  let _ : ∀ v : NumberField.InfinitePlace K, T2Space v.Completion :=
    fun v => inferInstance
  let _ : T2Space (NumberField.InfiniteAdeleRing K) :=
    @Pi.t2Space (NumberField.InfinitePlace K) (fun v => v.Completion)
      (fun _ => inferInstance) (fun _ => inferInstance)
  have hHinf : IsCompact Hinf := by
    rw [← hpre]
    exact Units.isClosedEmbedding_embedProduct.isCompact_preimage hS
  have hfin : IsCompact (chapter07FiniteIntegralUnitSubgroup R K :
      Set (chapter07FiniteIdeleGroup R K)) :=
    (chapter07_finiteIntegralUnits_compact_open R K).1
  let e : (chapter07IdeleGroup R K) ≃ₜ
      (NumberField.InfiniteAdeleRing K)ˣ × (chapter07FiniteAdeleRing R K)ˣ :=
    Homeomorph.prodUnits
  let T : Set ((NumberField.InfiniteAdeleRing K)ˣ ×
      (chapter07FiniteAdeleRing R K)ˣ) :=
    Hinf ×ˢ (chapter07FiniteIntegralUnitSubgroup R K :
      Set (chapter07FiniteIdeleGroup R K))
  have hT : IsCompact T := hHinf.prod hfin
  have heq : e.symm '' T =
      (chapter07GlobalMaximalCompact R K : Set (chapter07IdeleGroup R K)) := by
    have heinf_symm (y : (NumberField.InfiniteAdeleRing K)ˣ ×
        (chapter07FiniteAdeleRing R K)ˣ) (v : NumberField.InfinitePlace K) :
        (e.symm y).1.1 v = y.1.1 v := by
      rfl
    have hefin_symm (y : (NumberField.InfiniteAdeleRing K)ˣ ×
        (chapter07FiniteAdeleRing R K)ˣ) (v : chapter07FinitePlace R) :
        (e.symm y).1.2 v = y.2.1 v := by
      rfl
    have heinf_fwd (x : chapter07IdeleGroup R K) (v : NumberField.InfinitePlace K) :
        (e x).1.1 v = x.1.1 v := by
      rfl
    have hefin_fwd (x : chapter07IdeleGroup R K) (v : chapter07FinitePlace R) :
        (e x).2.1 v = x.1.2 v := by
      rfl
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyinf : ∀ v : NumberField.InfinitePlace K,
          ‖(e.symm y).1.1 v‖ = 1 := by
        intro v
        have hv := hy.1 v
        rw [heinf_symm]
        exact hv
      have hyfin : ∀ v : chapter07FinitePlace R,
          Valued.v ((e.symm y).1.2 v) = 1 := by
        have hv := (chapter07_finiteIntegralUnits_valued_iff R K y.2).1 hy.2
        intro v
        rw [hefin_symm]
        exact hv v
      exact ⟨hyinf, hyfin⟩
    · intro hx
      refine ⟨e x, ?_, e.symm_apply_apply x⟩
      refine ⟨?_, ?_⟩
      · intro v
        have hv := hx.1 v
        rw [heinf_fwd]
        exact hv
      · apply (chapter07_finiteIntegralUnits_valued_iff R K (e x).2).2
        intro v
        have hv := hx.2 v
        change Valued.v ((e x).2.1 v) = 1
        rw [hefin_fwd]
        exact hv
  rw [← heq]
  exact hT.image e.symm.continuous

theorem chapter07_global_maximal_compact_contains_compact_subgroups
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    (L : Subgroup (chapter07IdeleGroup R K))
    (hL : IsCompact (L : Set (chapter07IdeleGroup R K))) :
    L ≤ chapter07GlobalMaximalCompact R K := by
  intro u hu
  constructor
  · intro v
    let evA : chapter07AdeleRing R K →* v.Completion :=
      { toFun := fun x => x.1 v
        map_one' := by rfl
        map_mul' := by intro x y; rfl }
    let ev : chapter07IdeleGroup R K →* (v.Completion)ˣ := Units.map evA
    have hevA : Continuous evA := by
      change Continuous (fun x : chapter07AdeleRing R K => x.1 v)
      exact (continuous_apply v).comp continuous_fst
    have hev : Continuous ev := hevA.units_map evA
    have hcompact : IsCompact (L.map ev : Set (v.Completion)ˣ) := by
      rw [Subgroup.coe_map]
      exact hL.image hev
    have hnorm := chapter07_compact_units_norm_eq_one v.Completion (L.map ev)
      hcompact (ev u) ⟨u, hu, rfl⟩
    change ‖u.1.1 v‖ = 1 at hnorm
    exact hnorm
  · intro v
    let evA : chapter07AdeleRing R K →* chapter07LocalField R K v :=
      { toFun := fun x => x.2 v
        map_one' := by rfl
        map_mul' := by intro x y; rfl }
    let ev : chapter07IdeleGroup R K →* (chapter07LocalField R K v)ˣ :=
      Units.map evA
    have hevA : Continuous evA := by
      change Continuous (fun x : chapter07AdeleRing R K => x.2 v)
      exact (RestrictedProduct.continuous_eval
        (R := fun w : chapter07FinitePlace R => chapter07LocalField R K w)
        (A := fun w : chapter07FinitePlace R => chapter07LocalIntegerRing R K w) v).comp
        continuous_snd
    have hev : Continuous ev := hevA.units_map evA
    have hcompact : IsCompact (L.map ev : Set ((chapter07LocalField R K v)ˣ)) := by
      rw [Subgroup.coe_map]
      exact hL.image hev
    have hlocal := (chapter07_finite_local_maximal_compact_unique R K v).2
      (L.map ev) hcompact
    have hlocal' := hlocal ⟨u, hu, rfl⟩
    have hval :=
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
        (K := K) (v := v)).1 hlocal'
    change Valued.v (u.1.2 v) = 1
    exact hval

theorem chapter07_global_maximal_compact_unique
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    chapter07UniqueMaximalCompactSubgroup (chapter07IdeleGroup R K)
      (chapter07GlobalMaximalCompact R K) := by
  refine ⟨chapter07_global_maximal_compact_is_compact R K, ?_⟩
  exact chapter07_global_maximal_compact_contains_compact_subgroups R K

theorem chapter07_global_maximal_compact_not_open
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    ¬ IsOpen (chapter07GlobalMaximalCompact R K : Set (chapter07IdeleGroup R K)) := by
  classical
  intro hopen
  have hone : (1 : chapter07IdeleGroup R K) ∈
      (chapter07GlobalMaximalCompact R K : Set (chapter07IdeleGroup R K)) := by
    exact (chapter07GlobalMaximalCompact R K).one_mem
  have hbasis := (chapter07_idele_basic_open_basis R K
    (chapter07GlobalMaximalCompact R K : Set (chapter07IdeleGroup R K))).1 hopen
  rcases hbasis (1 : chapter07IdeleGroup R K) hone with
    ⟨S, Uinf, Uf, hUinf, hUf, honeB, hB⟩
  have hperturb : ∀ v : NumberField.InfinitePlace K, ∃ u : (v.Completion)ˣ,
      u ∈ Uinf v ∧ ‖(u : v.Completion)‖ ≠ 1 := by
    intro v
    have hone' : (1 : (v.Completion)ˣ) ∈ Uinf v := by
      have hv := honeB.1 v
      change chapter07IdeleInfiniteCoordinate R K (1 : chapter07IdeleGroup R K) v ∈ Uinf v at hv
      have hcoord : chapter07IdeleInfiniteCoordinate R K
          (1 : chapter07IdeleGroup R K) v = 1 := by
        apply Units.ext
        rfl
      rw [hcoord] at hv
      exact hv
    have hopenVal : IsOpen ((fun u : (v.Completion)ˣ =>
        (u : v.Completion)) '' Uinf v) := by
      exact (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.Completion)).isOpenMap _ (hUinf v)
    have honeVal : (1 : v.Completion) ∈ ((fun u : (v.Completion)ˣ =>
        (u : v.Completion)) '' Uinf v) := ⟨1, hone', rfl⟩
    rcases Metric.isOpen_iff.mp hopenVal 1 honeVal with ⟨ε, hε, hball⟩
    rcases NumberField.InfinitePlace.isReal_or_isComplex v with hv | hv
    · let e := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv
      have he1 : e 1 = 1 := by
        change NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv 1 = 1
        simp
      have he0 : e 0 = 0 := by
        change NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv 0 = 0
        simp
      let δ : ℝ := min (ε / 2) 1
      have hδ : 0 < δ := by
        dsimp [δ]
        positivity
      have hδε : δ < ε := by
        dsimp [δ]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      let z : ℝ := 1 + δ
      let q : v.Completion := e.symm z
      have hdist : dist q 1 < ε := by
        have hdist' : dist q 1 = dist z (e 1) := by
          dsimp [q]
          simpa using (e.symm.dist_eq z (e 1))
        rw [hdist']
        rw [he1]
        simpa [z, dist_eq_norm, abs_of_pos hδ] using hδε
      have hq : q ∈ (fun u : (v.Completion)ˣ => (u : v.Completion)) '' Uinf v :=
          hball (Metric.mem_ball.mpr hdist)
      rcases hq with ⟨u, hu, huq⟩
      refine ⟨u, hu, ?_⟩
      have hnorm : ‖q‖ = z := by
        calc
          ‖q‖ = dist q 0 := (dist_zero_right q).symm
          _ = dist (e q) (e 0) := (e.isometry.dist_eq q 0).symm
          _ = ‖e q‖ := by rw [he0, dist_zero_right]
          _ = z := by
            have hz : 0 ≤ z := by dsimp [z]; linarith
            simp [q, z, Real.norm_of_nonneg hz]
      have huq' : (u : v.Completion) = q := huq
      rw [huq', hnorm]
      linarith
    · let e := NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv
      have he1 : e 1 = 1 := by
        change NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv 1 = 1
        simp
      have he0 : e 0 = 0 := by
        change NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv 0 = 0
        simp
      let δ : ℝ := min (ε / 2) 1
      have hδ : 0 < δ := by
        dsimp [δ]
        positivity
      have hδε : δ < ε := by
        dsimp [δ]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      let z : ℂ := Complex.ofReal (1 + δ)
      let q : v.Completion := e.symm z
      have hdist : dist q 1 < ε := by
        have hdist' : dist q 1 = dist z (e 1) := by
          dsimp [q]
          simpa using (e.symm.dist_eq z (e 1))
        rw [hdist']
        rw [he1]
        simpa [z, dist_eq_norm, Complex.norm_real, abs_of_pos hδ] using hδε
      have hq : q ∈ (fun u : (v.Completion)ˣ => (u : v.Completion)) '' Uinf v :=
          hball (Metric.mem_ball.mpr hdist)
      rcases hq with ⟨u, hu, huq⟩
      refine ⟨u, hu, ?_⟩
      have hnorm : ‖q‖ = 1 + δ := by
        calc
          ‖q‖ = dist q 0 := (dist_zero_right q).symm
          _ = dist (e q) (e 0) := (e.isometry.dist_eq q 0).symm
          _ = ‖e q‖ := by rw [he0, dist_zero_right]
          _ = 1 + δ := by
            simp only [q, IsometryEquiv.apply_symm_apply]
            change ‖Complex.ofReal (1 + δ)‖ = 1 + δ
            rw [Complex.norm_real, Real.norm_of_nonneg]
            linarith
      have huq' : (u : v.Completion) = q := huq
      rw [huq', hnorm]
      linarith
  let v : NumberField.InfinitePlace K := Classical.choice (inferInstance : Nonempty
    (NumberField.InfinitePlace K))
  obtain ⟨u, hu, hnorm⟩ := hperturb v
  let a : (NumberField.InfiniteAdeleRing K)ˣ :=
    (ContinuousMulEquiv.piUnits (M := fun w : NumberField.InfinitePlace K => w.Completion)).symm
      (Pi.mulSingle (M := fun w : NumberField.InfinitePlace K => (w.Completion)ˣ) v u)
  let e : (chapter07IdeleGroup R K) ≃ₜ
      (NumberField.InfiniteAdeleRing K)ˣ × (chapter07FiniteAdeleRing R K)ˣ :=
    Homeomorph.prodUnits
  let x : chapter07IdeleGroup R K := e.symm (a, 1)
  have hxinf (w : NumberField.InfinitePlace K) :
      chapter07IdeleInfiniteCoordinate R K x w =
        (Pi.mulSingle (M := fun w : NumberField.InfinitePlace K => (w.Completion)ˣ)
          v u) w := by
    apply Units.ext
    rfl
  have hxfin (w : chapter07FinitePlace R) :
      chapter07IdeleFiniteCoordinate R K x w = 1 := by
    apply Units.ext
    rfl
  have hxB : x ∈ chapter07IdeleBasicOpen R K S Uinf Uf := by
    change (∀ w : NumberField.InfinitePlace K,
        chapter07IdeleInfiniteCoordinate R K x w ∈ Uinf w) ∧
      (∀ w : chapter07FinitePlace R, w ∈ S →
        chapter07IdeleFiniteCoordinate R K x w ∈ Uf w) ∧
      (∀ w : chapter07FinitePlace R, w ∉ S →
        chapter07IdeleFiniteCoordinate R K x w ∈
          (Submonoid.ofClass (chapter07LocalIntegerRing R K w)).units)
    refine ⟨?_, ?_, ?_⟩
    · intro w
      rw [hxinf]
      by_cases hw : w = v
      · subst w
        simpa using hu
      · rw [Pi.mulSingle_eq_of_ne hw]
        exact honeB.1 w
    · intro w hw
      rw [hxfin]
      have hw' := honeB.2.1 w hw
      change chapter07IdeleFiniteCoordinate R K (1 : chapter07IdeleGroup R K) w ∈ Uf w at hw'
      have hcoord : chapter07IdeleFiniteCoordinate R K
          (1 : chapter07IdeleGroup R K) w = 1 := by
        apply Units.ext
        rfl
      rw [hcoord] at hw'
      exact hw'
    · intro w hw
      rw [hxfin]
      simp
  have hxH : x ∈ (chapter07GlobalMaximalCompact R K : Set (chapter07IdeleGroup R K)) := hB hxB
  have hxnorm : ‖(u : v.Completion)‖ = 1 := by
    have hv := hxH.1 v
    have hv' : ‖(chapter07IdeleInfiniteCoordinate R K x v : v.Completion)‖ = 1 := by
      rw [chapter07IdeleInfiniteCoordinate_val]
      exact hv
    rw [hxinf] at hv'
    simpa using hv'
  exact hnorm hxnorm

theorem chapter07_global_maximal_compact_is_not_an_open_subgroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    ¬ IsOpen (chapter07GlobalMaximalCompact R K : Set (chapter07IdeleGroup R K)) :=
  chapter07_global_maximal_compact_not_open R K

end

end LastLib.Book04AdelesAndIdeles.Chapter07
