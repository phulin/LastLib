import LastLib.Book04AdelesAndIdeles.Chapter07.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter07.Section03AdditiveAndMultiplicativeInformation

namespace LastLib.Book04AdelesAndIdeles.Chapter07

noncomputable section

open Set Filter Topology WithZeroTopology
open scoped BigOperators DirectSum RestrictedProduct

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
  sorry

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
  sorry

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

theorem chapter07_real_maximal_compact_unique :
    chapter07UniqueMaximalCompactSubgroup ℝˣ chapter07RealMaximalCompact := by
  sorry

theorem chapter07_complex_maximal_compact_unique :
    chapter07UniqueMaximalCompactSubgroup ℂˣ chapter07ComplexMaximalCompact := by
  sorry

def chapter07FiniteLocalMaximalCompact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :
    Subgroup (chapter07LocalField R K v)ˣ :=
  chapter07LocalIntegralUnitSubgroup R K v

theorem chapter07_finite_local_maximal_compact_unique
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    (v : chapter07FinitePlace R) :
    chapter07UniqueMaximalCompactSubgroup (chapter07LocalField R K v)ˣ
      (chapter07FiniteLocalMaximalCompact R K v) := by
  sorry

theorem chapter07_finite_integral_units_unique_maximal_compact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    chapter07UniqueMaximalCompactSubgroup (chapter07FiniteIdeleGroup R K)
      (chapter07FiniteIntegralUnitSubgroup R K) := by
  sorry

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
  sorry

theorem chapter07_global_maximal_compact_contains_compact_subgroups
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    (L : Subgroup (chapter07IdeleGroup R K))
    (hL : IsCompact (L : Set (chapter07IdeleGroup R K))) :
    L ≤ chapter07GlobalMaximalCompact R K := by
  sorry

theorem chapter07_global_maximal_compact_unique
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    chapter07UniqueMaximalCompactSubgroup (chapter07IdeleGroup R K)
      (chapter07GlobalMaximalCompact R K) := by
  sorry

theorem chapter07_global_maximal_compact_not_open
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    ¬ IsOpen (chapter07GlobalMaximalCompact R K : Set (chapter07IdeleGroup R K)) := by
  sorry

theorem chapter07_global_maximal_compact_is_not_an_open_subgroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    ¬ IsOpen (chapter07GlobalMaximalCompact R K : Set (chapter07IdeleGroup R K)) :=
  chapter07_global_maximal_compact_not_open R K

end

end LastLib.Book04AdelesAndIdeles.Chapter07
