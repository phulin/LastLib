import LastLib.Book04AdelesAndIdeles.Chapter07.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter07.Section03AdditiveAndMultiplicativeInformation

namespace LastLib.Book04AdelesAndIdeles.Chapter07

noncomputable section

open Set Filter Topology
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
  sorry

theorem chapter07_local_order_coset_open
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (D : Chapter07LocalOrderDecompositionData G) (n : ℤ) :
    IsOpen (chapter07LocalOrderCoset D n) := by
  sorry

theorem chapter07_local_order_continuous
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (D : Chapter07LocalOrderDecompositionData G) :
    Continuous D.order :=
  D.order_continuous

theorem chapter07_local_order_cosets_cover
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (D : Chapter07LocalOrderDecompositionData G) :
    (⋃ n : ℤ, chapter07LocalOrderCoset D n) = Set.univ := by
  sorry

theorem chapter07_local_order_cosets_pairwise_disjoint
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (D : Chapter07LocalOrderDecompositionData G) :
    Pairwise (fun m n : ℤ =>
      Disjoint (chapter07LocalOrderCoset D m) (chapter07LocalOrderCoset D n)) := by
  sorry

theorem chapter07_finite_local_order_continuous
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :
    Continuous (chapter07LocalOrder R K v) := by
  sorry

theorem chapter07_finite_local_order_surjective
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :
    Function.Surjective (chapter07LocalOrder R K v) := by
  sorry

theorem chapter07_finite_local_order_kernel
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :
    {u | chapter07LocalOrder R K v u = 0} =
      chapter07LocalIntegralUnitSubgroup R K v := by
  sorry

theorem chapter07_finite_local_idele_coset_decomposition
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) (π : (chapter07LocalField R K v)ˣ)
    (hπ : chapter07LocalOrder R K v π = 1) :
    ∀ x : (chapter07LocalField R K v)ˣ, ∃ n : ℤ, ∃ u : (chapter07LocalField R K v)ˣ,
      u ∈ chapter07LocalIntegralUnitSubgroup R K v ∧
        x = π ^ n * u := by
  sorry

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
  sorry

theorem chapter07_finite_order_exact_sequence
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Function.MulExact (chapter07FiniteIntegralUnitInclusion R K)
      (chapter07FiniteOrderHom R K) := by
  sorry

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
  sorry

noncomputable def chapter07FiniteOrderQuotientEquiv
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    (chapter07FiniteIdeleGroup R K ⧸ chapter07FiniteIntegralUnitSubgroup R K) ≃*
      Multiplicative (chapter07FiniteDivisorGroup R) := by
  let hker : (chapter07FiniteOrderHom R K).ker =
      chapter07FiniteIntegralUnitSubgroup R K := by
    sorry
  exact
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (chapter07FiniteOrderHom R K)
        (chapter07_finite_order_surjective R K))

theorem chapter07_finite_order_quotient_is_discrete_topologically
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [NumberField K]
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
    ∃ t : TopologicalSpace (chapter07FiniteDivisorGroup R),
      @DiscreteTopology (chapter07FiniteDivisorGroup R) t := by
  exact ⟨chapter07FiniteDivisorDiscreteTopology R, chapter07_finite_divisor_group_is_discrete R⟩

/-- A choice of local uniformizers gives a noncanonical section of the finite order map. -/
structure Chapter07UniformizerChoice
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] where
  uniformizer : ∀ v : chapter07FinitePlace R, (chapter07LocalField R K v)ˣ
  order_uniformizer : ∀ v, chapter07LocalOrder R K v (uniformizer v) = 1

theorem chapter07_uniformizer_choice_exists
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    Nonempty (Chapter07UniformizerChoice R K) := by
  sorry

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
          (by sorry))
    map_one' := by sorry
    map_mul' := by sorry }

theorem chapter07_finite_order_section_right_inverse
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (c : Chapter07UniformizerChoice R K) :
    (chapter07FiniteOrderHom R K).comp (chapter07FiniteOrderSection R K c) =
      MonoidHom.id (Multiplicative (chapter07FiniteDivisorGroup R)) := by
  sorry

theorem chapter07_finite_order_section_continuous
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (c : Chapter07UniformizerChoice R K) :
    @Continuous (Multiplicative (chapter07FiniteDivisorGroup R))
      (chapter07FiniteIdeleGroup R K)
      (chapter07FiniteDivisorDiscreteTopology R) inferInstance
      (chapter07FiniteOrderSection R K c) := by
  sorry

theorem chapter07_finite_order_splitting_is_noncanonical
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    ∀ c : Chapter07UniformizerChoice R K,
      Function.RightInverse (chapter07FiniteOrderSection R K c)
        (chapter07FiniteOrderHom R K) := by
  sorry

/-! ### Maximal compact subgroups -/

def chapter07RealMaximalCompact : Subgroup ℝˣ where
  carrier := {u | (u : ℝ) = 1 ∨ (u : ℝ) = -1}
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry

def chapter07ComplexMaximalCompact : Subgroup ℂˣ where
  carrier := {u | ‖(u : ℂ)‖ = 1}
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry

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
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    (v : chapter07FinitePlace R) :
    chapter07UniqueMaximalCompactSubgroup (chapter07LocalField R K v)ˣ
      (chapter07FiniteLocalMaximalCompact R K v) := by
  sorry

theorem chapter07_finite_integral_units_unique_maximal_compact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
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
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry

theorem chapter07_global_maximal_compact_is_compact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    IsCompact (chapter07GlobalMaximalCompact R K : Set (chapter07IdeleGroup R K)) := by
  sorry

theorem chapter07_global_maximal_compact_contains_compact_subgroups
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    (L : Subgroup (chapter07IdeleGroup R K))
    (hL : IsCompact (L : Set (chapter07IdeleGroup R K))) :
    L ≤ chapter07GlobalMaximalCompact R K := by
  sorry

theorem chapter07_global_maximal_compact_unique
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    chapter07UniqueMaximalCompactSubgroup (chapter07IdeleGroup R K)
      (chapter07GlobalMaximalCompact R K) := by
  sorry

theorem chapter07_global_maximal_compact_not_open
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    ¬ IsOpen (chapter07GlobalMaximalCompact R K : Set (chapter07IdeleGroup R K)) := by
  sorry

theorem chapter07_global_maximal_compact_is_not_an_open_subgroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    ¬ IsOpen (chapter07GlobalMaximalCompact R K : Set (chapter07IdeleGroup R K)) :=
  chapter07_global_maximal_compact_not_open R K

end

end LastLib.Book04AdelesAndIdeles.Chapter07
