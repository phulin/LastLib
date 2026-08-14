import LastLib.Book04AdelesAndIdeles.Chapter07.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter07.Section01WhyNonzeroAdelesNotEnough
import LastLib.Book04AdelesAndIdeles.Chapter07.Section02TheIdeleGroup

namespace LastLib.Book04AdelesAndIdeles.Chapter07

noncomputable section

open Set Filter Topology
open scoped BigOperators DirectSum RestrictedProduct Classical

/-! # 7.3 Additive and multiplicative information -/

/-- The finite-support order vector attached to a restricted product and a family of local order
maps.  It records the nonzero order values at the finitely many places where the coordinate is
outside the chosen integral subgroup. -/
def chapter07FiniteOrderVector
    {ι : Type*} (G : ι → Type*) (A : (i : ι) → Set (G i))
    (ord : (i : ι) → G i → ℤ)
    (x : Πʳ i, [G i, A i]) : ι →₀ ℤ := by
  classical
  let S : Set ι := {i | (x i : G i) ∉ A i}
  have hS : S.Finite := by
    exact eventually_cofinite.mp x.2
  exact
    { support := hS.toFinset.filter (fun i => ord i (x i) ≠ 0)
      toFun := fun i => if i ∈ S then ord i (x i) else 0
      mem_support_toFun := by
        intro i
        simp [S] }

@[simp]
theorem chapter07FiniteOrderVector_apply
    {ι : Type*} (G : ι → Type*) (A : (i : ι) → Set (G i))
    (ord : (i : ι) → G i → ℤ)
    (x : Πʳ i, [G i, A i]) (i : ι) :
    chapter07FiniteOrderVector G A ord x i =
      if x i ∉ A i then ord i (x i) else 0 := by
  simp [chapter07FiniteOrderVector]

theorem chapter07FiniteOrderVector_finitely_supported
    {ι : Type*} (G : ι → Type*) (A : (i : ι) → Set (G i))
    (ord : (i : ι) → G i → ℤ)
    (x : Πʳ i, [G i, A i]) :
    ∀ᶠ i : ι in cofinite,
      chapter07FiniteOrderVector G A ord x i = 0 := by
  filter_upwards [x.2] with i hi
  rw [chapter07FiniteOrderVector_apply]
  exact if_neg (fun h => h hi)

/-- The order homomorphism on finite ideles. -/
def chapter07FiniteOrderHom
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    chapter07FiniteIdeleGroup R K →* Multiplicative (chapter07FiniteDivisorGroup R) :=
  { toFun := fun x =>
      Multiplicative.ofAdd <|
        chapter07FiniteOrderVector
          (fun v : chapter07FinitePlace R => (chapter07LocalField R K v)ˣ)
          (fun v : chapter07FinitePlace R =>
            (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units)
          (fun v : chapter07FinitePlace R => chapter07LocalOrder R K v)
          (chapter07FiniteIdeleEquiv R K x)
    map_one' := by
      ext v
      simp [chapter07FiniteOrderVector_apply]
    map_mul' := by
      intro x y
      ext v
      have hvec (z : chapter07FiniteIdeleGroup R K) :
          chapter07FiniteOrderVector
              (fun v : chapter07FinitePlace R => (chapter07LocalField R K v)ˣ)
              (fun v : chapter07FinitePlace R =>
                (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units)
              (fun v : chapter07FinitePlace R => chapter07LocalOrder R K v)
              (chapter07FiniteIdeleEquiv R K z) v =
            chapter07LocalOrder R K v (chapter07FiniteIdeleEquiv R K z v) := by
        rw [chapter07FiniteOrderVector_apply]
        split_ifs with hz
        · exact (chapter07LocalOrder_eq_zero_on_integral_units R K v
            (chapter07FiniteIdeleEquiv R K z v) hz).symm
        · rfl
      simp only [toAdd_ofAdd, toAdd_mul]
      simp only [Finsupp.add_apply]
      rw [hvec (x * y), hvec x, hvec y]
      simpa using (chapter07LocalOrder_mul R K v
        (chapter07FiniteIdeleEquiv R K x v) (chapter07FiniteIdeleEquiv R K y v)) }

/-- The same finite order map with its additive divisor-group codomain exposed to book-facing
statements. -/
def chapter07FiniteOrderValue
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    chapter07FiniteIdeleGroup R K → chapter07FiniteDivisorGroup R :=
  fun x => Multiplicative.toAdd (chapter07FiniteOrderHom R K x)

theorem chapter07FiniteOrderValue_mul
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x y : chapter07FiniteIdeleGroup R K) :
    chapter07FiniteOrderValue R K (x * y) =
      chapter07FiniteOrderValue R K x + chapter07FiniteOrderValue R K y := by
  change Multiplicative.toAdd (chapter07FiniteOrderHom R K (x * y)) = _
  rw [(chapter07FiniteOrderHom R K).map_mul]
  rfl

@[simp]
theorem chapter07FiniteOrderHom_apply
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07FiniteIdeleGroup R K) (v : chapter07FinitePlace R) :
    chapter07FiniteOrderHom R K x v =
      if chapter07FiniteIdeleEquiv R K x v ∈
          (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units then
        0
      else chapter07LocalOrder R K v (chapter07FiniteIdeleEquiv R K x v) := by
  change chapter07FiniteOrderVector
      (fun v : chapter07FinitePlace R => (chapter07LocalField R K v)ˣ)
      (fun v : chapter07FinitePlace R =>
        (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units)
      (fun v : chapter07FinitePlace R => chapter07LocalOrder R K v)
      (chapter07FiniteIdeleEquiv R K x) v = _
  rw [chapter07FiniteOrderVector_apply]
  by_cases h : chapter07FiniteIdeleEquiv R K x v ∈
      (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units <;> simp [h]

theorem chapter07_finite_idele_order_is_finitely_supported
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07FiniteIdeleGroup R K) :
    ((chapter07FiniteOrderValue R K x).support :
      Set (chapter07FinitePlace R)).Finite := by
  exact (chapter07FiniteOrderValue R K x).support.finite_toSet

theorem chapter07_finite_idele_order_is_zero_at_almost_all_places
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07FiniteIdeleGroup R K) :
    ∀ᶠ v : chapter07FinitePlace R in cofinite,
      chapter07FiniteOrderHom R K x v = 0 := by
  exact chapter07FiniteOrderVector_finitely_supported
    (G := fun v : chapter07FinitePlace R => (chapter07LocalField R K v)ˣ)
    (A := fun v : chapter07FinitePlace R =>
      (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units)
    (ord := fun v : chapter07FinitePlace R => chapter07LocalOrder R K v)
    (chapter07FiniteIdeleEquiv R K x)

theorem chapter07_finite_order_value_surjective
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Function.Surjective (chapter07FiniteOrderValue R K) := by
  intro d
  let u : ∀ v : chapter07FinitePlace R, (chapter07LocalField R K v)ˣ :=
    fun v => Classical.choose (chapter07LocalOrder_surjective R K v (d v))
  have hu : ∀ v : chapter07FinitePlace R,
      chapter07LocalOrder R K v (u v) = d v := by
    intro v
    exact Classical.choose_spec (chapter07LocalOrder_surjective R K v (d v))
  let y : chapter07FiniteIdeleRestrictedProduct R K :=
    RestrictedProduct.mk u (by
      filter_upwards [d.support.finite_toSet.compl_mem_cofinite] with v hv
      apply (chapter07LocalOrder_eq_zero_iff_mem_localIntegralUnitSubgroup R K v (u v)).1
      rw [hu v, Finsupp.notMem_support_iff.mp hv])
  refine ⟨(chapter07FiniteIdeleEquiv R K).symm y, ?_⟩
  change Multiplicative.toAdd (chapter07FiniteOrderHom R K ((chapter07FiniteIdeleEquiv R K).symm y)) = d
  ext v
  have hy : chapter07FiniteIdeleEquiv R K ((chapter07FiniteIdeleEquiv R K).symm y) v = u v := by
    change y v = u v
    rfl
  rw [chapter07FiniteOrderHom_apply, hy]
  by_cases hv : u v ∈ (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units
  · have hdv : d v = 0 := by
      have hv' : u v ∈ chapter07LocalIntegralUnitSubgroup R K v := hv
      have hord :=
        (chapter07LocalOrder_eq_zero_iff_mem_localIntegralUnitSubgroup R K v (u v)).2 hv'
      rw [hu v] at hord
      exact hord
    simp [hv, hdv]
  · simp [hv, hu v]

theorem chapter07_finite_order_value_eq_zero_iff
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07FiniteIdeleGroup R K) :
    chapter07FiniteOrderValue R K x = 0 ↔
      x ∈ chapter07FiniteIntegralUnitSubgroup R K := by
  constructor
  · intro hx
    rw [chapter07_mem_finiteIntegralUnitSubgroup_iff]
    intro v
    apply (chapter07LocalOrder_eq_zero_iff_mem_localIntegralUnitSubgroup R K v
      (chapter07FiniteIdeleEquiv R K x v)).1
    have hx' : chapter07FiniteOrderHom R K x =
        (1 : Multiplicative (chapter07FiniteDivisorGroup R)) := by
      simpa [chapter07FiniteOrderValue] using hx
    have hv := congrArg (fun d : Multiplicative (chapter07FiniteDivisorGroup R) => d v) hx'
    by_cases h : chapter07FiniteIdeleEquiv R K x v ∈
        (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units
    · exact chapter07LocalOrder_eq_zero_on_integral_units R K v
        (chapter07FiniteIdeleEquiv R K x v) h
    · simpa [chapter07FiniteOrderHom_apply, h] using hv
  · intro hx
    have hx' : ∀ v : chapter07FinitePlace R,
        chapter07FiniteIdeleEquiv R K x v ∈
          (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units :=
      (chapter07_mem_finiteIntegralUnitSubgroup_iff R K x).1 hx
    change Multiplicative.toAdd (chapter07FiniteOrderHom R K x) = 0
    ext v
    simp [chapter07FiniteOrderHom_apply, hx' v]

theorem chapter07_idele_coordinates_are_nonzero
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07IdeleGroup R K) :
    (∀ v : NumberField.InfinitePlace K, x.1.1 v ≠ 0) ∧
      ∀ v : chapter07FinitePlace R,
        x.1.2 v ≠ 0 := by
  have hx : IsUnit (x : chapter07AdeleRing R K) := x.isUnit
  have hx' := (Prod.isUnit_iff.mp hx)
  have hxi := hx'.1
  have hxf := hx'.2
  change IsUnit (fun v : NumberField.InfinitePlace K =>
    (x : chapter07AdeleRing R K).1 v) at hxi
  rw [Pi.isUnit_iff] at hxi
  rw [IsDedekindDomain.FiniteAdeleRing.isUnit_iff] at hxf
  have hinf : ∀ v : NumberField.InfinitePlace K, x.1.1 v ≠ 0 := by
    simpa only [isUnit_iff_ne_zero] using hxi
  exact ⟨hinf, by simpa only [isUnit_iff_ne_zero] using hxf.1⟩

theorem chapter07_idele_has_integral_units_at_almost_all_finite_places
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07IdeleGroup R K) :
    ∀ᶠ v : chapter07FinitePlace R in cofinite,
      Valued.v (x.1.2 v) = 1 := by
  have hx : IsUnit (x : chapter07AdeleRing R K) := x.isUnit
  have hx' := (Prod.isUnit_iff.mp hx)
  have hxf := hx'.2
  rw [IsDedekindDomain.FiniteAdeleRing.isUnit_iff] at hxf
  exact hxf.2

/-- The underlying-coordinate map forgets no information needed to recover the additive adele,
but the topology it induces is generally weaker than the idele topology. -/
def chapter07IdeleToAdele
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    chapter07IdeleGroup R K → chapter07AdeleRing R K :=
  fun x => x

theorem chapter07_idele_to_adele_continuous
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Continuous (chapter07IdeleToAdele R K) := by
  exact Units.continuous_val

theorem chapter07_idele_to_adele_injective
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Function.Injective (chapter07IdeleToAdele R K) := by
  intro x y hxy
  apply Units.ext
  exact hxy

theorem chapter07_idele_topology_is_finer_than_additive_induced_topology
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    (inferInstance : TopologicalSpace (chapter07IdeleGroup R K)) ≤
      chapter07NaiveIdeleTopology R K := by
  exact (chapter07_idele_to_adele_continuous R K).le_induced

theorem chapter07_idele_to_adele_not_an_inducing
    [NumberField ℚ] :
    ¬ @IsInducing (chapter07IdeleGroup ℤ ℚ) (chapter07AdeleRing ℤ ℚ)
      inferInstance inferInstance (chapter07IdeleToAdele ℤ ℚ) := by
  intro h
  have htop :
      (inferInstance : TopologicalSpace (chapter07IdeleGroup ℤ ℚ)) =
        chapter07NaiveIdeleTopology ℤ ℚ :=
    h.eq_induced
  have hinv : @Continuous (chapter07IdeleGroup ℤ ℚ) (chapter07IdeleGroup ℤ ℚ)
      inferInstance inferInstance (fun x => x⁻¹) :=
    continuous_inv
  rw [htop] at hinv
  exact chapter07_naive_idele_inversion_not_continuous hinv

/-- A partially zero adele: the additive adele ring permits local zero coordinates even when other
coordinates are nonzero. -/
noncomputable def chapter07PartialZeroAdele (v₀ : chapter07FinitePlace ℤ) :
    chapter07AdeleRing ℤ ℚ :=
  ⟨(1 : NumberField.InfiniteAdeleRing ℚ),
    RestrictedProduct.mk
      (fun v : chapter07FinitePlace ℤ => if v = v₀ then 0 else 1)
      (by
        filter_upwards [(finite_singleton v₀).compl_mem_cofinite] with v hv
        split_ifs
        · exact (chapter07LocalIntegerRing ℤ ℚ v).zero_mem
        · exact (chapter07LocalIntegerRing ℤ ℚ v).one_mem)⟩

theorem chapter07_partial_zero_adele_has_zero_coordinate
    (v₀ : chapter07FinitePlace ℤ) :
    (chapter07PartialZeroAdele v₀).2 v₀ = 0 := by
  change (if v₀ = v₀ then (0 : chapter07LocalField ℤ ℚ v₀) else 1) = 0
  simp

theorem chapter07_partial_zero_adele_has_nonzero_coordinate
    (v₀ : chapter07FinitePlace ℤ)
    (w : chapter07FinitePlace ℤ) (hw : w ≠ v₀) :
    (chapter07PartialZeroAdele v₀).2 w = 1 := by
  change (if w = v₀ then (0 : chapter07LocalField ℤ ℚ w) else 1) = 1
  simp [hw]

theorem chapter07_additive_adele_not_a_single_global_zero_extension :
    ∃ x : chapter07AdeleRing ℤ ℚ,
      (∃ v : chapter07FinitePlace ℤ, x.2 v = 0) ∧
        (∃ w : chapter07FinitePlace ℤ, x.2 w ≠ 0) := by
  let v₀ : chapter07FinitePlace ℤ :=
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨2, by decide⟩
  let w : chapter07FinitePlace ℤ :=
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨3, by decide⟩
  have hw : w ≠ v₀ := by
    intro h
    have h' : (⟨3, by decide⟩ : Nat.Primes) = ⟨2, by decide⟩ :=
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm.injective (by
        simpa [w, v₀] using h)
    norm_num at h'
  refine ⟨chapter07PartialZeroAdele v₀, ⟨v₀, ?_⟩, ⟨w, ?_⟩⟩
  · exact chapter07_partial_zero_adele_has_zero_coordinate v₀
  · rw [chapter07_partial_zero_adele_has_nonzero_coordinate v₀ w hw]
    exact one_ne_zero

theorem chapter07_additive_adele_allows_finite_zero_patterns
    (S : Set (chapter07FinitePlace ℤ)) (hS : S.Finite) :
    ∃ x : chapter07AdeleRing ℤ ℚ,
      (∀ v ∈ S, x.2 v = 0) ∧ (∀ v ∉ S, x.2 v = 1) := by
  refine ⟨⟨(1 : NumberField.InfiniteAdeleRing ℚ),
    RestrictedProduct.mk (fun v : chapter07FinitePlace ℤ => if v ∈ S then 0 else 1) (by
      filter_upwards [hS.compl_mem_cofinite] with v hv
      split_ifs
      · exact (chapter07LocalIntegerRing ℤ ℚ v).zero_mem
      · exact (chapter07LocalIntegerRing ℤ ℚ v).one_mem)⟩, ?_, ?_⟩
  · intro v hv
    change (if v ∈ S then (0 : chapter07LocalField ℤ ℚ v) else 1) = 0
    simp [hv]
  · intro v hv
    change (if v ∈ S then (0 : chapter07LocalField ℤ ℚ v) else 1) = 1
    simp [hv]

@[simp]
theorem chapter07_additive_adele_add_apply_finite
    (x y : chapter07AdeleRing ℤ ℚ) (v : chapter07FinitePlace ℤ) :
    (x + y).2 v = x.2 v + y.2 v := by
  rfl

@[simp]
theorem chapter07_additive_adele_add_apply_infinite
    (x y : chapter07AdeleRing ℤ ℚ) (v : NumberField.InfinitePlace ℚ) :
    (x + y).1 v = x.1 v + y.1 v := by
  rfl

end

end LastLib.Book04AdelesAndIdeles.Chapter07
