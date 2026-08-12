import LastLib.Book04AdelesAndIdeles.Chapter07.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter07.Section02TheIdeleGroup

namespace LastLib.Book04AdelesAndIdeles.Chapter07

noncomputable section

open Set Filter Topology
open scoped BigOperators DirectSum RestrictedProduct Classical

/-! # 7.3 Additive and multiplicative information -/

/-- The finite-support order vector attached to a restricted product and a family of local order
maps.  It records precisely the places where the restricted-product coordinate is outside the
chosen integral subgroup. -/
def chapter07FiniteOrderVector
    {ι : Type*} (G : ι → Type*) (A : (i : ι) → Set (G i))
    (ord : (i : ι) → G i → ℤ)
    (x : Πʳ i, [G i, A i]) : ι →₀ ℤ := by
  classical
  let S : Set ι := {i | x i ∉ A i}
  have hS : S.Finite := by
    sorry
  exact
    { support := hS.toFinset.filter (fun i => ord i (x i) ≠ 0)
      toFun := fun i => if i ∈ S then ord i (x i) else 0
      mem_support_toFun := by
        sorry }

@[simp]
theorem chapter07FiniteOrderVector_apply
    {ι : Type*} (G : ι → Type*) (A : (i : ι) → Set (G i))
    (ord : (i : ι) → G i → ℤ)
    (x : Πʳ i, [G i, A i]) (i : ι) :
    chapter07FiniteOrderVector G A ord x i =
      if x i ∉ A i then ord i (x i) else 0 := by
  sorry

theorem chapter07FiniteOrderVector_finitely_supported
    {ι : Type*} (G : ι → Type*) (A : (i : ι) → Set (G i))
    (ord : (i : ι) → G i → ℤ)
    (x : Πʳ i, [G i, A i]) :
    ∀ᶠ i : ι in cofinite,
      chapter07FiniteOrderVector G A ord x i = 0 := by
  sorry

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
      sorry
    map_mul' := by
      sorry }

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
  sorry

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
  sorry

theorem chapter07_finite_idele_order_is_finitely_supported
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07FiniteIdeleGroup R K) :
    ((chapter07FiniteOrderValue R K x).support :
      Set (chapter07FinitePlace R)).Finite := by
  sorry

theorem chapter07_finite_idele_order_is_zero_at_almost_all_places
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07FiniteIdeleGroup R K) :
    ∀ᶠ v : chapter07FinitePlace R in cofinite,
      chapter07FiniteOrderHom R K x v = 0 := by
  sorry

theorem chapter07_finite_order_value_surjective
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Function.Surjective (chapter07FiniteOrderValue R K) := by
  sorry

theorem chapter07_finite_order_value_eq_zero_iff
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07FiniteIdeleGroup R K) :
    chapter07FiniteOrderValue R K x = 0 ↔
      x ∈ chapter07FiniteIntegralUnitSubgroup R K := by
  sorry

theorem chapter07_idele_coordinates_are_nonzero
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07IdeleGroup R K) :
    (∀ v : NumberField.InfinitePlace K, x.1.1 v ≠ 0) ∧
      ∀ v : chapter07FinitePlace R,
        x.1.2 v ≠ 0 := by
  sorry

theorem chapter07_idele_has_integral_units_at_almost_all_finite_places
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07IdeleGroup R K) :
    ∀ᶠ v : chapter07FinitePlace R in cofinite,
      Valued.v (x.1.2 v) = 1 := by
  sorry

/-- The valuation map forgets no information needed to recover the underlying additive adele,
but the induced topology on its domain is generally weaker than the idele topology. -/
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

theorem chapter07_idele_topology_is_finer_than_additive_induced_topology
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    chapter07NaiveIdeleTopology R K ≤
      (inferInstance : TopologicalSpace (chapter07IdeleGroup R K)) := by
  sorry

theorem chapter07_idele_to_adele_not_an_inducing
    [NumberField ℚ] :
    ¬ @IsInducing (chapter07IdeleGroup ℤ ℚ) (chapter07AdeleRing ℤ ℚ)
      inferInstance inferInstance (chapter07IdeleToAdele ℤ ℚ) := by
  sorry

/-- A partially zero adele: the additive adele ring permits local zero coordinates even when other
coordinates are nonzero. -/
noncomputable def chapter07PartialZeroAdele (v₀ : chapter07FinitePlace ℤ) :
    chapter07AdeleRing ℤ ℚ :=
  ⟨(1 : NumberField.InfiniteAdeleRing ℚ),
    RestrictedProduct.mk
      (fun v : chapter07FinitePlace ℤ => if v = v₀ then 0 else 1)
      (by sorry)⟩

theorem chapter07_partial_zero_adele_has_zero_coordinate
    (v₀ : chapter07FinitePlace ℤ) :
    (chapter07PartialZeroAdele v₀).2 v₀ = 0 := by
  sorry

theorem chapter07_partial_zero_adele_has_nonzero_coordinate
    (v₀ : chapter07FinitePlace ℤ)
    (w : chapter07FinitePlace ℤ) (hw : w ≠ v₀) :
    (chapter07PartialZeroAdele v₀).2 w = 1 := by
  sorry

theorem chapter07_additive_adele_not_a_single_global_zero_extension :
    ∃ x : chapter07AdeleRing ℤ ℚ,
      (∃ v : chapter07FinitePlace ℤ, x.2 v = 0) ∧
        (∃ w : chapter07FinitePlace ℤ, x.2 w ≠ 0) := by
  sorry

theorem chapter07_additive_adele_allows_finite_zero_patterns
    (S : Set (chapter07FinitePlace ℤ)) (hS : S.Finite) :
    ∃ x : chapter07AdeleRing ℤ ℚ,
      (∀ v ∈ S, x.2 v = 0) ∧ (∀ v ∉ S, x.2 v = 1) := by
  sorry

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
