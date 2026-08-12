import LastLib.Book04AdelesAndIdeles.Chapter07.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter07

noncomputable section

open Set Filter Topology
open scoped BigOperators DirectSum RestrictedProduct

/-! # 7.2 The idele group -/

/-- A basic restricted-product neighborhood with a finite exceptional set. -/
def chapter07RestrictedProductBasicOpen
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    (S : Set ι) (U : (i : ι) → Set (R i)) :
    Set (Πʳ i, [R i, A i]) :=
  {x | (∀ i ∈ S, x i ∈ U i) ∧ ∀ i ∉ S, x i ∈ A i}

theorem chapter07_restrictedProduct_basicOpen_isOpen
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    [∀ i, TopologicalSpace (R i)]
    (S : Set ι) (hS : S.Finite) (U : (i : ι) → Set (R i))
    (hU : ∀ i, IsOpen (U i)) (hA : ∀ i, IsOpen (A i)) :
    IsOpen (chapter07RestrictedProductBasicOpen R A S U) := by
  sorry

theorem chapter07_restrictedProduct_basicOpen_basis
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    [∀ i, TopologicalSpace (R i)] (hA : ∀ i, IsOpen (A i)) :
    ∀ x : Πʳ i, [R i, A i], ∀ U ∈ 𝓝 x,
      ∃ S : Set ι, S.Finite ∧ ∃ V : (i : ι) → Set (R i),
        (∀ i, IsOpen (V i)) ∧ x ∈ chapter07RestrictedProductBasicOpen R A S V ∧
          chapter07RestrictedProductBasicOpen R A S V ⊆ U := by
  sorry

/-- The book's full-idele basic open set: all archimedean coordinates are restricted to chosen
local neighborhoods, while only the finite set `S` of finite places has arbitrary neighborhoods. -/
def chapter07IdeleBasicOpen
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (S : Finset (chapter07FinitePlace R))
    (Uinf : (v : NumberField.InfinitePlace K) → Set ((v.Completion)ˣ))
    (Uf : (v : chapter07FinitePlace R) → Set ((chapter07LocalField R K v)ˣ)) :
    Set (chapter07IdeleGroup R K) :=
  {x |
    (∀ v : NumberField.InfinitePlace K,
      chapter07IdeleInfiniteCoordinate R K x v ∈ Uinf v) ∧
      (∀ v : chapter07FinitePlace R, v ∈ S →
        chapter07IdeleFiniteCoordinate R K x v ∈ Uf v) ∧
      (∀ v : chapter07FinitePlace R, v ∉ S →
        chapter07IdeleFiniteCoordinate R K x v ∈
          (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units)}

theorem chapter07_idele_basic_open_isOpen
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (S : Finset (chapter07FinitePlace R))
    (Uinf : (v : NumberField.InfinitePlace K) → Set ((v.Completion)ˣ))
    (Uf : (v : chapter07FinitePlace R) → Set ((chapter07LocalField R K v)ˣ))
    (hInf : ∀ v, IsOpen (Uinf v)) (hf : ∀ v, IsOpen (Uf v)) :
    IsOpen (chapter07IdeleBasicOpen R K S Uinf Uf) := by
  sorry

theorem chapter07_idele_basic_open_basis
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    ∀ U : Set (chapter07IdeleGroup R K), IsOpen U ↔
      ∀ x ∈ U, ∃ (S : Finset (chapter07FinitePlace R))
        (Uinf : (v : NumberField.InfinitePlace K) → Set ((v.Completion)ˣ))
        (Uf : (v : chapter07FinitePlace R) → Set ((chapter07LocalField R K v)ˣ)),
        (∀ v, IsOpen (Uinf v)) ∧ (∀ v, IsOpen (Uf v)) ∧
          x ∈ chapter07IdeleBasicOpen R K S Uinf Uf ∧
          chapter07IdeleBasicOpen R K S Uinf Uf ⊆ U := by
  sorry

@[simp]
theorem chapter07_idele_mul_apply_infinite
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x y : chapter07IdeleGroup R K) (v : NumberField.InfinitePlace K) :
    (x * y).1.1 v = x.1.1 v * y.1.1 v := by
  rfl

@[simp]
theorem chapter07_idele_mul_apply_finite
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x y : chapter07IdeleGroup R K) (v : chapter07FinitePlace R) :
    (x * y).1.2 v = x.1.2 v * y.1.2 v := by
  rfl

@[simp]
theorem chapter07_idele_inv_apply_infinite
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07IdeleGroup R K) (v : NumberField.InfinitePlace K) :
    (x⁻¹ : chapter07IdeleGroup R K).1.1 v = (x.1.1 v)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  exact congrArg (fun a : chapter07AdeleRing R K => a.1 v) x.val_inv

@[simp]
theorem chapter07_idele_inv_apply_finite
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07IdeleGroup R K) (v : chapter07FinitePlace R) :
    (x⁻¹ : chapter07IdeleGroup R K).1.2 v = (x.1.2 v)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  exact congrArg (fun a : chapter07AdeleRing R K => a.2 v) x.val_inv

instance chapter07_idele_group_is_comm_group
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    CommGroup (chapter07IdeleGroup R K) := by
  infer_instance

theorem chapter07_idele_group_is_topological_group
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    IsTopologicalGroup (chapter07IdeleGroup R K) := by
  infer_instance

theorem chapter07_idele_group_is_locally_compact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    LocallyCompactSpace (chapter07IdeleGroup R K) := by
  sorry

/-- The compact-open subgroup usually denoted `\widehat{\mathcal O}_K^×`. -/
def chapter07FiniteIntegralUnitSubgroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Subgroup (chapter07FiniteIdeleGroup R K) where
  carrier := {x | ∀ v : chapter07FinitePlace R,
    chapter07FiniteIdeleEquiv R K x v ∈
      (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units}
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry

theorem chapter07_mem_finiteIntegralUnitSubgroup_iff
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07FiniteIdeleGroup R K) :
    x ∈ chapter07FiniteIntegralUnitSubgroup R K ↔
      ∀ v : chapter07FinitePlace R,
        chapter07FiniteIdeleEquiv R K x v ∈
          (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units :=
  Iff.rfl

theorem chapter07_finiteIntegralUnits_valued_iff
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07FiniteIdeleGroup R K) :
    x ∈ chapter07FiniteIntegralUnitSubgroup R K ↔
      ∀ v : chapter07FinitePlace R,
        Valued.v (chapter07FiniteIdeleEquiv R K x v).1 = 1 := by
  sorry

theorem chapter07_finiteIntegralUnits_compact_open
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    IsCompact (chapter07FiniteIntegralUnitSubgroup R K : Set (chapter07FiniteIdeleGroup R K)) ∧
      IsOpen (chapter07FiniteIntegralUnitSubgroup R K : Set (chapter07FiniteIdeleGroup R K)) := by
  sorry

theorem chapter07_idele_graph_subspace_topology
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    (inferInstance : TopologicalSpace (chapter07IdeleGroup R K)) =
      TopologicalSpace.induced (chapter07IdeleGraph R K) inferInstance :=
  chapter07_ideleTopology_is_graphTopology R K

end

end LastLib.Book04AdelesAndIdeles.Chapter07
