import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Mathlib.Topology.DiscreteSubset

namespace LastLib.Book04AdelesAndIdeles.Chapter07

noncomputable section

open Set Filter Topology
open scoped BigOperators DirectSum RestrictedProduct

/-!
Shared interfaces for Book 4, Chapter 7.

The pinned Mathlib already supplies the finite and full adele rings and the
topology on restricted products.  This file keeps the chapter's notation
close to those canonical definitions, and records the few book-facing
bridges which are not bundled into a single Mathlib declaration.
-/

abbrev chapter07AdeleRing
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  NumberField.AdeleRing R K

abbrev chapter07FiniteAdeleRing
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  IsDedekindDomain.FiniteAdeleRing R K

abbrev chapter07IdeleGroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  (chapter07AdeleRing R K)ˣ

/-- The topology inherited by the units from the additive adele ring. -/
@[instance_reducible]
def chapter07NaiveIdeleTopology
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    TopologicalSpace (chapter07IdeleGroup R K) :=
  TopologicalSpace.induced (fun x : chapter07IdeleGroup R K => (x : chapter07AdeleRing R K))
    inferInstance

abbrev chapter07FiniteIdeleGroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  (chapter07FiniteAdeleRing R K)ˣ

abbrev chapter07FinitePlace
    (R : Type*) [CommRing R] [IsDedekindDomain R] :=
  IsDedekindDomain.HeightOneSpectrum R

abbrev chapter07LocalField
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :=
  v.adicCompletion K

abbrev chapter07LocalIntegerRing
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :=
  v.adicCompletionIntegers K

/-- The unit subgroup of the local integer ring, viewed inside the local field's unit group. -/
abbrev chapter07LocalIntegralUnitSubgroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) : Subgroup (chapter07LocalField R K v)ˣ :=
  (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units

@[simp]
theorem chapter07_mem_localIntegralUnitSubgroup_iff
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) (u : (chapter07LocalField R K v)ˣ) :
    u ∈ chapter07LocalIntegralUnitSubgroup R K v ↔
      u ∈ (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units :=
  Iff.rfl

/-- The finite idele group, with its canonical restricted-product presentation available through
`chapter07FiniteIdeleEquiv`.  The primary definition is the unit group of the finite adele ring,
so it inherits the graph topology supplied by Mathlib. -/
abbrev chapter07FiniteIdeleRestrictedProduct
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] : Type _ :=
  Πʳ v : chapter07FinitePlace R,
    [(chapter07LocalField R K v)ˣ,
      chapter07LocalIntegralUnitSubgroup R K v]

/-- The canonical restricted-product description of the finite ideles. -/
def chapter07FiniteIdeleEquiv
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    chapter07FiniteIdeleGroup R K ≃*
      chapter07FiniteIdeleRestrictedProduct R K :=
  RestrictedProduct.unitsEquiv
    (𝓕 := Filter.cofinite)
    (B := fun v : chapter07FinitePlace R => chapter07LocalIntegerRing R K v)
    (fun v : chapter07FinitePlace R => chapter07LocalField R K v)

@[simp]
theorem chapter07FiniteIdeleEquiv_apply
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07FiniteIdeleGroup R K) (v : chapter07FinitePlace R) :
    chapter07FiniteIdeleEquiv R K x v = x.1 v :=
  rfl

/-- The finite divisor group in the book's direct-sum notation. -/
abbrev chapter07FiniteDivisorGroup
    (R : Type*) [CommRing R] [IsDedekindDomain R] :=
  chapter07FinitePlace R →₀ ℤ

def chapter07FiniteDivisorGroupToDirectSum
    (R : Type*) [CommRing R] [IsDedekindDomain R] :
    chapter07FiniteDivisorGroup R ≃+
      (⨁ _ : chapter07FinitePlace R, ℤ) :=
  letI : DecidableEq (chapter07FinitePlace R) := Classical.decEq _
  (finsuppLEquivDirectSum ℤ ℤ (chapter07FinitePlace R)).toAddEquiv

@[simp]
theorem chapter07FiniteDivisorGroupToDirectSum_apply
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (d : chapter07FiniteDivisorGroup R) (v : chapter07FinitePlace R) :
    chapter07FiniteDivisorGroupToDirectSum R d v = d v :=
by
  rfl

/-! ### The graph topology of units -/

def chapter07IdeleGraph
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    chapter07IdeleGroup R K → chapter07AdeleRing R K × chapter07AdeleRing R K :=
  fun x => (x.1, (x⁻¹ : chapter07IdeleGroup R K).1)

@[simp]
theorem chapter07IdeleGraph_apply_fst
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (x : chapter07IdeleGroup R K) :
    (chapter07IdeleGraph R K x).1 = x.1 :=
  rfl

@[simp]
theorem chapter07IdeleGraph_apply_snd
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (x : chapter07IdeleGroup R K) :
    (chapter07IdeleGraph R K x).2 = (x⁻¹ : chapter07IdeleGroup R K).1 :=
  rfl

/-! ### Local unit coordinates of a full idele -/

/-- The local unit represented by an infinite coordinate of a full idele.  The inverse coordinate
comes from the inverse adele and supplies the unit laws. -/
def chapter07IdeleInfiniteCoordinate
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07IdeleGroup R K) (v : NumberField.InfinitePlace K) : (v.Completion)ˣ where
  val := x.1.1 v
  inv := (x⁻¹ : chapter07IdeleGroup R K).1.1 v
  val_inv := by sorry
  inv_val := by sorry

@[simp]
theorem chapter07IdeleInfiniteCoordinate_val
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07IdeleGroup R K) (v : NumberField.InfinitePlace K) :
    (chapter07IdeleInfiniteCoordinate R K x v : v.Completion) = x.1.1 v :=
  rfl

/-- The local unit represented by a finite coordinate of a full idele. -/
def chapter07IdeleFiniteCoordinate
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07IdeleGroup R K) (v : chapter07FinitePlace R) :
    (chapter07LocalField R K v)ˣ where
  val := x.1.2 v
  inv := (x⁻¹ : chapter07IdeleGroup R K).1.2 v
  val_inv := by sorry
  inv_val := by sorry

@[simp]
theorem chapter07IdeleFiniteCoordinate_val
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07IdeleGroup R K) (v : chapter07FinitePlace R) :
    (chapter07IdeleFiniteCoordinate R K x v : chapter07LocalField R K v) = x.1.2 v :=
  rfl

/-! ### A restricted-product presentation over all places -/

abbrev chapter07AllPlace
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  Sum (NumberField.InfinitePlace K) (chapter07FinitePlace R)

abbrev chapter07AllLocalUnitGroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (w : chapter07AllPlace R K) : Type _ :=
  match w with
  | Sum.inl v => (v.Completion)ˣ
  | Sum.inr v => (chapter07LocalField R K v)ˣ

instance chapter07AllLocalUnitGroup_group
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (w : chapter07AllPlace R K) :
    Group (chapter07AllLocalUnitGroup R K w) := by
  cases w <;> infer_instance

instance chapter07AllLocalUnitGroup_topologicalSpace
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (w : chapter07AllPlace R K) :
    TopologicalSpace (chapter07AllLocalUnitGroup R K w) := by
  cases w <;> infer_instance

def chapter07AllIntegralUnitSubgroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (w : chapter07AllPlace R K) : Subgroup (chapter07AllLocalUnitGroup R K w) :=
  match w with
  | Sum.inl _ => ⊤
  | Sum.inr v => chapter07LocalIntegralUnitSubgroup R K v

abbrev chapter07AllIntegralUnitSet
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (w : chapter07AllPlace R K) : Set (chapter07AllLocalUnitGroup R K w) :=
  chapter07AllIntegralUnitSubgroup R K w

abbrev chapter07GlobalIdeleRestrictedProduct
  (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  Πʳ w : chapter07AllPlace R K,
    [chapter07AllLocalUnitGroup R K w, chapter07AllIntegralUnitSubgroup R K w]

/-- The full idele group is the restricted product of the local multiplicative groups, with no
restriction at archimedean places and the local integral unit restriction at finite places. -/
noncomputable def chapter07IdeleRestrictedProductEquiv
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    chapter07IdeleGroup R K ≃*
      chapter07GlobalIdeleRestrictedProduct R K where
  toFun x :=
    RestrictedProduct.mk
      (fun w => match w with
        | Sum.inl v => chapter07IdeleInfiniteCoordinate R K x v
        | Sum.inr v => chapter07IdeleFiniteCoordinate R K x v)
      (by sorry)
  invFun y :=
    { val :=
        ⟨(fun v : NumberField.InfinitePlace K =>
            (y (Sum.inl v) : v.Completion)),
          RestrictedProduct.mk
            (fun v : chapter07FinitePlace R =>
              (y (Sum.inr v) : chapter07LocalField R K v))
            (by sorry)⟩
      inv :=
        ⟨(fun v : NumberField.InfinitePlace K =>
            ((y (Sum.inl v))⁻¹ : v.Completion)),
          RestrictedProduct.mk
            (fun v : chapter07FinitePlace R =>
              ((y (Sum.inr v))⁻¹ : chapter07LocalField R K v))
            (by sorry)⟩
      val_inv := by sorry
      inv_val := by sorry }
  left_inv := by sorry
  right_inv := by sorry
  map_mul' := by sorry

theorem chapter07_idele_restrictedProduct_topology
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    (inferInstance : TopologicalSpace (chapter07IdeleGroup R K)) =
      TopologicalSpace.induced (chapter07IdeleRestrictedProductEquiv R K) inferInstance := by
  sorry

theorem chapter07_ideleGraph_isEmbedding
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    IsEmbedding (chapter07IdeleGraph R K) := by
  sorry

theorem chapter07_ideleTopology_is_graphTopology
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    (inferInstance : TopologicalSpace (chapter07IdeleGroup R K)) =
      TopologicalSpace.induced (chapter07IdeleGraph R K) inferInstance := by
  sorry

/-! ### A reusable maximal-compactness predicate -/

/-- A subgroup which contains every compact subgroup.  This packages the uniqueness assertion
used for the local and global maximal compact subgroups. -/
def chapter07UniqueMaximalCompactSubgroup
    (G : Type*) [Group G] [TopologicalSpace G] (H : Subgroup G) : Prop :=
  IsCompact (H : Set G) ∧
    ∀ L : Subgroup G, IsCompact (L : Set G) → L ≤ H

theorem chapter07UniqueMaximalCompactSubgroup.is_compact
    (G : Type*) [Group G] [TopologicalSpace G] (H : Subgroup G)
    (hH : chapter07UniqueMaximalCompactSubgroup G H) :
    IsCompact (H : Set G) :=
  hH.1

theorem chapter07UniqueMaximalCompactSubgroup.contains_compact
    (G : Type*) [Group G] [TopologicalSpace G] (H : Subgroup G)
    (hH : chapter07UniqueMaximalCompactSubgroup G H)
    (L : Subgroup G) (hL : IsCompact (L : Set G)) :
    L ≤ H :=
  hH.2 L hL

/-! ### Local orders -/

/- LOCAL_DEPENDENCY_GUESS: Mathlib exposes the normalized valuation on each finite completion, but
does not package its integer-valued order map on the local unit group.  The following map is the
canonical `-log` normalization; its two homomorphism laws are deferred to the proof pass. -/
noncomputable def chapter07LocalOrder
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :
    (chapter07LocalField R K v)ˣ → ℤ :=
  fun u => -WithZero.log (Valued.v u.1)

@[simp]
theorem chapter07LocalOrder_apply_one
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :
    chapter07LocalOrder R K v 1 = 0 := by
  sorry

theorem chapter07LocalOrder_mul
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) (u w : (chapter07LocalField R K v)ˣ) :
    chapter07LocalOrder R K v (u * w) =
      chapter07LocalOrder R K v u + chapter07LocalOrder R K v w := by
  sorry

theorem chapter07LocalOrder_inv
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) (u : (chapter07LocalField R K v)ˣ) :
    chapter07LocalOrder R K v u⁻¹ = -chapter07LocalOrder R K v u := by
  sorry

theorem chapter07LocalOrder_eq_zero_on_integral_units
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) (u : (chapter07LocalField R K v)ˣ)
    (hu : u ∈ chapter07LocalIntegralUnitSubgroup R K v) :
    chapter07LocalOrder R K v u = 0 := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter07
