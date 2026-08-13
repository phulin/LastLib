import LastLib.Book06GlobalClassFieldTheory.Chapter05.Dependencies
import LastLib.Book06GlobalClassFieldTheory.Chapter02.Dependencies
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.GroupTheory.Index

namespace LastLib.Book06GlobalClassFieldTheory.Chapter05

noncomputable section

/-! ## 5.2. Frobenius, decomposition, and inertia -/

universe uU uG uk uk' uC

/-- The local decomposition/inertia profile attached to a finite place. -/
structure Chapter05LocalDecompositionProfile
    (U : Type uU) (G : Type uG) [CommGroup U] [CommGroup G] [Finite G] where
  localArtin : U →* G
  units : Subgroup U
  unitFiltration : Chapter05UnitFiltration U
  decomposition : Subgroup G
  inertia : Subgroup G
  upperRamification : ℕ → Subgroup G
  units_eq_filtration_units : units = unitFiltration.units
  decomposition_eq_range : Subgroup.map localArtin ⊤ = decomposition
  inertia_eq_units_range : Subgroup.map localArtin units = inertia
  upperRamification_eq_unit_range :
    ∀ n, Subgroup.map localArtin (unitFiltration.level n) = upperRamification n

theorem chapter05_local_decomposition_range
    {U : Type uU} {G : Type uG} [CommGroup U] [CommGroup G] [Finite G]
    (D : Chapter05LocalDecompositionProfile U G) :
    Subgroup.map D.localArtin ⊤ = D.decomposition := by
  exact D.decomposition_eq_range

theorem chapter05_local_inertia_range
    {U : Type uU} {G : Type uG} [CommGroup U] [CommGroup G] [Finite G]
    (D : Chapter05LocalDecompositionProfile U G) :
    Subgroup.map D.localArtin D.units = D.inertia := by
  exact D.inertia_eq_units_range

theorem chapter05_local_upper_ramification_range
    {U : Type uU} {G : Type uG} [CommGroup U] [CommGroup G] [Finite G]
    (D : Chapter05LocalDecompositionProfile U G) (n : ℕ) :
    Subgroup.map D.localArtin (D.unitFiltration.level n) = D.upperRamification n := by
  exact D.upperRamification_eq_unit_range n

/-- Arithmetic Frobenius is the automorphism `x ↦ x^q` on the residue field. -/
def chapter05ArithmeticFrobenius
    {k : Type uk} {k' : Type uk'} [Field k] [Field k'] [Algebra k k']
    [Fintype k] [Finite k'] [Algebra.IsAlgebraic k k']
    (q : ℕ) (σ : Gal(k' / k)) : Prop :=
  ∀ x : k', σ x = x ^ q

/-
DEPENDENCY_GUESS: `Chapter05LocalOrder` is the local-field valuation
interface provided by the preceding chapters.  Its decomposition field is
the bridge needed for the unramified local Artin formula.
-/
/-- A local valuation vector used to state the unramified formula. -/
abbrev Chapter05LocalOrder
    (U : Type uU) [CommGroup U] (units : Subgroup U) :=
  LastLib.Book06GlobalClassFieldTheory.Chapter02.Chapter02DiscreteValuationData U units

/-- The local data at an unramified finite place, including the arithmetic
Frobenius normalization. -/
structure Chapter05UnramifiedPlaceProfile
    (U : Type uU) (G : Type uG) (k : Type uk) (k' : Type uk')
    [CommGroup U] [CommGroup G] [Finite G] [Field k] [Field k'] [Algebra k k']
    [Fintype k] [Finite k'] [Algebra.IsAlgebraic k k'] [FiniteDimensional k k']
    where
  units : Subgroup U
  order : Chapter05LocalOrder U units
  localArtin : U →* G
  decomposition : Subgroup G
  inertia : Subgroup G
  residueAction : G →* Gal(k' / k)
  q : ℕ
  q_eq_card : q = Fintype.card k
  frobenius : G
  inertia_trivial : inertia = ⊥
  range_decomposition : Subgroup.map localArtin ⊤ = decomposition
  range_units : Subgroup.map localArtin units = inertia
  localArtin_uniformizer : localArtin order.uniformizer = frobenius
  arithmetic_frobenius : chapter05ArithmeticFrobenius q (residueAction frobenius)

theorem chapter05_unramified_inertia_trivial
    {U : Type uU} {G : Type uG} {k : Type uk} {k' : Type uk'}
    [CommGroup U] [CommGroup G] [Finite G] [Field k] [Field k'] [Algebra k k']
    [Fintype k] [Finite k'] [Algebra.IsAlgebraic k k'] [FiniteDimensional k k']
    (D : Chapter05UnramifiedPlaceProfile U G k k') : D.inertia = ⊥ := by
  exact D.inertia_trivial

theorem chapter05_unramified_arithmetic_frobenius
    {U : Type uU} {G : Type uG} {k : Type uk} {k' : Type uk'}
    [CommGroup U] [CommGroup G] [Finite G] [Field k] [Field k'] [Algebra k k']
    [Fintype k] [Finite k'] [Algebra.IsAlgebraic k k'] [FiniteDimensional k k']
    (D : Chapter05UnramifiedPlaceProfile U G k k') :
    chapter05ArithmeticFrobenius D.q (D.residueAction D.frobenius) := by
  exact D.arithmetic_frobenius

/-- At an unramified place the local symbol depends only on the valuation. -/
theorem chapter05_unramified_local_artin_formula
    {U : Type uU} {G : Type uG} {k : Type uk} {k' : Type uk'}
    [CommGroup U] [CommGroup G] [Finite G] [Field k] [Field k'] [Algebra k k']
    [Fintype k] [Finite k'] [Algebra.IsAlgebraic k k'] [FiniteDimensional k k']
    (D : Chapter05UnramifiedPlaceProfile U G k k') (x : U) :
    D.localArtin x = D.frobenius ^ D.order.ord x := by
  sorry

theorem chapter05_unramified_local_artin_units
    {U : Type uU} {G : Type uG} {k : Type uk} {k' : Type uk'}
    [CommGroup U] [CommGroup G] [Finite G] [Field k] [Field k'] [Algebra k k']
    [Fintype k] [Finite k'] [Algebra.IsAlgebraic k k'] [FiniteDimensional k k']
    (D : Chapter05UnramifiedPlaceProfile U G k k') {x : U}
    (hx : x ∈ D.units) : D.localArtin x = 1 := by
  rw [chapter05_unramified_local_artin_formula D x]
  rw [D.order.unit_iff_ord_zero x] at hx
  simp [hx]

/-- An unramified prime ideal has an ideal Frobenius only because its inertia
group is trivial. -/
def chapter05IdealFrobeniusCanonical
    {G : Type uG} [CommGroup G] (inertia : Subgroup G) : Prop :=
  inertia = ⊥

theorem chapter05_ideal_frobenius_not_canonical_when_ramified
    {G : Type uG} [CommGroup G] (inertia : Subgroup G)
    (h : inertia ≠ ⊥) : ¬ chapter05IdealFrobeniusCanonical inertia := by
  exact h

/-- A class-level formulation of complete splitting. -/
def chapter05SplitsCompletely
    {G : Type uG} [Group G] (frobenius : G) : Prop := frobenius = 1

theorem chapter05_unramified_split_iff_norm_class
    {C : Type uC} {G : Type uG} [CommGroup C] [Group G] [Finite G]
    (classOfUniformizer : C) (normSubgroup : Subgroup C)
    (globalArtin : C →* G) (frobenius : G)
    (hker : globalArtin.ker = normSubgroup)
    (huniformizer : globalArtin classOfUniformizer = frobenius) :
    chapter05SplitsCompletely frobenius ↔ classOfUniformizer ∈ normSubgroup := by
  sorry

/-- The residue degree of the displayed finite residue extension. -/
def chapter05ResidueDegree
    {U : Type uU} {G : Type uG} {k : Type uk} {k' : Type uk'}
    [CommGroup U] [CommGroup G] [Finite G] [Field k] [Field k'] [Algebra k k']
    [Fintype k] [Finite k'] [Algebra.IsAlgebraic k k'] [FiniteDimensional k k']
    (_D : Chapter05UnramifiedPlaceProfile U G k k') : ℕ :=
  Module.finrank k k'

theorem chapter05_residue_degree_eq_frobenius_order
    {U : Type uU} {G : Type uG} {k : Type uk} {k' : Type uk'}
    [CommGroup U] [CommGroup G] [Finite G] [Field k] [Field k'] [Algebra k k']
    [Fintype k] [Finite k'] [Algebra.IsAlgebraic k k'] [FiniteDimensional k k']
    (D : Chapter05UnramifiedPlaceProfile U G k k') :
    chapter05ResidueDegree D = orderOf D.frobenius := by
  sorry

/-- The group-theoretic count of primes above a place, as the decomposition
index.  Identifying this index with an actual place fibre is supplied by the
valuation/decomposition interface of the preceding chapters. -/
def chapter05NumberOfPrimesAbove
    {G : Type uG} [Group G] [Finite G] (D : Subgroup G) : ℕ :=
  D.index

theorem chapter05_number_of_primes_above_eq_index
    {G : Type uG} [Group G] [Finite G] (D : Subgroup G) :
    chapter05NumberOfPrimesAbove D = Nat.card G / Nat.card D := by
  sorry

/-- The positive component of the real local multiplicative group. -/
def chapter05PositiveRealUnits : Subgroup ℝˣ where
  carrier := {u | 0 < (u : ℝ)}
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry

/-- The two possible images at a real place. -/
structure Chapter05RealPlaceProfile (G : Type uG) [CommGroup G] [Finite G] where
  localArtin : ℝˣ →* G
  decomposition : Subgroup G
  image_eq_decomposition : Subgroup.map localArtin ⊤ = decomposition
  positive_killed : chapter05PositiveRealUnits ≤ localArtin.ker
  every_place_above_real : Prop
  place_becomes_complex : Prop
  real_or_complex : every_place_above_real ∨ place_becomes_complex
  not_both : ¬ (every_place_above_real ∧ place_becomes_complex)
  image_trivial_if_real :
    every_place_above_real → Subgroup.map localArtin ⊤ = ⊥
  image_order_two_if_complex :
    place_becomes_complex → Nat.card (Subgroup.map localArtin ⊤) = 2

theorem chapter05_real_positive_component_killed
    {G : Type uG} [CommGroup G] [Finite G] (D : Chapter05RealPlaceProfile G) :
    chapter05PositiveRealUnits ≤ D.localArtin.ker := by
  exact D.positive_killed

theorem chapter05_real_image_trivial_if_all_real
    {G : Type uG} [CommGroup G] [Finite G] (D : Chapter05RealPlaceProfile G)
    (h : D.every_place_above_real) :
    Subgroup.map D.localArtin ⊤ = ⊥ := by
  exact D.image_trivial_if_real h

theorem chapter05_real_image_order_two_if_complex
    {G : Type uG} [CommGroup G] [Finite G] (D : Chapter05RealPlaceProfile G)
    (h : D.place_becomes_complex) :
    Nat.card (Subgroup.map D.localArtin ⊤) = 2 := by
  exact D.image_order_two_if_complex h

end

end LastLib.Book06GlobalClassFieldTheory.Chapter05
