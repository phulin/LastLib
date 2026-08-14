import LastLib.Book06GlobalClassFieldTheory.Chapter05.Dependencies
import LastLib.Book06GlobalClassFieldTheory.Chapter02.Dependencies
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.Finite.Basic
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
  q : ℕ
  q_eq_card : q = Fintype.card k
  frobenius : G
  /-- The residue action is defined on the decomposition group, not on the
  ambient global Galois group. -/
  residueAction : decomposition →* Gal(k' / k)
  inertia_trivial : inertia = ⊥
  range_decomposition : Subgroup.map localArtin ⊤ = decomposition
  range_units : Subgroup.map localArtin units = inertia
  /-- The residue action is faithful on the decomposition group.  This is the
  local exactness needed to transport the order of residue Frobenius to the
  ambient Galois group. -/
  frobenius_mem_decomposition : frobenius ∈ decomposition
  residueAction_injective_on_decomposition :
    ∀ {g : decomposition}, residueAction g = 1 → g = 1
  localArtin_uniformizer : localArtin order.uniformizer = frobenius
  arithmetic_frobenius :
    chapter05ArithmeticFrobenius q
      (residueAction ⟨frobenius, frobenius_mem_decomposition⟩)

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
    chapter05ArithmeticFrobenius D.q
      (D.residueAction ⟨D.frobenius, D.frobenius_mem_decomposition⟩) := by
  exact D.arithmetic_frobenius

/-- At an unramified place the local symbol depends only on the valuation. -/
theorem chapter05_unramified_local_artin_formula
    {U : Type uU} {G : Type uG} {k : Type uk} {k' : Type uk'}
    [CommGroup U] [CommGroup G] [Finite G] [Field k] [Field k'] [Algebra k k']
    [Fintype k] [Finite k'] [Algebra.IsAlgebraic k k'] [FiniteDimensional k k']
    (D : Chapter05UnramifiedPlaceProfile U G k k') (x : U) :
    D.localArtin x = D.frobenius ^ D.order.ord x := by
  obtain ⟨u, hu⟩ := D.order.decomposition x
  have hu_artin : D.localArtin (u : U) = 1 := by
    have hu_mem : D.localArtin (u : U) ∈ D.inertia := by
      rw [← D.range_units]
      exact Subgroup.mem_map_of_mem D.localArtin u.property
    rw [D.inertia_trivial] at hu_mem
    exact Subgroup.mem_bot.mp hu_mem
  calc
    D.localArtin x =
        D.localArtin ((u : U) * D.order.uniformizer ^ D.order.ord x) :=
      congrArg D.localArtin hu
    _ = D.localArtin (u : U) * D.localArtin D.order.uniformizer ^ D.order.ord x := by
      rw [map_mul, map_zpow]
    _ = D.frobenius ^ D.order.ord x := by
      rw [hu_artin, D.localArtin_uniformizer, one_mul]

theorem chapter05_unramified_local_artin_units
    {U : Type uU} {G : Type uG} {k : Type uk} {k' : Type uk'}
    [CommGroup U] [CommGroup G] [Finite G] [Field k] [Field k'] [Algebra k k']
    [Fintype k] [Finite k'] [Algebra.IsAlgebraic k k'] [FiniteDimensional k k']
    (D : Chapter05UnramifiedPlaceProfile U G k k') {x : U}
    (hx : x ∈ D.units) : D.localArtin x = 1 := by
  rw [chapter05_unramified_local_artin_formula D x]
  rw [D.order.unit_iff_ord_zero x] at hx
  simp [hx]

/-- The ideal Frobenius datum is a residue-Frobenius class modulo inertia.  It
has a unique representative exactly when the quotient map is injective. -/
def chapter05IdealFrobeniusClass
    {G : Type uG} [CommGroup G] (inertia : Subgroup G) (g : G) : G ⧸ inertia :=
  QuotientGroup.mk' inertia g

def chapter05IdealFrobeniusCanonical
    {G : Type uG} [CommGroup G] (inertia : Subgroup G) : Prop :=
  Function.Injective (QuotientGroup.mk' inertia)

theorem chapter05_ideal_frobenius_canonical_iff_inertia_trivial
    {G : Type uG} [CommGroup G] (inertia : Subgroup G) :
    chapter05IdealFrobeniusCanonical inertia ↔ inertia = ⊥ := by
  change Function.Injective (QuotientGroup.mk' inertia) ↔ inertia = ⊥
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']

theorem chapter05_ideal_frobenius_not_canonical_when_ramified
    {G : Type uG} [CommGroup G] (inertia : Subgroup G)
    (h : inertia ≠ ⊥) : ¬ chapter05IdealFrobeniusCanonical inertia := by
  intro hcanonical
  exact h ((chapter05_ideal_frobenius_canonical_iff_inertia_trivial inertia).mp hcanonical)

theorem chapter05_ideal_frobenius_lift_ambiguous_when_ramified
    {G : Type uG} [CommGroup G] (inertia : Subgroup G)
    (h : inertia ≠ ⊥) :
    ∃ g₁ g₂ : G, g₁ ≠ g₂ ∧
      chapter05IdealFrobeniusClass inertia g₁ =
        chapter05IdealFrobeniusClass inertia g₂ := by
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp h)
  refine ⟨1, (a : G), ?_, ?_⟩
  · intro h_one
    apply ha
    exact Subtype.ext h_one.symm
  · calc
      chapter05IdealFrobeniusClass inertia (1 : G) = 1 := by rfl
      _ = chapter05IdealFrobeniusClass inertia (a : G) := by
        symm
        exact (QuotientGroup.eq_one_iff (N := inertia) (a : G)).2 a.property

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
  change frobenius = 1 ↔ classOfUniformizer ∈ normSubgroup
  rw [← huniformizer, ← MonoidHom.mem_ker, hker]

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
  let σ : Gal(k' / k) :=
    D.residueAction ⟨D.frobenius, D.frobenius_mem_decomposition⟩
  have hσ : σ = FiniteField.frobeniusAlgEquivOfAlgebraic k k' := by
    ext x
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ← D.q_eq_card]
    exact D.arithmetic_frobenius x
  have hinj : Function.Injective D.residueAction := by
    intro a b hab
    apply (mul_inv_eq_one).mp
    apply D.residueAction_injective_on_decomposition
    simp only [map_mul, map_inv, hab, mul_inv_cancel]
  calc
    chapter05ResidueDegree D = Module.finrank k k' := rfl
    _ = orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic k k') :=
      (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic k k').symm
    _ = orderOf σ := by rw [hσ]
    _ = orderOf (⟨D.frobenius, D.frobenius_mem_decomposition⟩ : D.decomposition) :=
      orderOf_injective D.residueAction hinj _
    _ = orderOf D.frobenius :=
      Subgroup.orderOf_mk D.frobenius D.frobenius_mem_decomposition

/-- The group-theoretic count of primes above a place, as the decomposition
index.  Identifying this index with an actual place fibre is supplied by the
valuation/decomposition interface of the preceding chapters. -/
def chapter05NumberOfPrimesAbove
    {G : Type uG} [Group G] [Finite G] (D : Subgroup G) : ℕ :=
  D.index

theorem chapter05_number_of_primes_above_eq_index
    {G : Type uG} [Group G] [Finite G] (D : Subgroup G) :
    chapter05NumberOfPrimesAbove D = Nat.card G / Nat.card D := by
  change D.index = Nat.card G / Nat.card D
  symm
  have hcard := D.card_mul_index.symm
  rw [Nat.mul_comm] at hcard
  exact Nat.div_eq_of_eq_mul_left (Nat.card_pos (α := D))
    hcard

/-- The positive component of the real local multiplicative group. -/
def chapter05PositiveRealUnits : Subgroup ℝˣ where
  carrier := {u | 0 < (u : ℝ)}
  one_mem' := by
    change (0 : ℝ) < 1
    exact zero_lt_one
  mul_mem' := by
    intro a b ha hb
    change (0 : ℝ) < (a : ℝ) at ha
    change (0 : ℝ) < (b : ℝ) at hb
    change (0 : ℝ) < ((a * b : ℝˣ) : ℝ)
    simpa using mul_pos ha hb
  inv_mem' := by
    intro a ha
    change (0 : ℝ) < (a : ℝ) at ha
    change (0 : ℝ) < ((a⁻¹ : ℝˣ) : ℝ)
    simpa using (inv_pos.mpr ha)

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
