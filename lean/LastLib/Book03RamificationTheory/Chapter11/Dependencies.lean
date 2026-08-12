import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Rep.Res

namespace LastLib.Book03RamificationTheory.Chapter11

noncomputable section

open CategoryTheory
open scoped BigOperators

/-!
Shared interfaces for Book 3, Chapter 11.

The preceding Book 3 chapters are not present in this checkout.  The finite
ramification-data structure below is the smallest book-facing interface needed
by the Artin-character statements: it records the lower filtration, its finite
support, the inertia and residue-degree factors, and the conjugation and
separable-residue hypotheses used in this chapter.  It is deliberately
independent of a particular valuation implementation, so it can later be
identified with the canonical local-field data from the preceding chapters.
-/

/- LOCAL_DEPENDENCY_GUESS: replace this interface by the canonical Book 3
  finite-Galois/local-ramification structure when Chapters 1--10 are merged. -/
structure Chapter11RamificationData (G : Type*) [Fintype G] [Group G] where
  /-- The lower-numbered ramification subgroups. -/
  lower : ℕ → Subgroup G
  /-- The inertia subgroup, exposed as the zeroth lower group. -/
  inertia : Subgroup G
  /-- Ramification index, residue degree, and a finite-support bound. -/
  e : ℕ
  f : ℕ
  bound : ℕ
  lower_zero : lower 0 = inertia
  lower_succ_le : ∀ i, lower (i + 1) ≤ lower i
  lower_eq_bot_of_bound_le : ∀ i, bound ≤ i → lower i = ⊥
  inertia_normal : inertia.Normal
  inertia_card : Nat.card inertia = e
  group_card : Fintype.card G = e * f
  e_pos : 0 < e
  f_pos : 0 < f
  /-- Non-inertia elements have zero displacement. -/
  support_outside_inertia :
    ∀ {σ : G}, σ ∉ inertia → ∀ i, σ ∉ lower i
  /-- Every lower level is stable under conjugation. -/
  lower_conj_invariant :
    ∀ i (g σ : G), σ ∈ lower i ↔ g * σ * g⁻¹ ∈ lower i
  /-- The residue extension hypothesis used by the classical `i_G` theory. -/
  residue_separable : Prop

noncomputable instance chapter11SubgroupFintype
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/- A concrete realization of the preceding abstract interface.  The residue
  fields and valuation identifications belong to the missing Book 3 chapters;
  this wrapper keeps the finite-Galois and characteristic hypotheses visible
  without choosing a duplicate valuation implementation here. -/
structure Chapter11FiniteGaloisRamificationContext
    {K L G : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype G] [Group G]
    (D : Chapter11RamificationData G) where
  group_identification : G ≃* Gal(L / K)
  residue_separable : D.residue_separable

abbrev Chapter11Inertia
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) : Subgroup G := D.inertia

abbrev Chapter11LowerGroup
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (i : ℕ) : Subgroup G := D.lower i

/-- The finite set of lower levels at which a group element occurs. -/
def chapter11LowerSupport
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (σ : G) : Finset ℕ := by
  classical
  exact (Finset.range D.bound).filter (fun i => σ ∈ D.lower i)

/-- The lower displacement `i_G(σ)`, counted from the finite lower filtration. -/
def chapter11Displacement
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (σ : G) : ℕ :=
  (chapter11LowerSupport D σ).card

theorem chapter11_displacement_eq_zero_of_not_mem_inertia
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) {σ : G} (hσ : σ ∉ D.inertia) :
    chapter11Displacement D σ = 0 := by
  sorry

/-!
The conductor is recorded as a rational number.  This keeps the weighted
formula honest before Artin integrality is applied; integrality statements
below identify these rationals with nonnegative integers.
-/

/-- The codimension of the fixed space at a subgroup. -/
def chapter11FixedSpaceCodimension
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (_D : Chapter11RamificationData G)
    (ρ : Representation k G V) (H : Subgroup G) : ℕ :=
  Module.finrank k V - Module.finrank k (Representation.invariants (ρ.comp H.subtype))

/-- The rational weight attached to a lower level. -/
def chapter11LowerWeight
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (i : ℕ) : ℚ :=
  (Nat.card (D.lower i) : ℚ) / (Nat.card D.inertia : ℚ)

/-- The Artin conductor in its fixed-space, lower-numbered form. -/
def chapter11ArtinConductor
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) : ℚ :=
  ∑ i ∈ Finset.range D.bound,
    chapter11LowerWeight D i *
      (chapter11FixedSpaceCodimension D ρ (D.lower i) : ℚ)

/-- The tame contribution, namely the codimension of inertia-fixed vectors. -/
def chapter11TameConductor
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) : ℚ :=
  (chapter11FixedSpaceCodimension D ρ D.inertia : ℚ)

/-- The Swan conductor, defined as the wild remainder of the Artin conductor. -/
def chapter11SwanConductor
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) : ℚ :=
  chapter11ArtinConductor D ρ - chapter11TameConductor D ρ

end
end LastLib.Book03RamificationTheory.Chapter11
