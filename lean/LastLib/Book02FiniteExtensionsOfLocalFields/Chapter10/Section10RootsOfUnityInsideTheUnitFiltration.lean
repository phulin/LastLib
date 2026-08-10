import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section09UnitCoordinatesAndTheirLimitations

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing

/-! ## 10.10. Roots of unity inside the unit filtration -/

/-- Torsion whose order is a power of the residue characteristic. -/
def Chapter10PowerTorsion
    {G : Type*} [Group G] (p : ℕ) (u : G) : Prop :=
  ∃ r : ℕ, u ^ (p ^ r) = 1

/-- Finite-order torsion in a unit group. -/
def Chapter10FiniteOrderTorsion
    {G : Type*} [Group G] (u : G) : Prop :=
  ∃ m : ℕ, 0 < m ∧ u ^ m = 1

/-- Prime-to-residue-characteristic roots inject under reduction. -/
theorem chapter10_prime_to_residue_characteristic_roots_reduce_injectively
    {L : Type*} [Field L] (A : ValuationSubring L)
    (m p : ℕ) [Fact p.Prime] [CharP (Chapter10ResidueField A) p]
    (hcoprime : Nat.Coprime m p) :
    Function.Injective (fun u : chapter10RootOfUnitySubgroup A m =>
      chapter10UnitReduction A (u : Aˣ)) := by
  sorry

/-- Roots of residue-characteristic-power order reduce to `1`, hence are principal units. -/
theorem chapter10_residue_characteristic_power_roots_are_principal
    {L : Type*} [Field L] (A : ValuationSubring L)
    (p r : ℕ) [Fact p.Prime] [CharP (Chapter10ResidueField A) p]
    (u : Aˣ) (hu : u ^ (p ^ r) = 1) :
    u ∈ chapter10UnitFiltration A 1 := by
  sorry

/-- In the finite-residue mixed-characteristic case, the visible roots are cyclic. -/
theorem chapter10_padic_prime_to_p_roots_are_cyclic
    {L : Type*} [Field L] (A : ValuationSubring L) (p : ℕ)
    [Fact p.Prime] [Fintype (Chapter10ResidueField A)]
    [CharP (Chapter10ResidueField A) p] [CharZero A]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    IsCyclic
      (chapter10RootOfUnitySubgroup A
        (Fintype.card (Chapter10ResidueField A) - 1)) := by
  sorry

/-- Finite-order unit torsion separates into Teichmüller and principal parts. -/
theorem chapter10_finite_order_unit_torsion_decomposes
    {L : Type*} [Field L] (A : ValuationSubring L) (p : ℕ)
    [Fact p.Prime] [Fintype (Chapter10ResidueField A)]
    [CharP (Chapter10ResidueField A) p] [CharZero A]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A)
    (u : Aˣ) (hu : Chapter10FiniteOrderTorsion u) :
    ∃ t : chapter10RootOfUnitySubgroup A
        (Fintype.card (Chapter10ResidueField A) - 1),
      ∃ w : chapter10UnitFiltration A 1,
        u = (t : Aˣ) * (w : Aˣ) ∧
          Chapter10PowerTorsion p (w : Aˣ) := by
  sorry

/-- In a field of characteristic `p`, a `p`-power root of unity is `1`. -/
theorem chapter10_equal_characteristic_p_power_root_is_one
    {K : Type*} [Field K] (p r : ℕ) [Fact p.Prime] [CharP K p]
    (x : K) (hx : x ^ (p ^ r) = 1) : x = 1 := by
  sorry

/-- Equal-characteristic power-series units have no nontrivial principal `p`-power torsion. -/
theorem chapter10_equal_characteristic_principal_units_have_no_p_power_torsion
    {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (u : (PowerSeries k)ˣ)
    (hu : Chapter10PowerTorsion p u) : u = 1 := by
  sorry

/-- A primitive residue-characteristic-power root in mixed characteristic is principal. -/
theorem chapter10_mixed_characteristic_cyclotomic_roots_are_principal
    {L : Type*} [Field L] (A : ValuationSubring L) (p r : ℕ)
    [Fact p.Prime] [CharP (Chapter10ResidueField A) p]
    (ζ : Aˣ) (hζ : IsPrimitiveRoot (ζ : A) (p ^ r)) :
    ζ ∈ chapter10UnitFiltration A 1 := by
  sorry

/-- The filtration records torsion information not determined by the pair `(e,f)`. -/
def Chapter10UnitTorsionProfile
    {L : Type*} [Field L] (A : ValuationSubring L) (p : ℕ) : Prop :=
  ∃ u : chapter10UnitFiltration A 1, Chapter10PowerTorsion p (u : Aˣ)

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
