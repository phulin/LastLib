import LastLib.Book01ValuationsDVRsAndCompletions.Chapter13.Section03PBasesAndDerivations
import Mathlib.RingTheory.PowerSeries.Inverse

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter13

open Filter Ideal IsLocalRing
open scoped PowerSeries Topology

noncomputable section

/-! # Book 1, Chapter 13, Section 13.4: Coefficient fields in equal characteristic `p` -/

universe u v

/-- A family of lifts of a `p`-basis in the residue ring. -/
def Chapter13AdmissiblePBaseLiftFamily
    {A : Type u} [CommRing A] [IsLocalRing A]
    (B : Set (Chapter13ResidueRing A)) (a : B → A) : Prop :=
  ∀ b : B, Chapter13ResidueMap A (a b) = (b : Chapter13ResidueRing A)

/-- The type of coefficient fields of a fixed local ring. -/
def Chapter13CoefficientFields
    (A : Type u) [CommRing A] [IsLocalRing A] : Type u :=
  {K : Chapter13Subfield A // Chapter13IsCoefficientField K}

/-- A power-series presentation of a complete equicharacteristic DVR. -/
structure Chapter13PowerSeriesDVRModel
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] (π : A) (u : K →+* A) where
  equiv : PowerSeries K ≃+* A
  maps_constants : equiv.toRingHom.comp (PowerSeries.C : K →+* PowerSeries K) = u
  maps_uniformizer : equiv PowerSeries.X = π
  maps_maximal_ideal :
    (Ideal.span ({PowerSeries.X} : Set (PowerSeries K))).map equiv.toRingHom =
      IsLocalRing.maximalIdeal A

/-- Chosen lifts of a `p`-basis determine a unique coefficient-field splitting. -/
theorem chapter13_equal_characteristic_p_coefficient_field_splitting
    {A : Type u} [CommRing A] [IsLocalRing A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP A p]
    (B : Set (Chapter13ResidueRing A))
    (hB : Chapter13PBasis (Chapter13PthPowerSubfield (Chapter13ResidueRing A) p) B p)
    (a : B → A) (ha : Chapter13AdmissiblePBaseLiftFamily B a)
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A) :
    ∃! φ : Chapter13ResidueRing A →+* A,
      (Chapter13ResidueMap A).comp φ = RingHom.id _ ∧
        ∀ b : B, φ (b : Chapter13ResidueRing A) = a b := by
  sorry

/-- Coefficient fields are parametrized by admissible lifts of a residue `p`-basis. -/
theorem chapter13_equal_characteristic_p_coefficient_fields_bijection
    {A : Type u} [CommRing A] [IsLocalRing A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP A p]
    (B : Set (Chapter13ResidueRing A))
    (hB : Chapter13PBasis (Chapter13PthPowerSubfield (Chapter13ResidueRing A) p) B p)
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A) :
    Nonempty
      (Chapter13CoefficientFields A ≃
        {a : B → A // Chapter13AdmissiblePBaseLiftFamily B a}) := by
  sorry

/-- A complete separated local ring containing a field has a coefficient field. -/
theorem chapter13_coefficient_field_exists_when_contains_field
    {A : Type u} [CommRing A] [IsLocalRing A]
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hfield : Chapter13ContainsField A) :
    ∃ K : Chapter13Subfield A,
      Chapter13IsCoefficientField K ∧
        Chapter13CoefficientDecomposition K ∧
        (∀ a : A, ∃! z : K.carrier × A,
          z.2 ∈ IsLocalRing.maximalIdeal A ∧ a = z.1.1 + z.2) := by
  sorry

/-- The coefficient decomposition is unique. -/
theorem chapter13_coefficient_decomposition_unique
    {A : Type u} [CommRing A] [IsLocalRing A]
    (K : Chapter13Subfield A) (hK : Chapter13IsCoefficientField K) :
    ∀ a : A, ∃! z : K.carrier × A,
      z.2 ∈ IsLocalRing.maximalIdeal A ∧ a = z.1.1 + z.2 := by
  sorry

/-- Powers of a perfect residue field give the canonical coefficient field. -/
theorem chapter13_perfect_residue_unique_coefficient_field
    {A : Type u} [CommRing A] [IsLocalRing A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP A p]
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hperfect : Chapter13PerfectAtPrime (Chapter13ResidueRing A) p) :
    ∃! K : Chapter13Subfield A,
      Chapter13IsCoefficientField K ∧
        (K.carrier : Set A) =
          ⋂ n : ℕ, Set.range (fun x : A => x ^ (p ^ n)) := by
  sorry

/-- An equicharacteristic complete DVR is a one-variable power-series ring. -/
theorem chapter13_equicharacteristic_complete_dvr_power_series
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type v} [Field K]
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π})
    (u : K →+* A)
    (hu : IsLocalHom u ∧
      Function.Bijective ((Chapter13ResidueMap A).comp u)) :
    Nonempty (Chapter13PowerSeriesDVRModel A K π u) := by
  sorry

/-- The coefficient expansion of a complete equicharacteristic DVR is the Cauchy expansion. -/
theorem chapter13_equicharacteristic_dvr_cauchy_expansion
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type v} [Field K]
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π})
    (u : K →+* A) (hu : IsLocalHom u ∧
      Function.Bijective ((Chapter13ResidueMap A).comp u)) :
    ∃ e : PowerSeries K ≃+* A,
      e.toRingHom.comp (PowerSeries.C : K →+* PowerSeries K) = u ∧
        e PowerSeries.X = π := by
  sorry

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter13
