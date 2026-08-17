import LastLib.Book01ValuationsDVRsAndCompletions.Chapter13.Section07TheStructureTheorem
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.Section03ArithmeticAndExamples
import Mathlib.Algebra.Polynomial.Div
import Mathlib.NumberTheory.Padics.RingHoms

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter13

open Ideal IsLocalRing

noncomputable section

/-! # Book 1, Chapter 13, Section 13.8: Worked examples and counterexamples -/

universe u

/-- Two distinct coefficient fields in one complete power-series ring. -/
structure Chapter13TwoCoefficientFieldExample
    (k : Type u) [Field k] (u₀ : k) where
  first : Chapter13Subfield (PowerSeries k)
  second : Chapter13Subfield (PowerSeries k)
  first_is_coefficient : Chapter13IsCoefficientField first
  second_is_coefficient : Chapter13IsCoefficientField second
  constants_mem_first : ∀ a : k, PowerSeries.C a ∈ first.carrier
  translated_generator : PowerSeries.C u₀ + PowerSeries.X ∈ second.carrier
  distinct : first.carrier ≠ second.carrier

/-- A power-series lift of a chosen `p`-basis family by elements of the maximal ideal. -/
def Chapter13PowerSeriesPBasisLift
    {k : Type u} [Field k] {B : Set k}
    (g : B → PowerSeries k) : B → PowerSeries k :=
  fun b => PowerSeries.C b.1 + g b

theorem chapter13_nonunique_coefficient_fields
    (k : Type u) [Field k] [Algebra ℚ k] (u₀ : k)
    (hu₀ : Transcendental ℚ u₀) :
    Nonempty (Chapter13TwoCoefficientFieldExample k u₀) := by
  sorry

theorem chapter13_p_basis_lift_family_power_series
    (k : Type u) [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (B : Set k)
    (hB : Chapter13PBasis (Chapter13PthPowerSubfield k p) B p)
    (g : B → PowerSeries k)
    (hg : ∀ b : B, g b ∈ Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) :
    ∃ K : Chapter13Subfield (PowerSeries k),
      Chapter13IsCoefficientField K := by
  sorry

/-! ### A maximal subfield can miss part of the residue field -/

theorem chapter13_maximal_subfield_not_coefficient
    (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ K : Chapter13Subfield
        (PowerSeries (FractionRing (Polynomial (ZMod p)))),
      Chapter13IsMaximalSubfield K ∧ ¬Chapter13IsCoefficientField K := by
  sorry

/-! ### The cusp -/

abbrev Chapter13CuspPowerSeriesSubring (k : Type u) [CommRing k] :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.chapter04CuspPowerSeriesSubring k

abbrev Chapter13CuspPowerSeriesMaximalIdeal (k : Type u) [Field k] :
    Ideal (Chapter13CuspPowerSeriesSubring k) :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.chapter04CuspPowerSeriesMaximalIdeal k

def Chapter13CuspRelation (k : Type u) [CommRing k] :
    MvPowerSeries (Fin 2) k :=
  (MvPowerSeries.X (1 : Fin 2)) ^ 2 - (MvPowerSeries.X (0 : Fin 2)) ^ 3

theorem chapter13_cusp_presentation
    (k : Type u) [Field k] :
    Nonempty
        ((MvPowerSeries (Fin 2) k ⧸
            Ideal.span {Chapter13CuspRelation k}) ≃+*
          Chapter13CuspPowerSeriesSubring k) ∧
      ¬IsRegularLocalRing (Chapter13CuspPowerSeriesSubring k) := by
  sorry

/-! ### Mixed-characteristic examples -/

abbrev Chapter13PrimeSquareRing (p : ℕ) := ZMod (p ^ 2)

instance chapter13PrimeSquareLocalRing
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocalRing (Chapter13PrimeSquareRing p) := by
  sorry

theorem chapter13_prime_square_has_no_coefficient_field
    (p : ℕ) [Fact (Nat.Prime p)] :
    Chapter13CompleteNoetherianLocalRing (Chapter13PrimeSquareRing p) ∧
      Chapter13MixedCharacteristic (Chapter13PrimeSquareRing p) p ∧
      ¬Chapter13ContainsField (Chapter13PrimeSquareRing p) ∧
      Chapter13IsCohenRing (PadicInt p) (ZMod p) p ∧
      Function.Surjective (@PadicInt.toZModPow p _ 2) := by
  sorry

theorem chapter13_padic_integers_have_no_subfield
    (p : ℕ) [Fact (Nat.Prime p)] :
    ¬Chapter13ContainsField (PadicInt p) := by
  sorry

abbrev Chapter13PadicPowerSeries (p : ℕ) [Fact (Nat.Prime p)] :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.chapter04PadicPowerSeries p

abbrev Chapter13PadicPowerSeriesMaximalIdeal
    (p : ℕ) [Fact (Nat.Prime p)] : Ideal (Chapter13PadicPowerSeries p) :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.chapter04PadicPowerSeriesMaximalIdeal p

theorem chapter13_padic_power_series_is_unramified_regular
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsAdicComplete (Chapter13PadicPowerSeriesMaximalIdeal p)
        (Chapter13PadicPowerSeries p) ∧
      IsRegularLocalRing (Chapter13PadicPowerSeries p) ∧
      ringKrullDim (Chapter13PadicPowerSeries p) = 2 ∧
      (p : Chapter13PadicPowerSeries p) ∉
        (IsLocalRing.maximalIdeal (Chapter13PadicPowerSeries p)) ^ 2 ∧
      Chapter13MixedCharacteristic (Chapter13PadicPowerSeries p) p ∧
      ¬Chapter13ContainsField (Chapter13PadicPowerSeries p) := by
  sorry

/-- The Eisenstein polynomial obtained from `((1 + X)^p - 1) / X`. -/
def Chapter13CyclotomicEisensteinPolynomial
    (p : ℕ) [Fact (Nat.Prime p)] : Polynomial (PadicInt p) :=
  ((Polynomial.X + 1) ^ p - 1) /ₘ Polynomial.X

abbrev Chapter13CyclotomicOrder
    (p : ℕ) [Fact (Nat.Prime p)] :=
  Polynomial (PadicInt p) ⧸
    Ideal.span {Chapter13CyclotomicEisensteinPolynomial p}

instance chapter13CyclotomicOrderLocalRing
    (p : ℕ) [Fact (Nat.Prime p)] : IsLocalRing (Chapter13CyclotomicOrder p) := by
  sorry

instance chapter13CyclotomicOrderDomain
    (p : ℕ) [Fact (Nat.Prime p)] : IsDomain (Chapter13CyclotomicOrder p) := by
  sorry

theorem chapter13_cyclotomic_order_is_ramified
    (p : ℕ) [Fact (Nat.Prime p)] (hp : 2 < p) :
    IsAdicComplete (IsLocalRing.maximalIdeal (Chapter13CyclotomicOrder p))
        (Chapter13CyclotomicOrder p) ∧
      IsRegularLocalRing (Chapter13CyclotomicOrder p) ∧
      IsDiscreteValuationRing (Chapter13CyclotomicOrder p) ∧
      ringKrullDim (Chapter13CyclotomicOrder p) = 1 ∧
      (p : Chapter13CyclotomicOrder p) ∈
        (IsLocalRing.maximalIdeal (Chapter13CyclotomicOrder p)) ^ 2 ∧
      ¬Chapter13IsCohenRing (Chapter13CyclotomicOrder p) (ZMod p) p := by
  sorry

/-! ### Formal local coordinates -/

theorem chapter13_formal_local_coordinates
    {R k : Type u} [CommRing R] [IsLocalRing R] [Field k] (d : ℕ)
    (hR : IsNoetherianRing R)
    (hregular : IsRegularLocalRing R)
    (hdim : ringKrullDim R = d)
    (hcontains : Chapter13ContainsField R)
    (e : Chapter13ResidueRing R ≃+* k) :
    Nonempty
      (MvPowerSeries (Fin d) k ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  sorry

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter13
