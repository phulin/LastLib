import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section01WhyTheValuationRingMustBeTheIntegralClosure

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02

noncomputable section

open Set
open Ideal IsLocalRing Polynomial
open scoped BigOperators WithZero

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-! ## Book 2, Chapter 2, §2.2

The source's `B` is represented by `vL.valuationSubring`; the fraction-field
claim is exposed as `IsFractionRing B L`, and the rank claim is stated with
`Module.rank` so that the field degree is `Module.finrank K L`.
-/

/-- The finite-lattice theorem for the integral closure in a complete discrete extension. -/
theorem finite_integral_closure_is_free
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Module.Finite vK.valuationSubring vL.valuationSubring ∧
      Module.Free vK.valuationSubring vL.valuationSubring ∧
      Cardinal.toNat (Module.rank vK.valuationSubring vL.valuationSubring) =
        Module.finrank K L ∧
      IsAdicComplete (IsLocalRing.maximalIdeal vL.valuationSubring)
        vL.valuationSubring ∧
      IsDiscreteValuationRing vL.valuationSubring ∧
      IsFractionRing vL.valuationSubring L := by
  sorry

/-- The integral closure is finite over the base valuation ring. -/
theorem integral_closure_is_module_finite
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Module.Finite vK.valuationSubring (integralClosure vK.valuationSubring L) := by
  sorry

/-- An integral basis is a basis of `B` over `A` indexed by the field degree. -/
theorem exists_integral_basis
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [Module.Free vK.valuationSubring vL.valuationSubring]
    (hrank : Cardinal.toNat
      (Module.rank vK.valuationSubring vL.valuationSubring) = Module.finrank K L) :
    ∃ b : Module.Basis (Fin (Module.finrank K L)) vK.valuationSubring
        vL.valuationSubring,
      ∀ x : vL.valuationSubring, ∃! c : Fin (Module.finrank K L) →
        vK.valuationSubring,
        x = ∑ i, c i • b i := by
  sorry

/-- Every element of a finite algebra satisfies a monic integral equation. -/
theorem finite_extension_multiplication_is_integral
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (x : B) : IsIntegral A x := by
  exact IsIntegral.of_finite A x

/-- The characteristic polynomial of multiplication by an element of a finite module. -/
def chapter2CharacteristicPolynomial
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (x : B) : A[X] :=
  LinearMap.charpoly (Algebra.lmul A B x)

/-- Cayley--Hamilton's root assertion, stated directly over Mathlib's polynomial API. -/
def chapter2RootOfCharacteristicPolynomial
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (f : A[X]) (x : B) : Prop :=
  Polynomial.eval x (Polynomial.map (algebraMap A B) f) = 0

/-- Cayley--Hamilton gives the characteristic-polynomial equation used in §2.2. -/
theorem multiplication_characteristic_polynomial_annihilates
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (x : B) :
    chapter2RootOfCharacteristicPolynomial A B
      (chapter2CharacteristicPolynomial A B x) x := by
  sorry

/-- The integral basis elements are integral over the base valuation ring. -/
theorem integral_basis_elements_are_integral
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [Module.Free vK.valuationSubring vL.valuationSubring]
    (b : Module.Basis (Fin (Module.finrank K L)) vK.valuationSubring
      vL.valuationSubring) :
    ∀ i, IsIntegral vK.valuationSubring
      (algebraMap vL.valuationSubring L (b i)) := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02
