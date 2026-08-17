import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section05Conclusion
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section05MixedAndEqualCharacteristic

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12

noncomputable section

open Polynomial

/-! ## 12.6. What separability is doing -/

/-- In positive characteristic the derivative of `T^p-a` vanishes. -/
theorem chapter12_pth_power_derivative_zero
    {K : Type*} [Field K] (p : ℕ) (hp : Nat.Prime p) [CharP K p]
    (a : K) :
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03PurelyInseparableResiduePolynomial
      K p a).derivative = 0 := by
  sorry

/-- Over a field of characteristic `p`, a chosen root of `T^p-a` is its only
geometric root and the polynomial has multiplicity `p` there. -/
theorem chapter12_pth_power_has_one_geometric_root
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : ℕ) (hp : Nat.Prime p) [CharP K p] [CharP L p]
    (a : K) (α : L)
    (hroot : aeval α
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03PurelyInseparableResiduePolynomial
        K p a) = 0) :
    Polynomial.map (algebraMap K L)
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03PurelyInseparableResiduePolynomial
          K p a) =
        ((X : L[X]) - C α) ^ p ∧
      ∀ β : L,
        aeval β
          (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03PurelyInseparableResiduePolynomial
            K p a) = 0 → β = α := by
  sorry

/- A nonzero linear coefficient can be made arbitrarily small.  Adding it to
the inseparable equation gives a separable nearby polynomial. -/
theorem chapter12_pth_power_coefficients_can_be_perturbed
    {K : Type*} [NontriviallyNormedField K] (p : ℕ) (hp : Nat.Prime p)
    [CharP K p] (a : K) :
    ∀ ε : ℝ, 0 < ε →
      ∃ c : K, c ≠ 0 ∧ ‖c‖ < ε ∧
        (X : K[X]) ^ p + C c * X - C a ≠
          LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03PurelyInseparableResiduePolynomial
            K p a ∧
        ((X : K[X]) ^ p + C c * X - C a).Separable := by
  sorry

/-- Every finite extension of a characteristic-zero field is separable. -/
theorem chapter12_characteristic_zero_finite_extensions_are_separable
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [CharZero K] :
    Algebra.IsSeparable K L := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12
