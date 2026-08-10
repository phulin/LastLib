import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section01TheLocalExtensionProblem

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01

noncomputable section

universe u

open scoped Polynomial TensorProduct WithZero

/-! # Book 2, Chapter 1, Section 1.2

This file records Theorem 1.1, the henselian-versus-complete distinction, and
the concrete Gaussian example at the prime `5`.
-/

/-! ### Existence, uniqueness, and branches -/

/-- The valuation-theoretic extension theorem, in valuation-subring form. -/
theorem chapter01_algebraic_extension_exists
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) :
    ∃ W : ValuationSubring L,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ContractsTo
        vK.valuationSubring.toSubring W.toSubring := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_algebraic_valuation_extension_exists vK

/-- Adic completeness of the valuation ring implies henselianity of the field. -/
theorem chapter01_complete_field_is_henselian
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    HenselianLocalRing vK.valuationSubring := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.complete_valued_field_is_henselian vK hcomplete

/-- Henselianity, rather than completeness, is enough for uniqueness of an algebraic extension. -/
theorem chapter01_henselian_discrete_field_unique_extension
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [Valuation.IsRankOneDiscrete vK]
    [HenselianLocalRing vK.valuationSubring] :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueValuationExtension vK L := by
  sorry

/-- Theorem 1.1, in the heterogeneous value-group interface. -/
theorem chapter01_theorem_1_1
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [Valuation.IsRankOneDiscrete vK]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueValuationExtension vK L := by
  sorry

/-- A heterogeneous extension is discrete when its own value group is discrete. -/
def chapter01DiscreteHeterogeneousExtension
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    (W : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.HeterogeneousValuationExtension vK L) : Prop :=
  letI : LinearOrderedCommGroupWithZero W.valueGroup := W.orderedValueGroup
  Valuation.IsRankOneDiscrete W.valuation

/-- Finite algebraic extensions of a discrete field have discrete extension values. -/
theorem chapter01_finite_extension_value_group_is_discrete
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [FiniteDimensional K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [Valuation.IsRankOneDiscrete vK]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    ∀ W : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.HeterogeneousValuationExtension vK L,
      chapter01DiscreteHeterogeneousExtension vK W := by
  sorry

/-- The value-group quotient in a finite extension is finite. -/
theorem chapter01_finite_value_group_quotient_is_finite
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    (hext : chapter01SamePlace vK vL)
    (hΓ : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK ≤
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL) :
    Finite
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL ⧸
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK).subgroupOf
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL)) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_value_group_quotient_finite
    vK vL hext hΓ

/-- A discrete value group has a canonical ordered integer model. -/
theorem chapter01_discrete_value_group_can_be_normalized
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Valuation.IsRankOneDiscrete v] :
    Nonempty
      (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v) ≃*o ℤᵐ⁰) := by
  exact ⟨Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v⟩

/-- The finite normalization is local over a henselian valuation ring. -/
theorem chapter01_henselian_integral_closure_is_local
    {A K L : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] [HenselianLocalRing A]
    (hfinite : Module.Finite A (integralClosure A L)) :
    IsLocalRing (integralClosure A L) := by
  sorry

/-- Maximal ideals above the base maximal ideal are the finite-extension branches. -/
theorem chapter01_henselian_branch_is_unique
    {A K L : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] [HenselianLocalRing A]
    (hfinite : Module.Finite A (integralClosure A L)) :
    ∃! P : Ideal (integralClosure A L),
      P.IsMaximal ∧ P.LiesOver (IsLocalRing.maximalIdeal A) := by
  sorry

/-! ### The nonhenselian `5`-adic Gaussian example -/

/-- Irreducibility supplies the field instance for Book 1's Gaussian presentation. -/
theorem chapter01_gaussian_polynomial_irreducible :
    Irreducible
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℚ) := by
  sorry

noncomputable instance chapter01GaussianPolynomialIrreducible :
    Fact (Irreducible
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℚ)) :=
  ⟨chapter01_gaussian_polynomial_irreducible⟩

/-- The normalized `5`-adic valuation on the rational field. -/
abbrev chapter01FiveAdicValuation [Fact (Nat.Prime 5)] : Valuation ℚ ℤᵐ⁰ :=
  Rat.padicValuation 5

/-- Two inequivalent extension places, retaining Book 1's heterogeneous groups. -/
def chapter01TwoInequivalentValuationExtensions
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] (vK : Valuation K ΓK) : Prop :=
  ∃ w₁ w₂ :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Chapter09ValuationExtension (L := L) vK,
    ¬ LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Chapter09ValuationExtensionEquivalent
      (L := L) vK w₁ w₂

/-- `X² + 1` has two distinct roots modulo `5`. -/
theorem chapter01_gaussian_mod_five_has_two_distinct_roots
    [Fact (Nat.Prime 5)] :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11SimpleResidueRoots (ZMod 5)
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial (ZMod 5)) := by
  simpa using
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_gaussian_odd_prime_one_mod_four_has_two_roots
      5 (by decide) (by decide))

/-- The two residue roots lift to two distinct linear factors over `ℚ₅`. -/
theorem chapter01_gaussian_polynomial_splits_over_five_adics
    [Fact (Nat.Prime 5)] :
    ∃ a b : ℚ_[5], a ≠ b ∧
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial (ℚ_[5]) =
        (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b) := by
  sorry

/-- The rational `5`-adic field is nonhenselian. -/
theorem chapter01_rationals_five_adic_are_not_henselian
    [Fact (Nat.Prime 5)] :
    ¬ HenselianLocalRing
      (chapter01FiveAdicValuation.valuationSubring) := by
  sorry

/-- `ℚ(i)` has two inequivalent extensions of the rational `5`-adic place. -/
theorem chapter01_gaussian_has_two_five_adic_extensions
    [Fact (Nat.Prime 5)] :
    chapter01TwoInequivalentValuationExtensions
      (L := LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField)
      (Rat.padicValuation 5) := by
  sorry

/-- Completion at `5` separates the Gaussian tensor product into two local factors. -/
theorem chapter01_gaussian_completed_tensor_product_at_five
    [Fact (Nat.Prime 5)] :
    Nonempty
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField ⊗[ℚ] ℚ_[5] ≃+*
        ℚ_[5] × ℚ_[5]) := by
  simpa [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11TensorSplit] using
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_gaussian_completed_tensor_at_five

/-- Each factor in the completed split tensor product is a local field. -/
theorem chapter01_gaussian_completed_factors_are_fields
    [Fact (Nat.Prime 5)] :
    Nonempty
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField ⊗[ℚ] ℚ_[5] ≃+*
        ℚ_[5] × ℚ_[5]) ∧
      IsField ℚ_[5] := by
  exact ⟨chapter01_gaussian_completed_tensor_product_at_five, Field.toIsField _⟩

/-- The split completed tensor product is not itself a field. -/
theorem chapter01_gaussian_completed_tensor_product_not_field
    [Fact (Nat.Prime 5)] :
    ¬ IsField
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField ⊗[ℚ] ℚ_[5]) := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01
