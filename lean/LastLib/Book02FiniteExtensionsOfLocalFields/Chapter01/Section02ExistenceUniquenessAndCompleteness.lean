import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section01TheLocalExtensionProblem
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section01TheExtensionProblem
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section02ExistenceByMaximalDomination
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section03IntegralElementsAreBounded
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section04RamificationIndexAndResidueDegree
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section05SplittingPatterns
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section05UniqueExtensionAndHenselianity

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01

noncomputable section

universe u

open scoped Polynomial TensorProduct WithZero

/-! # Book 2, Chapter 1, Section 1.2

This file records the henselian-versus-complete distinction and the concrete
Gaussian example at the prime `5`; the uniqueness bridge is exported by the
leaf interface in Section 1.1 so later chapter modules can import it without
creating an import cycle through this section.
-/

/-! ### Existence, uniqueness, and branches

The statements in this section keep the algebraic extension interface separate
from the later finite-dimensional local-field interface.
-/

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

/-! ### The prime/valuation branch interface -/

/-- In a finite field extension, valuation branches are parametrized by primes
of an integral model above the base maximal ideal. -/
theorem chapter01_finite_extension_prime_valuation_correspondence
    {A B K L Γ : Type*} [CommRing A] [IsDomain A]
    [ValuationRing A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    [CommRing B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ)
    (hA : vK.Integers A) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ExtensionPrimeCorrespondence
      (A := A) (B := B) (L := L) vK hA := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_finite_extension_prime_valuation_correspondence
    vK hA

/-- The prime/valuation correspondence turns uniqueness of a branch into
uniqueness of the corresponding maximal ideal, and conversely. -/
theorem chapter01_unique_prime_iff_unique_valuation_extension
    {A B K L Γ : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [IsIntegrallyClosed A]
    [Field K] [Field L] [CommRing B] [Algebra A B] [Algebra B L]
    [Algebra A L] [IsScalarTower A B L] [IsIntegralClosure B A L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [FiniteDimensional K L]
    [IsScalarTower A K L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ)
    (hA : vK.Integers A)
    (hcor :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ExtensionPrimeCorrespondence
        (A := A) (B := B) (L := L) vK hA) :
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HasUniquePrimeAbove
        (A := A) (B := B) ↔
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HasUniqueValuationExtension
        (L := L) vK) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_unique_prime_iff_unique_valuation_extension
    vK hA hcor

/-- A heterogeneous extension is discrete when its canonical value group is
discrete. A branch may use an ambient ordered codomain larger than the image
of its valuation, so discreteness must not be imposed on that arbitrary
codomain. -/
def chapter01DiscreteHeterogeneousExtension
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    (W : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.HeterogeneousValuationExtension vK L) : Prop :=
  letI : LinearOrderedCommGroupWithZero W.valueGroup := W.orderedValueGroup
  Nonempty
    (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass W.valuation) ≃*o ℤᵐ⁰)

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

/-- The finite part of Theorem 1.1 packages uniqueness and discreteness of
the extension branches in one interface. -/
theorem chapter01_theorem_1_1_finite
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [FiniteDimensional K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [Valuation.IsRankOneDiscrete vK]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueValuationExtension vK L ∧
      ∀ W :
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.HeterogeneousValuationExtension
          vK L,
        chapter01DiscreteHeterogeneousExtension vK W := by
  exact ⟨chapter01_theorem_1_1 vK hcomplete,
    chapter01_finite_extension_value_group_is_discrete vK hcomplete⟩

/-! ### The canonical finite value-group quotient -/

/-- A finite branch carries a canonical finite quotient of value groups. -/
theorem chapter01_heterogeneous_value_group_quotient_is_finite
    {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL] [FiniteDimensional K L]
    (vK : Valuation K ΓK) (vL : Valuation L ΓL)
    (hext : vK.IsEquiv (vL.comap (algebraMap K L))) :
    ∃ data :
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousExtensionData
          vK vL hext,
      Finite
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL ⧸
          data.valueGroupMap.range) := by
  obtain ⟨data⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_heterogeneous_extension_data_exists
      vK vL hext
  exact ⟨data, data.finite_quotient⟩

/-- The value-group quotient in a finite extension is finite. -/
theorem chapter01_finite_value_group_quotient_is_finite
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (hext : chapter01SamePlace vK vL)
    (hΓ : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK ≤
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL) :
    Finite
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL ⧸
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK).subgroupOf
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL)) := by
  sorry

/-- A discrete value group has a canonical ordered integer model. -/
theorem chapter01_discrete_value_group_can_be_normalized
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Valuation.IsRankOneDiscrete v] :
    Nonempty
      (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v) ≃*o ℤᵐ⁰) := by
  exact ⟨Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v⟩

/-- The finite normalization is local over a henselian valuation ring. -/
theorem chapter01_henselian_integral_closure_is_local
    {A K L : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] [HenselianLocalRing A]
    (hfinite : Module.Finite A (integralClosure A L)) :
    IsLocalRing (integralClosure A L) := by
  sorry

/-- Maximal ideals above the base maximal ideal are the finite-extension branches. -/
theorem chapter01_henselian_branch_is_unique
    {A K L : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
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
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hnat :
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℚ).natDegree = 2 := by
      simpa [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial] using
        (Polynomial.natDegree_X_pow_add_C (R := ℚ) (n := 2) (r := (1 : ℚ)))
    rw [hnat]
    norm_num
  · intro x hx
    have hx' : x ^ 2 + 1 = 0 := by
      simpa [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial,
        Polynomial.IsRoot] using hx
    nlinarith [sq_nonneg x]

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
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousValuationExtension
        L vK,
    ¬ LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValuationExtensionsEquivalent
      vK w₁ w₂

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
  intro hfield
  obtain ⟨e⟩ := chapter01_gaussian_completed_tensor_product_at_five
  have hprod : IsField (ℚ_[5] × ℚ_[5]) :=
    MulEquiv.isField hfield e.symm.toMulEquiv
  have hleft : ((1, 0) : ℚ_[5] × ℚ_[5]) ≠ 0 := by
    intro h
    have := congrArg Prod.fst h
    simp at this
  obtain ⟨b, hb⟩ := hprod.mul_inv_cancel hleft
  have hsecond := congrArg Prod.snd hb
  simp at hsecond

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01
