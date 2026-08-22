import LastLib.Book03RamificationTheory.Chapter03.Dependencies
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section07ConcreteFiniteExtensions
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section04RamificationIndexAndResidueDegree
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section08PrimeToP_RadicalExtensions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

namespace LastLib.Book03RamificationTheory.Chapter03

noncomputable section

open Polynomial
open scoped BigOperators

/-! ## 3.5. A wild Kummer calculation -/

/- The cyclotomic polynomial in the coordinate `λ = ζ_p - 1`. -/
def chapter03CyclotomicPolynomial
  (R : Type*) [CommRing R] (p : ℕ) : R[X] :=
  ∑ i ∈ Finset.range p,
    C (Nat.choose p (i + 1) : R) * X ^ i

theorem chapter03_cyclotomic_polynomial_is_the_displayed_quotient
    (R : Type*) [CommRing R] (p : ℕ) :
    X * chapter03CyclotomicPolynomial R p = (1 + X) ^ p - 1 := by
  sorry

theorem chapter03_cyclotomic_polynomial_is_eisenstein_at_p
    (p : ℕ) [Fact p.Prime] :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt
      (p : ℤ_[p]) (chapter03CyclotomicPolynomial (ℤ_[p]) p) := by
  sorry

theorem chapter03_cyclotomic_lambda_is_a_root
    (p : ℕ) [Fact p.Prime]
    {K : Type*} [Field K] (ζ lambda : K)
    (hζ : IsPrimitiveRoot ζ p) (hlambda : lambda = ζ - 1)
    (hlambda_ne : lambda ≠ 0) :
    aeval lambda (chapter03CyclotomicPolynomial K p) = 0 := by
  sorry

theorem chapter03_cyclotomic_base_degree_and_normalization
    (p : ℕ) [Fact p.Prime]
    {K : Type*} [Field K] [Algebra (ℚ_[p]) K]
    [FiniteDimensional (ℚ_[p]) K]
    (ζ lambda : K) (vK : AddValuation K (WithTop ℤ))
    (hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation
        vK)
    (hext : (Padic.addValuation (p := p)).IsEquiv
      (vK.comap (algebraMap (ℚ_[p]) K)))
    (hζ : IsPrimitiveRoot ζ p) (hlambda : lambda = ζ - 1)
    (hroot :
      aeval lambda
        ((chapter03CyclotomicPolynomial (ℤ_[p]) p).map
          (algebraMap (ℤ_[p]) (ℚ_[p]))) = 0)
    (hgen : Algebra.adjoin (ℚ_[p]) ({ζ} : Set K) = ⊤)
    (hlambda_value : vK lambda = 1) :
    Module.finrank (ℚ_[p]) K = p - 1 ∧
      vK (algebraMap (ℚ_[p]) K (p : ℚ_[p])) = p - 1 := by
  sorry

/- The data for the second Eisenstein radical. -/
structure Chapter03WildKummerExtensionData
    (p : ℕ) [Fact p.Prime]
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] where
  ζ : K
  primitive_root : IsPrimitiveRoot ζ p
  lambda : K
  lambda_eq : lambda = ζ - 1
  lambda_nonzero : lambda ≠ 0
  α : L
  root : α ^ p = algebraMap K L lambda
  generated : Algebra.adjoin K ({α} : Set L) = ⊤
  degree : Module.finrank K L = p

theorem chapter03_wild_kummer_polynomial_is_eisenstein
    {A K : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (lambda : A) (p : ℕ) (hp : 0 < p)
    (hlambda : Ideal.span ({lambda} : Set A) = IsLocalRing.maximalIdeal A) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt lambda
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08KummerPolynomial
        lambda p) := by
  sorry

theorem chapter03_wild_kummer_extension_is_cyclic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p : ℕ) [Fact p.Prime]
    (D : Chapter03WildKummerExtensionData p K L) :
    ∃ κ : rootsOfUnity p K ≃* (L ≃ₐ[K] L),
      ∀ ζ : rootsOfUnity p K,
        κ ζ D.α = algebraMap K L ((ζ : Kˣ) : K) * D.α := by
  sorry

theorem chapter03_wild_kummer_extension_profile
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p : ℕ) [Fact p.Prime]
    (D : Chapter03WildKummerExtensionData p K L)
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (hdiscreteL :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hval : vK.IsEquiv (vL.comap (algebraMap K L)))
    (hvalue_lambda : vK D.lambda = 1)
    (hvalue_alpha : vL D.α = 1) :
    ∃ d : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousExtensionData
        vK vL hval,
      ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ProfileRealizedByData d q ∧
          q.degree = p ∧ q.ramificationIndex = p ∧ q.residueDegree = 1 ∧
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified q := by
  sorry

theorem chapter03_wild_kummer_restriction_scales_by_p
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p : ℕ) [Fact p.Prime]
    (D : Chapter03WildKummerExtensionData p K L)
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (hval_lambda : vK D.lambda = 1) (hval_alpha : vL D.α = 1)
    (hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (hdiscreteL :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    (hrestriction : vL (algebraMap K L D.lambda) = p) :
    ∀ x : K, vL (algebraMap K L x) = p • vK x := by
  sorry

theorem chapter03_wild_kummer_root_difference_ratio_is_a_unit
    {K : Type*} [Field K] (p a : ℕ) [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (ha : 1 ≤ a) (hap : a < p) :
    IsUnit ((ζ ^ a - 1) / (ζ - 1)) := by
  sorry

/- The field-level unit statement above is supplemented by the valuation
   consequence used in the displacement calculation. -/
theorem chapter03_wild_kummer_root_difference_ratio_has_value_zero
    {K : Type*} [Field K] (p a : ℕ) [Fact p.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (ha : 1 ≤ a) (hap : a < p)
    (vK : AddValuation K (WithTop ℤ))
    (hvalue : vK (ζ - 1) = 1) :
    vK ((ζ ^ a - 1) / (ζ - 1)) = 0 := by
  sorry

theorem chapter03_wild_kummer_displacement_calculation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p a : ℕ) [Fact p.Prime]
    (D : Chapter03WildKummerExtensionData p K L)
    (vL : AddValuation L (WithTop ℤ))
    (σ : L ≃ₐ[K] L)
    (ha : 1 ≤ a) (hap : a < p)
    (hσ : σ D.α = algebraMap K L (D.ζ ^ a) * D.α)
    (hval_zeta : vL (algebraMap K L (D.ζ ^ a - 1)) = p)
    (hval_alpha : vL D.α = 1) :
    vL (σ D.α - D.α) = p + 1 := by
  sorry

theorem chapter03_wild_kummer_lower_groups
    {G : Type*} [Group G] [Finite G]
    (F : Chapter03LowerDisplacementFiltration G)
    (p : ℕ)
    (hdisp : ∀ {σ : G}, σ ≠ 1 → F.displacement σ = p + 1)
    (hnontrivial : ∃ σ : G, σ ≠ 1) :
    F.lower (-1) = ⊤ ∧
      (∀ n : ℕ, n ≤ p → F.lower (n : ℤ) = ⊤) ∧
      (∀ n : ℕ, p + 1 ≤ n → F.lower (n : ℤ) = ⊥) ∧
      chapter03LowerBreak F p := by
  have hprofile :=
    chapter03_one_break_profile_of_constant_displacement F p hdisp
  have hbreak := chapter03_one_break_is_unique F p hdisp hnontrivial
  exact ⟨F.lower_neg_one, hprofile.1, hprofile.2, hbreak⟩

/- SOURCE_WARNING (3.5): A radical equation is not a tameness criterion.
   The `chapter03_wild_kummer_*` declarations retain the degree divisibility
   by the residue characteristic and the resulting break `p`; the prime-to-
   `p` case is isolated in Section 3.2. -/

end
end LastLib.Book03RamificationTheory.Chapter03
