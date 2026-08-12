import LastLib.Book03RamificationTheory.Chapter01.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter01

noncomputable section

open scoped BigOperators WithZero

/-! ## 1.1. The question left by inertia -/

/-- A finite local valuation profile retains the two normalized invariants used
by the chapter.  The branch and completeness fields keep the notation tied to
an actual pair of valuation rings rather than to unrelated natural numbers. -/
structure Chapter01FiniteLocalValuationProfile
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [FiniteDimensional K L] [Valuation.HasExtension vK vL] where
  base_complete : chapter01CompleteDiscreteValuation vK
  extension_discrete : Valuation.IsRankOneDiscrete vL
  same_place : chapter01SamePlace vK vL
  e : ℕ
  f : ℕ
  e_positive : 0 < e
  f_positive : 0 < f
  e_eq : e = chapter01RamificationIndex vK vL
  f_eq : f = chapter01ResidueDegree vK vL

/-- The normalized additive restriction has the source's ramification factor. -/
theorem chapter01_restriction_scale_apply
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ)
    (hscale : chapter01ValuationRestrictionScale vK vL e)
    {x : K} (hx : x ≠ 0) :
    vL (algebraMap K L x) = e • vK x := by
  exact hscale.2 x hx

/-- A positive normalized scale determines the same valuation place. -/
theorem chapter01_restriction_scale_is_same_place
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ)
    (hscale : chapter01ValuationRestrictionScale vK vL e) :
    chapter01SamePlace vK.toValuation vL.toValuation := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01_restriction_scale_is_same_place
      vK vL e hscale

/-- Equivalent valuation representatives have the same integral elements. -/
theorem chapter01_same_place_mem_valuation_subring_iff
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    (h : chapter01SamePlace vK vL) (x : K) :
    x ∈ vK.valuationSubring ↔
      algebraMap K L x ∈ vL.valuationSubring := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01_same_place_mem_valuation_subring_iff
      vK vL h x

/-- In the complete base case the selected valuation branch is preserved by
every Galois automorphism. -/
theorem chapter01_complete_base_all_automorphisms_preserve_branch
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    (hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    (_hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hunique :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05UniqueNormalizedValuationExtension
        vK vL) :
    ∀ σ : chapter01GaloisGroup K L,
      ∀ x : L, x ∈ vL.valuationSubring ↔ σ x ∈ vL.valuationSubring := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.unique_local_valuation_gives_integral_symmetries
      vK vL hext hunique

/-- Under the same hypotheses the decomposition group is the full Galois group. -/
theorem chapter01_complete_base_decomposition_group_eq_top
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    (hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hunique :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05UniqueNormalizedValuationExtension
        vK vL) :
    chapter01DecompositionGroup K vL.valuationSubring = ⊤ := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.complete_base_decomposition_group_eq_galois_group
      vK vL hext hcomplete hunique

/-- The characteristic exponent has the residue-characteristic-zero value one. -/
theorem chapter01_characteristic_exponent_eq_one_of_char_zero
    (k : Type*) [Ring k] [CharZero k] :
    chapter01CharacteristicExponent k = 1 := by
  simp [chapter01CharacteristicExponent]

/-- In positive characteristic the characteristic exponent is the prime
characteristic. -/
theorem chapter01_characteristic_exponent_eq_prime
    (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    chapter01CharacteristicExponent k = p := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter01
