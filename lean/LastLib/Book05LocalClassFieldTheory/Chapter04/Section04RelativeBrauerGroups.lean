import LastLib.Book05LocalClassFieldTheory.Chapter04.Section03UnramifiedSplittingAndInvariant

namespace LastLib.Book05LocalClassFieldTheory.Chapter04

noncomputable section

open scoped BigOperators
open LastLib.Book05LocalClassFieldTheory.Chapter03

/-! ## 4.4. Relative Brauer groups and the norm index -/

def chapter04RelativeInvariantImage
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (I : Chapter04LocalInvariantData K)
    (R : Chapter04BrauerRestrictionData K L) : Set chapter04RationalResidue :=
  Set.range (chapter04InvariantOfRelativeClass I R)

def chapter04RationalResidueOneOverMultiples (n : ℕ) : Set chapter04RationalResidue :=
  {q | ∃ r : ℤ, q = r • chapter04RationalResidueOneOver n}

theorem chapter04_relative_brauer_invariant_mem_one_over_multiples
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (I : Chapter04LocalInvariantData K)
    (R : Chapter04BrauerRestrictionData K L)
    (n : ℕ) (hn : 0 < n)
    (hcompat : R.representative_compatibility)
    (a : chapter04RelativeBrauerGroup K L R) :
    chapter04InvariantOfRelativeClass I R a ∈
      chapter04RationalResidueOneOverMultiples n := by
  sorry

theorem chapter04_relative_brauer_invariant_image_eq_one_over_multiples
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (I : Chapter04LocalInvariantData K)
    (J : Chapter04LocalInvariantData L)
    (R : Chapter04BrauerRestrictionData K L)
    (n : ℕ) (hdegree : Module.finrank K L = n)
    (hcompat : R.representative_compatibility) :
    chapter04RelativeInvariantImage I R =
      chapter04RationalResidueOneOverMultiples n := by
  sorry

theorem chapter04_relative_brauer_invariant_kernel_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (I : Chapter04LocalInvariantData K)
    (R : Chapter04BrauerRestrictionData K L)
    (n : ℕ) (hdegree : Module.finrank K L = n)
    (hcompat : R.representative_compatibility)
    (a : chapter04BrauerGroup K) :
    R.restriction a = R.splitClass ↔ I.invariant a ∈
      chapter04RationalResidueOneOverMultiples n := by
  sorry

theorem chapter04_relative_brauer_group_card_eq_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (I : Chapter04LocalInvariantData K)
    (J : Chapter04LocalInvariantData L)
    (R : Chapter04BrauerRestrictionData K L)
    (n : ℕ) (hdegree : Module.finrank K L = n)
    (hcompat : R.representative_compatibility) :
    Nat.card (chapter04RelativeBrauerGroup K L R) = n := by
  sorry

structure Chapter04CyclicNormBrauerEquivalence
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (R : Chapter04BrauerRestrictionData K L) where
  forward : chapter03NormQuotient K L ≃
    chapter04RelativeBrauerGroup K L R
  parameter_class_compatibility : Prop

theorem chapter04_cyclic_norm_quotient_relative_brauer_equiv
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L / K))
    (hcyc : chapter03CyclicExtension K L n σ)
    (R : Chapter04BrauerRestrictionData K L)
    (hcompat : R.representative_compatibility) :
    Nonempty (Chapter04CyclicNormBrauerEquivalence K L R) := by
  sorry

theorem chapter04_cyclic_norm_quotient_card_eq_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L / K))
    (hcyc : chapter03CyclicExtension K L n σ)
    (R : Chapter04BrauerRestrictionData K L)
    (E : Chapter04CyclicNormBrauerEquivalence K L R) :
    Nat.card (chapter03NormQuotient K L) = n := by
  sorry

theorem chapter04_cyclic_norm_quotient_index
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L / K))
    (hcyc : chapter03CyclicExtension K L n σ)
    (R : Chapter04BrauerRestrictionData K L)
    (hcompat : R.representative_compatibility) :
    Nat.card (Kˣ ⧸ chapter03NormSubgroup K L) = n := by
  sorry

/- This form intentionally has no ramification hypothesis: the invariant
  argument covers tame and wildly ramified cyclic extensions alike. -/
theorem chapter04_cyclic_norm_index_including_wild_extensions
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L / K))
    (hcyc : chapter03CyclicExtension K L n σ)
    (R : Chapter04BrauerRestrictionData K L)
    (hcompat : R.representative_compatibility) :
    Nat.card (Kˣ ⧸ chapter03NormSubgroup K L) = n := by
  exact chapter04_cyclic_norm_quotient_index n σ hcyc R hcompat

theorem chapter04_theorem_4_2_cyclic_norm_index
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L / K))
    (hcyc : chapter03CyclicExtension K L n σ)
    (R : Chapter04BrauerRestrictionData K L)
    (hcompat : R.representative_compatibility) :
    Nat.card (Kˣ ⧸ chapter03NormSubgroup K L) = n := by
  exact chapter04_cyclic_norm_quotient_index n σ hcyc R hcompat

end

end LastLib.Book05LocalClassFieldTheory.Chapter04
