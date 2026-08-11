import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section02FiniteFreeness

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02

noncomputable section

open Ideal IsLocalRing
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
open scoped BigOperators WithZero

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-! ## Book 2, Chapter 2, §2.3

`chapterRamificationIndex` and `chapterResidueDegree` are the Book 1
Chapter 12 wrappers around Mathlib's `Ideal.ramificationIdx` and
`Ideal.inertiaDeg`.  Under the complete DVR hypotheses these are the
ideal-theoretic realizations of the value-group index and residue-field
dimension in the source.
-/

/-- The normalized restriction formula in Mathlib's multiplicative notation. -/
def chapter2NormalizedValuationRestriction
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰) (e : ℕ) : Prop :=
  ∀ x : K, vL (algebraMap K L x) = vK x ^ e

/-- A valuation to `ℤᵐ⁰` is normalized when it is surjective onto its target. -/
def chapter2SurjectiveIntegerValuation
    {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰) : Prop :=
  Function.Surjective v

/-- The residue-field extension attached to two extending valuation rings. -/
def chapter2ResidueFieldExtension
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] : Prop :=
  Module.Finite (IsLocalRing.ResidueField vK.valuationSubring)
    (IsLocalRing.ResidueField vL.valuationSubring)

/-- In the normalized convention, restriction scales by the ramification index. -/
-- SOURCE_ISSUE: `Valuation.HasExtension` identifies valuations only up to
-- order equivalence.  It does not fix the integer scale: even with `K = L`,
-- replacing `vL` by a positive power preserves `HasExtension` and the
-- valuation subring while changing the displayed equality.  The corrected
-- normalized interface is `normalized_valuation_restriction_has_ramification_factor`
-- below; this legacy declaration preserves the source-facing signature used
-- by later book chapters.
theorem valuation_restriction_is_power_of_ramification_index
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e) :
    ∀ x : K, vL (algebraMap K L x) = vK x ^ e := by
  sorry

/-- The restriction formula with surjective integer-valued normalizations. -/
theorem normalized_valuation_restriction_has_ramification_factor
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (hK : chapter2SurjectiveIntegerValuation vK)
    (hL : chapter2SurjectiveIntegerValuation vL)
    (e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e) :
    chapter2NormalizedValuationRestriction vK vL e := by
  sorry

/-- Uniformizers give the principal-ideal factorization `π_K = u π_L^e`. -/
theorem uniformizer_factorization
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (πK : vK.valuationSubring) (πL : vL.valuationSubring)
    (hπK : vK.IsUniformizer πK) (hπL : vL.IsUniformizer πL) :
    ∃ u : vL.valuationSubringˣ,
      algebraMap vK.valuationSubring vL.valuationSubring πK =
      (u : vL.valuationSubring) * (πL : vL.valuationSubring) ^ e := by
  let : FaithfulSMul vK.valuationSubring vL.valuationSubring :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (Valuation.HasExtension.algebraMap_injective (vK := vK) (vA := vL))
  let A := vK.valuationSubring
  let B := vL.valuationSubring
  let mA := IsLocalRing.maximalIdeal A
  let mB := IsLocalRing.maximalIdeal B
  let J : Ideal B := mA.map (algebraMap A B)
  have hJ0 : J ≠ ⊥ := by
    exact Ideal.map_ne_bot_of_ne_bot (IsDiscreteValuationRing.not_a_field A)
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal B
    (IsPrincipalIdealRing.principal mB) J hJ0
  have hlen :
      (Module.length (Localization.AtPrime mB)
        (Localization.AtPrime mB ⧸
          mA.map (algebraMap A (Localization.AtPrime mB)))).toNat = n := by
    have hmaploc :
      mA.map (algebraMap A (Localization.AtPrime mB)) =
          J.map (algebraMap B (Localization.AtPrime mB)) := by
      rw [Ideal.map_map]
      congr 1

    let : IsDiscreteValuationRing (Localization.AtPrime mB) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B
        (IsDiscreteValuationRing.not_a_field B) (Localization.AtPrime mB)
    rw [hmaploc, hn, Ideal.map_pow,
      Localization.AtPrime.map_eq_maximalIdeal,
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    rfl
  have hen : e = n := by
    calc
      e = chapterRamificationIndex A B mB := he.symm
      _ = (Module.length (Localization.AtPrime mB)
          (Localization.AtPrime mB ⧸
            mA.map (algebraMap A (Localization.AtPrime mB)))).toNat := by
        unfold chapterRamificationIndex
        exact Ideal.ramificationIdx_eq mA mB
      _ = n := hlen
  have hmap : mA.map (algebraMap A B) = mB ^ e := by
    change J = mB ^ e
    rw [hn, ← hen]
  have hspan :
      Ideal.span ({(πL : vL.valuationSubring) ^ e} :
          Set vL.valuationSubring) =
        Ideal.span ({algebraMap vK.valuationSubring vL.valuationSubring πK} :
          Set vL.valuationSubring) := by
    calc
      Ideal.span ({(πL : vL.valuationSubring) ^ e} :
          Set vL.valuationSubring) =
          (IsLocalRing.maximalIdeal vL.valuationSubring) ^ e := by
            rw [hπL.is_generator, Ideal.span_singleton_pow]
      _ = (IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring) := hmap.symm
      _ = Ideal.span ({algebraMap vK.valuationSubring vL.valuationSubring πK} :
          Set vL.valuationSubring) := by
            rw [hπK.is_generator, Ideal.map_span]
            simp
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨u, ?_⟩
  simpa [mul_comm] using hu.symm

/-- The extension of the base maximal ideal is the `e`th power upstairs. -/
theorem maximal_ideal_extension_is_power
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e) :
    (IsLocalRing.maximalIdeal vK.valuationSubring).map
        (algebraMap vK.valuationSubring vL.valuationSubring) =
      (IsLocalRing.maximalIdeal vL.valuationSubring) ^ e := by
  let : FaithfulSMul vK.valuationSubring vL.valuationSubring :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (Valuation.HasExtension.algebraMap_injective (vK := vK) (vA := vL))
  let A := vK.valuationSubring
  let B := vL.valuationSubring
  let mA := IsLocalRing.maximalIdeal A
  let mB := IsLocalRing.maximalIdeal B
  let J : Ideal B := mA.map (algebraMap A B)
  have hJ0 : J ≠ ⊥ := by
    exact Ideal.map_ne_bot_of_ne_bot (IsDiscreteValuationRing.not_a_field A)
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal B
    (IsPrincipalIdealRing.principal mB) J hJ0
  have hlen :
      (Module.length (Localization.AtPrime mB)
        (Localization.AtPrime mB ⧸
          mA.map (algebraMap A (Localization.AtPrime mB)))).toNat = n := by
    have hmaploc :
      mA.map (algebraMap A (Localization.AtPrime mB)) =
          J.map (algebraMap B (Localization.AtPrime mB)) := by
      rw [Ideal.map_map]
      congr 1

    let : IsDiscreteValuationRing (Localization.AtPrime mB) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B
        (IsDiscreteValuationRing.not_a_field B) (Localization.AtPrime mB)
    rw [hmaploc, hn, Ideal.map_pow,
      Localization.AtPrime.map_eq_maximalIdeal,
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    rfl
  have hen : e = n := by
    calc
      e = chapterRamificationIndex A B mB := he.symm
      _ = (Module.length (Localization.AtPrime mB)
          (Localization.AtPrime mB ⧸
            mA.map (algebraMap A (Localization.AtPrime mB)))).toNat := by
        unfold chapterRamificationIndex
        exact Ideal.ramificationIdx_eq mA mB
      _ = n := hlen
  change J = mB ^ e
  rw [hn, ← hen]

/-- The residue degree is the finite-dimensional degree of `l/k`. -/
theorem residue_degree_is_residue_field_finrank
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring] :
    chapterResidueDegree vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) =
      Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
        (IsLocalRing.ResidueField vL.valuationSubring) := by
  unfold chapterResidueDegree
  exact Ideal.inertiaDeg_eq_of_isMaximal
    (IsLocalRing.maximalIdeal vK.valuationSubring)
    (IsLocalRing.maximalIdeal vL.valuationSubring)

/-- The residue-degree formula has no separability hypothesis. -/
theorem residue_degree_formula_without_separability
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring] :
    chapterResidueDegree vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) =
      Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
        (IsLocalRing.ResidueField vL.valuationSubring) := by
  exact residue_degree_is_residue_field_finrank vK vL

/-- A residue degree is not replaced by a count of embeddings without separability. -/
def chapter2ResidueDegreeUsesVectorSpaceDimension
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] (f : ℕ) : Prop :=
  f = Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
    (IsLocalRing.ResidueField vL.valuationSubring)

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02
