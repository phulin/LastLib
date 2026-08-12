import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section02TheCompletedProductTheorem
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section03RamificationIndexAndResidueDegree
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section01WhyTowerFormulasMatter
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section03Transitivity

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter15
noncomputable section

open Ideal IsLocalRing
open scoped BigOperators TensorProduct WithZero

universe u

/-! ## 15.1. The structural dictionary -/

/--
The multiplicative form of the normalized restriction formula.  Mathlib's
`Valuation` is multiplicative, so the additive identity
`v_L|_K = e • v_K` is represented by `v_L(x) = v_K(x)^e`.
-/
def normalizedValuationRestriction
    {K L Γ : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (e : ℕ) : Prop :=
  ∀ x : K, vL (algebraMap K L x) = (vK x) ^ e

/-- The ideal-theoretic form of `m_K B = m_L^e`. -/
def maximalIdealExtensionIsPower
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (mA : Ideal A) (mB : Ideal B) (e : ℕ) : Prop :=
  Ideal.map (algebraMap A B) mA = mB ^ e

/-
The source's opening paragraph is a bundle of compatible data rather than a
single equality.  This structure keeps the rank, ideal, valuation, and
completeness interfaces together while retaining the explicit normalization
choice required by `Valuation.HasExtension`.
-/
structure Chapter15LocalExtensionProfile
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [Algebra vK.valuationSubring L]
    [Algebra vK.valuationSubring vL.valuationSubring]
    [IsScalarTower vK.valuationSubring K L]
    [IsScalarTower vK.valuationSubring vL.valuationSubring L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [PerfectField (IsLocalRing.ResidueField vK.valuationSubring)] where
  e : ℕ
  f : ℕ
  complete_base :
    IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring
  integral_closure :
    (integralClosure vK.valuationSubring L : Set L) =
      (vL.valuationSubring : Set L)
  finite_free :
    Module.Finite vK.valuationSubring vL.valuationSubring ∧
      Module.Free vK.valuationSubring vL.valuationSubring
  upstairs_complete :
    IsAdicComplete (IsLocalRing.maximalIdeal vL.valuationSubring)
      vL.valuationSubring
  upstairs_dvr : IsDiscreteValuationRing vL.valuationSubring
  e_eq_ramification_index :
    e = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring)
  f_eq_residue_degree :
    f = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring)
  degree_eq_ef : Module.finrank K L = e * f
  normalized_restriction : normalizedValuationRestriction vK vL e
  maximal_ideal_extension :
    maximalIdealExtensionIsPower
      (IsLocalRing.maximalIdeal vK.valuationSubring)
      (IsLocalRing.maximalIdeal vL.valuationSubring) e

/- The profile is the book-facing constructor/eliminator for the dictionary. -/
theorem complete_extension_has_local_extension_profile
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (e f : ℕ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [Algebra vK.valuationSubring L]
    [Algebra vK.valuationSubring vL.valuationSubring]
    [IsScalarTower vK.valuationSubring K L]
    [IsScalarTower vK.valuationSubring vL.valuationSubring L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [PerfectField (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (he : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = f)
    (hrestriction : normalizedValuationRestriction vK vL e) :
    ∃ d : Chapter15LocalExtensionProfile vK vL,
      d.e = e ∧ d.f = f ∧
        IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
          vK.valuationSubring := by
  sorry

/--
Residue trace and norm formulas are stated with the residue maps explicit.
This avoids pretending that Mathlib can infer a map between arbitrary
quotients from ideals alone; in the local-field application these maps are
the canonical quotient residue maps.
-/
-- SOURCE_ISSUE: The residue trace and norm identities in §15.1 also rely on
-- defectlessness: applying the trace identity to a base element detects the
-- degree factor.  The shadow data therefore records the independent
-- defectless rank equality instead of asserting the identities from only the
-- ring and residue maps.
structure Chapter15ResidueArithmeticShadow
    {A B k l : Type*} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [IsLocalRing A] [IsLocalRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra.IsIntegral A B]
    [Module.Finite A B] [Module.Free A B]
    [Module.Finite k l] [Module.Free k l] where
  e : ℕ
  f : ℕ
  e_eq_ramification_index :
    e = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      A B (IsLocalRing.maximalIdeal B)
  f_eq_residue_degree :
    f = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      A B (IsLocalRing.maximalIdeal B)
  f_eq_residue_finrank : f = Module.finrank k l
  degree_eq_ef : Module.finrank A B = e * f
  baseResidue : A →+* k
  extensionResidue : B →+* l
  baseResidue_surjective : Function.Surjective baseResidue
  extensionResidue_surjective : Function.Surjective extensionResidue
  baseResidue_kernel : RingHom.ker baseResidue = IsLocalRing.maximalIdeal A
  extensionResidue_kernel : RingHom.ker extensionResidue = IsLocalRing.maximalIdeal B
  residueCompatibility : ∀ a : A,
    extensionResidue (algebraMap A B a) = algebraMap k l (baseResidue a)

/--
Book 2, §15.1: in a finite extension of complete discretely valued fields,
the valuation ring upstairs is the integral closure and is finite free.  The
rank is exposed by a basis indexed by the field degree.
-/
theorem complete_extension_has_finite_free_integral_closure
    {K L Γ : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [Algebra vK.valuationSubring L]
    [IsScalarTower vK.valuationSubring K L]
    [IsScalarTower vK.valuationSubring vL.valuationSubring L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    (integralClosure vK.valuationSubring L : Set L) =
        (vL.valuationSubring : Set L) ∧
      Module.Finite vK.valuationSubring vL.valuationSubring ∧
      Module.Free vK.valuationSubring vL.valuationSubring ∧
    Nonempty (Module.Basis (Fin (Module.finrank K L))
        vK.valuationSubring vL.valuationSubring) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal vL.valuationSubring)
        vL.valuationSubring ∧
      IsDiscreteValuationRing vL.valuationSubring := by
  sorry

/-
The class `Valuation.HasExtension` identifies the restriction only up to
valuation equivalence.  It therefore does not by itself justify the literal
normalization used in the displayed power formula.
-/
-- API_NOTE: The source writes a literal equality for normalized
-- valuations, but the canonical extension interface supplies only valuation
-- equivalence.  The bridge below records that canonical weaker fact; the
-- displayed normalization is exposed with an explicit normalization datum.
theorem restriction_is_equivalent_to_base_valuation
    {K L : Type*} [Field K] [Field L]
    [Algebra K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] :
    vK.IsEquiv (vL.comap (algebraMap K L)) :=
  Valuation.HasExtension.val_isEquiv_comap

/- The explicit normalization datum needed for a literal power formula. -/
structure Chapter15NormalizedValuationChoice
    {K L : Type*} [Field K] [Field L]
    [Algebra K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring] where
  e : ℕ
  e_eq_ramification_index :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = e
  restriction : normalizedValuationRestriction vK vL e

/- Book 2, §15.1: the normalized valuation restriction carries the factor
`e`, once the chosen representatives have been normalized literally. -/
theorem normalized_restriction_has_ramification_factor
    {K L : Type*} [Field K] [Field L]
    [Algebra K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    [Module.Finite K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (d : Chapter15NormalizedValuationChoice vK vL) :
    normalizedValuationRestriction vK vL d.e :=
  d.restriction

/-- Book 2, §15.1: extension of the base maximal ideal. -/
theorem maximal_ideal_extension_is_ramification_power
    {K L : Type*} [Field K] [Field L]
    [Algebra K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰) (e : ℕ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (he : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = e) :
    maximalIdealExtensionIsPower
      (IsLocalRing.maximalIdeal vK.valuationSubring)
      (IsLocalRing.maximalIdeal vL.valuationSubring) e := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.maximal_ideal_extension_is_power
      vK vL e he

/-- Book 2, §15.1: one valuation/residue block accounts for `e * f` dimensions. -/
-- SOURCE_ISSUE: §§15.1–15.2 state `[L : K] = e f` for every finite extension of a complete discretely valued field without a defectless or perfect-residue hypothesis. Complete discretely valued fields with imperfect residue field can have finite defect extensions, so the equality is false as stated; the minimally corrected interface below assumes a perfect base residue field, a standard hypothesis implying defectlessness.
theorem complete_extension_degree_is_ramification_times_residue_degree
    {K L Γ : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (e f : ℕ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [PerfectField (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (he : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = f)
    :
    Module.finrank K L = e * f := by
  sorry

/-- Book 2, §15.1: both local indices multiply in a tower. -/
theorem ramification_and_residue_degrees_multiply_in_a_tower
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T]
    (p : Ideal R) (q : Ideal S) (r : Ideal T)
    [p.IsPrime] [q.IsPrime] [r.IsPrime]
    [q.LiesOver p] [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S ∧
      r.inertiaDeg R = q.inertiaDeg R * r.inertiaDeg S := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03_tower_ramification_and_residue_laws
      p q r

/-- Book 2, §15.1: trace and norm transfer through a finite tower. -/
theorem trace_and_norm_transfer_in_a_tower
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [Module.Finite K M] [Module.Finite M L] [Module.Finite K L] (x : L) :
    Algebra.trace K L x = Algebra.trace K M (Algebra.trace M L x) ∧
      Algebra.norm K x = Algebra.norm K (Algebra.norm M x) := by
  exact ⟨
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04_trace_transitive
      K M L x,
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04_norm_transitive
      K M L x⟩

/-- Book 2, §15.1: the valuation of a norm records the residue degree. -/
-- SOURCE_ISSUE: The norm valuation identity in §15.1 implies the degree
-- equality when applied to a nonzero base element, so it is also false for a
-- finite defect extension.  The corrected interface assumes a perfect base
-- residue field and completeness, which imply defectlessness in this setting.
theorem structural_norm_valuation_formula
    {K L : Type*} [Field K] [Field L]
    [Algebra K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰) (f : ℕ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [Module.Finite K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [PerfectField (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = f)
    (x : L) :
    vK (Algebra.norm K x) = (vL x) ^ f := by
  sorry

/-- Book 2, §15.1: the residue trace shadow, with no separability assumption. -/
theorem residue_trace_shadow_formula
    {A B k l : Type*} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra.IsIntegral A B]
    [Module.Finite A B] [Module.Free A B]
    [Module.Finite k l] [Module.Free k l]
    (d : Chapter15ResidueArithmeticShadow) (x : B) :
    d.baseResidue (Algebra.trace A B x) =
      (d.e : k) * Algebra.trace k l (d.extensionResidue x) := by
  sorry

/-- Book 2, §15.1: the residue norm shadow, with no separability assumption. -/
theorem residue_norm_shadow_formula
    {A B k l : Type*} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra A B] [Algebra k l]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra.IsIntegral A B]
    [Module.Finite A B] [Module.Free A B]
    [Module.Finite k l] [Module.Free k l]
    (d : Chapter15ResidueArithmeticShadow) (u : Bˣ) :
    d.baseResidue (Algebra.norm A (u : B)) =
      (Algebra.norm k ((Units.map d.extensionResidue.toMonoidHom u : lˣ) : l)) ^ d.e := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter15
