import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.LocalRing.Quotient
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section03RamificationIndexAndResidueDegree

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02

noncomputable section

open Ideal IsLocalRing
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
open scoped BigOperators WithZero

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-! ## Book 2, Chapter 2, §2.4

The length statements below use Mathlib's `Module.length` and its `toNat`
projection.  This retains the source proof's two counts: finite freeness over
the base and the `e` successive residue-field layers upstairs.
-/

/- Completeness and rank-one discreteness give the one-branch fundamental
equality without a separability or residue-perfection hypothesis.  The
finite-lattice theorem for the extension valuation ring supplies the needed
finite freeness. -/

/-- The central degree formula, with no separability or residue perfection
hypothesis. -/
theorem fundamental_equality
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Module.finrank K L =
      chapterRamificationIndex vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) *
      chapterResidueDegree vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) := by
  exact complete_extension_defectless_without_separability vK vL hcomplete

/-- The first base-precision quotient has length equal to the field degree. -/
theorem first_precision_length_is_field_degree
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [Module.Free vK.valuationSubring vL.valuationSubring]
    (hrank : Cardinal.toNat
      (Module.rank vK.valuationSubring vL.valuationSubring) = Module.finrank K L) :
    (Module.length vK.valuationSubring
      (vL.valuationSubring ⧸
        (IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring))).toNat =
      Module.finrank K L := by
  have hfinrank : Module.finrank vK.valuationSubring vL.valuationSubring =
      Module.finrank K L := by
    calc
      Module.finrank vK.valuationSubring vL.valuationSubring =
          Cardinal.toNat (Module.finrank vK.valuationSubring
            vL.valuationSubring : Cardinal) := by simp
      _ = Cardinal.toNat (Module.rank vK.valuationSubring
            vL.valuationSubring) := by rw [Module.finrank_eq_rank]
      _ = Module.finrank K L := hrank
  let b := Module.finBasisOfFinrankEq vK.valuationSubring
    vL.valuationSubring hfinrank
  let bq := IsLocalRing.basisQuotient b
  let : Field (vK.valuationSubring ⧸
      IsLocalRing.maximalIdeal vK.valuationSubring) :=
    Ideal.Quotient.field _
  calc
    (Module.length vK.valuationSubring
      (vL.valuationSubring ⧸
        (IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring))).toNat =
        (Module.length (vK.valuationSubring ⧸
          IsLocalRing.maximalIdeal vK.valuationSubring)
          (vL.valuationSubring ⧸
            (IsLocalRing.maximalIdeal vK.valuationSubring).map
              (algebraMap vK.valuationSubring vL.valuationSubring))).toNat := by
      exact congrArg ENat.toNat (Module.length_eq_of_surjective
        (M := vL.valuationSubring ⧸
          (IsLocalRing.maximalIdeal vK.valuationSubring).map
            (algebraMap vK.valuationSubring vL.valuationSubring))
        Ideal.Quotient.mk_surjective)
    _ = Module.finrank (vK.valuationSubring ⧸
          IsLocalRing.maximalIdeal vK.valuationSubring)
          (vL.valuationSubring ⧸
            (IsLocalRing.maximalIdeal vK.valuationSubring).map
              (algebraMap vK.valuationSubring vL.valuationSubring)) := by
      simpa using congrArg ENat.toNat
        (Module.length_eq_finrank
          (vK.valuationSubring ⧸ IsLocalRing.maximalIdeal vK.valuationSubring)
          (vL.valuationSubring ⧸
            (IsLocalRing.maximalIdeal vK.valuationSubring).map
              (algebraMap vK.valuationSubring vL.valuationSubring)))
    _ = Fintype.card (Fin (Module.finrank vK.valuationSubring
          vL.valuationSubring)) := by
      rw [Module.finrank_eq_card_basis bq]
      simp [hfinrank]
    _ = Module.finrank vK.valuationSubring vL.valuationSubring := by
      simp
    _ = Module.finrank K L := hfinrank

/-- The nested ideal quotient representing a maximal-ideal power layer. -/
abbrev chapter2PrimePowerLayer
    (B : Type*) [CommRing B] (P : Ideal B) (i : ℕ) : Type _ :=
  (P ^ i : Ideal B) ⧸ (P • ⊤ : Submodule B (P ^ i : Ideal B))

/-- Each nonzero maximal-ideal layer is one copy of the extension residue field. -/
theorem maximal_ideal_layers_are_residue_lines
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] [IsPrincipalIdealRing B]
    (i : ℕ) (hP0 : P ≠ ⊥) :
    Nonempty
    (chapter2PrimePowerLayer B P i ≃ₗ[B]
        (B ⧸ P)) := by
  exact ⟨(Ideal.quotEquivPowQuotPowSucc
    (IsPrincipalIdealRing.principal P) hP0 i).symm⟩

/-- The length comparison behind `[L : K] = e f`. -/
theorem first_precision_length_is_ramification_times_residue
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [Module.Free vK.valuationSubring vL.valuationSubring]
    (e f : ℕ)
    (hrank : Cardinal.toNat
      (Module.rank vK.valuationSubring vL.valuationSubring) = Module.finrank K L)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hf : chapterResidueDegree vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = f) :
    (Module.length vK.valuationSubring
      (vL.valuationSubring ⧸
      (IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring))).toNat =
      e * f := by
  have hdegree := first_precision_length_is_field_degree vK vL hrank
  have hprod :
      (IsLocalRing.maximalIdeal vK.valuationSubring).ramificationIdx'
          (IsLocalRing.maximalIdeal vL.valuationSubring) *
          (IsLocalRing.maximalIdeal vK.valuationSubring).inertiaDeg'
          (IsLocalRing.maximalIdeal vL.valuationSubring) = Module.finrank K L := by
    let : FaithfulSMul vK.valuationSubring vL.valuationSubring :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr
        (Valuation.HasExtension.algebraMap_injective (vK := vK) (vA := vL))
    have hsum :=
      Ideal.sum_ramification_inertia_eq_finrank
        (p := IsLocalRing.maximalIdeal vK.valuationSubring)
        (S := vL.valuationSubring)
    have hq_eq (q : (IsLocalRing.maximalIdeal vK.valuationSubring).primesOver
        vL.valuationSubring) :
        q.1 = IsLocalRing.maximalIdeal vL.valuationSubring := by
      exact IsLocalRing.eq_maximalIdeal
        (q.2.1.isMaximal (Ideal.ne_bot_of_mem_primesOver
          (IsDiscreteValuationRing.not_a_field vK.valuationSubring) q.2))
    let : Unique ((IsLocalRing.maximalIdeal vK.valuationSubring).primesOver
        vL.valuationSubring) :=
      { default := Ideal.primesOver.mk
          (IsLocalRing.maximalIdeal vK.valuationSubring)
          (IsLocalRing.maximalIdeal vL.valuationSubring)
        uniq := fun q => Subtype.ext (hq_eq q) }
    have hdefault :
        (default : (IsLocalRing.maximalIdeal vK.valuationSubring).primesOver
          vL.valuationSubring).1 = IsLocalRing.maximalIdeal vL.valuationSubring :=
      hq_eq default
    have hfinrank : Module.finrank vK.valuationSubring vL.valuationSubring =
        Module.finrank K L := by
      calc
        Module.finrank vK.valuationSubring vL.valuationSubring =
            Cardinal.toNat (Module.finrank vK.valuationSubring
              vL.valuationSubring : Cardinal) := by simp
        _ = Cardinal.toNat (Module.rank vK.valuationSubring
              vL.valuationSubring) := by rw [Module.finrank_eq_rank]
        _ = Module.finrank K L := hrank
    rw [Fintype.sum_unique, hfinrank] at hsum
    rw [Ideal.ramificationIdx'_eq_ramificationIdx
      (IsLocalRing.maximalIdeal vK.valuationSubring)
      (IsLocalRing.maximalIdeal vL.valuationSubring)
      (IsDiscreteValuationRing.not_a_field vK.valuationSubring),
      Ideal.inertiaDeg'_eq_inertiaDeg
        (IsLocalRing.maximalIdeal vK.valuationSubring)
        (IsLocalRing.maximalIdeal vL.valuationSubring)]
    simpa only [hdefault] using hsum
  have hram :
      (IsLocalRing.maximalIdeal vK.valuationSubring).ramificationIdx'
          (IsLocalRing.maximalIdeal vL.valuationSubring) = e := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx
      (IsLocalRing.maximalIdeal vK.valuationSubring)
      (IsLocalRing.maximalIdeal vL.valuationSubring)
      (IsDiscreteValuationRing.not_a_field vK.valuationSubring)]
    exact he
  have hres :
      (IsLocalRing.maximalIdeal vK.valuationSubring).inertiaDeg'
          (IsLocalRing.maximalIdeal vL.valuationSubring) = f := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg
      (IsLocalRing.maximalIdeal vK.valuationSubring)
      (IsLocalRing.maximalIdeal vL.valuationSubring)]
    exact hf
  calc
    (Module.length vK.valuationSubring
      (vL.valuationSubring ⧸
        (IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring))).toNat =
        Module.finrank K L := hdegree
    _ = (IsLocalRing.maximalIdeal vK.valuationSubring).ramificationIdx'
          (IsLocalRing.maximalIdeal vL.valuationSubring) *
        (IsLocalRing.maximalIdeal vK.valuationSubring).inertiaDeg'
          (IsLocalRing.maximalIdeal vL.valuationSubring) := hprod.symm
    _ = e * f := by rw [hram, hres]

/-- The layer count is the finite sum `∑_{i < e} f = e f`. -/
theorem fundamental_equality_as_layer_sum
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (e f : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hf : chapterResidueDegree vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = f)
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Module.finrank K L = (∑ _ : Fin e, f) ∧
      (∑ _ : Fin e, f) = e * f := by
  have hfund := fundamental_equality vK vL hcomplete
  constructor
  · calc
      Module.finrank K L =
          chapterRamificationIndex vK.valuationSubring vL.valuationSubring
            (IsLocalRing.maximalIdeal vL.valuationSubring) *
          chapterResidueDegree vK.valuationSubring vL.valuationSubring
            (IsLocalRing.maximalIdeal vL.valuationSubring) := hfund
      _ = e * f := by rw [he, hf]
      _ = ∑ _ : Fin e, f := by simp
  · simp

/-- Completeness and discreteness remove the defect factor without a
separability or residue-perfection hypothesis. -/
theorem fundamental_equality_without_separability_or_perfectness
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Module.finrank K L =
      chapterRamificationIndex vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) *
      chapterResidueDegree vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) := by
  exact complete_extension_defectless_without_separability vK vL hcomplete

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02
