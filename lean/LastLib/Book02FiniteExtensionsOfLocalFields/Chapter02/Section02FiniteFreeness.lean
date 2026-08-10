import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section01WhyTheValuationRingMustBeTheIntegralClosure

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02

noncomputable section

open Set
open Ideal IsLocalRing Polynomial
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
open scoped BigOperators WithZero

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-! ## Book 2, Chapter 2, §2.2

The source's `B` is represented by `vL.valuationSubring`; the fraction-field
claim is exposed as `IsFractionRing B L`, and the rank claim is stated with
`Module.rank` so that the field degree is `Module.finrank K L`.
-/

/-- The finite-lattice theorem for the integral closure in a complete discrete
extension. -/
theorem finite_integral_closure_is_free
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    (integralClosure vK.valuationSubring L : Set L) =
        (vL.valuationSubring : Set L) ∧
      Module.Finite vK.valuationSubring vL.valuationSubring ∧
      Module.Free vK.valuationSubring vL.valuationSubring ∧
      Cardinal.toNat (Module.rank vK.valuationSubring vL.valuationSubring) =
        Module.finrank K L ∧
      IsAdicComplete (IsLocalRing.maximalIdeal vL.valuationSubring)
        vL.valuationSubring ∧
      IsDiscreteValuationRing vL.valuationSubring ∧
      IsFractionRing vL.valuationSubring L := by
  have hstruct := finite_complete_extension_valuation_ring vK vL hcomplete
  letI : Module.Finite vK.valuationSubring vL.valuationSubring := hstruct.1
  have hclosure := complete_extension_unit_ball_is_integral_closure vK vL
  letI : IsFractionRing vK.valuationSubring K :=
    (Valuation.valuationSubring.integers vK).isFractionRing
  letI : IsFractionRing vL.valuationSubring L :=
    (Valuation.valuationSubring.integers vL).isFractionRing
  have hfinrank : Module.finrank vK.valuationSubring vL.valuationSubring =
      Module.finrank K L :=
    (IsFractionRing.finrank_eq vK.valuationSubring K vL.valuationSubring L).symm
  have hrank : Cardinal.toNat
      (Module.rank vK.valuationSubring vL.valuationSubring) = Module.finrank K L := by
    calc
      Cardinal.toNat (Module.rank vK.valuationSubring vL.valuationSubring) =
          Cardinal.toNat (Module.finrank vK.valuationSubring
            vL.valuationSubring : Cardinal) := by
            rw [Module.finrank_eq_rank]
      _ = Module.finrank vK.valuationSubring vL.valuationSubring := by
            rw [Cardinal.toNat_natCast]
      _ = Module.finrank K L := hfinrank
  exact ⟨hclosure.symm, hstruct.1, hstruct.2.1, hrank, hstruct.2.2.1,
    hstruct.2.2.2, inferInstance⟩

/-- The integral closure is finite over the base valuation ring. -/
theorem integral_closure_is_module_finite
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Module.Finite vK.valuationSubring (integralClosure vK.valuationSubring L) := by
  have h := finite_integral_closure_is_free vK vL hcomplete
  letI : Module.Finite vK.valuationSubring vL.valuationSubring := h.2.1
  let f : vL.valuationSubring →ₗ[vK.valuationSubring]
    integralClosure vK.valuationSubring L :=
    ((IsScalarTower.toAlgHom vK.valuationSubring vL.valuationSubring L).toLinearMap).codRestrict
      (integralClosure vK.valuationSubring L).toSubmodule (by
        intro x
        have hx : IsIntegral vK.valuationSubring x :=
          IsIntegral.of_finite vK.valuationSubring x
        have hxmap : IsIntegral vK.valuationSubring
            (algebraMap vL.valuationSubring L x) :=
          IsIntegral.algebraMap (R := vK.valuationSubring)
            (A := vL.valuationSubring) (B := L) hx
        change IsIntegral vK.valuationSubring
          ((IsScalarTower.toAlgHom vK.valuationSubring
            vL.valuationSubring L) x)
        simpa only [IsScalarTower.toAlgHom_apply] using hxmap)
  apply Module.Finite.of_surjective f
  intro x
  have hx : (x : L) ∈ vL.valuationSubring := by
    have hx' : (x : L) ∈ (integralClosure vK.valuationSubring L : Set L) :=
      x.property
    rw [h.1] at hx'
    exact hx'
  refine ⟨⟨(x : L), hx⟩, ?_⟩
  rfl

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
  refine ⟨b, ?_⟩
  intro x
  refine ⟨fun i => b.repr x i, ?_, ?_⟩
  · exact (b.sum_repr x).symm
  · intro c hc
    funext i
    have hi := congrArg (fun y => b.repr y i) hc
    rw [b.repr_sum_self] at hi
    exact hi.symm

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
  change Polynomial.eval x
      (Polynomial.map (algebraMap A B)
        (LinearMap.charpoly (Algebra.lmul A B x))) = 0
  rw [Polynomial.eval_map_algebraMap]
  exact Algebra.aeval_self_charpoly_lmul x

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
  intro i
  exact (IsIntegral.of_finite vK.valuationSubring (b i)).algebraMap

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02
