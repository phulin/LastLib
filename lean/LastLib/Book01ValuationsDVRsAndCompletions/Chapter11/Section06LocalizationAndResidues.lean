import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section02FinitenessHypotheses
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

universe u v

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter11

noncomputable section

open Ideal IsLocalRing
open Polynomial
open scoped BigOperators TensorProduct WithZero Polynomial nonZeroDivisors

/-! # Chapter 11: several places above one place

This file is a statement-only formalization of sections 11.1--11.9 of Book 1.
The declarations are intentionally local to this namespace because the chapters
are generated independently.
-/

/-! # Book 1, Chapter 11, Section 11.6: Localization and Residues
-/

/-! ## 11.6. Localization, residue fields, and lengths -/

/-- The localized residue ring B_P / P B_P. -/
abbrev chapter11LocalizedResidueRing (B : Type*) [CommRing B] (P : Ideal B) [P.IsPrime] : Type _ :=
  Localization.AtPrime P ⧸
    Ideal.map (algebraMap B (Localization.AtPrime P)) P

/-- The quotient B_P / P B_P identifies with the fraction field of B/P. -/
theorem chapter11_localized_residue_is_fraction_field
    (B : Type*) [CommRing B] (P : Ideal B) [P.IsPrime] :
    Nonempty
        (chapter11LocalizedResidueRing B P ≃+* FractionRing (B ⧸ P)) := by
  let hmap : Ideal.map (algebraMap B (Localization.AtPrime P)) P =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    Localization.AtPrime.map_eq_maximalIdeal
  let e₀ :
      (Localization.AtPrime P ⧸
        Ideal.map (algebraMap B (Localization.AtPrime P)) P) ≃+*
        IsLocalRing.ResidueField (Localization.AtPrime P) :=
    Ideal.quotEquivOfEq hmap
  let e : FractionRing (B ⧸ P) ≃ₐ[B ⧸ P]
      IsLocalRing.ResidueField (Localization.AtPrime P) :=
    IsFractionRing.algEquivOfAlgEquiv
      (R := B ⧸ P) (A := B ⧸ P) (K := FractionRing (B ⧸ P))
      (B := B ⧸ P)
      (L := IsLocalRing.ResidueField (Localization.AtPrime P))
      (AlgEquiv.refl : (B ⧸ P) ≃ₐ[B ⧸ P] (B ⧸ P))
  exact ⟨e₀.trans e.symm.toRingEquiv⟩

/-- Since P is maximal in the Dedekind situation, that fraction field is already B/P. -/
theorem chapter11_localized_residue_is_the_residue_field
    (B : Type*) [CommRing B] (P : Ideal B) [P.IsPrime] [P.IsMaximal] :
    IsField (B ⧸ P) ∧
      Nonempty (chapter11LocalizedResidueRing B P ≃+* (B ⧸ P)) := by
  constructor
  · exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mp inferInstance
  · let hmap : Ideal.map (algebraMap B (Localization.AtPrime P)) P =
        IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
      Localization.AtPrime.map_eq_maximalIdeal
    exact ⟨(Ideal.quotEquivOfEq hmap).trans
      (IsLocalization.AtPrime.equivQuotMaximalIdeal P
        (Localization.AtPrime P)).symm⟩

/-- The length valuation w_P(x) = length(B_P/xB_P). -/
def chapter11LocalLengthValue (B : Type*) [CommRing B] (P : Ideal B) [P.IsPrime] (x : B) : ℕ :=
  (Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸
        Ideal.span {algebraMap B (Localization.AtPrime P) x})).toNat

/-- The length value of a base element is its ramification index. -/
theorem chapter11_length_value_of_base_uniformizer
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B]
    [Algebra A B]
    (m : Ideal A) (π : A) (_hm : m = IsLocalRing.maximalIdeal A)
    (hπ : chapter11IsUniformizer A m π)
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] [P.LiesOver m] :
    chapter11LocalLengthValue B P (algebraMap A B π) = P.ramificationIdx A := by
  rw [chapter11LocalLengthValue]
  rw [← IsScalarTower.algebraMap_apply A B (Localization.AtPrime P)]
  have hspan :
      Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span ({π} : Set A)) =
        Ideal.span ({algebraMap A (Localization.AtPrime P) π} : Set _) := by
    simpa using (Ideal.map_span (algebraMap A (Localization.AtPrime P)) ({π} : Set A))
  rw [← hspan, ← hπ]
  exact (Ideal.ramificationIdx_eq m P).symm

/-- Computing the same length over A multiplies by the residue degree. -/
theorem chapter11_length_as_base_module_is_e_f
    (A B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.Finite A B]
    [Module.IsTorsionFree A B]
    (m : Ideal A) (π : A) (hπ : chapter11IsUniformizer A m π)
    (hm : m = IsLocalRing.maximalIdeal A)
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] [P.LiesOver m] :
    (Module.length A
        (Localization.AtPrime P ⧸
          Ideal.span {algebraMap A (Localization.AtPrime P) π})).toNat =
      P.ramificationIdx A * P.inertiaDeg A := by
  let S := Localization.AtPrime P
  let M := S ⧸ Ideal.span {algebraMap A S π}
  let _ : m.IsPrime := by
    rw [hm]
    exact (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  let _ : m.IsMaximal := by
    rw [hm]
    exact IsLocalRing.maximalIdeal.isMaximal A
  let _ : P.LiesOver (IsLocalRing.maximalIdeal A) := by
    rw [← hm]
    infer_instance
  let _ := Localization.AtPrime.algebraOfLiesOver m P
  let _ : IsLocalHom (algebraMap A S) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap A S)).out 4 0).mp
    change (IsLocalRing.maximalIdeal S).under A = IsLocalRing.maximalIdeal A
    rw [← Ideal.under_under (B := B), Localization.AtPrime.under_maximalIdeal]
    exact (P.over_def (IsLocalRing.maximalIdeal A)).symm
  have hspan : Ideal.span {algebraMap A S π} = m.map (algebraMap A S) := by
    change m = Ideal.span ({π} : Set A) at hπ
    rw [hπ, Ideal.map_span]
    simp
  have hres : Module.length (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField S) = P.inertiaDeg A := by
    let e : (B ⧸ P) ≃+* (IsLocalRing.ResidueField S) :=
      IsLocalization.AtPrime.equivQuotMaximalIdeal P S
    let eA : (A ⧸ IsLocalRing.maximalIdeal A) ≃+*
        (IsLocalRing.ResidueField A) := RingEquiv.refl _
    let _ : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ P) := inferInstance
    let _ : Module.Finite (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField S) := by
      apply Module.Finite.of_equiv_equiv eA e
      apply RingHom.ext
      intro a
      exact Quotient.inductionOn' a (fun a => rfl)
    have hfin : Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ P) =
        Module.finrank (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField S) := by
      apply Algebra.finrank_eq_of_equiv_equiv eA e
      apply RingHom.ext
      intro a
      exact Quotient.inductionOn' a (fun a => rfl)
    rw [Module.length_eq_finrank, hfin.symm,
      (Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal A) P).symm]
  have hlength : Module.length A M =
      Module.length S M * Module.length (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField S) :=
    IsLocalRing.length_restrictScalars A S M
  have hS : (Module.length S M).toNat = P.ramificationIdx A := by
    dsimp [M]
    rw [hspan]
    exact (Ideal.ramificationIdx_eq m P).symm
  calc
    (Module.length A M).toNat =
        (Module.length S M * Module.length (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField S)).toNat := by rw [hlength]
    _ = (Module.length S M).toNat *
        (Module.length (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField S)).toNat := by simp
    _ = P.ramificationIdx A * P.inertiaDeg A := by
      rw [hS, hres]
      simp

/-- The localized length is additive on nonzero integral elements; this is the
multiplicative part of the associated normalized discrete valuation. -/
theorem chapter11_length_value_is_additive_on_products
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal]
    (x y : B) (hx : x ≠ 0) (hy : y ≠ 0) :
    chapter11LocalLengthValue B P (x * y) =
      chapter11LocalLengthValue B P x + chapter11LocalLengthValue B P y := by
  let S := Localization.AtPrime P
  have hS : Function.Injective (algebraMap B S) :=
    IsLocalization.injective S P.primeCompl_le_nonZeroDivisors
  have hyS : algebraMap B S y ≠ 0 := by
    intro hyS
    exact hy (hS (by simpa using hyS))
  have hxS : algebraMap B S x ≠ 0 := by
    intro hxS
    exact hx (hS (by simpa using hxS))
  have hxNzd : algebraMap B S x ∈ nonZeroDivisors S :=
    mem_nonZeroDivisors_of_ne_zero hxS
  have hyNzd : algebraMap B S y ∈ nonZeroDivisors S :=
    mem_nonZeroDivisors_of_ne_zero hyS
  have hxo : Ring.ord S (algebraMap B S x) ≠ ⊤ :=
    Ring.ord_ne_top hxNzd
  have hyo : Ring.ord S (algebraMap B S y) ≠ ⊤ :=
    Ring.ord_ne_top hyNzd
  have hmul := Ring.ord_mul (R := S) (a := algebraMap B S x)
    (b := algebraMap B S y) hyNzd
  change (Ring.ord S (algebraMap B S (x * y))).toNat =
    (Ring.ord S (algebraMap B S x)).toNat +
      (Ring.ord S (algebraMap B S y)).toNat
  rw [map_mul]
  have hmulNat := congrArg ENat.toNat hmul
  rw [ENat.toNat_add hxo hyo] at hmulNat
  simpa [chapter11LocalLengthValue, Ring.ord] using hmulNat

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
