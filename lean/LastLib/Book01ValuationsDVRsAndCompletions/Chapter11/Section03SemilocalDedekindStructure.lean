import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section02FinitenessHypotheses

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

/-! # Book 1, Chapter 11, Section 11.3: Semilocal Dedekind Structure
-/

/-! ## 11.3. The semilocal Dedekind picture -/

/-- A finite list of branches over `m`, including their numerical invariants. -/
structure Chapter11BranchData (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (m : Ideal A) where
  index : Type*
  [finite_index : Fintype index]
  prime : index → Ideal B
  prime_isPrime : ∀ i, (prime i).IsPrime
  prime_isMaximal : ∀ i, (prime i).IsMaximal
  prime_liesOver : ∀ i, (prime i).LiesOver m
  prime_injective : Function.Injective prime
  exhaustive : ∀ P, chapter11Branch A B m P → ∃ i, prime i = P
  ramification : index → ℕ
  inertia : index → ℕ
  ramification_eq : ∀ i, ramification i = (prime i).ramificationIdx A
  inertia_eq : ∀ i, inertia i = (prime i).inertiaDeg A

/-- Every extension of the base valuation has a unique center among the
normalization branches.  The stronger localization equivalence is packaged in
`Chapter11ValuationBranchCorrespondence` and in the finite-normalization
correspondence theorem above. -/
theorem chapter11_every_extension_is_one_of_the_branch_localizations
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsIntegralClosure B A L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Module.Finite A B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B] [FaithfulSMul A B]
    (hAinj : Function.Injective (algebraMap A K))
    (hKinj : Function.Injective (algebraMap K L))
    (hbranches : chapter11IsSemilocal B)
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    (hext : chapter11ValuationExtensionAt K L vK vL)
    (ιA : A →+* vK.valuationSubring)
    (hιA : ∀ a : A, (ιA a : K) = algebraMap A K a)
    (hcenter : chapter11ValuationCenter A K (IsLocalRing.maximalIdeal A) vK ιA) :
    ∃! P : Ideal B,
      chapter11Branch A B (IsLocalRing.maximalIdeal A) P ∧
        ∃ ι : B →+* vL.valuationSubring,
          chapter11ValuationCenter B L P vL ι ∧
            ∀ b : B, (ι b : L) = algebraMap B L b := by
  let W : ValuationSubring L := vL.valuationSubring
  have hWext : vK.IsEquiv (W.valuation.comap (algebraMap K L)) := by
    simpa [W] using hext.trans (Valuation.IsEquiv.comap (algebraMap K L)
      (Valuation.isEquiv_valuation_valuationSubring vL))
  have hmemA : ∀ a : A, algebraMap A L a ∈ W := by
    intro a
    change vL (algebraMap A L a) ≤ 1
    have ha : vK (algebraMap A K a) ≤ 1 := by
      have ha' : vK (ιA a : K) ≤ 1 :=
        (Valuation.mem_valuationSubring_iff vK (ιA a : K)).mp (ιA a).property
      simpa [hιA a] using ha'
    have ha' : vK (algebraMap A K a) ≤ vK 1 := by simpa using ha
    have hv : vK (algebraMap A K a) ≤ vK 1 ↔
        vL (algebraMap K L (algebraMap A K a)) ≤ vL (algebraMap K L 1) :=
      hext (algebraMap A K a) 1
    have hv' := hv.mp ha'
    simpa [IsScalarTower.algebraMap_apply A K L] using hv'
  let ιA' : A →+* W.valuation.valuationSubring :=
    (RingHom.codRestrict (algebraMap A L) W.valuation.valuationSubring
      (by simpa [W] using hmemA))
  have hιA' : ∀ a : A, (ιA' a : L) = algebraMap A L a := by
    intro a
    rfl
  have hcenter' : chapter11ValuationCenter A L (IsLocalRing.maximalIdeal A)
      W.valuation ιA' := by
    change IsLocalRing.maximalIdeal A =
      (IsLocalRing.maximalIdeal W.valuation.valuationSubring).comap ιA'
    change IsLocalRing.maximalIdeal A =
      (IsLocalRing.maximalIdeal vK.valuationSubring).comap ιA at hcenter
    have hlt_equiv : ∀ a : A,
        vK (algebraMap A K a) < vK 1 ↔
          W.valuation (algebraMap A L a) < W.valuation 1 := by
      intro a
      have hxy : vK (algebraMap A K a) ≤ vK 1 ↔
          W.valuation (algebraMap A L a) ≤ W.valuation 1 := by
        simpa [IsScalarTower.algebraMap_apply A K L] using
          (hWext (algebraMap A K a) 1)
      have hyx : W.valuation (algebraMap A L a) ≤ W.valuation 1 ↔
          vK (algebraMap A K a) ≤ vK 1 := hxy.symm
      have hyx' : W.valuation 1 ≤ W.valuation (algebraMap A L a) ↔
          vK 1 ≤ vK (algebraMap A K a) := by
        simpa [IsScalarTower.algebraMap_apply A K L] using
          (hWext 1 (algebraMap A K a)).symm
      constructor
      · intro h
        rw [lt_iff_le_not_ge] at h ⊢
        exact ⟨hxy.mp h.1, fun h' => h.2 (hyx'.mp h')⟩
      · intro h
        rw [lt_iff_le_not_ge] at h ⊢
        exact ⟨hyx.mp h.1, fun h' => h.2 (hyx'.mpr h')⟩
    apply Ideal.ext
    intro a
    constructor
    · intro ha
      have haK : ιA a ∈ IsLocalRing.maximalIdeal vK.valuationSubring := by
        exact (show a ∈ (IsLocalRing.maximalIdeal vK.valuationSubring).comap ιA from
          hcenter ▸ ha)
      have hltK : vK (algebraMap A K a) < 1 := by
        rw [← hιA a]
        exact (Valuation.mem_maximalIdeal_iff (K := K) vK).mp haK
      have hltW : W.valuation (algebraMap A L a) < W.valuation 1 :=
        (hlt_equiv a).mp (by simpa using hltK)
      exact (Valuation.mem_maximalIdeal_iff (K := L) W.valuation).mpr
        (by simpa [hιA' a] using hltW)
    · intro ha
      have hltW : W.valuation (algebraMap A L a) < 1 := by
        have hltW' := (Valuation.mem_maximalIdeal_iff (K := L) W.valuation).mp ha
        simpa [hιA' a] using hltW'
      have hltK : vK (algebraMap A K a) < vK 1 :=
        (hlt_equiv a).mpr (by simpa using hltW)
      have haK : ιA a ∈ IsLocalRing.maximalIdeal vK.valuationSubring := by
        apply (Valuation.mem_maximalIdeal_iff (K := K) vK).mpr
        simpa [hιA a] using hltK
      exact hcenter ▸ haK
  let ιA_W : A →+* W :=
    (RingHom.codRestrict (algebraMap A L) W hmemA)
  have hιA_W : ∀ a : A, (ιA_W a : L) = algebraMap A L a := by
    intro a
    rfl
  letI : Algebra A W := ιA_W.toAlgebra
  letI : IsScalarTower A W L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro a
    exact hιA_W a
  have hmemB : ∀ b : B, algebraMap B L b ∈ W := by
    intro b
    have hb : IsIntegral A b := Algebra.IsIntegral.isIntegral (R := A) b
    have hbW : IsIntegral W (algebraMap B L b) := by
      exact hb.map_of_comp_eq (algebraMap A W) (algebraMap B L) (by
        apply RingHom.ext
        intro a
        calc
          (algebraMap W L) (algebraMap A W a) = algebraMap A L a := hιA_W a
          _ = algebraMap B L (algebraMap A B a) :=
            IsScalarTower.algebraMap_apply A B L a)
    have hInt : W.valuation.Integers W := by
      refine
        { hom_inj := Subtype.val_injective
          map_le_one := ?_
          exists_of_le_one := ?_ }
      · intro x
        have hx : (x : L) ∈ W.valuation.valuationSubring := by
          simpa only [ValuationSubring.valuationSubring_valuation] using x.property
        exact (Valuation.mem_valuationSubring_iff W.valuation _).mp hx
      · intro r hr
        have hrW : r ∈ W := by
          simpa only [ValuationSubring.valuationSubring_valuation] using
            (Valuation.mem_valuationSubring_iff W.valuation _).mpr hr
        exact ⟨⟨r, hrW⟩, rfl⟩
    have hval : W.valuation (algebraMap B L b) ≤ 1 :=
      (Valuation.Integers.isIntegral_iff_v_le_one hInt).mp hbW
    simpa only [ValuationSubring.valuationSubring_valuation] using
      (Valuation.mem_valuationSubring_iff W.valuation _).mpr hval
  let ιB : B →+* W.valuation.valuationSubring :=
    (RingHom.codRestrict (algebraMap B L) W.valuation.valuationSubring
      (by simpa only [ValuationSubring.valuationSubring_valuation] using hmemB))
  have hιB : ∀ b : B, (ιB b : L) = algebraMap B L b := by
    intro b
    rfl
  let ιB' : B →+* vL.valuationSubring :=
    (RingHom.codRestrict (algebraMap B L) vL.valuationSubring
      (by simpa [W] using hmemB))
  have hιB' : ∀ b : B, (ιB' b : L) = algebraMap B L b := by
    intro b
    rfl
  have hconv := chapter11_valuation_ring_converse
    A B K L hAinj hKinj (IsLocalRing.maximalIdeal A) rfl W
      (W.valuation.comap (algebraMap K L)) (Valuation.IsEquiv.refl)
      ιB hιB ιA' hιA' hcenter'
  rcases hconv with ⟨P, hP, hPcenter⟩
  have hVeq : vL.IsEquiv W.valuation := by
    simpa [W] using (Valuation.isEquiv_valuation_valuationSubring vL)
  have hltVeq : ∀ b : B,
      W.valuation (algebraMap B L b) < W.valuation 1 ↔
        vL (algebraMap B L b) < vL 1 := by
    intro b
    have hxy : vL (algebraMap B L b) ≤ vL 1 ↔
        W.valuation (algebraMap B L b) ≤ W.valuation 1 := by
      simpa using hVeq (algebraMap B L b) 1
    have hyx : W.valuation 1 ≤ W.valuation (algebraMap B L b) ↔
        vL 1 ≤ vL (algebraMap B L b) := by
      simpa using (hVeq 1 (algebraMap B L b)).symm
    constructor
    · intro h
      rw [lt_iff_le_not_ge] at h ⊢
      exact ⟨hxy.mpr h.1, fun h' => h.2 (hyx.mpr h')⟩
    · intro h
      rw [lt_iff_le_not_ge] at h ⊢
      exact ⟨hxy.mp h.1, fun h' => h.2 (hyx.mp h')⟩
  have hPcenter' : chapter11ValuationCenter B L P vL ιB' := by
    change P = (IsLocalRing.maximalIdeal vL.valuationSubring).comap ιB'
    change P = (IsLocalRing.maximalIdeal W.valuation.valuationSubring).comap ιB at hPcenter
    apply Ideal.ext
    intro b
    constructor
    · intro hb
      have hbW : ιB b ∈ IsLocalRing.maximalIdeal W.valuation.valuationSubring := by
        have hbP : b ∈
            (IsLocalRing.maximalIdeal W.valuation.valuationSubring).comap ιB := by
          rw [← hPcenter]
          exact hb
        exact hbP
      have hltW : W.valuation (algebraMap B L b) < W.valuation 1 := by
        have hlt := (Valuation.mem_maximalIdeal_iff (K := L) W.valuation).mp hbW
        simpa [hιB b] using hlt
      have hltV : vL (algebraMap B L b) < vL 1 := (hltVeq b).mp hltW
      have hbV : ιB' b ∈ IsLocalRing.maximalIdeal vL.valuationSubring := by
        apply (Valuation.mem_maximalIdeal_iff (K := L) vL).mpr
        simpa [hιB' b] using hltV
      exact hbV
    · intro hb
      have hltV : vL (algebraMap B L b) < vL 1 := by
        have hlt := (Valuation.mem_maximalIdeal_iff (K := L) vL).mp hb
        simpa [hιB' b] using hlt
      have hltW : W.valuation (algebraMap B L b) < W.valuation 1 :=
        (hltVeq b).mpr hltV
      have hbW : ιB b ∈ IsLocalRing.maximalIdeal W.valuation.valuationSubring := by
        apply (Valuation.mem_maximalIdeal_iff (K := L) W.valuation).mpr
        simpa [hιB b] using hltW
      rw [hPcenter]
      exact hbW
  refine ⟨P, ?_, ?_⟩
  · refine ⟨hP, ?_⟩
    refine ⟨ιB', ?_, hιB'⟩
    exact hPcenter'
  · intro Q hQ
    rcases hQ.2 with ⟨ιQ, hQcenter, hιQ⟩
    have hιEq : ιQ = ιB' := by
      apply RingHom.ext
      intro b
      apply Subtype.ext
      calc
        ((ιQ b : vL.valuationSubring) : L) = algebraMap B L b := hιQ b
        _ = ((ιB' b : vL.valuationSubring) : L) := (hιB' b).symm
    have hQeq : Q = P := by
      change Q = (IsLocalRing.maximalIdeal vL.valuationSubring).comap ιQ at hQcenter
      change P = (IsLocalRing.maximalIdeal vL.valuationSubring).comap ιB' at hPcenter'
      calc
        Q = (IsLocalRing.maximalIdeal vL.valuationSubring).comap ιQ := hQcenter
        _ = (IsLocalRing.maximalIdeal vL.valuationSubring).comap ιB' := by rw [hιEq]
        _ = P := hPcenter'.symm
    exact hQeq

/-- A split extension is not itself a valuation ring: opposite branches see opposite signs. -/
theorem chapter11_split_semilocal_ring_is_not_a_valuation_ring
    (L : Type*) [Field L] (v₁ v₂ : AddValuation L (WithTop ℤ))
    (h : chapter11OppositeBranchValues L v₁ v₂) :
    ¬ ∀ x : L,
      (0 ≤ v₁ x ∧ 0 ≤ v₂ x) ∨
        (0 ≤ v₁ x⁻¹ ∧ 0 ≤ v₂ x⁻¹) := by
  exact chapter11_semilocality_is_essential L v₁ v₂ h

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
