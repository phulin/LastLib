import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section04TheFundamentalEquality
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section01WhyTheValuationRingMustBeTheIntegralClosure

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02

noncomputable section

open Ideal IsLocalRing
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
open scoped BigOperators WithZero

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-! ## Book 2, Chapter 2, §2.6

Finite precision is expressed with powers of maximal ideals.  This avoids
choosing uniformizers in the statements that concern arbitrary precision;
the uniformizer form is recovered from §2.3.
-/

/-- A finite-precision quotient at an ideal. -/
abbrev chapter2FinitePrecisionQuotient
    (R : Type*) [CommRing R] (I : Ideal R) (n : ℕ) : Type _ :=
  R ⧸ I ^ n

/-- The `r`-digit version of the ideal-power formula. -/
theorem finite_precision_ideal_power_formula
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (r e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e) :
      ((IsLocalRing.maximalIdeal vK.valuationSubring).map
        (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r =
      (IsLocalRing.maximalIdeal vL.valuationSubring) ^ (r * e) := by
  have hpower := maximal_ideal_extension_is_power vK vL e he
  calc
    ((IsLocalRing.maximalIdeal vK.valuationSubring).map
        (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r =
        ((IsLocalRing.maximalIdeal vL.valuationSubring) ^ e) ^ r := by
          rw [hpower]
    _ = (IsLocalRing.maximalIdeal vL.valuationSubring) ^ (e * r) := by
          rw [pow_mul]
    _ = (IsLocalRing.maximalIdeal vL.valuationSubring) ^ (r * e) := by
          rw [Nat.mul_comm]

/-- Finite freeness identifies the `r`-digit quotient with `n` copies upstairs. -/
theorem finite_precision_quotient_linear_equiv
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [Module.Free vK.valuationSubring vL.valuationSubring]
    (r : ℕ)
    (hrank : Cardinal.toNat
      (Module.rank vK.valuationSubring vL.valuationSubring) = Module.finrank K L) :
    Nonempty
      ((vL.valuationSubring ⧸
          ((IsLocalRing.maximalIdeal vK.valuationSubring).map
            (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r) ≃ₗ[
          vK.valuationSubring]
        (Fin (Module.finrank K L) →
          (vK.valuationSubring ⧸
            (IsLocalRing.maximalIdeal vK.valuationSubring) ^ r))) := by
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
  let e₁ := LinearEquiv.restrictScalars vK.valuationSubring
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor
      vL.valuationSubring
        (IsLocalRing.maximalIdeal vK.valuationSubring ^ r)).toLinearEquiv)
  let e₂ := LinearEquiv.restrictScalars vK.valuationSubring
    ((Algebra.TensorProduct.basis
      (vK.valuationSubring ⧸ IsLocalRing.maximalIdeal vK.valuationSubring ^ r) b).equivFun)
  refine ⟨?_⟩
  rw [← Ideal.map_pow
    (f := algebraMap vK.valuationSubring vL.valuationSubring)
    (I := IsLocalRing.maximalIdeal vK.valuationSubring) r]
  exact e₁.trans e₂

/-- The two length computations agree at every positive base precision. -/
theorem finite_precision_length_formula
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [Module.Free vK.valuationSubring vL.valuationSubring]
    (r e f : ℕ)
    (hrank : Cardinal.toNat
      (Module.rank vK.valuationSubring vL.valuationSubring) = Module.finrank K L)
    (_hr : 0 < r)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hf : chapterResidueDegree vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = f) :
    (Module.length vK.valuationSubring
      (vL.valuationSubring ⧸
        ((IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r)).toNat =
        r * Module.finrank K L ∧
    (Module.length vK.valuationSubring
      (vL.valuationSubring ⧸
        ((IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r)).toNat =
        (r * e) * f := by
  obtain ⟨equiv⟩ := finite_precision_quotient_linear_equiv vK vL r hrank
  have hfirst :
      (Module.length vK.valuationSubring
        (vL.valuationSubring ⧸
          ((IsLocalRing.maximalIdeal vK.valuationSubring).map
            (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r)).toNat =
        r * Module.finrank K L := by
    calc
      (Module.length vK.valuationSubring
          (vL.valuationSubring ⧸
            ((IsLocalRing.maximalIdeal vK.valuationSubring).map
              (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r)).toNat =
          (Module.length vK.valuationSubring
            (Fin (Module.finrank K L) →
              (vK.valuationSubring ⧸
                (IsLocalRing.maximalIdeal vK.valuationSubring) ^ r))).toNat := by
        exact congrArg ENat.toNat equiv.length_eq
      _ = r * Module.finrank K L := by
        rw [Module.length_pi_of_fintype,
          IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
        simp [Nat.mul_comm]
  have hdegree : Module.finrank K L = e * f := by
    exact (first_precision_length_is_field_degree vK vL hrank).symm.trans
      (first_precision_length_is_ramification_times_residue vK vL e f hrank he hf)
  refine ⟨hfirst, ?_⟩
  calc
    (Module.length vK.valuationSubring
      (vL.valuationSubring ⧸
        ((IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r)).toNat =
        r * Module.finrank K L := hfirst
    _ = r * (e * f) := by rw [hdegree]
    _ = (r * e) * f := by rw [Nat.mul_assoc]

/-- The intrinsic `L`-adic quotient has `f n` residue-field coordinates. -/
theorem extension_precision_cardinality_exponent
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [Module.Free vK.valuationSubring vL.valuationSubring]
    [Fintype (IsLocalRing.ResidueField vK.valuationSubring)]
    [Fintype (IsLocalRing.ResidueField vL.valuationSubring)]
    (q f n : ℕ)
    (hq : Fintype.card (IsLocalRing.ResidueField vK.valuationSubring) = q)
    (hf : chapterResidueDegree vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = f)
    [Fintype (vL.valuationSubring ⧸
      (IsLocalRing.maximalIdeal vL.valuationSubring) ^ n)] :
    Fintype.card (vL.valuationSubring ⧸
        (IsLocalRing.maximalIdeal vL.valuationSubring) ^ n) =
      q ^ (f * n) := by
  let : IsPrincipalIdealRing vL.valuationSubring := inferInstance
  let : IsDedekindDomain vL.valuationSubring := inferInstance
  let : Fintype (vK.valuationSubring ⧸
      IsLocalRing.maximalIdeal vK.valuationSubring) := by
    change Fintype (IsLocalRing.ResidueField vK.valuationSubring)
    infer_instance
  have hP0 : IsLocalRing.maximalIdeal vL.valuationSubring ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field vL.valuationSubring
  have hres :
      (IsLocalRing.maximalIdeal vK.valuationSubring).cardQuot ^ f =
        (IsLocalRing.maximalIdeal vL.valuationSubring).cardQuot := by
    rw [← hf]
    exact Ideal.cardQuot_pow_inertiaDeg
      (IsLocalRing.maximalIdeal vK.valuationSubring)
      (IsLocalRing.maximalIdeal vL.valuationSubring)
  have hqcard :
      (IsLocalRing.maximalIdeal vK.valuationSubring).cardQuot = q := by
    rw [Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact hq
  calc
    Fintype.card (vL.valuationSubring ⧸
        (IsLocalRing.maximalIdeal vL.valuationSubring) ^ n) =
        Nat.card (vL.valuationSubring ⧸
          (IsLocalRing.maximalIdeal vL.valuationSubring) ^ n) := by
            rw [Nat.card_eq_fintype_card]
    _ = (IsLocalRing.maximalIdeal vL.valuationSubring ^ n).cardQuot := by
          rw [Submodule.cardQuot_apply]
    _ = (IsLocalRing.maximalIdeal vL.valuationSubring).cardQuot ^ n :=
          cardQuot_pow_of_prime hP0
    _ = ((IsLocalRing.maximalIdeal vK.valuationSubring).cardQuot ^ f) ^ n := by
          rw [hres]
    _ = (IsLocalRing.maximalIdeal vK.valuationSubring).cardQuot ^ (f * n) := by
          rw [← pow_mul]
    _ = q ^ (f * n) := by rw [hqcard]

/-- The base-precision quotient retains `r e` uniformizer digits upstairs. -/
theorem base_precision_cardinality_formula
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    [Fintype (IsLocalRing.ResidueField vK.valuationSubring)]
    [Fintype (IsLocalRing.ResidueField vL.valuationSubring)]
    (q e f r : ℕ)
    (hq : Fintype.card (IsLocalRing.ResidueField vK.valuationSubring) = q)
    (_he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (_hf : chapterResidueDegree vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = f)
    (hrank : Cardinal.toNat
      (Module.rank vK.valuationSubring vL.valuationSubring) = Module.finrank K L)
    (hdegree : Module.finrank K L = e * f)
    [Fintype (vL.valuationSubring ⧸
      ((IsLocalRing.maximalIdeal vK.valuationSubring).map
        (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r)] :
    Fintype.card (vL.valuationSubring ⧸
        ((IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r) =
      q ^ (r * f * e) ∧
    Fintype.card (vL.valuationSubring ⧸
        ((IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r) =
      q ^ (r * Module.finrank K L) := by
  let : Module.Free vK.valuationSubring vL.valuationSubring :=
    finite_torsion_free_over_dvr_is_free
      (complete_extension_unit_ball_is_torsion_free vK vL)
  let : IsPrincipalIdealRing vK.valuationSubring := inferInstance
  let : IsDedekindDomain vK.valuationSubring := inferInstance
  let : Finite (vK.valuationSubring ⧸
      IsLocalRing.maximalIdeal vK.valuationSubring) := by
    change Finite (IsLocalRing.ResidueField vK.valuationSubring)
    infer_instance
  let : Fintype (vK.valuationSubring ⧸
      IsLocalRing.maximalIdeal vK.valuationSubring) := by
    change Fintype (IsLocalRing.ResidueField vK.valuationSubring)
    infer_instance
  let : Finite (vK.valuationSubring ⧸
      IsLocalRing.maximalIdeal vK.valuationSubring ^ r) := by
    exact Ideal.finite_quotient_pow
      (IsLocalRing.maximalIdeal vK.valuationSubring).fg_of_isNoetherianRing r
  let : Fintype (vK.valuationSubring ⧸
      IsLocalRing.maximalIdeal vK.valuationSubring ^ r) :=
    Fintype.ofFinite _
  have hbase : Fintype.card (vK.valuationSubring ⧸
      IsLocalRing.maximalIdeal vK.valuationSubring ^ r) = q ^ r := by
    have hP0 : IsLocalRing.maximalIdeal vK.valuationSubring ≠ ⊥ :=
      IsDiscreteValuationRing.not_a_field vK.valuationSubring
    have hqcard :
        (IsLocalRing.maximalIdeal vK.valuationSubring).cardQuot = q := by
      rw [Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
      exact hq
    calc
      Fintype.card (vK.valuationSubring ⧸
          IsLocalRing.maximalIdeal vK.valuationSubring ^ r) =
          Nat.card (vK.valuationSubring ⧸
            IsLocalRing.maximalIdeal vK.valuationSubring ^ r) := by
              rw [Nat.card_eq_fintype_card]
      _ = (IsLocalRing.maximalIdeal vK.valuationSubring ^ r).cardQuot := by
            rw [Submodule.cardQuot_apply]
      _ = (IsLocalRing.maximalIdeal vK.valuationSubring).cardQuot ^ r :=
            cardQuot_pow_of_prime hP0
      _ = q ^ r := by rw [hqcard]
  have hfree_equiv := finite_precision_quotient_linear_equiv
    vK vL r hrank
  obtain ⟨equiv⟩ := hfree_equiv
  have hcard := Fintype.card_congr equiv.toEquiv
  have hfun : Fintype.card (Fin (Module.finrank K L) →
      (vK.valuationSubring ⧸
        IsLocalRing.maximalIdeal vK.valuationSubring ^ r)) =
      q ^ (r * Module.finrank K L) := by
    calc
      Fintype.card (Fin (Module.finrank K L) →
          (vK.valuationSubring ⧸
            IsLocalRing.maximalIdeal vK.valuationSubring ^ r)) =
          Fintype.card (vK.valuationSubring ⧸
            IsLocalRing.maximalIdeal vK.valuationSubring ^ r) ^
            Fintype.card (Fin (Module.finrank K L)) := by
              rw [Fintype.card_fun]
      _ = (q ^ r) ^ Module.finrank K L := by simp [hbase]
      _ = q ^ (r * Module.finrank K L) := by rw [← pow_mul]
  constructor
  · calc
      Fintype.card (vL.valuationSubring ⧸
          ((IsLocalRing.maximalIdeal vK.valuationSubring).map
            (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r) =
          Fintype.card (Fin (Module.finrank K L) →
            (vK.valuationSubring ⧸
              IsLocalRing.maximalIdeal vK.valuationSubring ^ r)) := hcard
      _ = q ^ (r * Module.finrank K L) := hfun
      _ = q ^ (r * (e * f)) := by rw [hdegree]
      _ = q ^ (r * f * e) := by congr 1; ac_rfl
  · calc
      Fintype.card (vL.valuationSubring ⧸
          ((IsLocalRing.maximalIdeal vK.valuationSubring).map
            (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r) =
          Fintype.card (Fin (Module.finrank K L) →
            (vK.valuationSubring ⧸
              IsLocalRing.maximalIdeal vK.valuationSubring ^ r)) := hcard
      _ = q ^ (r * Module.finrank K L) := hfun

/-- The compatible four-map diagram of base and residue precision. -/
structure Chapter2FinitePrecisionResidueDiagram
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰) (r : ℕ)
    [vK.HasExtension vL] where
  positive : 0 < r
  topHorizontal :
    (vK.valuationSubring ⧸
      (IsLocalRing.maximalIdeal vK.valuationSubring) ^ r) →+*
      (vL.valuationSubring ⧸
        ((IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r)
  leftVertical :
    (vK.valuationSubring ⧸
      (IsLocalRing.maximalIdeal vK.valuationSubring) ^ r) →+*
      IsLocalRing.ResidueField vK.valuationSubring
  bottomHorizontal :
    IsLocalRing.ResidueField vK.valuationSubring →+*
      IsLocalRing.ResidueField vL.valuationSubring
  rightVertical :
    (vL.valuationSubring ⧸
      ((IsLocalRing.maximalIdeal vK.valuationSubring).map
        (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r) →+*
      IsLocalRing.ResidueField vL.valuationSubring
  topHorizontal_spec :
    ∀ x : vK.valuationSubring,
      topHorizontal (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal vK.valuationSubring) ^ r) x) =
        Ideal.Quotient.mk
          (((IsLocalRing.maximalIdeal vK.valuationSubring).map
            (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r)
          (algebraMap vK.valuationSubring vL.valuationSubring x)
  leftVertical_spec :
    ∀ x : vK.valuationSubring,
      leftVertical (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal vK.valuationSubring) ^ r) x) =
        IsLocalRing.residue vK.valuationSubring x
  bottomHorizontal_spec :
    ∀ x : vK.valuationSubring,
      bottomHorizontal (IsLocalRing.residue vK.valuationSubring x) =
        IsLocalRing.residue vL.valuationSubring
          (algebraMap vK.valuationSubring vL.valuationSubring x)
  rightVertical_spec :
    ∀ x : vL.valuationSubring,
      rightVertical (Ideal.Quotient.mk
        (((IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring)) ^ r) x) =
        IsLocalRing.residue vL.valuationSubring x
  commutes :
    rightVertical.comp topHorizontal = bottomHorizontal.comp leftVertical

/-- The diagram in §2.6 exists for every finite precision. -/
theorem finite_precision_residue_diagram_exists
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (r : ℕ) (hr : 0 < r) :
    Nonempty (Chapter2FinitePrecisionResidueDiagram vK vL r) := by
  let A := vK.valuationSubring
  let B := vL.valuationSubring
  let mA := IsLocalRing.maximalIdeal A
  let mB := IsLocalRing.maximalIdeal B
  let f : A →+* B := algebraMap A B
  let J : Ideal B := mA.map f
  have hJ : J ≤ mB := by
    apply (Ideal.map_le_iff_le_comap).mpr
    change IsLocalRing.maximalIdeal vK.valuationSubring ≤
      (IsLocalRing.maximalIdeal vL.valuationSubring).comap
        (algebraMap vK.valuationSubring vL.valuationSubring)
    rw [extension_maximal_ideal_comap_eq_base_maximal_ideal vK vL]
  have htop : mA ^ r ≤ (J ^ r).comap f := by
    apply (Ideal.map_le_iff_le_comap).mp
    rw [Ideal.map_pow]
  have hleft : mA ^ r ≤ mA := Ideal.pow_le_self hr.ne'
  have hright : J ^ r ≤ mB :=
    (Ideal.pow_right_mono hJ r).trans (Ideal.pow_le_self hr.ne')
  let top : (A ⧸ mA ^ r) →+* (B ⧸ J ^ r) :=
    Ideal.quotientMap (J ^ r) f htop
  let left : (A ⧸ mA ^ r) →+* (A ⧸ mA) :=
    Ideal.Quotient.factor hleft
  let bottom : IsLocalRing.ResidueField A →+*
      IsLocalRing.ResidueField B := algebraMap _ _
  let right : (B ⧸ J ^ r) →+* IsLocalRing.ResidueField B := by
    change (B ⧸ J ^ r) →+* (B ⧸ mB)
    exact Ideal.Quotient.factor hright
  have hcomm : right.comp top = bottom.comp left := by
    apply RingHom.ext
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk mB (f x) =
      Ideal.Quotient.mk mB (f x)
    rfl
  refine ⟨{
    positive := hr
    topHorizontal := top
    leftVertical := left
    bottomHorizontal := bottom
    rightVertical := right
    topHorizontal_spec := by
      intro x
      rfl
    leftVertical_spec := by
      intro x
      rfl
    bottomHorizontal_spec := by
      intro x
      exact IsLocalRing.ResidueField.algebraMap_residue
        (R := vK.valuationSubring) (S := vL.valuationSubring) x
    rightVertical_spec := by
      intro x
      rfl
    commutes := hcomm }⟩

/-- For `r > 1`, the base precision quotient has nonzero nilpotent thickness. -/
theorem base_precision_quotient_has_nonzero_nilpotent
    (vK : Valuation K ℤᵐ⁰) [Valuation.IsRankOneDiscrete vK]
    (r : ℕ) (hr : 1 < r) :
    ∃ x : vK.valuationSubring ⧸
        (IsLocalRing.maximalIdeal vK.valuationSubring) ^ r,
      x ≠ 0 ∧ IsNilpotent x := by
  let A := vK.valuationSubring
  let m := IsLocalRing.maximalIdeal A
  obtain ⟨π, hπ⟩ :=
    Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial vK
  have hπm : (π : A) ∈ m := by
    change (π : A) ∈ IsLocalRing.maximalIdeal vK.valuationSubring
    rw [hπ.is_generator]
    exact Ideal.mem_span_singleton_self _
  have hπ0 : (π : A) ≠ 0 := by
    intro h
    apply hπ.ne_zero
    exact congrArg Subtype.val h
  let x : A ⧸ m ^ r := Ideal.Quotient.mk (m ^ r) π
  refine ⟨x, ?_, ?_⟩
  · intro hx
    have hmem : (π : A) ∈ m ^ r :=
      Ideal.Quotient.eq_zero_iff_mem.mp hx
    change (π : A) ∈ (IsLocalRing.maximalIdeal vK.valuationSubring) ^ r at hmem
    rw [hπ.is_generator, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton'] at hmem
    obtain ⟨a, ha⟩ := hmem
    have hpow : a * (π : A) ^ (r - 1) = 1 := by
      refine (mul_left_cancel₀ hπ0) ?_
      calc
        (π : A) * (a * (π : A) ^ (r - 1)) =
            a * (π : A) ^ r := by
          calc
            (π : A) * (a * (π : A) ^ (r - 1)) =
                a * ((π : A) ^ (r - 1) * (π : A)) := by ac_rfl
            _ = a * (π : A) ^ r := by
              rw [← pow_succ, Nat.sub_add_cancel hr.le]
        _ = (π : A) := ha
        _ = (π : A) * 1 := by simp
    have hunitpow : IsUnit ((π : A) ^ (r - 1)) :=
      isUnit_iff_exists_inv'.mpr ⟨a, hpow⟩
    have hunit : IsUnit (π : A) :=
      (isUnit_pow_iff (Nat.sub_ne_zero_of_lt hr)).mp hunitpow
    exact hπ.not_isUnit hunit
  · refine ⟨r, ?_⟩
    change (Ideal.Quotient.mk (m ^ r) (π : A)) ^ r = 0
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hπm r)

/-- If `e > 1`, ramification makes the first upstairs quotient nonreduced. -/
theorem ramified_first_quotient_has_nonzero_nilpotent
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hepos : 1 < e) :
    ∃ x : vL.valuationSubring ⧸
        (IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring),
      x ≠ 0 ∧ IsNilpotent x := by
  let A := vK.valuationSubring
  let B := vL.valuationSubring
  let mB := IsLocalRing.maximalIdeal B
  let J : Ideal B := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
  have hJ : J = mB ^ e := by
    exact maximal_ideal_extension_is_power vK vL e he
  obtain ⟨π, hπ⟩ :=
    Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial vL
  have hπm : (π : B) ∈ mB := by
    change (π : B) ∈ IsLocalRing.maximalIdeal vL.valuationSubring
    rw [hπ.is_generator]
    exact Ideal.mem_span_singleton_self _
  have hπ0 : (π : B) ≠ 0 := by
    intro h
    apply hπ.ne_zero
    exact congrArg Subtype.val h
  let x : B ⧸ J := Ideal.Quotient.mk J π
  refine ⟨x, ?_, ?_⟩
  · intro hx
    have hmem : (π : B) ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hx
    rw [hJ] at hmem
    change (π : B) ∈ (IsLocalRing.maximalIdeal vL.valuationSubring) ^ e at hmem
    rw [hπ.is_generator, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton'] at hmem
    obtain ⟨a, ha⟩ := hmem
    have hpow : a * (π : B) ^ (e - 1) = 1 := by
      refine (mul_left_cancel₀ hπ0) ?_
      calc
        (π : B) * (a * (π : B) ^ (e - 1)) =
            a * (π : B) ^ e := by
          calc
            (π : B) * (a * (π : B) ^ (e - 1)) =
                a * ((π : B) ^ (e - 1) * (π : B)) := by ac_rfl
            _ = a * (π : B) ^ e := by
              rw [← pow_succ, Nat.sub_add_cancel hepos.le]
        _ = (π : B) := ha
        _ = (π : B) * 1 := by simp
    have hunitpow : IsUnit ((π : B) ^ (e - 1)) :=
      isUnit_iff_exists_inv'.mpr ⟨a, hpow⟩
    have hunit : IsUnit (π : B) :=
      (isUnit_pow_iff (Nat.sub_ne_zero_of_lt hepos)).mp hunitpow
    exact hπ.not_isUnit hunit
  · refine ⟨e, ?_⟩
    change (Ideal.Quotient.mk J (π : B)) ^ e = 0
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hJ ▸ Ideal.pow_mem_pow hπm e)

/-- In the unramified case the first quotient is exactly the residue field. -/
theorem unramified_first_quotient_is_residue_field
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = 1) :
    Nonempty
      ((vL.valuationSubring ⧸
          (IsLocalRing.maximalIdeal vK.valuationSubring).map
            (algebraMap vK.valuationSubring vL.valuationSubring)) ≃+*
        IsLocalRing.ResidueField vL.valuationSubring) := by
  let A := vK.valuationSubring
  let B := vL.valuationSubring
  let mB := IsLocalRing.maximalIdeal B
  let J : Ideal B := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
  have hJ : J = mB := by
    calc
      J = mB ^ 1 := maximal_ideal_extension_is_power vK vL 1 (by simpa using he)
      _ = mB := pow_one mB
  change Nonempty ((B ⧸ J) ≃+* (B ⧸ mB))
  exact ⟨Ideal.quotEquivOfEq hJ⟩

/-- The nilpotence index of the maximal ideal in `B / π_K B` is `e`. -/
theorem ramification_is_nilpotence_index
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (hepos : 0 < e) :
    let I := Ideal.map
      (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring)))
      (IsLocalRing.maximalIdeal vL.valuationSubring)
    I ^ e = ⊥ ∧ I ^ (e - 1) ≠ ⊥ := by
  let A := vK.valuationSubring
  let B := vL.valuationSubring
  let mA := IsLocalRing.maximalIdeal A
  let mB := IsLocalRing.maximalIdeal B
  let J : Ideal B := mA.map (algebraMap A B)
  let q : B →+* B ⧸ J := Ideal.Quotient.mk J
  let I : Ideal (B ⧸ J) := Ideal.map q mB
  change I ^ e = ⊥ ∧ I ^ (e - 1) ≠ ⊥
  have hJ : J = mB ^ e := maximal_ideal_extension_is_power vK vL e he
  constructor
  · calc
      I ^ e = Ideal.map q (mB ^ e) := by
        dsimp [I]
        rw [Ideal.map_pow]
      _ = Ideal.map q J := congrArg (Ideal.map q) hJ.symm
      _ = ⊥ := Ideal.map_mk_eq_bot_of_le le_rfl
  · intro hzero
    have hmap : Ideal.map q (mB ^ (e - 1)) = ⊥ := by
      rw [Ideal.map_pow]
      exact hzero
    have hle : mB ^ (e - 1) ≤ J := by
      have hle' := (Ideal.map_eq_bot_iff_le_ker q).mp hmap
      simpa only [q, Ideal.mk_ker] using hle'
    have hlt : mB ^ e < mB ^ (e - 1) := by
      simpa [Nat.sub_add_cancel hepos] using
        (Ideal.pow_succ_lt_pow (P := mB)
          (IsDiscreteValuationRing.not_a_field B) (e - 1))
    exact (not_le_of_gt hlt) (hJ ▸ hle)

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02
