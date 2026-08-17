import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Dependencies
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section01CorrectingAnApproximateRoot
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.RootsOfUnity.Basic

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing
open scoped Polynomial

/-! ## 10.2. The first quotient -/

/-- Reduction on the ring-of-integers unit group is surjective. -/
theorem chapter10_unit_reduction_surjective
    {L : Type*} [Field L] (A : ValuationSubring L) :
    Function.Surjective (chapter10UnitReduction A) := by
  exact IsLocalRing.surjective_units_map_of_local_ringHom
    (IsLocalRing.residue A) IsLocalRing.residue_surjective
    (inferInstanceAs (IsLocalHom (IsLocalRing.residue A)))

/-- The kernel of unit reduction is exactly the first principal-unit group. -/
theorem chapter10_unit_reduction_kernel
    {L : Type*} [Field L] (A : ValuationSubring L) :
    (chapter10UnitReduction A).ker = chapter10UnitFiltration A 1 := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.chapter08_unit_reduction_kernel A

/-- The first unit quotient is the multiplicative group of the residue field. -/
theorem chapter10_first_unit_quotient_equiv_residue_units
    {L : Type*} [Field L] (A : ValuationSubring L) :
    Nonempty
      ((Chapter10UnitRingQuotient A 1) ≃*
        (Chapter10ResidueField A)ˣ) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.chapter08_units_mod_principal_units A

/-- Units whose order divides a specified exponent. -/
abbrev chapter10RootOfUnitySubgroup
    {L : Type*} [Field L] (A : ValuationSubring L) (m : ℕ) : Subgroup Aˣ :=
  rootsOfUnity m A

/-- In a finite residue field, every nonzero root of the Teichmüller
polynomial is simple. -/
theorem chapter10_teichmuller_residue_roots_are_simple
    {L : Type*} [Field L] (A : ValuationSubring L)
    [Fintype (Chapter10ResidueField A)]
    (a : Chapter10ResidueField A)
    (ha : a ≠ 0)
    (_hroot : a ^ (Fintype.card (Chapter10ResidueField A) - 1) = 1) :
    (Polynomial.derivative
      (Polynomial.X ^ (Fintype.card (Chapter10ResidueField A) - 1) -
        Polynomial.C 1)).eval a ≠ 0 := by
  have hcard : 1 ≤ Fintype.card (Chapter10ResidueField A) :=
    Fintype.card_pos
  have hcoef :
      ((Fintype.card (Chapter10ResidueField A) - 1 : ℕ) :
        Chapter10ResidueField A) = -1 := by
    rw [Nat.cast_sub hcard, FiniteField.cast_card_eq_zero]
    simp
  simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
    Polynomial.derivative_C, sub_zero, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, hcoef]
  exact mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero _ ha)

/-- A multiplicative residue section with the simple-root lifting property. -/
def Chapter10TeichmullerSectionSpec
    {L : Type*} [Field L] (A : ValuationSubring L) (q : ℕ) : Prop :=
  ∃ s : (Chapter10ResidueField A)ˣ →* Aˣ,
    (∀ a, chapter10UnitReduction A (s a) = a) ∧
      (∀ a, (s a) ^ (q - 1) = 1) ∧
      (∀ a u, chapter10UnitReduction A u = a →
        u ^ (q - 1) = 1 → u = s a)

/-- Existence and uniqueness of Teichmüller lifts over a finite residue field. -/
theorem chapter10_teichmuller_section_exists_unique
    {L : Type*} [Field L] (A : ValuationSubring L)
    [Fintype (Chapter10ResidueField A)]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    ∃! s : (Chapter10ResidueField A)ˣ →* Aˣ,
      (∀ a, chapter10UnitReduction A (s a) = a) ∧
      (∀ a, (s a) ^ (Fintype.card (Chapter10ResidueField A) - 1) = 1) ∧
        (∀ a u, chapter10UnitReduction A u = a →
          u ^ (Fintype.card (Chapter10ResidueField A) - 1) = 1 → u = s a) := by
  classical
  let q := Fintype.card (Chapter10ResidueField A)
  let f : A[X] := Polynomial.X ^ (q - 1) - Polynomial.C 1
  let _ : LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.CompleteDVR A :=
    { toIsDiscreteValuationRing := hDVR
      isAdicComplete' := hcomplete }
  have lift (a : (Chapter10ResidueField A)ˣ) :
      ∃ y : A, y ^ (q - 1) = 1 ∧
        IsLocalRing.residue A y = a ∧
          ∀ z : A, z ^ (q - 1) = 1 →
            IsLocalRing.residue A z = a → z = y := by
    obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective (a : Chapter10ResidueField A)
    have ha₀' : IsLocalRing.residue A a₀ = (a : Chapter10ResidueField A) := by
      change (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) a₀ =
        (a : Chapter10ResidueField A)
      exact ha₀
    have ha_pow : (a : Chapter10ResidueField A) ^ (q - 1) = 1 := by
      exact FiniteField.pow_card_sub_one_eq_one (a : Chapter10ResidueField A)
        (Units.ne_zero a)
    have hrootres : (f.map (IsLocalRing.residue A)).eval
        (a : Chapter10ResidueField A) = 0 := by
      simp [f, ha_pow]
    have hfa : f.eval a₀ ∈ IsLocalRing.maximalIdeal A := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change IsLocalRing.residue A (f.eval a₀) = 0
      rw [← Polynomial.eval_map_apply]
      rw [ha₀']
      exact hrootres
    have hsimple := chapter10_teichmuller_residue_roots_are_simple A
      (a : Chapter10ResidueField A) (Units.ne_zero a) ha_pow
    have hderivres : IsLocalRing.residue A (f.derivative.eval a₀) ≠ 0 := by
      rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map, ha₀']
      simpa [f] using hsimple
    have hunit : IsUnit (f.derivative.eval a₀) := by
      apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
      exact hderivres
    obtain ⟨y, ⟨hy, hycongr⟩, hyuniq⟩ :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.hensel_simple_root
        f a₀ hfa hunit
    have hypow : y ^ (q - 1) = 1 := by
      have hy' : y ^ (q - 1) - 1 = 0 := by simpa [f] using hy
      exact sub_eq_zero.mp hy'
    have hyres : IsLocalRing.residue A y = a := by
      have hya₀ : IsLocalRing.residue A y = IsLocalRing.residue A a₀ := by
        apply sub_eq_zero.mp
        rw [← map_sub]
        apply (IsLocalRing.residue_eq_zero_iff _).2
        exact hycongr
      exact hya₀.trans ha₀'
    refine ⟨y, hypow, hyres, ?_⟩
    intro z hzpow hzres
    apply hyuniq z
    refine ⟨?_, ?_⟩
    · have hz' : z ^ (q - 1) - 1 = 0 := by
        simpa [f] using (sub_eq_zero.mpr hzpow)
      simpa [f] using hz'
    · unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.CongruentModIdeal
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      simp only [map_sub, hzres, ha₀', sub_self]
  choose y hy hres huniq using
    fun a : (Chapter10ResidueField A)ˣ => lift a
  let rootUnit : (Chapter10ResidueField A)ˣ → Aˣ := fun a =>
    (IsUnit.of_pow_eq_one (hy a)
      (Nat.sub_ne_zero_iff_lt.mpr Fintype.one_lt_card)).unit
  have rootUnit_val (a : (Chapter10ResidueField A)ˣ) :
      ((rootUnit a : Aˣ) : A) = y a := by
    dsimp [rootUnit]
  have rootUnit_red (a : (Chapter10ResidueField A)ˣ) :
      chapter10UnitReduction A (rootUnit a) = a := by
    apply Units.ext
    change IsLocalRing.residue A ((rootUnit a : Aˣ) : A) = a
    rw [rootUnit_val]
    exact hres a
  have rootUnit_pow (a : (Chapter10ResidueField A)ˣ) :
      rootUnit a ^ (q - 1) = 1 := by
    apply Units.ext
    change ((rootUnit a : Aˣ) : A) ^ (q - 1) = 1
    rw [rootUnit_val]
    exact hy a
  have rootUnit_residue (a : (Chapter10ResidueField A)ˣ) :
      IsLocalRing.residue A ((rootUnit a : Aˣ) : A) = a := by
    have h := congrArg Units.val (rootUnit_red a)
    simpa [Chapter10ResidueField, chapter10UnitReduction,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08UnitReduction] using h
  let s : (Chapter10ResidueField A)ˣ →* Aˣ :=
    { toFun := rootUnit
      map_one' := by
        apply Units.ext
        rw [rootUnit_val]
        exact (huniq 1 (1 : A) (by simp) (by simp)).symm
      map_mul' := by
        intro a b
        apply Units.ext
        rw [rootUnit_val]
        apply (huniq (a * b) ((rootUnit a * rootUnit b : Aˣ) : A) ?_ ?_).symm
        · change
            ((((rootUnit a : Aˣ) : A) * ((rootUnit b : Aˣ) : A)) ^ (q - 1)) = 1
          rw [mul_pow]
          have ha : ((rootUnit a : Aˣ) : A) ^ (q - 1) = 1 := by
            simpa using congrArg Units.val (rootUnit_pow a)
          have hb : ((rootUnit b : Aˣ) : A) ^ (q - 1) = 1 := by
            simpa using congrArg Units.val (rootUnit_pow b)
          rw [ha, hb]
          simp
        · change
            IsLocalRing.residue A
                (((rootUnit a : Aˣ) : A) * ((rootUnit b : Aˣ) : A)) =
              (a : Chapter10ResidueField A) * (b : Chapter10ResidueField A)
          rw [map_mul, rootUnit_residue a, rootUnit_residue b] }
  refine ⟨s, ?_, ?_⟩
  · refine ⟨rootUnit_red, ?_, ?_⟩
    · simpa [s] using rootUnit_pow
    · intro a u hua hup
      apply Units.ext
      change (u : A) = y a
      apply huniq a (u : A)
      · exact Units.ext_iff.mp hup
      · have h := congrArg Units.val hua
        simpa [Chapter10ResidueField, chapter10UnitReduction,
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08UnitReduction] using h
  · intro t ht
    apply MonoidHom.ext
    intro a
    apply Units.ext
    change (t a : A) = y a
    have htu : (t a : A) ^ (q - 1) = 1 := by
      exact Units.ext_iff.mp (ht.2.1 a)
    have htr : IsLocalRing.residue A (t a : A) = a := by
      have h := congrArg Units.val (ht.1 a)
      simpa [Chapter10ResidueField, chapter10UnitReduction,
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08UnitReduction] using h
    exact huniq a (t a : A) htu htr

/-- The Teichmüller lift extends by the convention `[0] = 0`. -/
theorem chapter10_teichmuller_zero_extension
    {L : Type*} [Field L] (A : ValuationSubring L)
    (s : (Chapter10ResidueField A)ˣ →* Aˣ)
    (hs : ∀ a, chapter10UnitReduction A (s a) = a) :
    ∃ t : Chapter10ResidueField A → A,
      t 0 = 0 ∧
        (∀ a : (Chapter10ResidueField A)ˣ, t a = (s a : A)) ∧
        ∀ a, a ≠ 0 → IsLocalRing.residue A (t a) = a := by
  classical
  let t : Chapter10ResidueField A → A := fun a =>
    if h : a = 0 then 0 else (s (Units.mk0 a h) : A)
  refine ⟨t, ?_, ?_, ?_⟩
  · simp [t]
  · intro a
    simp [t, Units.ne_zero a]
  · intro a ha
    simp only [t, dif_neg ha]
    simpa [Chapter10ResidueField, chapter10UnitReduction,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08UnitReduction] using
      congrArg Units.val (hs (Units.mk0 a ha))

/-- The finite-residue-field splitting of the unit group. -/
theorem chapter10_teichmuller_unit_splitting
    {L : Type*} [Field L] (A : ValuationSubring L)
    [Fintype (Chapter10ResidueField A)]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    Nonempty
      (Aˣ ≃*
        (chapter10RootOfUnitySubgroup A
            (Fintype.card (Chapter10ResidueField A) - 1) ×
          chapter10UnitFiltration A 1)) := by
  classical
  let q := Fintype.card (Chapter10ResidueField A)
  obtain ⟨s, hs, _hsunique⟩ :=
    chapter10_teichmuller_section_exists_unique A hcomplete hDVR
  rcases hs with ⟨hsred, hspow, hsuniq⟩
  let H : Subgroup Aˣ := chapter10RootOfUnitySubgroup A (q - 1)
  let K : Subgroup Aˣ := chapter10UnitFiltration A 1
  change Nonempty (Aˣ ≃* H × K)
  let t : Aˣ →* H :=
    { toFun := fun u =>
        ⟨s (chapter10UnitReduction A u), by
          change (s (chapter10UnitReduction A u)) ^ (q - 1) = 1
          simpa [q] using hspow (chapter10UnitReduction A u)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro u v
        apply Subtype.ext
        simp }
  have htred (u : Aˣ) :
      chapter10UnitReduction A (t u : Aˣ) = chapter10UnitReduction A u := by
    change chapter10UnitReduction A (s (chapter10UnitReduction A u)) =
      chapter10UnitReduction A u
    exact hsred _
  have w_mem (u : Aˣ) : (t u : Aˣ)⁻¹ * u ∈ K := by
    change (t u : Aˣ)⁻¹ * u ∈ chapter10UnitFiltration A 1
    rw [← chapter10_unit_reduction_kernel A]
    apply MonoidHom.mem_ker.mpr
    change chapter10UnitReduction A ((t u : Aˣ)⁻¹ * u) = 1
    rw [map_mul, map_inv, htred]
    simp
  let w : Aˣ →* K :=
    { toFun := fun u => ⟨(t u : Aˣ)⁻¹ * u, w_mem u⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro u v
        apply Subtype.ext
        change (t (u * v) : Aˣ)⁻¹ * (u * v) =
          ((t u : Aˣ)⁻¹ * u) * ((t v : Aˣ)⁻¹ * v)
        rw [map_mul]
        change (((t u : Aˣ) * (t v : Aˣ))⁻¹ * (u * v)) =
          ((t u : Aˣ)⁻¹ * u) * ((t v : Aˣ)⁻¹ * v)
        group
        ac_rfl }
  let e : Aˣ ≃* H × K :=
    { toFun := fun u => (t u, w u)
      invFun := fun x => (x.1 : Aˣ) * (x.2 : Aˣ)
      left_inv := by
        intro u
        change (t u : Aˣ) * (w u : Aˣ) = u
        simp [w]
      right_inv := by
        intro x
        have hx2red : chapter10UnitReduction A (x.2 : Aˣ) = 1 := by
          have hx2ker : (x.2 : Aˣ) ∈ (chapter10UnitReduction A).ker := by
            rw [chapter10_unit_reduction_kernel A]
            change (x.2 : Aˣ) ∈ K
            exact x.2.property
          exact MonoidHom.mem_ker.mp hx2ker
        have hprodred :
            chapter10UnitReduction A ((x.1 : Aˣ) * (x.2 : Aˣ)) =
              chapter10UnitReduction A (x.1 : Aˣ) := by
          rw [map_mul, hx2red, mul_one]
        have hx1pow : (x.1 : Aˣ) ^ (q - 1) = 1 := by
          exact x.1.property
        have htprod :
            (t ((x.1 : Aˣ) * (x.2 : Aˣ)) : Aˣ) = (x.1 : Aˣ) := by
          change s (chapter10UnitReduction A ((x.1 : Aˣ) * (x.2 : Aˣ))) =
            (x.1 : Aˣ)
          rw [hprodred]
          exact (hsuniq _ _ rfl hx1pow).symm
        apply Prod.ext
        · apply Subtype.ext
          exact htprod
        · apply Subtype.ext
          change
            (t ((x.1 : Aˣ) * (x.2 : Aˣ)) : Aˣ)⁻¹ *
                ((x.1 : Aˣ) * (x.2 : Aˣ)) = (x.2 : Aˣ)
          rw [htprod]
          simp
      map_mul' := by
        intro u v
        apply Prod.ext
        · exact t.map_mul u v
        · exact w.map_mul u v }
  exact ⟨e⟩

/-- A multiplicative residue section is additional choice data. -/
def Chapter10ResidueUnitSection
    {L : Type*} [Field L] (A : ValuationSubring L) : Prop :=
  ∃ s : (Chapter10ResidueField A)ˣ →* Aˣ,
    ∀ a, chapter10UnitReduction A (s a) = a

/-- Not every residue-unit surjection is supplied with a multiplicative section. -/
theorem chapter10_arbitrary_residue_fields_need_not_split_canonically :
    ¬ (∀ (L : Type) [Field L] (A : ValuationSubring L),
      Chapter10ResidueUnitSection A) := by
  intro hall
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let A : ValuationSubring ℚ := (Rat.padicValuation 5).valuationSubring
  rcases hall ℚ A with ⟨s, hs⟩
  have h2 : (2 : ℚ) ∈ A := by
    change (2 : ℚ) ∈ (Rat.padicValuation 5).valuationSubring
    rw [Valuation.mem_valuationSubring_iff]
    apply (Rat.padicValuation_le_one_iff (p := 5)).2
    norm_num
  have h2inv : (2 : ℚ)⁻¹ ∈ A := by
    change (2 : ℚ)⁻¹ ∈ (Rat.padicValuation 5).valuationSubring
    rw [Valuation.mem_valuationSubring_iff]
    apply (Rat.padicValuation_le_one_iff (p := 5)).2
    norm_num
  let u2 : Aˣ :=
    { val := ⟨(2 : ℚ), h2⟩
      inv := ⟨(2 : ℚ)⁻¹, h2inv⟩
      val_inv := by
        apply Subtype.ext
        norm_num
      inv_val := by
        apply Subtype.ext
        norm_num }
  have h5mem : (5 : A) ∈ IsLocalRing.maximalIdeal A := by
    apply (Valuation.mem_maximalIdeal_iff (v := Rat.padicValuation 5)).2
    change Rat.padicValuation 5 (5 : ℚ) < 1
    rw [show (5 : ℚ) = (Int.cast 5 : ℚ) by norm_num,
      Rat.padicValuation_cast]
    apply (Int.padicValuation_lt_one_iff (p := 5)).2
    norm_num
  have h5zero : IsLocalRing.residue A (5 : A) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 h5mem
  let a : (Chapter10ResidueField A)ˣ := chapter10UnitReduction A u2
  have ha_pow : a ^ 4 = 1 := by
    apply Units.ext
    change IsLocalRing.residue A ((u2 : Aˣ) : A) ^ 4 = 1
    change IsLocalRing.residue A ((2 : A) ^ 4) = 1
    have h5zero' : (5 : Chapter10ResidueField A) = 0 := by
      change IsLocalRing.residue A (5 : A) = 0
      exact h5zero
    calc
      IsLocalRing.residue A ((2 : A) ^ 4) = (16 : Chapter10ResidueField A) := by
        change (2 : Chapter10ResidueField A) ^ 4 = 16
        norm_num
      _ = 1 + 3 * 5 := by norm_num
      _ = 1 := by rw [h5zero']; simp
  have h1not : (1 : A) ∉ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.notMem_maximalIdeal).2 isUnit_one
  have h3 : (3 : ℚ) ∈ A := by
    change (3 : ℚ) ∈ (Rat.padicValuation 5).valuationSubring
    rw [Valuation.mem_valuationSubring_iff]
    apply (Rat.padicValuation_le_one_iff (p := 5)).2
    norm_num
  have h3inv : (3 : ℚ)⁻¹ ∈ A := by
    change (3 : ℚ)⁻¹ ∈ (Rat.padicValuation 5).valuationSubring
    rw [Valuation.mem_valuationSubring_iff]
    apply (Rat.padicValuation_le_one_iff (p := 5)).2
    norm_num
  let u3 : Aˣ :=
    { val := ⟨(3 : ℚ), h3⟩
      inv := ⟨(3 : ℚ)⁻¹, h3inv⟩
      val_inv := by
        apply Subtype.ext
        norm_num
      inv_val := by
        apply Subtype.ext
        norm_num }
  have h3not : (3 : A) ∉ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.notMem_maximalIdeal).2 u3.isUnit
  have ha_ne_one : (a : Chapter10ResidueField A) ≠ 1 := by
    intro ha1
    have hred2 : IsLocalRing.residue A (2 : A) = 1 := by
      have h : IsLocalRing.residue A (2 : A) =
          (a : Chapter10ResidueField A) := by
        rfl
      rw [ha1] at h
      exact h
    have hzero : IsLocalRing.residue A ((2 : A) - 1) = 0 := by
      simpa [map_sub] using sub_eq_zero.mpr hred2
    have hmem := (IsLocalRing.residue_eq_zero_iff _).mp hzero
    have hmem' : ¬ IsUnit (1 : A) := by
      convert hmem using 1
      norm_num
    exact hmem' isUnit_one
  have ha_ne_neg_one : (a : Chapter10ResidueField A) ≠ -1 := by
    intro haneg
    have hred2 : IsLocalRing.residue A (2 : A) = -1 := by
      have h : IsLocalRing.residue A (2 : A) =
          (a : Chapter10ResidueField A) := by
        rfl
      rw [haneg] at h
      exact h
    have hzero : IsLocalRing.residue A ((2 : A) - (-1)) = 0 := by
      simpa [map_sub] using sub_eq_zero.mpr hred2
    have hmem := (IsLocalRing.residue_eq_zero_iff _).mp hzero
    have hmem' : ¬ IsUnit (3 : A) := by
      convert hmem using 1
      norm_num
    exact hmem' u3.isUnit
  have hsa_pow : (s a) ^ 4 = 1 := by
    rw [← map_pow, ha_pow]
    simp
  have hvalpow : ((s a : Aˣ) : A) ^ 4 = 1 :=
    Units.ext_iff.mp hsa_pow
  let x : ℚ := (((s a : Aˣ) : A) : ℚ)
  have hxpow : x ^ 4 = 1 := by
    simpa [x] using congrArg (fun z : A => (z : ℚ)) hvalpow
  have hxpm : x = 1 ∨ x = -1 := by
    have hfactor : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by
      nlinarith [hxpow]
    rcases mul_eq_zero.mp hfactor with hminus | hplus
    · have hsq : x ^ 2 = 1 := by nlinarith
      have hfactor' : (x - 1) * (x + 1) = 0 := by
        nlinarith [hsq]
      rcases mul_eq_zero.mp hfactor' with hone | hneg
      · left
        nlinarith
      · right
        nlinarith
    · exfalso
      nlinarith [sq_nonneg x]
  have hred_sa : IsLocalRing.residue A ((s a : Aˣ) : A) =
      (a : Chapter10ResidueField A) := by
    have h := congrArg Units.val (hs a)
    simpa [Chapter10ResidueField, chapter10UnitReduction,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08UnitReduction] using h
  rcases hxpm with hx | hx
  · have hsa_one : ((s a : Aˣ) : A) = 1 := by
      apply Subtype.ext
      simpa [x] using hx
    rw [hsa_one] at hred_sa
    exact ha_ne_one hred_sa.symm
  · have hsa_neg_one : ((s a : Aˣ) : A) = -1 := by
      apply Subtype.ext
      simpa [x] using hx
    rw [hsa_neg_one] at hred_sa
    exact ha_ne_neg_one hred_sa.symm

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
