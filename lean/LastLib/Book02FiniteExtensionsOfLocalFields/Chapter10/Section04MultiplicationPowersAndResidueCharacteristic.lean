import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section03HigherQuotientsAreAdditiveResidueFields
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section01CorrectingAnApproximateRoot

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators Polynomial

/-! ## 10.4. Multiplication, powers, and the residue characteristic -/

/-- First-order power congruence, including the integer-power formulation. -/
theorem chapter10_unit_power_first_order_congruence
    {L : Type*} [Field L] (A : ValuationSubring L) (m : ℤ) (n : ℕ)
    (_hn : 0 < n) (x : A) (hx : x ∈ (IsLocalRing.maximalIdeal A) ^ n)
    (u : Aˣ) (hu : (u : A) = 1 + x) :
    ((u ^ m : Aˣ) : A) - (1 + (m : A) * x) ∈
      (IsLocalRing.maximalIdeal A) ^ (2 * n) := by
  let I : Ideal A := IsLocalRing.maximalIdeal A
  let J : Ideal A := I ^ (2 * n)
  have hx2 : x * x ∈ J := by
    change x * x ∈ I ^ (2 * n)
    rw [show 2 * n = n + n by omega,
      Ideal.IsTwoSided.pow_add (I := I) n n]
    exact Ideal.mul_mem_mul hx hx
  have hsucc (z : ℤ)
      (hz : ((u ^ z : Aˣ) : A) - (1 + (z : A) * x) ∈ J) :
      ((u ^ (z + 1) : Aˣ) : A) - (1 + ((z + 1 : ℤ) : A) * x) ∈ J := by
    have hidentity :
        ((u ^ (z + 1) : Aˣ) : A) - (1 + ((z + 1 : ℤ) : A) * x) =
          (((u ^ z : Aˣ) : A) - (1 + (z : A) * x)) * (u : A) +
            (z : A) * (x * x) := by
      simp only [zpow_add_one, Units.val_mul, Int.cast_add, Int.cast_one]
      rw [hu]
      ring_nf
    rw [hidentity]
    exact J.add_mem
      (by simpa [mul_comm] using J.mul_mem_left (u : A) hz)
      (J.mul_mem_left (z : A) hx2)
  have hpred (z : ℤ)
      (hz : ((u ^ z : Aˣ) : A) - (1 + (z : A) * x) ∈ J) :
      ((u ^ (z - 1) : Aˣ) : A) - (1 + ((z - 1 : ℤ) : A) * x) ∈ J := by
    have hu_inv : ((u⁻¹ : Aˣ) : A) * (u : A) = 1 := u.inv_mul
    have hidentity :
        (((u ^ (z - 1) : Aˣ) : A) -
            (1 + ((z - 1 : ℤ) : A) * x)) * (u : A) =
          (((u ^ z : Aˣ) : A) - (1 + (z : A) * x)) -
            ((z : A) - 1) * (x * x) := by
      simp only [zpow_sub_one, Units.val_mul]
      calc
        (((u ^ z : Aˣ) : A) * ((u⁻¹ : Aˣ) : A) -
            (1 + ((z - 1 : ℤ) : A) * x)) * (u : A) =
            (((u ^ z : Aˣ) : A) * ((u⁻¹ : Aˣ) : A)) * (u : A) -
              (1 + ((z - 1 : ℤ) : A) * x) * (u : A) := by ring
        _ = ((u ^ z : Aˣ) : A) -
              (1 + ((z - 1 : ℤ) : A) * x) * (u : A) := by
          rw [mul_assoc, hu_inv, mul_one]
        _ = (((u ^ z : Aˣ) : A) - (1 + (z : A) * x)) -
              ((z : A) - 1) * (x * x) := by
          rw [hu]
          norm_num [Int.cast_sub]
          ring
    have hprod :
        (((u ^ (z - 1) : Aˣ) : A) -
            (1 + ((z - 1 : ℤ) : A) * x)) * (u : A) ∈ J := by
      rw [hidentity]
      exact J.sub_mem hz (J.mul_mem_left ((z : A) - 1) hx2)
    have htarget :
        ((u ^ (z - 1) : Aˣ) : A) - (1 + ((z - 1 : ℤ) : A) * x) =
          ((u⁻¹ : Aˣ) : A) *
            ((((u ^ (z - 1) : Aˣ) : A) -
              (1 + ((z - 1 : ℤ) : A) * x)) * (u : A)) := by
      calc
        ((u ^ (z - 1) : Aˣ) : A) - (1 + ((z - 1 : ℤ) : A) * x) =
            (((u ^ (z - 1) : Aˣ) : A) -
              (1 + ((z - 1 : ℤ) : A) * x)) * 1 := by rw [mul_one]
        _ = (((u ^ (z - 1) : Aˣ) : A) -
              (1 + ((z - 1 : ℤ) : A) * x)) *
            (((u⁻¹ : Aˣ) : A) * (u : A)) := by rw [hu_inv]
        _ = ((u⁻¹ : Aˣ) : A) *
            ((((u ^ (z - 1) : Aˣ) : A) -
              (1 + ((z - 1 : ℤ) : A) * x)) * (u : A)) := by ring
    rw [htarget]
    exact J.mul_mem_left ((u⁻¹ : Aˣ) : A) hprod
  change ((u ^ m : Aˣ) : A) - (1 + (m : A) * x) ∈ J
  exact Int.induction_on m (by simp)
    (fun i hi => hsucc (i : ℤ) hi)
    (fun i hi => hpred (-(i : ℤ)) hi)

/-- The induced power map on a multiplicative graded layer. -/
noncomputable def chapter10UnitLayerPowerMap
    {L : Type*} [Field L] (A : ValuationSubring L) (m n : ℕ) :
    Chapter10UnitLayerQuotient A n →* Chapter10UnitLayerQuotient A n := by
  let U : Subgroup Aˣ := chapter10UnitFiltration A n
  let V : Subgroup U :=
    (chapter10UnitFiltration A (n + 1)).subgroupOf U
  let f : U →* U :=
    { toFun := fun u => u ^ m
      map_one' := by simp
      map_mul' := by intro u v; simp [mul_pow] }
  exact QuotientGroup.map V V f (by
    intro u hu
    change (u : Aˣ) ^ m ∈ chapter10UnitFiltration A (n + 1)
    exact (chapter10UnitFiltration A (n + 1)).pow_mem hu m)

/- The scalar action on the additive ideal layer is kept explicit so that the
   comparison below does not identify a power map with the identity map. -/
noncomputable def chapter10IdealLayerScalarMap
    {L : Type*} [Field L] (A : ValuationSubring L) (m n : ℕ) :
    Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n →+
      Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n := by
  exact
    { toFun := fun z => (m : A) • z
      map_zero' := by simp
      map_add' := by intro z w; simp [smul_add] }

/-- On a layer, the power map is represented by scalar multiplication by the residue of `m`. -/
theorem chapter10_unit_layer_power_is_residue_scalar
    {L : Type*} [Field L] (A : ValuationSubring L) (m n : ℕ) (hn : 0 < n) :
    ∃ e : Multiplicative
        (Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n) ≃*
        Chapter10UnitLayerQuotient A n,
      ∀ z : Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n,
        e (Multiplicative.ofAdd (chapter10IdealLayerScalarMap A m n z)) =
          chapter10UnitLayerPowerMap A m n (e (Multiplicative.ofAdd z)) := by
  let e := Classical.choice (chapter10_higher_unit_layer_is_additive A n hn)
  refine ⟨e, ?_⟩
  intro z
  change e (Multiplicative.ofAdd ((m : A) • z)) =
    chapter10UnitLayerPowerMap A m n (e (Multiplicative.ofAdd z))
  rw [Nat.cast_smul_eq_nsmul]
  dsimp [chapter10UnitLayerPowerMap]
  change e (Multiplicative.ofAdd z ^ m) = (e (Multiplicative.ofAdd z)) ^ m
  exact map_pow e (Multiplicative.ofAdd z) m

/-- The hypothesis that an integer is a unit of the valuation ring. -/
def Chapter10IntegerIsUnit
    {L : Type*} [Field L] (A : ValuationSubring L) (m : ℕ) : Prop :=
  IsUnit (m : A)

private theorem chapter10_principal_unit_power_root_lift
    {L : Type*} [Field L] (A : ValuationSubring L) (m : ℕ)
    (hm : Chapter10IntegerIsUnit A m)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    ∀ u : chapter10UnitFiltration A 1, ∃! y,
      y ^ m = u := by
  classical
  have hm0 : m ≠ 0 := by
    intro hm0
    subst m
    simp [Chapter10IntegerIsUnit] at hm
  let _ : LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.CompleteDVR A :=
    { toIsDiscreteValuationRing := hDVR
      isAdicComplete' := hcomplete }
  intro u
  let f : A[X] :=
    Polynomial.X ^ m - Polynomial.C ((u : Aˣ) : A)
  have hfa : f.eval (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    have hu := u.property
    change ((u : Aˣ) : A) - 1 ∈
      (IsLocalRing.maximalIdeal A) ^ 1 at hu
    have hu' : ((u : Aˣ) : A) - 1 ∈ IsLocalRing.maximalIdeal A := by
      simpa [pow_one] using hu
    have h := (IsLocalRing.maximalIdeal A).neg_mem hu'
    simpa [f] using h
  have hderiv : f.derivative.eval (1 : A) = (m : A) := by
    simp [f, Polynomial.derivative_X_pow]
  have hunit : IsUnit (f.derivative.eval (1 : A)) := by
    rw [hderiv]
    simpa [Chapter10IntegerIsUnit] using hm
  obtain ⟨y, hyP, hyuniq⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.hensel_simple_root
      f (1 : A) hfa hunit
  rcases hyP with ⟨hy, hycongr⟩
  have hy_pow : y ^ m = ((u : Aˣ) : A) := by
    have hy' : y ^ m - ((u : Aˣ) : A) = 0 := by
      simpa [f] using hy
    exact sub_eq_zero.mp hy'
  have hyunit : IsUnit y := by
    apply (isUnit_pow_iff hm0).mp
    rw [hy_pow]
    exact (u : Aˣ).isUnit
  let v : Aˣ := hyunit.unit
  have hvval : ((v : Aˣ) : A) = y := by
    dsimp [v]
  have hvpow : v ^ m = (u : Aˣ) := by
    apply Units.ext
    change ((v : Aˣ) : A) ^ m = ((u : Aˣ) : A)
    rw [hvval]
    exact hy_pow
  have hvfil : v ∈ chapter10UnitFiltration A 1 := by
    change ((v : Aˣ) : A) - 1 ∈
      (IsLocalRing.maximalIdeal A) ^ 1
    rw [hvval]
    rw [pow_one]
    unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.CongruentModIdeal at hycongr
    exact hycongr
  let yU : chapter10UnitFiltration A 1 := ⟨v, hvfil⟩
  refine ⟨yU, ?_, ?_⟩
  · apply Subtype.ext
    exact hvpow
  · intro z hz
    apply Subtype.ext
    have hzpowU : (z : Aˣ) ^ m = (u : Aˣ) :=
      congrArg Subtype.val hz
    have hzpowA : ((z : Aˣ) : A) ^ m = ((u : Aˣ) : A) :=
      congrArg Units.val hzpowU
    have hzroot : f.eval ((z : Aˣ) : A) = 0 := by
      have hz' : ((z : Aˣ) : A) ^ m - ((u : Aˣ) : A) = 0 :=
        sub_eq_zero.mpr hzpowA
      simpa [f] using hz'
    have hzcongr :
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.CongruentModIdeal
          (IsLocalRing.maximalIdeal A) ((z : Aˣ) : A) 1 := by
      unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.CongruentModIdeal
      have hzfil := z.property
      change ((z : Aˣ) : A) - 1 ∈
        (IsLocalRing.maximalIdeal A) ^ 1 at hzfil
      simpa [pow_one] using hzfil
    have hz_eq : ((z : Aˣ) : A) = y :=
      hyuniq _ ⟨hzroot, hzcongr⟩
    apply Units.ext
    change ((z : Aˣ) : A) = ((v : Aˣ) : A)
    exact hz_eq.trans hvval.symm

/-- Prime-to-residue-characteristic powers are automorphisms of principal units. -/
theorem chapter10_principal_unit_power_isomorphism
    {L : Type*} [Field L] (A : ValuationSubring L) (m : ℕ)
    (hm : Chapter10IntegerIsUnit A m)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    ∃ e : chapter10UnitFiltration A 1 ≃* chapter10UnitFiltration A 1,
      ∀ u, e u = u ^ m := by
  let P : chapter10UnitFiltration A 1 →* chapter10UnitFiltration A 1 :=
    { toFun := fun u => ⟨u ^ m, (chapter10UnitFiltration A 1).pow_mem u.property m⟩
      map_one' := by simp
      map_mul' := by
        intro u v
        simp [mul_pow] }
  have hsurj : Function.Surjective P := by
    intro u
    obtain ⟨y, hy, _hyunique⟩ :=
      chapter10_principal_unit_power_root_lift A m hm hcomplete hDVR u
    refine ⟨y, ?_⟩
    change y ^ m = u
    exact hy
  have hinj : Function.Injective P := by
    intro x y hxy
    obtain ⟨z, _hz, hzunique⟩ :=
      chapter10_principal_unit_power_root_lift A m hm hcomplete hDVR (P x)
    have hx : x ^ m = P x := by
      rfl
    have hy : y ^ m = P x := by
      change y ^ m = x ^ m
      exact hxy.symm
    exact (hzunique x hx).trans (hzunique y hy).symm
  let e := MulEquiv.ofBijective P ⟨hinj, hsurj⟩
  refine ⟨e, ?_⟩
  intro u
  rfl

/-- Solving `yᵐ=u` is unique on principal units when `m` is a ring unit. -/
theorem chapter10_principal_unit_power_root_exists_unique
    {L : Type*} [Field L] (A : ValuationSubring L) (m : ℕ)
    (hm : Chapter10IntegerIsUnit A m)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    ∀ u : chapter10UnitFiltration A 1, ∃! y,
      y ^ m = u := by
  obtain ⟨e, he⟩ :=
    chapter10_principal_unit_power_isomorphism A m hm hcomplete hDVR
  intro u
  refine ⟨e.symm u, ?_, ?_⟩
  · have h := e.apply_symm_apply u
    rw [he] at h
    exact h
  · intro y hy
    apply e.injective
    rw [he, e.apply_symm_apply]
    exact hy

/-- The binomial expansion displays the terms competing in a residue-characteristic power. -/
theorem chapter10_residue_characteristic_binomial_expansion
    {L : Type*} [Field L] (A : ValuationSubring L) (p : ℕ) (x : A) :
    (1 + x) ^ p =
      Finset.sum (Finset.range (p + 1))
        (fun k => (p.choose k : A) * x ^ k) := by
  simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using
    (add_pow x (1 : A) p)

/-- If the residue of `m` vanishes, the first-order map on every layer vanishes. -/
theorem chapter10_residue_characteristic_layer_map_can_vanish
    {L : Type*} [Field L] (A : ValuationSubring L) (m n : ℕ) (hn : 0 < n)
    (hzero : (m : Chapter10ResidueField A) = 0) :
    ∃ f : Chapter10ResidueField A →+ Chapter10ResidueField A,
      (∀ a, f a = (m : Chapter10ResidueField A) * a) ∧
        (∀ a, f a = 0) ∧
        ∀ z : Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n,
          chapter10IdealLayerScalarMap A m n z = 0 := by
  let f : Chapter10ResidueField A →+ Chapter10ResidueField A := {
    toFun := fun a => (m : Chapter10ResidueField A) * a
    map_zero' := by simp
    map_add' := by intro a b; simp [mul_add] }
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a
    rfl
  · intro a
    change (m : Chapter10ResidueField A) * a = 0
    simp [hzero]
  · intro z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    change Submodule.Quotient.mk ((m : A) • y) = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    change (m : A) * (y : A) ∈
      (IsLocalRing.maximalIdeal A) ^ (n + 1)
    have hm : (m : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      simpa using hzero
    have hm1 : (m : A) ∈ (IsLocalRing.maximalIdeal A) ^ 1 := by
      simpa [pow_one] using hm
    have hmul := Ideal.mul_mem_mul hm1 y.property
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    rw [← Ideal.IsTwoSided.pow_add (I := IsLocalRing.maximalIdeal A) 1 n] at hmul
    simpa [Nat.add_comm, hn0] using hmul

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
