import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section03HigherQuotientsAreAdditiveResidueFields

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators

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
  sorry

/-- The hypothesis that an integer is a unit of the valuation ring. -/
def Chapter10IntegerIsUnit
    {L : Type*} [Field L] (A : ValuationSubring L) (m : ℕ) : Prop :=
  IsUnit (m : A)

/-- Prime-to-residue-characteristic powers are automorphisms of principal units. -/
theorem chapter10_principal_unit_power_isomorphism
    {L : Type*} [Field L] (A : ValuationSubring L) (m : ℕ)
    (hm : Chapter10IntegerIsUnit A m)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    ∃ e : chapter10UnitFiltration A 1 ≃* chapter10UnitFiltration A 1,
      ∀ u, e u = u ^ m := by
  sorry

/-- Solving `yᵐ=u` is unique on principal units when `m` is a ring unit. -/
theorem chapter10_principal_unit_power_root_exists_unique
    {L : Type*} [Field L] (A : ValuationSubring L) (m : ℕ)
    (hm : Chapter10IntegerIsUnit A m)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    ∀ u : chapter10UnitFiltration A 1, ∃! y,
      y ^ m = u := by
  sorry

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
    sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
