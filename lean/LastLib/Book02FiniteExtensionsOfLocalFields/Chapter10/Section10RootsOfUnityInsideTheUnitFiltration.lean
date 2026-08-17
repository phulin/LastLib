import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section02TheFirstQuotient
import Mathlib.Data.Nat.Factorization.Basic

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing

/-! ## 10.10. Roots of unity inside the unit filtration -/

/-- Torsion whose order is a power of the residue characteristic. -/
def Chapter10PowerTorsion
    {G : Type*} [Group G] (p : ℕ) (u : G) : Prop :=
  ∃ r : ℕ, u ^ (p ^ r) = 1

/-- Finite-order torsion in a unit group. -/
def Chapter10FiniteOrderTorsion
    {G : Type*} [Group G] (u : G) : Prop :=
  ∃ m : ℕ, 0 < m ∧ u ^ m = 1

/-- A root of unity in the fraction field has valuation zero. -/
theorem chapter10_field_root_of_unity_is_ring_unit
    {L : Type*} [Field L] (A : ValuationSubring L) (m : ℕ) (hm : 0 < m)
    (ζ : Lˣ) (hζ : (ζ : L) ^ m = 1) :
    ∃ u : Aˣ, Units.map A.subtype.toMonoidHom u = ζ := by
  have hinv_mem_of_mem (x : L) (hx : x ∈ A) (hxm : x ^ m = 1) :
      x⁻¹ ∈ A := by
    have hx0 : x ≠ 0 := by
      intro hx0
      subst x
      simp [hm.ne'] at hxm
    have hpow : x ^ (m - 1) * x = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_iff.mpr hm), hxm]
    have hinv : x⁻¹ = x ^ (m - 1) := by
      apply (mul_right_cancel₀ hx0)
      rw [inv_mul_cancel₀ hx0]
      exact hpow.symm
    rw [hinv]
    exact A.pow_mem hx _
  have hζA : (ζ : L) ∈ A := by
    rcases ValuationSubring.mem_or_inv_mem A (ζ : L) with h | h
    · exact h
    · have hpow : ((ζ : L)⁻¹) ^ m = 1 := by
        rw [inv_pow, hζ, inv_one]
      have h := hinv_mem_of_mem ((ζ : L)⁻¹) h hpow
      simpa using h
  have hζinvA : (ζ : L)⁻¹ ∈ A := hinv_mem_of_mem (ζ : L) hζA hζ
  let a : A := ⟨(ζ : L), hζA⟩
  let b : A := ⟨(ζ : L)⁻¹, hζinvA⟩
  let u : Aˣ :=
    { val := a
      inv := b
      val_inv := by
        apply Subtype.ext
        change (ζ : L) * (ζ : L)⁻¹ = 1
        exact mul_inv_cancel₀ ζ.ne_zero
      inv_val := by
        apply Subtype.ext
        change (ζ : L)⁻¹ * (ζ : L) = 1
        exact inv_mul_cancel₀ ζ.ne_zero }
  refine ⟨u, ?_⟩
  apply Units.ext
  rfl

/-- The characteristic-`p` identity used to detect principal-unit torsion. -/
theorem chapter10_equal_characteristic_p_power_sub_one_identity
    {K : Type*} [Field K] (p r : ℕ) [Fact p.Prime] [CharP K p]
    (x : K) :
    x ^ (p ^ r) - 1 = (x - 1) ^ (p ^ r) := by
  rw [sub_pow_char_pow]
  ring

/-- Prime-to-residue-characteristic roots inject under reduction. -/
theorem chapter10_prime_to_residue_characteristic_roots_reduce_injectively
    {L : Type*} [Field L] (A : ValuationSubring L)
    (m p : ℕ) [Fact p.Prime] [CharP (Chapter10ResidueField A) p]
    (hcoprime : Nat.Coprime m p) :
    Function.Injective (fun u : chapter10RootOfUnitySubgroup A m =>
      chapter10UnitReduction A (u : Aˣ)) := by
  intro u v huv
  apply Subtype.ext
  let z : Aˣ := (u : Aˣ) * (v : Aˣ)⁻¹
  have hu_pow : (u : Aˣ) ^ m = 1 := by
    exact u.property
  have hv_pow : (v : Aˣ) ^ m = 1 := by
    exact v.property
  have hz_pow : z ^ m = 1 := by
    simp [z, mul_pow, hu_pow, hv_pow]
  have hz_red : chapter10UnitReduction A z = 1 := by
    simp [z, huv]
  have hz_red_val : IsLocalRing.residue A (z : A) = 1 := by
    exact congrArg Units.val hz_red
  have hm_unit : IsUnit (m : Chapter10ResidueField A) :=
    (CharP.isUnit_natCast_iff (R := Chapter10ResidueField A)
      (Fact.out : Nat.Prime p)).2
      ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcoprime.symm)
  let S : A := Finset.sum (Finset.range m) (fun i => (z : A) ^ i)
  have hS_res : IsLocalRing.residue A S = (m : Chapter10ResidueField A) := by
    simp [S, hz_red_val]
  have hS_unit : IsUnit S :=
    (IsLocalRing.residue_ne_zero_iff_isUnit S).mp (by
      rw [hS_res]
      exact hm_unit.ne_zero)
  have hz_pow_val : (z : A) ^ m = 1 := congrArg Units.val hz_pow
  have hprod : ((z : A) - 1) * S = 0 := by
    rw [mul_geom_sum, hz_pow_val, sub_self]
  have hz_sub : (z : A) - 1 = 0 := by
    apply hS_unit.mul_right_cancel
    simpa using hprod
  have hz_eq : z = 1 := by
    apply Units.ext
    exact sub_eq_zero.mp hz_sub
  exact mul_inv_eq_one.mp (by simpa [z] using hz_eq)

/-- Roots of residue-characteristic-power order reduce to `1`, hence are principal units. -/
theorem chapter10_residue_characteristic_power_roots_are_principal
    {L : Type*} [Field L] (A : ValuationSubring L)
    (p r : ℕ) [Fact p.Prime] [CharP (Chapter10ResidueField A) p]
    (u : Aˣ) (hu : u ^ (p ^ r) = 1) :
    u ∈ chapter10UnitFiltration A 1 := by
  rw [← chapter10_unit_reduction_kernel A]
  apply MonoidHom.mem_ker.mpr
  apply Units.ext
  change (chapter10UnitReduction A u : Chapter10ResidueField A) = 1
  have hpow :
      (chapter10UnitReduction A u : Chapter10ResidueField A) ^ (p ^ r) = 1 := by
    have h := congrArg (fun z : Aˣ => chapter10UnitReduction A z) hu
    have h' := congrArg
      (fun z : (Chapter10ResidueField A)ˣ => (z : Chapter10ResidueField A)) h
    simpa using h'
  have hsub :
      ((chapter10UnitReduction A u : Chapter10ResidueField A) - 1) ^ (p ^ r) = 0 := by
    rw [sub_pow_char_pow, hpow]
    simp
  have hzero :
      (chapter10UnitReduction A u : Chapter10ResidueField A) - 1 = 0 :=
    (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero)).mp hsub
  exact sub_eq_zero.mp hzero

/-- In the finite-residue mixed-characteristic case, the visible roots are cyclic. -/
theorem chapter10_padic_prime_to_p_roots_are_cyclic
    {L : Type*} [Field L] (A : ValuationSubring L) (p : ℕ)
    [Fact p.Prime] [Fintype (Chapter10ResidueField A)]
    [CharP (Chapter10ResidueField A) p] :
    IsCyclic
      (chapter10RootOfUnitySubgroup A
        (Fintype.card (Chapter10ResidueField A) - 1)) := by
  let q : ℕ := Fintype.card (Chapter10ResidueField A)
  obtain ⟨d, hp, hq⟩ := FiniteField.card (Chapter10ResidueField A) p
  have hq_pos : 0 < q := Fintype.card_pos
  have hq_coprime : Nat.Coprime (q - 1) q :=
    (Nat.coprime_self_sub_left (m := 1) (n := q) (by omega)).2 (by simp)
  have hp_dvd_q : p ∣ q := by
    dsimp [q]
    rw [hq]
    exact dvd_pow_self p d.ne_zero
  have hcoprime : Nat.Coprime (q - 1) p :=
    Nat.Coprime.of_dvd_right hp_dvd_q hq_coprime
  let H : Subgroup Aˣ := chapter10RootOfUnitySubgroup A (q - 1)
  let f : H →* (Chapter10ResidueField A)ˣ :=
    (chapter10UnitReduction A).comp H.subtype
  have hf : Function.Injective f := by
    exact chapter10_prime_to_residue_characteristic_roots_reduce_injectively
      A (q - 1) p hcoprime
  let _ : Finite H := Finite.of_injective f hf
  change IsCyclic H
  infer_instance

/-- Finite-order unit torsion separates into Teichmüller and principal parts. -/
theorem chapter10_finite_order_unit_torsion_decomposes
    {L : Type*} [Field L] (A : ValuationSubring L) (p : ℕ)
    [Fact p.Prime] [Fintype (Chapter10ResidueField A)]
    [CharP (Chapter10ResidueField A) p] [CharZero A]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A)
    (u : Aˣ) (hu : Chapter10FiniteOrderTorsion u) :
    ∃ t : chapter10RootOfUnitySubgroup A
        (Fintype.card (Chapter10ResidueField A) - 1),
      ∃ w : chapter10UnitFiltration A 1,
        u = (t : Aˣ) * (w : Aˣ) ∧
          Chapter10PowerTorsion p (w : Aˣ) := by
  classical
  let q := Fintype.card (Chapter10ResidueField A)
  obtain ⟨s, hs, _hsunique⟩ :=
    chapter10_teichmuller_section_exists_unique A hcomplete hDVR
  rcases hs with ⟨hsred, hspow, hsuniq⟩
  let H : Subgroup Aˣ := chapter10RootOfUnitySubgroup A (q - 1)
  let K : Subgroup Aˣ := chapter10UnitFiltration A 1
  let t : Aˣ → H := fun x =>
    ⟨s (chapter10UnitReduction A x), by
      change (s (chapter10UnitReduction A x)) ^ (q - 1) = 1
      simpa [q] using hspow (chapter10UnitReduction A x)⟩
  have htred (x : Aˣ) :
      chapter10UnitReduction A (t x : Aˣ) = chapter10UnitReduction A x := by
    change chapter10UnitReduction A (s (chapter10UnitReduction A x)) =
      chapter10UnitReduction A x
    exact hsred _
  have w_mem (x : Aˣ) : (t x : Aˣ)⁻¹ * x ∈ K := by
    change (t x : Aˣ)⁻¹ * x ∈ chapter10UnitFiltration A 1
    rw [← chapter10_unit_reduction_kernel A]
    apply MonoidHom.mem_ker.mpr
    change chapter10UnitReduction A ((t x : Aˣ)⁻¹ * x) = 1
    rw [map_mul, map_inv, htred]
    simp
  let w : Aˣ → K := fun x => ⟨(t x : Aˣ)⁻¹ * x, w_mem x⟩
  have hdecomp (x : Aˣ) : x = (t x : Aˣ) * (w x : Aˣ) := by
    simp [w]
  have hinter {x : Aˣ} (hx : x ∈ H) (hy : x ∈ K) : x = 1 := by
    have hred : chapter10UnitReduction A x = 1 := by
      have hker : x ∈ (chapter10UnitReduction A).ker := by
        rw [chapter10_unit_reduction_kernel A]
        exact hy
      exact MonoidHom.mem_ker.mp hker
    change x ^ (q - 1) = 1 at hx
    have hxs := hsuniq (chapter10UnitReduction A x) x rfl hx
    rw [hred] at hxs
    simpa using hxs
  obtain ⟨m, hmpos, hum⟩ := hu
  obtain ⟨r, d, hd, hmd⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.ne_of_gt hmpos) p
      (Fact.out : Nat.Prime p).ne_one
  have htw :
      (t u : Aˣ) ^ m * (w u : Aˣ) ^ m = 1 := by
    calc
      (t u : Aˣ) ^ m * (w u : Aˣ) ^ m =
          ((t u : Aˣ) * (w u : Aˣ)) ^ m := (mul_pow _ _ _).symm
      _ = u ^ m := congrArg (fun z : Aˣ => z ^ m) (hdecomp u).symm
      _ = 1 := hum
  have htm_mem : (t u : Aˣ) ^ m ∈ H := by
    exact H.pow_mem (t u).property m
  have hwm_mem : (w u : Aˣ) ^ m ∈ K := by
    exact K.pow_mem (w u).property m
  have htm_mem_K : (t u : Aˣ) ^ m ∈ K := by
    rw [eq_inv_of_mul_eq_one_left htw]
    exact K.inv_mem hwm_mem
  have htm : (t u : Aˣ) ^ m = 1 := hinter htm_mem htm_mem_K
  have hwm : (w u : Aˣ) ^ m = 1 := by
    simpa [htm] using htw
  have hzd : ((w u : Aˣ) ^ (p ^ r)) ^ d = 1 := by
    calc
      ((w u : Aˣ) ^ (p ^ r)) ^ d =
          (w u : Aˣ) ^ (p ^ r * d) := (pow_mul _ _ _).symm
      _ = (w u : Aˣ) ^ m := by rw [hmd]
      _ = 1 := hwm
  have hwred : chapter10UnitReduction A (w u : Aˣ) = 1 := by
    have hker : (w u : Aˣ) ∈ (chapter10UnitReduction A).ker := by
      rw [chapter10_unit_reduction_kernel A]
      exact (w u).property
    exact MonoidHom.mem_ker.mp hker
  have hzred : chapter10UnitReduction A ((w u : Aˣ) ^ (p ^ r)) = 1 := by
    rw [map_pow, hwred]
    simp
  have hcoprime : Nat.Coprime d p :=
    ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hd).symm
  let z : chapter10RootOfUnitySubgroup A d :=
    ⟨(w u : Aˣ) ^ (p ^ r), hzd⟩
  let zone : chapter10RootOfUnitySubgroup A d :=
    ⟨1, by simp⟩
  have hz : z = zone := by
    apply chapter10_prime_to_residue_characteristic_roots_reduce_injectively
      A d p hcoprime
    change chapter10UnitReduction A ((w u : Aˣ) ^ (p ^ r)) =
      chapter10UnitReduction A (1 : Aˣ)
    rw [hzred]
    simp
  have hpowp : (w u : Aˣ) ^ (p ^ r) = 1 := by
    have hz' := congrArg
      (fun x : chapter10RootOfUnitySubgroup A d => (x : Aˣ)) hz
    simpa [z, zone] using hz'
  refine ⟨t u, w u, hdecomp u, ?_⟩
  exact ⟨r, hpowp⟩

/-- In a field of characteristic `p`, a `p`-power root of unity is `1`. -/
theorem chapter10_equal_characteristic_p_power_root_is_one
    {K : Type*} [Field K] (p r : ℕ) [Fact p.Prime] [CharP K p]
    (x : K) (hx : x ^ (p ^ r) = 1) : x = 1 := by
  have hsub : (x - 1) ^ (p ^ r) = 0 := by
    rw [sub_pow_char_pow, hx]
    simp
  exact sub_eq_zero.mp
    ((pow_eq_zero_iff (pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero)).mp hsub)

/-- Equal-characteristic power-series units have no nontrivial principal `p`-power torsion. -/
theorem chapter10_equal_characteristic_principal_units_have_no_p_power_torsion
    {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (u : (PowerSeries k)ˣ)
    (hu : Chapter10PowerTorsion p u) : u = 1 := by
  let _ : CharP (PowerSeries k) p :=
    charP_of_injective_algebraMap (R := k) (A := PowerSeries k)
      (fun a b h => by
        have h₀ := congrArg (PowerSeries.coeff 0) h
        simpa [PowerSeries.algebraMap_apply] using h₀)
      p
  obtain ⟨r, hr⟩ := hu
  have hpow :
      ((u : PowerSeries k) - 1) ^ (p ^ r) = 0 := by
    rw [sub_pow_char_pow]
    have hru : ((u : PowerSeries k) ^ (p ^ r)) = 1 := by
      simpa using congrArg (fun z : (PowerSeries k)ˣ => (z : PowerSeries k)) hr
    rw [hru]
    simp
  have hzero : (u : PowerSeries k) - 1 = 0 :=
    (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero)).mp hpow
  apply Units.ext
  exact sub_eq_zero.mp hzero

/-- A primitive residue-characteristic-power root in mixed characteristic is principal. -/
theorem chapter10_mixed_characteristic_cyclotomic_roots_are_principal
    {L : Type*} [Field L] (A : ValuationSubring L) (p r : ℕ)
    [Fact p.Prime] [CharP (Chapter10ResidueField A) p]
    (ζ : Aˣ) (hζ : IsPrimitiveRoot (ζ : A) (p ^ r)) :
    ζ ∈ chapter10UnitFiltration A 1 := by
  apply chapter10_residue_characteristic_power_roots_are_principal A p r ζ
  apply Units.ext
  exact hζ.pow_eq_one

/-- The filtration records torsion information not determined by the pair `(e,f)`. -/
def Chapter10UnitTorsionProfile
    {L : Type*} [Field L] (A : ValuationSubring L) (p : ℕ) : Prop :=
  ∃ u : chapter10UnitFiltration A 1,
    (u : Aˣ) ≠ 1 ∧ Chapter10PowerTorsion p (u : Aˣ)

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
