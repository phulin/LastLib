import LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Section02InfiniteDigits
import Mathlib.RingTheory.AdicCompletion.LocalRing

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter08

open Polynomial IsLocalRing
open Filter
open scoped BigOperators Topology

noncomputable section

/-!
# Chapter 8: Inverse limits and digit expansions

This file is deliberately a statement-generation pass. The declarations use Mathlib's
AdicCompletion, ideal quotients, PadicInt, Padic, PowerSeries, and LaurentSeries
where those interfaces match the book. A few predicates package the adic convergence and
digit notation used in the prose.
-/

/-! # Book 1, Chapter 8, Section 8.5: Units and Principal Units
-/

/-! ### 8.5 Units and principal units -/

/-- The subgroup 1 + I ^ n inside the unit group. -/
def Chapter08UnitLayer
    (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ) : Subgroup Aˣ where
  carrier := {u | ((u : Aˣ) : A) - 1 ∈ I ^ n}
  one_mem' := by
    simp
  mul_mem' := by
    intro u v hu hv
    change ((u : A) * (v : A) - 1) ∈ I ^ n
    rw [show (u : A) * (v : A) - 1 =
        (u : A) * ((v : A) - 1) + ((u : A) - 1) by ring]
    exact (I ^ n).add_mem ((I ^ n).mul_mem_left _ hv) hu
  inv_mem' := by
    intro u hu
    change ((↑(u⁻¹) : A) - 1) ∈ I ^ n
    have hwu : (↑(u⁻¹) : A) * (u : A) = 1 := by simp
    have hEq : (↑(u⁻¹) : A) - 1 =
        -(↑(u⁻¹) : A) * ((u : A) - 1) := by
      calc
        (↑(u⁻¹) : A) - 1 = (↑(u⁻¹) : A) - (↑(u⁻¹) : A) * (u : A) := by rw [hwu]
        _ = -(↑(u⁻¹) : A) * ((u : A) - 1) := by ring
    rw [hEq]
    simpa [neg_mul] using
      (I ^ n).neg_mem ((I ^ n).mul_mem_left (↑(u⁻¹) : A) hu)

/-- The first principal-unit group in a local ring. -/
abbrev Chapter08PrincipalUnitGroup
    (A : Type*) [CommRing A] [IsLocalRing A] : Subgroup Aˣ :=
  Chapter08UnitLayer A (IsLocalRing.maximalIdeal A) 1

/-- Reduction of units to units in the residue field. -/
def Chapter08UnitReduction
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Aˣ →* (IsLocalRing.ResidueField A)ˣ :=
  Units.map (IsLocalRing.residue A).toMonoidHom

theorem chapter08_unit_reduction_kernel
    (A : Type*) [CommRing A] [IsLocalRing A] :
    (Chapter08UnitReduction A).ker = Chapter08PrincipalUnitGroup A := by
  classical
  ext u
  constructor
  · intro hu
    change Chapter08UnitReduction A u = 1 at hu
    have hval : IsLocalRing.residue A (u : A) = 1 := by
      have h := congrArg Units.val hu
      simpa [Chapter08UnitReduction] using h
    change ((u : Aˣ) : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ 1
    rw [pow_one]
    rw [← IsLocalRing.residue_eq_zero_iff]
    simpa [map_sub] using (sub_eq_zero.mpr hval)
  · intro hu
    change ((u : Aˣ) : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ 1 at hu
    rw [pow_one] at hu
    have hzero : IsLocalRing.residue A (u : A) - 1 = 0 :=
      (show IsLocalRing.residue A ((u : Aˣ) : A) - 1 = 0 from by
        have hz : IsLocalRing.residue A (((u : Aˣ) : A) - 1) = 0 := by
          exact (IsLocalRing.residue_eq_zero_iff _).2 hu
        simpa [map_sub] using hz)
    have hval : IsLocalRing.residue A (u : A) = 1 := sub_eq_zero.mp hzero
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    change IsLocalRing.residue A (u : A) = 1
    exact hval

-- Reduction gives A^× / U^1 ≅ k^×. -/
theorem chapter08_units_mod_principal_units
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Nonempty ((Aˣ ⧸ Chapter08PrincipalUnitGroup A) ≃*
      (IsLocalRing.ResidueField A)ˣ) := by
  classical
  have hsurj : Function.Surjective (Chapter08UnitReduction A) := by
    exact IsLocalRing.surjective_units_map_of_local_ringHom
      (IsLocalRing.residue A) IsLocalRing.residue_surjective
      (inferInstanceAs (IsLocalHom (IsLocalRing.residue A)))
  exact ⟨QuotientGroup.liftEquiv (Chapter08PrincipalUnitGroup A) hsurj
    (chapter08_unit_reduction_kernel A).symm⟩

/-- The additive residue-field layer represented inside the quotient modulo I^(n+1). -/
def Chapter08IdealLayer
    (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ) :
    AddSubgroup (A ⧸ I ^ (n + 1)) :=
  ((I ^ n).map (Ideal.Quotient.mk (I ^ (n + 1)))).toAddSubgroup

/-- The (n+1)-st unit layer viewed as a subgroup of the n-th layer. -/
def Chapter08UnitLayerIn
    (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ) :
    Subgroup (Chapter08UnitLayer A I n) :=
  (Chapter08UnitLayer A I (n + 1)).comap
    (Chapter08UnitLayer A I n).subtype

/-- The map 1+x ↦ x into the additive layer. -/
def Chapter08UnitLayerToIdealLayer
    (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ)
    (u : Chapter08UnitLayer A I n) : Chapter08IdealLayer A I n := by
  refine ⟨Ideal.Quotient.mk (I ^ (n + 1)) (((u : Aˣ) : A) - 1), ?_⟩
  classical
  change Ideal.Quotient.mk (I ^ (n + 1)) (((u : Aˣ) : A) - 1) ∈
    (I ^ n).map (Ideal.Quotient.mk (I ^ (n + 1)))
  exact Ideal.mem_map_of_mem (Ideal.Quotient.mk (I ^ (n + 1))) u.2

/-! Each multiplicative layer is one copy of the additive residue-field layer. -/
private theorem chapter08_principal_unit_layer_equiv_with_formula
    (A : Type*) [CommRing A] [IsLocalRing A] (I : Ideal A)
    (hI : I = IsLocalRing.maximalIdeal A) (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : Additive
          (Chapter08UnitLayer A I n ⧸ Chapter08UnitLayerIn A I n) ≃+
        Chapter08IdealLayer A I n,
      ∀ u : Chapter08UnitLayer A I n,
        e (QuotientGroup.mk' (Chapter08UnitLayerIn A I n) u) =
          Chapter08UnitLayerToIdealLayer A I n u := by
  classical
  let φ : Additive (Chapter08UnitLayer A I n) →+
      Chapter08IdealLayer A I n :=
    { toFun := fun u =>
        Chapter08UnitLayerToIdealLayer A I n (Additive.toMul u)
      map_zero' := by
        apply Subtype.ext
        change Ideal.Quotient.mk (I ^ (n + 1)) (1 - 1) = 0
        simp
      map_add' := by
        intro u v
        apply Subtype.ext
        change
          Ideal.Quotient.mk (I ^ (n + 1))
              ((((Additive.toMul u : Chapter08UnitLayer A I n) : Aˣ) : A) *
                (((Additive.toMul v : Chapter08UnitLayer A I n) : Aˣ) : A) - 1) =
            Ideal.Quotient.mk (I ^ (n + 1))
                ((((Additive.toMul u : Chapter08UnitLayer A I n) : Aˣ) : A) - 1) +
              Ideal.Quotient.mk (I ^ (n + 1))
                ((((Additive.toMul v : Chapter08UnitLayer A I n) : Aˣ) : A) - 1)
        rw [← map_add]
        apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
        have hpow : I ^ n * I ^ n ≤ I ^ (n + 1) := by
          calc
            I ^ n * I ^ n = I ^ (n + n) :=
              (Ideal.IsTwoSided.pow_add (I := I) n n).symm
            _ ≤ I ^ (n + 1) := Ideal.pow_le_pow_right (by omega)
        have hprod :
            ((((Additive.toMul u : Chapter08UnitLayer A I n) : Aˣ) : A) - 1) *
                ((((Additive.toMul v : Chapter08UnitLayer A I n) : Aˣ) : A) - 1) ∈
              I ^ (n + 1) :=
          hpow (Ideal.mul_mem_mul (Additive.toMul u).property
            (Additive.toMul v).property)
        convert hprod using 1; ring }
  let ψ : Chapter08UnitLayer A I n →* Multiplicative (Chapter08IdealLayer A I n) :=
    AddMonoidHom.toMultiplicativeRight φ
  have hker : ψ.ker = Chapter08UnitLayerIn A I n := by
    ext u
    constructor
    · intro hu
      change φ (Additive.ofMul u) = 0 at hu
      have hq :
          Ideal.Quotient.mk (I ^ (n + 1)) (((u : Aˣ) : A) - 1) = 0 := by
        have h := congrArg Subtype.val hu
        simpa [φ, Chapter08UnitLayerToIdealLayer] using h
      change ((u : Aˣ) : A) - 1 ∈ I ^ (n + 1)
      exact Ideal.Quotient.eq_zero_iff_mem.mp hq
    · intro hu
      change ((u : Aˣ) : A) - 1 ∈ I ^ (n + 1) at hu
      apply MonoidHom.mem_ker.mpr
      change φ (Additive.ofMul u) = 0
      apply Subtype.ext
      change Ideal.Quotient.mk (I ^ (n + 1)) (((u : Aˣ) : A) - 1) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hu
  have hsurj : Function.Surjective ψ := by
    intro z
    let q : Chapter08IdealLayer A I n := Multiplicative.toAdd z
    obtain ⟨r, hr, hqr⟩ :=
      (Ideal.mem_map_iff_of_surjective
        (Ideal.Quotient.mk (I ^ (n + 1))) Ideal.Quotient.mk_surjective).1 q.2
    have hrI : r ∈ I := by
      have hp : I ^ n ≤ I := by
        simpa [pow_one] using (Ideal.pow_le_pow_right (I := I) hn)
      exact hp hr
    have hrmax : r ∈ IsLocalRing.maximalIdeal A := by
      rw [← hI]
      exact hrI
    have hnegmax : -r ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.maximalIdeal A).neg_mem hrmax
    have hneg : -r ∈ nonunits A :=
      (IsLocalRing.mem_maximalIdeal (-r)).1 hnegmax
    have hu : IsUnit (1 + r) := by
      have h := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-r) hneg
      convert h using 1; ring
    let w : Aˣ := hu.unit
    have hw : (w : A) - 1 = r := by
      dsimp [w]
      ring
    have hwmem : (w : A) - 1 ∈ I ^ n := by
      rw [hw]
      exact hr
    let u : Chapter08UnitLayer A I n := ⟨w, hwmem⟩
    have hφq : φ (Additive.ofMul u) = q := by
      apply Subtype.ext
      change Ideal.Quotient.mk (I ^ (n + 1)) (((u : Aˣ) : A) - 1) = q.1
      have huw : ((u : Aˣ) : A) - 1 = r := by
        simpa [u] using hw
      rw [huw, hqr]
    refine ⟨u, ?_⟩
    change φ (Additive.ofMul u) = q
    exact hφq
  let eMul := QuotientGroup.liftEquiv (Chapter08UnitLayerIn A I n)
    hsurj hker.symm
  let e : Additive
        (Chapter08UnitLayer A I n ⧸ Chapter08UnitLayerIn A I n) ≃+
      Chapter08IdealLayer A I n := MulEquiv.toAdditiveLeft eMul
  refine ⟨e, ?_⟩
  intro u
  change Multiplicative.toAdd
      (eMul (QuotientGroup.mk' (Chapter08UnitLayerIn A I n) u)) =
    φ (Additive.ofMul u)
  simp [eMul, ψ, φ]

theorem chapter08_principal_unit_layer_quotient
    (A : Type*) [CommRing A] [IsLocalRing A] (I : Ideal A)
    (hI : I = IsLocalRing.maximalIdeal A) (n : ℕ) (hn : 1 ≤ n) :
    Nonempty
      (Additive
      (Chapter08UnitLayer A I n ⧸ Chapter08UnitLayerIn A I n) ≃+
        Chapter08IdealLayer A I n) := by
  classical
  obtain ⟨e, he⟩ :=
    chapter08_principal_unit_layer_equiv_with_formula A I hI n hn
  exact ⟨e⟩

theorem chapter08_principal_unit_layer_formula
    (A : Type*) [CommRing A] [IsLocalRing A] (I : Ideal A)
    (hI : I = IsLocalRing.maximalIdeal A) (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : Additive
          (Chapter08UnitLayer A I n ⧸ Chapter08UnitLayerIn A I n) ≃+
        Chapter08IdealLayer A I n,
      ∀ u : Chapter08UnitLayer A I n,
        e (QuotientGroup.mk' (Chapter08UnitLayerIn A I n) u) =
          Chapter08UnitLayerToIdealLayer A I n u := by
  classical
  exact chapter08_principal_unit_layer_equiv_with_formula A I hI n hn

/-- Partial products of principal units in the adic completion. -/
def Chapter08PrincipalUnitPartialProduct
    {A : Type*} [CommRing A] (I : Ideal A) (a : ℕ → A) (m : ℕ) :
    AdicCompletion I A :=
  ∏ i ∈ Finset.range m, (1 + algebraMap A (AdicCompletion I A) (a i))

def Chapter08PrincipalUnitProductConverges
    {A : Type*} [CommRing A] (I : Ideal A) (a : ℕ → A)
    (x : AdicCompletion I A) : Prop :=
  (∀ i : ℕ, a i ∈ I) ∧
    Chapter08AdicConverges I (Chapter08PrincipalUnitPartialProduct I a) x

-- Infinite products of principal units converge when a_n tends to zero adically. -/
theorem chapter08_infinite_principal_unit_product_converges
    {A : Type*} [CommRing A]
    (I : Ideal A) (a : ℕ → A)
    (hprincipal : ∀ i : ℕ, a i ∈ I)
    (htends : Chapter08AdicTendsToZero I a) :
    ∃ x : AdicCompletion I A, Chapter08PrincipalUnitProductConverges I a x := by
  classical
  choose b hb using htends
  let N : ℕ → ℕ := fun n =>
    Nat.rec (b 0) (fun k q => max (q + 1) (max (b (k + 1)) q)) n
  have hN_succ (n : ℕ) :
      N (n + 1) = max (N n + 1) (max (b (n + 1)) (N n)) := by
    rfl
  have hNb : ∀ n : ℕ, b n ≤ N n := by
    intro n
    induction n with
    | zero => simp [N]
    | succ n ih =>
        rw [hN_succ]
        exact (le_max_left _ _).trans (le_max_right _ _)
  have hNinc : ∀ n : ℕ, N n < N (n + 1) := by
    intro n
    rw [hN_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  let P : ℕ → A := fun m =>
    ∏ i ∈ Finset.range m, (1 + a i)
  have hPdiff : ∀ (n l m : ℕ), N n ≤ l → l ≤ m →
      P m - P l ∈ I ^ n := by
    intro n l m hNl hlm
    induction m, hlm using Nat.le_induction with
    | base => simp
    | succ m hlm ih =>
        have ham : a m ∈ I ^ n := hb n m
          ((hNb n).trans (hNl.trans hlm))
        have hident : P (m + 1) - P l =
            (P m - P l) * (1 + a m) + P l * a m := by
          rw [show P (m + 1) = P m * (1 + a m) by
            simp [P, Finset.prod_range_succ]]
          ring
        rw [hident]
        exact (I ^ n).add_mem ((I ^ n).mul_mem_right _ ih)
          ((I ^ n).mul_mem_left _ ham)
  let s : ℕ → A := fun n => P (N n)
  have hs : ∀ n : ℕ,
      s n ≡ s (n + 1) [SMOD (I ^ n • (⊤ : Submodule A A))] := by
    intro n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have h := hPdiff n (N n) (N (n + 1)) (le_rfl) (hNinc n).le
    simpa [s, sub_eq_add_neg] using (I ^ n).neg_mem h
  let c : AdicCompletion.AdicCauchySequence I A :=
    AdicCompletion.AdicCauchySequence.mk I A s hs
  let x : AdicCompletion I A := AdicCompletion.mk I A c
  refine ⟨x, hprincipal, ?_⟩
  intro n
  refine ⟨N n, fun m hm => ?_⟩
  have hquot : Ideal.Quotient.mk (I ^ n) (P m) =
      Ideal.Quotient.mk (I ^ n) (P (N n)) :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
      (hPdiff n (N n) m (le_rfl) hm)
  calc
    AdicCompletion.evalₐ I n
        (Chapter08PrincipalUnitPartialProduct I a m) =
        Ideal.Quotient.mk (I ^ n) (P m) := by
          simp [Chapter08PrincipalUnitPartialProduct, P]
    _ = Ideal.Quotient.mk (I ^ n) (P (N n)) := hquot
    _ = AdicCompletion.evalₐ I n x := by
      simp [x, c, s]

/-- Separating the valuation leaves a unit times a power of a uniformizer. -/
theorem chapter08_dvr_unit_power_separation
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (hπ : Irreducible π) {x : A} (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ u : Aˣ, x = (u : A) * π ^ n := by
  classical
  exact IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter08
