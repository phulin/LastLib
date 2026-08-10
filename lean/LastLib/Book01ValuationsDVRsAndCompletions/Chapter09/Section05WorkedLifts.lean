import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section04HenselianLocalRings

namespace LastLib.Book01ValuationsDVRsAndCompletions
namespace Chapter09

universe u uK uL uΓ uA uH uC uI

open scoped BigOperators Polynomial WithZeroTopology
open Ideal IsLocalRing Polynomial

noncomputable section

local instance chapter09FactPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance chapter09FactPrime2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩

/-! # Chapter 9: Hensel lifting

This file is a statement-generation pass for Chapter 9 of Book 1.  The
declarations deliberately keep the hypotheses visible: in particular, a
complete DVR means adic completeness, while the valuation form is stated for
an arbitrary additive valuation.
-/

/-! # Book 1, Chapter 9, Section 9.5: Worked Lifts
-/

/-! ## 9.5 Worked lifts -/

/-- A unit has a square residue in `𝔽_p` when its residue is a square. -/
def PadicUnitResidueSquare (p : ℕ) [Fact p.Prime] (u : ℤ_[p]) : Prop :=
  IsUnit u ∧ ∃ z : ZMod p, z ^ 2 = PadicInt.toZMod u

/-- At odd `p`, the derivative of `X²-u` is a unit at every unit approximation. -/
theorem odd_padic_square_derivative_is_unit (p : ℕ) [Fact p.Prime]
    (hpodd : p ≠ 2) (a₀ : ℤ_[p]) (ha₀ : IsUnit a₀) :
    IsUnit ((2 : ℤ_[p]) * a₀) := by
  have hp2 : p.Coprime 2 := by
    apply (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr
    intro hdiv
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdiv with h | h
    · exact (Fact.out : Nat.Prime p).ne_one h
    · exact hpodd h
  have htwo : IsUnit (2 : ℤ_[p]) := by
    apply PadicInt.isUnit_iff.mpr
    exact PadicInt.norm_natCast_eq_one_iff.mpr hp2
  exact htwo.mul ha₀

/-- For odd `p`, a p-adic unit is a square exactly when its residue is a square. -/
theorem odd_padic_unit_square_iff_residue_square (p : ℕ) [Fact p.Prime]
    (hpodd : p ≠ 2) (u : ℤ_[p]) (hu : IsUnit u) :
    (∃ a : ℤ_[p], a ^ 2 = u) ↔
      ∃ z : ZMod p, z ^ 2 = PadicInt.toZMod u := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨PadicInt.toZMod a, ?_⟩
    simpa only [map_pow] using congrArg (PadicInt.toZMod (p := p)) ha
  · rintro ⟨z, hz⟩
    obtain ⟨a₀, ha₀⟩ := ZMod.ringHom_surjective PadicInt.toZMod z
    have ha₀unit : IsUnit a₀ := by
      apply IsLocalRing.notMem_maximalIdeal.mp
      intro ha₀m
      have hz0 : z = 0 := by
        rw [← ha₀]
        rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
        exact ha₀m
      have hu0 : PadicInt.toZMod u = 0 := by simpa [hz0] using hz.symm
      have hum : u ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
        rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
        exact hu0
      exact (notMem_maximalIdeal.mpr hu) hum
    have hmem : a₀ ^ 2 - u ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
      simp [map_sub, map_pow, ha₀, hz]
    have herr : ‖a₀ ^ 2 - u‖ < 1 := by
      rw [PadicInt.maximalIdeal_eq_span_p] at hmem
      rw [Ideal.mem_span_singleton] at hmem
      exact (PadicInt.norm_lt_one_iff_dvd _).mpr hmem
    have hder : IsUnit ((quadraticPolynomial u).derivative.eval a₀) := by
      have heval : (quadraticPolynomial u).derivative.eval a₀ =
          (2 : ℤ_[p]) * a₀ := by
        simp only [quadraticPolynomial, derivative_sub, derivative_X_pow,
          derivative_C, eval_mul, eval_C, eval_X, Nat.cast_ofNat,
          eval_pow, sub_zero]
        norm_num
      rw [heval]
      exact odd_padic_square_derivative_is_unit p hpodd a₀ ha₀unit
    have hnorm : ‖(quadraticPolynomial u).aeval a₀‖ <
        ‖(quadraticPolynomial u).derivative.aeval a₀‖ ^ 2 := by
      have hdernorm : ‖(quadraticPolynomial u).derivative.aeval a₀‖ = 1 := by
        simpa [aeval_def, eval₂_at_apply] using (PadicInt.isUnit_iff.mp hder)
      calc
        ‖(quadraticPolynomial u).aeval a₀‖ = ‖a₀ ^ 2 - u‖ := by
          simp [quadraticPolynomial, aeval_def]
        _ < 1 := herr
        _ = ‖(quadraticPolynomial u).derivative.aeval a₀‖ ^ 2 := by
          rw [hdernorm]
          norm_num
    obtain ⟨a, ha, -, -, -⟩ := hensels_lemma hnorm
    refine ⟨a, ?_⟩
    have ha' : a ^ 2 - u = 0 := by
      simpa [quadraticPolynomial, aeval_def, eval₂_at_apply] using ha
    exact sub_eq_zero.mp ha'

/-- A chosen square residue root has a unique p-adic square-root lift. -/
theorem odd_padic_square_simple_lift (p : ℕ) [Fact p.Prime]
    (hpodd : p ≠ 2) (u a₀ : ℤ_[p]) (hu : IsUnit u)
    (hroot : (PadicInt.toZMod a₀) ^ 2 = PadicInt.toZMod u) :
    ∃! a : ℤ_[p], a ^ 2 = u ∧ PadicInt.toZMod a = PadicInt.toZMod a₀ := by
  have ha₀unit : IsUnit a₀ := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro ha₀m
    have hz0 : PadicInt.toZMod a₀ = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
      exact ha₀m
    have hum : u ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
      simpa [hz0] using hroot.symm
    exact (notMem_maximalIdeal.mpr hu) hum
  have hmem : a₀ ^ 2 - u ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
    simp [map_sub, map_pow, hroot]
  have herr : ‖a₀ ^ 2 - u‖ < 1 := by
    rw [PadicInt.maximalIdeal_eq_span_p] at hmem
    rw [Ideal.mem_span_singleton] at hmem
    exact (PadicInt.norm_lt_one_iff_dvd _).mpr hmem
  have hder : IsUnit ((quadraticPolynomial u).derivative.eval a₀) := by
    have heval : (quadraticPolynomial u).derivative.eval a₀ =
        (2 : ℤ_[p]) * a₀ := by
      simp only [quadraticPolynomial, derivative_sub, derivative_X_pow,
        derivative_C, eval_mul, eval_C, eval_X, Nat.cast_ofNat,
        eval_pow, sub_zero]
      norm_num
    rw [heval]
    exact odd_padic_square_derivative_is_unit p hpodd a₀ ha₀unit
  have hdernorm : ‖(quadraticPolynomial u).derivative.aeval a₀‖ = 1 := by
    simpa [aeval_def, eval₂_at_apply] using (PadicInt.isUnit_iff.mp hder)
  have hnorm : ‖(quadraticPolynomial u).aeval a₀‖ <
      ‖(quadraticPolynomial u).derivative.aeval a₀‖ ^ 2 := by
    calc
      ‖(quadraticPolynomial u).aeval a₀‖ = ‖a₀ ^ 2 - u‖ := by
        simp [quadraticPolynomial, aeval_def]
      _ < 1 := herr
      _ = ‖(quadraticPolynomial u).derivative.aeval a₀‖ ^ 2 := by
        rw [hdernorm]
        norm_num
  obtain ⟨z, hz, hzclose, hzder, hzuniq⟩ := hensels_lemma hnorm
  have hzroot : z ^ 2 = u := by
    have hz' : z ^ 2 - u = 0 := by
      simpa [quadraticPolynomial, aeval_def, eval₂_at_apply] using hz
    exact sub_eq_zero.mp hz'
  have hzclose' : ‖z - a₀‖ < 1 := by
    have hdernorm' : ‖(quadraticPolynomial u).derivative.eval a₀‖ = 1 :=
      PadicInt.isUnit_iff.mp hder
    simpa [aeval_def, eval₂_at_apply, hdernorm'] using hzclose
  have hzres : PadicInt.toZMod z = PadicInt.toZMod a₀ := by
    have hzm : z - a₀ ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
      exact (PadicInt.norm_lt_one_iff_dvd _).mp hzclose'
    have hzero : PadicInt.toZMod (z - a₀) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
      exact hzm
    simpa [map_sub, sub_eq_zero] using hzero
  refine ⟨z, ⟨hzroot, hzres⟩, ?_⟩
  intro b hb
  have hbm : b - a₀ ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
    simp [map_sub, hb.2]
  have hbclose : ‖b - a₀‖ < 1 := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hbm
    exact (PadicInt.norm_lt_one_iff_dvd _).2 hbm
  have hbclose' : ‖b - a₀‖ <
      ‖(quadraticPolynomial u).derivative.aeval a₀‖ := by
    calc
      ‖b - a₀‖ < 1 := hbclose
      _ = ‖(quadraticPolynomial u).derivative.aeval a₀‖ := by
        rw [hdernorm]
  have hbeval : (quadraticPolynomial u).aeval b = 0 := by
    have hb' : b ^ 2 - u = 0 := sub_eq_zero.mpr hb.1
    simpa [quadraticPolynomial, aeval_def, eval₂_at_apply] using hb'
  exact hzuniq b hbeval hbclose'

/-- For odd `p`, the two residue roots give the two square roots overall. -/
theorem odd_padic_square_has_two_roots (p : ℕ) [Fact p.Prime]
    (hpodd : p ≠ 2) (u : ℤ_[p]) (hu : IsUnit u)
    (hres : ∃ z : ZMod p, z ^ 2 = PadicInt.toZMod u) :
    ∃ aPlus aMinus : ℤ_[p],
      aPlus ^ 2 = u ∧ aMinus ^ 2 = u ∧ aPlus ≠ aMinus ∧
        ∀ a : ℤ_[p], a ^ 2 = u → a = aPlus ∨ a = aMinus := by
  obtain ⟨z, hz⟩ := hres
  obtain ⟨a₀, ha₀⟩ := ZMod.ringHom_surjective PadicInt.toZMod z
  have hzroot : (PadicInt.toZMod a₀) ^ 2 = PadicInt.toZMod u := by
    simpa [ha₀] using hz
  obtain ⟨aPlus, hPlus, hPlusuniq⟩ :=
    odd_padic_square_simple_lift p hpodd u a₀ hu hzroot
  have hnegroot : (PadicInt.toZMod (-a₀)) ^ 2 = PadicInt.toZMod u := by
    simpa [map_neg, neg_sq] using hzroot
  obtain ⟨aMinus, hMinus, hMinusuniq⟩ :=
    odd_padic_square_simple_lift p hpodd u (-a₀) hu hnegroot
  have hzunit : IsUnit z := by
    apply isUnit_iff_ne_zero.mpr
    intro hz0
    have hu0 : PadicInt.toZMod u = 0 := by simpa [hz0] using hz.symm
    have hum : u ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
      exact hu0
    exact (notMem_maximalIdeal.mpr hu) hum
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro htwo
    have hpdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp htwo
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hpdiv with h | h
    · exact (Fact.out : Nat.Prime p).ne_one h
    · exact hpodd h
  have hneq : aPlus ≠ aMinus := by
    intro heq
    have hresEq : z = -z := by
      calc
        z = PadicInt.toZMod aPlus := ha₀.symm.trans hPlus.2.symm
        _ = PadicInt.toZMod aMinus := by rw [heq]
        _ = -z := by simpa [ha₀] using hMinus.2
    have hzsum : (2 : ZMod p) * z = 0 := by
      calc
        (2 : ZMod p) * z = z + z := by ring
        _ = (-z) + z := congrArg (fun t : ZMod p => t + z) hresEq
        _ = 0 := neg_add_cancel z
    rcases mul_eq_zero.mp hzsum with h | h
    · exact htwo h
    · exact hzunit.ne_zero h
  refine ⟨aPlus, aMinus, hPlus.1, hMinus.1, hneq, ?_⟩
  intro a ha
  have hprod : (a - aPlus) * (a + aPlus) = 0 := by
    calc
      (a - aPlus) * (a + aPlus) = a ^ 2 - aPlus ^ 2 := by ring
      _ = u - u := by rw [ha, hPlus.1]
      _ = 0 := sub_self u
  rcases mul_eq_zero.mp hprod with hleft | hright
  · exact Or.inl (sub_eq_zero.mp hleft)
  · right
    have hminus_eq : aMinus = -aPlus := by
      exact (hMinusuniq (-aPlus) (by
        constructor
        · simp [hPlus.1]
        · simp [map_neg, hPlus.2])).symm
    rw [hminus_eq]
    exact eq_neg_of_add_eq_zero_left hright

/-- The polynomial and first approximation in the numerical `u=2` example over `ℤ₇`. -/
def padicSevenPolynomial : (ℤ_[7])[X] :=
  quadraticPolynomial (2 : ℤ_[7])

def padicSevenInitialApproximation : ℤ_[7] :=
  3

def padicSevenFirstNewtonApproximation : ℤ_[7] :=
  3 - (7 : ℤ_[7]) * Ring.inverse (6 : ℤ_[7])

/-- The first Newton approximation agrees with `3-7/6`. -/
theorem padicSeven_first_newton_formula :
    padicSevenFirstNewtonApproximation =
      newtonCorrection padicSevenPolynomial padicSevenInitialApproximation := by
  simp [padicSevenFirstNewtonApproximation, padicSevenPolynomial,
    padicSevenInitialApproximation, newtonCorrection, quadraticPolynomial]
  ring_nf

/-- The inverse of six modulo forty-nine is forty-one. -/
theorem inverse_six_mod_49 : (6 : ZMod 49) * 41 = 1 := by
  decide

/-- The first approximation is `10` modulo `49`. -/
theorem padicSeven_first_approximation_mod_49 :
    PadicInt.toZModPow 2 padicSevenFirstNewtonApproximation = (10 : ZMod (7 ^ 2)) := by
  have h6 : IsUnit (6 : ℤ_[7]) := by
    apply PadicInt.isUnit_iff.mpr
    exact PadicInt.norm_natCast_eq_one_iff.mpr (by norm_num)
  have hmapinv :
      PadicInt.toZModPow 2 (Ring.inverse (6 : ℤ_[7])) *
          PadicInt.toZModPow 2 (6 : ℤ_[7]) = 1 := by
    rw [← map_mul, Ring.inverse_mul_cancel _ h6, map_one]
  have h6mod : IsUnit (6 : ZMod (7 ^ 2)) := by
    apply (ZMod.isUnit_iff_coprime 6 (7 ^ 2)).mpr
    norm_num
  have hinvmod :
      PadicInt.toZModPow 2 (Ring.inverse (6 : ℤ_[7])) = (41 : ZMod (7 ^ 2)) := by
    apply h6mod.mul_right_cancel
    calc
      PadicInt.toZModPow 2 (Ring.inverse (6 : ℤ_[7])) * 6 = 1 := by
        have hmap6 : PadicInt.toZModPow 2 (6 : ℤ_[7]) =
            (6 : ZMod (7 ^ 2)) := by
          change PadicInt.toZModPow 2 ((6 : ℕ) : ℤ_[7]) =
            ((6 : ℕ) : ZMod (7 ^ 2))
          exact map_natCast (PadicInt.toZModPow 2) 6
        rw [hmap6] at hmapinv
        exact hmapinv
      _ = (41 : ZMod (7 ^ 2)) * 6 := by
        rw [mul_comm, inverse_six_mod_49]
  unfold padicSevenFirstNewtonApproximation
  rw [map_sub, map_mul, hinvmod]
  change PadicInt.toZModPow 2 (3 : ℤ_[7]) -
      PadicInt.toZModPow 2 (7 : ℤ_[7]) * 41 = (10 : ZMod (7 ^ 2))
  have hmap3 : PadicInt.toZModPow 2 (3 : ℤ_[7]) =
      (3 : ZMod (7 ^ 2)) := by
    change PadicInt.toZModPow 2 ((3 : ℕ) : ℤ_[7]) =
      ((3 : ℕ) : ZMod (7 ^ 2))
    exact map_natCast (PadicInt.toZModPow 2) 3
  have hmap7 : PadicInt.toZModPow 2 (7 : ℤ_[7]) =
      (7 : ZMod (7 ^ 2)) := by
    change PadicInt.toZModPow 2 ((7 : ℕ) : ℤ_[7]) =
      ((7 : ℕ) : ZMod (7 ^ 2))
    exact map_natCast (PadicInt.toZModPow 2) 7
  rw [hmap3, hmap7]
  decide

/-- Indeed `10²=2` modulo `49`. -/
theorem padicSeven_square_mod_49 :
    (10 : ZMod 49) ^ 2 = 2 := by
  decide

/-- The next Newton step has fourth-power precision, reflecting valuation doubling. -/
def padicSevenSecondNewtonApproximation : ℤ_[7] :=
  newtonCorrection padicSevenPolynomial padicSevenFirstNewtonApproximation

def IsRootModuloPower {A : Type*} [CommRing A] (π : A) (f : A[X]) (a : A) (n : ℕ) : Prop :=
  f.eval a ∈ Ideal.span ({π ^ n} : Set A)

/-- The second numerical correction determines the root modulo `7⁴`, not only `7³`. -/
theorem padicSeven_second_newton_precision :
    IsRootModuloPower (7 : ℤ_[7]) padicSevenPolynomial
      padicSevenSecondNewtonApproximation 4 := by
  let hDVR : CompleteDVR ℤ_[7] := {
    toIsDiscreteValuationRing := inferInstance
    isAdicComplete' := inferInstance
  }
  have h6 : IsUnit (6 : ℤ_[7]) := by
    apply PadicInt.isUnit_iff.mpr
    exact PadicInt.norm_natCast_eq_one_iff.mpr (by norm_num)
  have hinv : ‖(Ring.inverse (6 : ℤ_[7]))‖ = 1 := by
    apply PadicInt.isUnit_iff.mp
    exact isUnit_iff_exists_inv.mpr
      ⟨(6 : ℤ_[7]), Ring.inverse_mul_cancel 6 h6⟩
  have hcorr : ‖((7 : ℤ_[7]) * Ring.inverse (6 : ℤ_[7]))‖ < 1 := by
    rw [norm_mul, hinv, mul_one]
    exact PadicInt.norm_natCast_lt_one_iff.mpr (by norm_num)
  have ha₁unit : IsUnit padicSevenFirstNewtonApproximation := by
    apply PadicInt.isUnit_iff.mpr
    have hnorm :
        ‖(padicSevenFirstNewtonApproximation : ℚ_[7])‖ = ‖(3 : ℚ_[7])‖ := by
      apply Padic.norm_eq_of_norm_sub_lt_right
      change ‖((padicSevenFirstNewtonApproximation - 3 : ℤ_[7]) : ℚ_[7])‖ <
        ‖(3 : ℚ_[7])‖
      rw [show padicSevenFirstNewtonApproximation - 3 =
          -((7 : ℤ_[7]) * Ring.inverse (6 : ℤ_[7])) by
        change (3 - (7 : ℤ_[7]) * Ring.inverse (6 : ℤ_[7])) - 3 =
          -((7 : ℤ_[7]) * Ring.inverse (6 : ℤ_[7]))
        ring]
      change ‖-((7 : ℤ_[7]) * Ring.inverse (6 : ℤ_[7]))‖ <
        ‖(3 : ℚ_[7])‖
      rw [norm_neg]
      have h3 : ‖(3 : ℚ_[7])‖ = 1 := by
        exact Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
      exact lt_of_lt_of_le hcorr h3.ge
    change ‖(padicSevenFirstNewtonApproximation : ℚ_[7])‖ = 1
    rw [hnorm]
    have h3 : ‖(3 : ℚ_[7])‖ = 1 := by
      exact Padic.norm_natCast_eq_one_iff.mpr (by norm_num)
    exact h3
  have hderiv : IsUnit
      (padicSevenPolynomial.derivative.eval padicSevenFirstNewtonApproximation) := by
    have heval : padicSevenPolynomial.derivative.eval
        padicSevenFirstNewtonApproximation =
        (2 : ℤ_[7]) * padicSevenFirstNewtonApproximation := by
      simp [padicSevenPolynomial, quadraticPolynomial]
      norm_num
    rw [heval]
    exact odd_padic_square_derivative_is_unit 7 (by norm_num)
      padicSevenFirstNewtonApproximation ha₁unit
  have hroot₂ : padicSevenPolynomial.eval padicSevenFirstNewtonApproximation ∈
      (IsLocalRing.maximalIdeal ℤ_[7]) ^ 2 := by
    have hroot₂' : padicSevenPolynomial.eval padicSevenFirstNewtonApproximation ∈
        Ideal.span ({(7 : ℤ_[7]) ^ 2} : Set ℤ_[7]) := by
      rw [show padicSevenPolynomial.eval padicSevenFirstNewtonApproximation =
          padicSevenFirstNewtonApproximation ^ 2 - (2 : ℤ_[7]) by
        simp [padicSevenPolynomial, quadraticPolynomial]]
      have hmem : padicSevenFirstNewtonApproximation ^ 2 - (2 : ℤ_[7]) ∈
          RingHom.ker (PadicInt.toZModPow 2 : ℤ_[7] →+* ZMod (7 ^ 2)) := by
        rw [RingHom.mem_ker]
        rw [map_sub, map_pow, padicSeven_first_approximation_mod_49,
          padicSeven_square_mod_49]
        rw [show PadicInt.toZModPow 2 (2 : ℤ_[7]) =
            (2 : ZMod (7 ^ 2)) by
          exact map_natCast (PadicInt.toZModPow 2) 2]
        norm_num
      rw [PadicInt.ker_toZModPow] at hmem
      simpa only [Nat.cast_ofNat] using hmem
    simpa [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow] using hroot₂'
  have hroot₄ := @newton_precision_doubles ℤ_[7] _ _ hDVR padicSevenPolynomial
    padicSevenFirstNewtonApproximation 2 hderiv hroot₂
  simpa [IsRootModuloPower, padicSevenSecondNewtonApproximation,
    PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow] using hroot₄

/-- At `p=2`, the derivative of `X²-u` is never a unit at a unit. -/
theorem two_adic_square_derivative_never_unit (a : ℤ_[2]) (ha : IsUnit a) :
    ¬ IsUnit ((2 : ℤ_[2]) * a) := by
  have _ha := ha
  rw [PadicInt.not_isUnit_iff]
  calc
    ‖(2 : ℤ_[2]) * a‖ = ‖(2 : ℤ_[2])‖ * ‖a‖ := norm_mul _ _
    _ ≤ ‖(2 : ℤ_[2])‖ * 1 :=
      mul_le_mul_of_nonneg_left (PadicInt.norm_le_one a) (norm_nonneg _)
    _ = ‖(2 : ℤ_[2])‖ := by simp
    _ < 1 := by
      simpa only [Nat.cast_ofNat] using
        (PadicInt.norm_natCast_lt_one_iff (p := 2) (n := 2)).mpr (dvd_refl 2)

/-- Being congruent to one modulo eight is the strengthened two-adic Newton condition. -/
theorem two_adic_one_mod_eight_gives_newton_condition (u : ℤ_[2])
    (hu : PadicInt.toZModPow 3 u = 1) :
    Padic.addValuation (p := 2) (1 - (u : ℚ_[2])) ≥ (3 : WithTop ℤ) ∧
      Padic.addValuation (p := 2) (2 : ℚ_[2]) = (1 : WithTop ℤ) ∧
      Padic.addValuation (p := 2) (1 - (u : ℚ_[2])) >
      Padic.addValuation (p := 2) (2 : ℚ_[2]) +
          Padic.addValuation (p := 2) (2 : ℚ_[2]) := by
  have hmem : 1 - u ∈ Ideal.span ({(2 : ℤ_[2]) ^ 3} : Set ℤ_[2]) := by
    change 1 - u ∈ Ideal.span ({((2 : ℕ) : ℤ_[2]) ^ 3} : Set ℤ_[2])
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
    simp [hu]
  have hv : Padic.addValuation (p := 2) (1 - (u : ℚ_[2])) ≥
      (3 : WithTop ℤ) := by
    have hcoe : ((1 - u : ℤ_[2]) : ℚ_[2]) = 1 - (u : ℚ_[2]) := by
      norm_num
    by_cases hz : 1 - u = 0
    · rw [← hcoe, hz]
      simp
    · rw [← hcoe, Padic.addValuation.apply (PadicInt.coe_ne_zero.mpr hz),
      PadicInt.valuation_coe]
      have hle := (PadicInt.mem_span_pow_iff_le_valuation
        (1 - u) hz 3).mp hmem
      change (3 : WithTop ℤ) ≤ (PadicInt.valuation (1 - u) : WithTop ℤ)
      exact_mod_cast hle
  have htwo : Padic.addValuation (p := 2) (2 : ℚ_[2]) =
      (1 : WithTop ℤ) := by
    rw [Padic.addValuation.apply (by norm_num), Padic.valuation_ofNat]
    norm_num
  refine ⟨hv, htwo, ?_⟩
  rw [htwo]
  calc
    (2 : WithTop ℤ) < 3 := by exact_mod_cast (show (2 : ℤ) < 3 by norm_num)
    _ ≤ Padic.addValuation (p := 2) (1 - (u : ℚ_[2])) := hv

/-- Every `2`-adic integer congruent to one modulo eight is a square. -/
theorem two_adic_unit_square_of_one_mod_eight (u : ℤ_[2])
    (hu : PadicInt.toZModPow 3 u = 1) :
    ∃ a : ℤ_[2], a ^ 2 = u := by
  have hmem : 1 - u ∈ Ideal.span ({(2 : ℤ_[2]) ^ 3} : Set ℤ_[2]) := by
    change 1 - u ∈ Ideal.span ({((2 : ℕ) : ℤ_[2]) ^ 3} : Set ℤ_[2])
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
    simp [hu]
  have hnormerr : ‖1 - u‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by
    exact (PadicInt.norm_le_pow_iff_mem_span_pow (1 - u) 3).mpr hmem
  have hnormtwo : ‖(2 : ℤ_[2])‖ = (2 : ℝ) ^ (-1 : ℤ) := by
    rw [PadicInt.norm_eq_zpow_neg_valuation (by norm_num)]
    have hval : PadicInt.valuation (2 : ℤ_[2]) = 1 := PadicInt.valuation_p
    rw [hval]
    norm_num
  have hnorm : ‖(quadraticPolynomial u).aeval (1 : ℤ_[2])‖ <
      ‖(quadraticPolynomial u).derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    calc
      ‖(quadraticPolynomial u).aeval (1 : ℤ_[2])‖ = ‖1 - u‖ := by
        simp [quadraticPolynomial, aeval_def]
      _ ≤ (2 : ℝ) ^ (-3 : ℤ) := hnormerr
      _ < ((2 : ℝ) ^ (-1 : ℤ)) ^ 2 := by norm_num
      _ = ‖(quadraticPolynomial u).derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
        have hderiv :
            (quadraticPolynomial u).derivative.aeval (1 : ℤ_[2]) =
              (2 : ℤ_[2]) := by
          simp [quadraticPolynomial, aeval_def]
          norm_num
        rw [hderiv, hnormtwo]
  obtain ⟨a, ha, -, -, -⟩ := hensels_lemma hnorm
  refine ⟨a, ?_⟩
  have ha' : a ^ 2 - u = 0 := by
    simpa [quadraticPolynomial, aeval_def, eval₂_at_apply] using ha
  exact sub_eq_zero.mp ha'

/-- The polynomial and first Newton iterate in the `u=17` two-adic example. -/
def padicTwoSeventeenPolynomial : (ℚ_[2])[X] :=
  quadraticPolynomial (17 : ℚ_[2])

def padicTwoSeventeenFirstNewtonApproximation : ℚ_[2] :=
  1 - ((-16 : ℚ_[2]) / (2 : ℚ_[2]))

/-- For `f=X²-17`, the initial error and derivative have values four and one. -/
theorem padicTwoSeventeen_initial_values :
    Padic.addValuation (p := 2) (padicTwoSeventeenPolynomial.eval 1) = (4 : WithTop ℤ) ∧
      Padic.addValuation (p := 2)
          (padicTwoSeventeenPolynomial.derivative.eval 1) = (1 : WithTop ℤ) := by
  constructor
  · norm_num [padicTwoSeventeenPolynomial, quadraticPolynomial,
      Padic.addValuation, AddValuation.of_apply, Padic.addValuationDef,
      Padic.valuation_intCast]
    have hpv : padicValNat 2 16 = 4 := by
      convert padicValNat_base_pow (p := 2) (by norm_num) 4 using 1
    exact_mod_cast hpv
  · norm_num [padicTwoSeventeenPolynomial, quadraticPolynomial,
      Padic.addValuation, AddValuation.of_apply, Padic.addValuationDef,
      Padic.valuation_intCast]

/-- The first Newton iterate is nine, and its new error is sixty-four of value six. -/
theorem padicTwoSeventeen_first_iterate_and_error :
    padicTwoSeventeenFirstNewtonApproximation = 9 ∧
      padicTwoSeventeenPolynomial.eval padicTwoSeventeenFirstNewtonApproximation = 64 ∧
      Padic.addValuation (p := 2)
          (padicTwoSeventeenPolynomial.eval padicTwoSeventeenFirstNewtonApproximation) =
        (6 : WithTop ℤ) := by
  constructor
  · norm_num [padicTwoSeventeenFirstNewtonApproximation, div_eq_mul_inv]
  constructor
  · norm_num [padicTwoSeventeenFirstNewtonApproximation, padicTwoSeventeenPolynomial,
      quadraticPolynomial, div_eq_mul_inv]
  · norm_num [padicTwoSeventeenFirstNewtonApproximation, padicTwoSeventeenPolynomial,
      quadraticPolynomial, div_eq_mul_inv, Padic.addValuation,
      AddValuation.of_apply, Padic.addValuationDef, Padic.valuation_intCast]
    have hpv : padicValNat 2 64 = 6 := by
      convert padicValNat_base_pow (p := 2) (by norm_num) 6 using 1
    exact_mod_cast hpv

/-- The lifted root has displacement of value three from one, matching the first correction. -/
theorem padicTwoSeventeen_lifted_root_displacement
    : ∃ a : ℚ_[2], padicTwoSeventeenPolynomial.eval a = 0 ∧
      Padic.addValuation (p := 2) (a - 1) = (3 : WithTop ℤ) := by
  let F : (ℤ_[2])[X] := quadraticPolynomial (17 : ℤ_[2])
  have hF : F.aeval (1 : ℤ_[2]) = (-16 : ℤ_[2]) := by
    norm_num [F, quadraticPolynomial, Polynomial.aeval_def, eval₂_at_apply]
  have hFd : F.derivative.aeval (1 : ℤ_[2]) = (2 : ℤ_[2]) := by
    norm_num [F, quadraticPolynomial, Polynomial.aeval_def, eval₂_at_apply]
  have hnorm : ‖F.aeval (1 : ℤ_[2])‖ <
      ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hF, hFd]
    have h16 : (16 : ℤ_[2]) = (2 : ℤ_[2]) ^ 4 := by norm_num
    rw [norm_neg, h16, norm_pow]
    have hnorm2 : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p
    rw [hnorm2]
    norm_num
  obtain ⟨z, hz, hzclose, _, _⟩ :=
    hensels_lemma (p := 2) (F := F) (a := (1 : ℤ_[2])) hnorm
  let a : ℚ_[2] := z
  have ha : padicTwoSeventeenPolynomial.eval a = 0 := by
    have hz' := congrArg (fun x : ℤ_[2] => (x : ℚ_[2])) hz
    have hz'' : (z : ℚ_[2]) ^ 2 - ((17 : ℤ_[2]) : ℚ_[2]) = 0 := by
      simpa [F, quadraticPolynomial, Polynomial.aeval_def, eval₂_at_apply] using hz'
    have h17 : ((17 : ℤ_[2]) : ℚ_[2]) = (17 : ℚ_[2]) := by
      exact PadicInt.coe_natCast 17
    rw [h17] at hz''
    simpa [a, padicTwoSeventeenPolynomial, quadraticPolynomial,
      Polynomial.aeval_def, eval₂_at_apply] using hz''
  have hclose : ‖(z - 1 : ℤ_[2])‖ < (2 : ℝ) ^ (-1 : ℤ) := by
    calc
      ‖(z - 1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ := hzclose
      _ = (2 : ℝ) ^ (-1 : ℤ) := by
        rw [hFd]
        have hnorm2 : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p
        rw [hnorm2]
        norm_num
  have hzsub : z - 1 ≠ 0 := by
    intro hzsub
    have : z = 1 := sub_eq_zero.mp hzsub
    rw [this] at hz
    norm_num [F, quadraticPolynomial, Polynomial.aeval_def, eval₂_at_apply] at hz
  have hnormle : ‖(z - 1 : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-2 : ℤ) := by
    exact (PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one (z - 1) (-1)).mp hclose
  have hzval : (2 : ℕ) ≤ (z - 1).valuation := by
    exact (PadicInt.norm_le_pow_iff_le_valuation (z - 1) hzsub 2).mp hnormle
  have hcast_sub : ((z - 1 : ℤ_[2]) : ℚ_[2]) = a - 1 := by
    simp [a]
  have hval_sub_cast :
      Padic.addValuation (p := 2) (a - 1) =
        (((z - 1).valuation : ℤ) : WithTop ℤ) := by
    rw [← hcast_sub, Padic.addValuation.apply (PadicInt.coe_ne_zero.mpr hzsub),
      PadicInt.valuation_coe]
  have hvalgt : Padic.addValuation (p := 2) (a - 1) > (1 : WithTop ℤ) := by
    rw [hval_sub_cast]
    exact_mod_cast (show (1 : ℕ) < (z - 1).valuation by omega)
  have hfactor : (a - 1) * (a + 1) = (16 : ℚ_[2]) := by
    have ha' : a ^ 2 - (17 : ℚ_[2]) = 0 := by
      simpa [padicTwoSeventeenPolynomial, quadraticPolynomial,
        Polynomial.eval₂_at_apply] using ha
    have ha_sq : a ^ 2 = (17 : ℚ_[2]) := sub_eq_zero.mp ha'
    calc
      (a - 1) * (a + 1) = a ^ 2 - 1 := by ring
      _ = (17 : ℚ_[2]) - 1 := by rw [ha_sq]
      _ = 16 := by norm_num
  have hval_a_sub : Padic.addValuation (p := 2) (a - 1) ≠ ⊤ := by
    rw [hval_sub_cast]
    exact WithTop.coe_ne_top
  have hzadd : z + 1 ≠ 0 := by
    intro hzadd
    have hzneg : z = -1 := eq_neg_of_add_eq_zero_left hzadd
    rw [hzneg] at hz
    norm_num [F, quadraticPolynomial, Polynomial.aeval_def, eval₂_at_apply] at hz
  have hcast_add : ((z + 1 : ℤ_[2]) : ℚ_[2]) = a + 1 := by
    simp [a]
  have hval_add_cast :
      Padic.addValuation (p := 2) (a + 1) =
        (((z + 1).valuation : ℤ) : WithTop ℤ) := by
    rw [← hcast_add, Padic.addValuation.apply (PadicInt.coe_ne_zero.mpr hzadd),
      PadicInt.valuation_coe]
  have hval_a_add : Padic.addValuation (p := 2) (a + 1) ≠ ⊤ := by
    rw [hval_add_cast]
    exact WithTop.coe_ne_top
  have hval_a_add_eq : Padic.addValuation (p := 2) (a + 1) = (1 : WithTop ℤ) := by
    have hneq : Padic.addValuation (p := 2) (a - 1) ≠
        Padic.addValuation (p := 2) 2 := by
      have htwo : Padic.addValuation (p := 2) (2 : ℚ_[2]) = (1 : WithTop ℤ) := by
        have hp : Padic.valuation (2 : ℚ_[2]) = 1 := by
          exact Padic.valuation_p (p := 2)
        rw [Padic.addValuation.apply (by norm_num), hp]
        norm_num
      rw [hval_sub_cast, htwo]
      exact_mod_cast (show (z - 1).valuation ≠ 1 by omega)
    have hadd := (Padic.addValuation (p := 2)).map_add_of_distinct_val hneq
    have htwo : Padic.addValuation (p := 2) (2 : ℚ_[2]) = (1 : WithTop ℤ) := by
      have hp : Padic.valuation (2 : ℚ_[2]) = 1 := by
        exact Padic.valuation_p (p := 2)
      rw [Padic.addValuation.apply (by norm_num), hp]
      norm_num
    calc
      Padic.addValuation (p := 2) (a + 1) =
          Padic.addValuation (p := 2) ((a - 1) + 2) := by
            congr 1 ; ring
      _ = min (Padic.addValuation (p := 2) (a - 1))
          (Padic.addValuation (p := 2) 2) := hadd
      _ = Padic.addValuation (p := 2) 2 :=
        min_eq_right (by rw [htwo]; exact le_of_lt hvalgt)
      _ = (1 : WithTop ℤ) := htwo
  have hsum : Padic.addValuation (p := 2) (a - 1) +
      Padic.addValuation (p := 2) (a + 1) =
        Padic.addValuation (p := 2) (16 : ℚ_[2]) := by
    calc
      Padic.addValuation (p := 2) (a - 1) +
          Padic.addValuation (p := 2) (a + 1) =
          Padic.addValuation (p := 2) ((a - 1) * (a + 1)) := by
            rw [(Padic.addValuation (p := 2)).map_mul]
      _ = Padic.addValuation (p := 2) (16 : ℚ_[2]) :=
        congrArg (Padic.addValuation (p := 2)) hfactor
  have hval16 : Padic.addValuation (p := 2) (16 : ℚ_[2]) = (4 : WithTop ℤ) := by
    norm_num [Padic.addValuation, AddValuation.of_apply, Padic.addValuationDef,
      Padic.valuation_intCast]
    have hpv : padicValNat 2 16 = 4 := by
      convert padicValNat_base_pow (p := 2) (by norm_num) 4 using 1
    exact_mod_cast hpv
  rw [hval16] at hsum
  have hval_a_sub_eq : Padic.addValuation (p := 2) (a - 1) = (3 : WithTop ℤ) := by
    rw [hval_sub_cast, hval_a_add_eq] at hsum
    have hsum_int : ((z - 1).valuation : ℤ) + 1 = 4 := by
      apply WithTop.coe_injective
      simpa using hsum
    have hzval3 : (z - 1).valuation = 3 := by
      exact_mod_cast (by omega : ((z - 1).valuation : ℤ) = 3)
    rw [hval_sub_cast, hzval3]
    norm_num
  exact ⟨a, ha, hval_a_sub_eq⟩

/-- The Artin--Schreier polynomial `X^p-X-a`. -/
def artinSchreierPolynomial {A : Type*} [CommRing A] (p : ℕ) (a : A) : A[X] :=
  X ^ p - X - C a

/-- The Artin--Schreier polynomial is monic for positive residue characteristic. -/
theorem artinSchreierPolynomial_monic {A : Type*} [CommRing A] [Nontrivial A]
    (p : ℕ) (hp : 1 < p) (a : A) :
    (artinSchreierPolynomial p a).Monic := by
  have hdeg : (X + C a : A[X]).degree < p := by
    rw [degree_X_add_C]
    exact_mod_cast hp
  simpa [artinSchreierPolynomial, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using
    (monic_X_pow_sub (p := X + C a) hdeg)

/-- In residue characteristic `p`, the derivative of `X^p-X-a` is a unit. -/
theorem artinSchreier_derivative_is_unit {A : Type*} [CommRing A] [IsLocalRing A]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueRing A) p] (a x : A) :
    IsUnit ((artinSchreierPolynomial p a).derivative.eval x) := by
  have hpmax : (p : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change (p : ResidueRing A) = 0
    exact CharP.cast_eq_zero (ResidueRing A) p
  have hplus :
      (artinSchreierPolynomial p a).derivative.eval x + 1 ∈
        IsLocalRing.maximalIdeal A := by
    have hmul := (IsLocalRing.maximalIdeal A).mul_mem_left
      (x ^ (p - 1)) hpmax
    have hcalc :
        (artinSchreierPolynomial p a).derivative.eval x + 1 =
          (p : A) * x ^ (p - 1) := by
      simp [artinSchreierPolynomial, derivative_sub, derivative_pow]
    rw [hcalc]
    simpa [mul_comm] using hmul
  rw [← notMem_maximalIdeal]
  intro hder
  have hone := (IsLocalRing.maximalIdeal A).sub_mem hplus hder
  simp [sub_eq_add_neg, add_assoc] at hone

/-- Every residue root of `X^p-X-a` lifts uniquely over a complete DVR. -/
theorem artinSchreier_every_residue_root_lifts {A : Type*} [CommRing A] [IsDomain A]
    [CompleteDVR A] (p : ℕ) [Fact p.Prime] [CharP (ResidueRing A) p]
    (a : A) (x₀ : ResidueRing A)
    (hroot : (residuePolynomial (artinSchreierPolynomial p a)).eval x₀ = 0) :
    ∃! x : A,
      (artinSchreierPolynomial p a).eval x = 0 ∧ residueClass x = x₀ := by
  obtain ⟨x₀lift, hx₀lift⟩ := Ideal.Quotient.mk_surjective x₀
  let F := artinSchreierPolynomial p a
  have hfa : F.eval x₀lift ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residueMap A (F.eval x₀lift) = 0
    rw [← hx₀lift] at hroot
    change (residuePolynomial F).eval (residueMap A x₀lift) = 0 at hroot
    simpa only [residuePolynomial, Polynomial.eval_map_apply] using hroot
  have hunit : IsUnit (F.derivative.eval x₀lift) := by
    exact artinSchreier_derivative_is_unit p a x₀lift
  obtain ⟨x, hx, hcx⟩ := hensel_simple_root F x₀lift hfa hunit
  refine ⟨x, ?_, ?_⟩
  · constructor
    · simpa [F] using hx.1
    · unfold residueClass
      rw [← hx₀lift]
      unfold residueMap
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hx.2
  · intro y hy
    have hyF : F.eval y = 0 := by simpa [F] using hy.1
    have hyq : residueMap A y = residueMap A x₀lift := by
      calc
        residueMap A y = x₀ := hy.2
        _ = residueMap A x₀lift := hx₀lift.symm
    have hym : y - x₀lift ∈ IsLocalRing.maximalIdeal A := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change residueMap A (y - x₀lift) = 0
      rw [map_sub, hyq]
      simp
    exact hcx y ⟨hyF, hym⟩

/-- The Artin--Schreier calculation is the simple-root, unramified-style lifting test. -/
theorem artinSchreier_simple_root_separates_unramified_behavior {A : Type*}
    [CommRing A] [IsLocalRing A] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueRing A) p] (a x : A) :
    IsUnit ((artinSchreierPolynomial p a).derivative.eval x) := by
  exact artinSchreier_derivative_is_unit p a x

end
end Chapter09
end LastLib.Book01ValuationsDVRsAndCompletions
