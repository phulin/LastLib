import LastLib.Book01ValuationsDVRsAndCompletions.Chapter13.Section07TheStructureTheorem
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.Section03ArithmeticAndExamples
import Mathlib.Algebra.Polynomial.Div
import Mathlib.NumberTheory.Padics.RingHoms

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter13

open Ideal IsLocalRing

noncomputable section

/-! # Book 1, Chapter 13, Section 13.8: Worked examples and counterexamples -/

universe u

/-- Two distinct coefficient fields in one complete power-series ring. -/
structure Chapter13TwoCoefficientFieldExample
    (k : Type u) [Field k] (u₀ : k) where
  first : Chapter13Subfield (PowerSeries k)
  second : Chapter13Subfield (PowerSeries k)
  first_is_coefficient : Chapter13IsCoefficientField first
  second_is_coefficient : Chapter13IsCoefficientField second
  constants_mem_first : ∀ a : k, PowerSeries.C a ∈ first.carrier
  translated_generator : PowerSeries.C u₀ + PowerSeries.X ∈ second.carrier
  distinct : first.carrier ≠ second.carrier

/-- A power-series lift of a chosen `p`-basis family by elements of the maximal ideal. -/
def Chapter13PowerSeriesPBasisLift
    {k : Type u} [Field k] {B : Set k}
    (g : B → PowerSeries k) : B → PowerSeries k :=
  fun b => PowerSeries.C b.1 + g b

theorem chapter13_nonunique_coefficient_fields
    (k : Type u) [Field k] [Algebra ℚ k] (u₀ : k)
    (hu₀ : Transcendental ℚ u₀) :
    Nonempty (Chapter13TwoCoefficientFieldExample k u₀) := by
  sorry

theorem chapter13_p_basis_lift_family_power_series
    (k : Type u) [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (B : Set k)
    (hB : Chapter13PBasis (Chapter13PthPowerSubfield k p) B p)
    (g : B → PowerSeries k)
    (hg : ∀ b : B, g b ∈ Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) :
    ∃ K : Chapter13Subfield (PowerSeries k),
      Chapter13IsCoefficientField K := by
  sorry

/-! ### A maximal subfield can miss part of the residue field -/

theorem chapter13_maximal_subfield_not_coefficient
    (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ K : Chapter13Subfield
        (PowerSeries (FractionRing (Polynomial (ZMod p)))),
      Chapter13IsMaximalSubfield K ∧ ¬Chapter13IsCoefficientField K := by
  sorry

/-! ### The cusp -/

abbrev Chapter13CuspPowerSeriesSubring (k : Type u) [CommRing k] :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.chapter04CuspPowerSeriesSubring k

abbrev Chapter13CuspPowerSeriesMaximalIdeal (k : Type u) [Field k] :
    Ideal (Chapter13CuspPowerSeriesSubring k) :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.chapter04CuspPowerSeriesMaximalIdeal k

def Chapter13CuspRelation (k : Type u) [CommRing k] :
    MvPowerSeries (Fin 2) k :=
  (MvPowerSeries.X (1 : Fin 2)) ^ 2 - (MvPowerSeries.X (0 : Fin 2)) ^ 3

theorem chapter13_cusp_presentation
    (k : Type u) [Field k] :
    Nonempty
        ((MvPowerSeries (Fin 2) k ⧸
            Ideal.span {Chapter13CuspRelation k}) ≃+*
          Chapter13CuspPowerSeriesSubring k) ∧
      ¬IsRegularLocalRing (Chapter13CuspPowerSeriesSubring k) := by
  sorry

/-! ### Mixed-characteristic examples -/

abbrev Chapter13PrimeSquareRing (p : ℕ) := ZMod (p ^ 2)

instance chapter13PrimeSquareLocalRing
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocalRing (Chapter13PrimeSquareRing p) := by
  have hp : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hp2 : 1 < p ^ 2 := by
    calc
      1 < 2 * 2 := by decide
      _ ≤ p * p := Nat.mul_le_mul hp hp
      _ = p ^ 2 := by simp [pow_two]
  let : Fact (1 < p ^ 2) := ⟨hp2⟩
  exact @IsLocalRing.of_surjective' (PadicInt p) (ZMod (p ^ 2)) _ _ _
    inferInstance (PadicInt.toZModPow 2) (ZMod.ringHom_surjective _)

theorem chapter13_prime_square_has_no_coefficient_field
    (p : ℕ) [Fact (Nat.Prime p)] :
    Chapter13CompleteNoetherianLocalRing (Chapter13PrimeSquareRing p) ∧
      Chapter13MixedCharacteristic (Chapter13PrimeSquareRing p) p ∧
      ¬Chapter13ContainsField (Chapter13PrimeSquareRing p) ∧
      Chapter13IsCohenRing (PadicInt p) (ZMod p) p ∧
      Function.Surjective (@PadicInt.toZModPow p _ 2) := by
  let A := Chapter13PrimeSquareRing p
  have hp : Nat.Prime p := Fact.out
  have hp2 : 1 < p ^ 2 := by
    calc
      1 < 2 * 2 := by decide
      _ ≤ p * p := Nat.mul_le_mul hp.two_le hp.two_le
      _ = p ^ 2 := by simp [pow_two]
  have hdiv : p ∣ p ^ 2 := by
    refine ⟨p, ?_⟩
    simp [pow_two]
  let q : A →+* ZMod p := ZMod.castHom hdiv (ZMod p)
  have hqsurj : Function.Surjective q := by
    simpa [q] using (ZMod.castHom_surjective hdiv)
  have hker : RingHom.ker q = IsLocalRing.maximalIdeal A :=
    IsLocalRing.ker_eq_maximalIdeal q hqsurj
  let e : Chapter13ResidueRing A ≃+* ZMod p :=
    (Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective hqsurj)
  have hres : CharP (Chapter13ResidueRing A) p := by
    exact (e.symm.toRingHom.charP_iff_charP p).mp (ZMod.charP p)
  have hnonzero : (p : A) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have hlt : p < p ^ 2 := by
      rw [pow_two]
      simpa using Nat.mul_lt_mul_of_pos_left hp.one_lt
        (Nat.zero_lt_of_lt hp.two_le)
    exact (Nat.not_dvd_of_pos_of_lt (Nat.zero_lt_of_lt hp.two_le) hlt) h
  have hnonunit : ¬IsUnit (p : A) := by
    intro hu
    have hq : IsUnit (q (p : A)) := IsUnit.map q hu
    have hqp : q (p : A) = 0 := by
      change ZMod.castHom hdiv (ZMod p) (p : ZMod (p ^ 2)) = 0
      rw [map_natCast]
      simp
    exact hq.ne_zero hqp
  have hnotchar : ¬CharP A p := by
    intro hchar
    exact hnonzero (@CharP.cast_eq_zero A _ p hchar)
  have hcontains : ¬Chapter13ContainsField A := by
    rintro ⟨K⟩
    have hpK : (p : K.carrier) ≠ 0 := by
      intro hpK
      apply hnonzero
      exact congrArg K.carrier.subtype hpK
    have huK : IsUnit (p : K.carrier) :=
      (@isUnit_iff_ne_zero K.carrier
        (@Field.toSemifield K.carrier K.field_carrier.toField).toCommGroupWithZero.toGroupWithZero).mpr hpK
    have huA : IsUnit (p : A) := by
      simpa using IsUnit.map K.carrier.subtype huK
    exact hnonunit huA
  refine ⟨?_, ⟨hp, hres, hnotchar⟩, hcontains, ?_, ?_⟩
  · exact ⟨inferInstance, inferInstance⟩
  · exact chapter13_padic_integers_are_cohen p
  · exact ZMod.ringHom_surjective _

theorem chapter13_padic_integers_have_no_subfield
    (p : ℕ) [Fact (Nat.Prime p)] :
    ¬Chapter13ContainsField (PadicInt p) := by
  rintro ⟨K⟩
  let : Field K.carrier := K.field_carrier.toField
  have hp0 : (p : K.carrier) ≠ 0 := by
    intro hp
    have hp' : (p : PadicInt p) = 0 := congrArg K.carrier.subtype hp
    have hpne : (p : PadicInt p) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    exact hpne hp'
  have hu : IsUnit (p : K.carrier) := isUnit_iff_ne_zero.mpr hp0
  have hu' : IsUnit (p : PadicInt p) := by
    simpa using IsUnit.map K.carrier.subtype hu
  apply (IsLocalRing.notMem_maximalIdeal.mpr hu')
  exact (IsLocalRing.mem_maximalIdeal _).mpr PadicInt.p_nonunit

abbrev Chapter13PadicPowerSeries (p : ℕ) [Fact (Nat.Prime p)] :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.chapter04PadicPowerSeries p

abbrev Chapter13PadicPowerSeriesMaximalIdeal
    (p : ℕ) [Fact (Nat.Prime p)] : Ideal (Chapter13PadicPowerSeries p) :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.chapter04PadicPowerSeriesMaximalIdeal p

theorem chapter13_padic_power_series_is_unramified_regular
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsAdicComplete (Chapter13PadicPowerSeriesMaximalIdeal p)
        (Chapter13PadicPowerSeries p) ∧
      IsRegularLocalRing (Chapter13PadicPowerSeries p) ∧
      ringKrullDim (Chapter13PadicPowerSeries p) = 2 ∧
      (p : Chapter13PadicPowerSeries p) ∉
        (IsLocalRing.maximalIdeal (Chapter13PadicPowerSeries p)) ^ 2 ∧
      Chapter13MixedCharacteristic (Chapter13PadicPowerSeries p) p ∧
      ¬Chapter13ContainsField (Chapter13PadicPowerSeries p) := by
  let A := Chapter13PadicPowerSeries p
  let M := Chapter13PadicPowerSeriesMaximalIdeal p
  have h04 :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.padic_power_series_is_complete_regular_local_two_dimensional p
  have hM : M = Ideal.span
      ({PowerSeries.C (p : PadicInt p), PowerSeries.X} : Set A) := by
    rfl
  have hp0 : (p : PadicInt p) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hnotpow : (p : PadicInt p) ∉
      (Ideal.span {(p : PadicInt p)}) ^ 2 := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨a, ha⟩
    have hpa : (p : PadicInt p) * a = 1 := by
      apply (mul_left_cancel₀ hp0)
      simpa [pow_two, mul_assoc] using ha.symm
    exact (mem_nonunits_iff.mp PadicInt.p_nonunit)
      (IsUnit.of_mul_eq_one a hpa)
  have hnotm : (p : A) ∉ M ^ 2 := by
    intro hpM
    let c : A →+* PadicInt p := PowerSeries.constantCoeff
    have hc : Ideal.map c (M ^ 2) ≤
        (Ideal.span {(p : PadicInt p)}) ^ 2 := by
      rw [Ideal.map_pow]
      apply Ideal.pow_right_mono
      rw [hM, Ideal.map_span]
      apply Ideal.span_le.2
      intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      rcases Set.mem_insert_iff.mp hz with hz | hz
      · rw [Set.mem_singleton_iff.mp hz]
        simp [c]
      · rw [Set.mem_singleton_iff.mp hz]
        rw [PowerSeries.constantCoeff_X]
        exact Ideal.zero_mem _
    apply hnotpow
    apply hc
    exact Ideal.mem_map_of_mem c hpM
  have hker : RingHom.ker (PadicInt.toZMod.comp
      (PowerSeries.constantCoeff : A →+* PadicInt p)) = M := by
    apply le_antisymm
    · intro f hf
      change PadicInt.toZMod (PowerSeries.constantCoeff f) = 0 at hf
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod] at hf
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hf
      obtain ⟨a, ha⟩ := hf
      rw [hM, PowerSeries.eq_X_mul_shift_add_const f, ha]
      apply Ideal.add_mem
      · exact M.mul_mem_right _ (Ideal.subset_span (by simp))
      · rw [map_mul]
        exact M.mul_mem_right _ (Ideal.subset_span (by simp))
    · rw [hM]
      apply Ideal.span_le.2
      intro y hy
      rcases hy with rfl | rfl
      · simp [RingHom.mem_ker]
      · change PadicInt.toZMod (PowerSeries.constantCoeff PowerSeries.X) = 0
        rw [PowerSeries.constantCoeff_X, map_zero]
  have hsurj : Function.Surjective
      (PadicInt.toZMod.comp
        (PowerSeries.constantCoeff : A →+* PadicInt p)) := by
    intro y
    obtain ⟨z, hz⟩ := ZMod.ringHom_surjective (PadicInt.toZMod :
      PadicInt p →+* ZMod p) y
    refine ⟨PowerSeries.C z, ?_⟩
    change PadicInt.toZMod z = y
    exact hz
  have hmax : IsLocalRing.maximalIdeal A = M := h04.2.2.2.1
  let e : Chapter13ResidueRing A ≃+* ZMod p :=
    (Ideal.quotEquivOfEq (hmax.trans hker.symm)).trans
      (RingHom.quotientKerEquivOfSurjective hsurj)
  have hreschar : CharP (Chapter13ResidueRing A) p := by
    exact (e.symm.toRingHom.charP_iff_charP p).mp (ZMod.charP p)
  have hcharA : ¬CharP A p := by
    intro h
    let : CharP A p := h
    have hz : (p : A) = 0 := CharP.cast_eq_zero A p
    have hz' : (p : PadicInt p) = 0 := by
      simpa only [map_natCast, map_zero] using
        congrArg PowerSeries.constantCoeff hz
    exact hp0 hz'
  have hcontains : ¬Chapter13ContainsField A := by
    rintro ⟨K⟩
    let : Field K.carrier := K.field_carrier.toField
    have hpa0 : (p : A) ≠ 0 := by
      intro h
      have h' := congrArg PowerSeries.constantCoeff h
      exact hp0 (by simpa only [map_natCast, map_zero] using h')
    have hpK : (p : K.carrier) ≠ 0 := by
      intro h
      exact hpa0 (congrArg K.carrier.subtype h)
    have hu : IsUnit (p : A) := by
      simpa using IsUnit.map K.carrier.subtype
        (isUnit_iff_ne_zero.mpr hpK)
    exact (mem_nonunits_iff.mp PadicInt.p_nonunit)
      (by simpa using PowerSeries.isUnit_iff_constantCoeff.mp hu)
  have hnotmax : (p : A) ∉ (IsLocalRing.maximalIdeal A) ^ 2 := by
    rw [hmax]
    exact hnotm
  refine ⟨h04.1, h04.2.1, h04.2.2.1, hnotmax,
    ⟨(Fact.out : Nat.Prime p), hreschar, hcharA⟩, hcontains⟩

/-- The Eisenstein polynomial obtained from `((1 + X)^p - 1) / X`. -/
def Chapter13CyclotomicEisensteinPolynomial
    (p : ℕ) [Fact (Nat.Prime p)] : Polynomial (PadicInt p) :=
  ((Polynomial.X + 1) ^ p - 1) /ₘ Polynomial.X

abbrev Chapter13CyclotomicOrder
    (p : ℕ) [Fact (Nat.Prime p)] :=
  Polynomial (PadicInt p) ⧸
    Ideal.span {Chapter13CyclotomicEisensteinPolynomial p}

instance chapter13CyclotomicOrderLocalRing
    (p : ℕ) [Fact (Nat.Prime p)] : IsLocalRing (Chapter13CyclotomicOrder p) := by
  sorry

instance chapter13CyclotomicOrderDomain
    (p : ℕ) [Fact (Nat.Prime p)] : IsDomain (Chapter13CyclotomicOrder p) := by
  sorry

theorem chapter13_cyclotomic_order_is_ramified
    (p : ℕ) [Fact (Nat.Prime p)] (hp : 2 < p) :
    IsAdicComplete (IsLocalRing.maximalIdeal (Chapter13CyclotomicOrder p))
        (Chapter13CyclotomicOrder p) ∧
      IsRegularLocalRing (Chapter13CyclotomicOrder p) ∧
      IsDiscreteValuationRing (Chapter13CyclotomicOrder p) ∧
      ringKrullDim (Chapter13CyclotomicOrder p) = 1 ∧
      (p : Chapter13CyclotomicOrder p) ∈
        (IsLocalRing.maximalIdeal (Chapter13CyclotomicOrder p)) ^ 2 ∧
      ¬Chapter13IsCohenRing (Chapter13CyclotomicOrder p) (ZMod p) p := by
  sorry

/-! ### Formal local coordinates -/

theorem chapter13_formal_local_coordinates
    {R k : Type u} [CommRing R] [IsLocalRing R] [Field k] (d : ℕ)
    (hR : IsNoetherianRing R)
    (hregular : IsRegularLocalRing R)
    (hdim : ringKrullDim R = d)
    (hcontains : Chapter13ContainsField R)
    (e : Chapter13ResidueRing R ≃+* k) :
    Nonempty
      (MvPowerSeries (Fin d) k ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  sorry

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter13
