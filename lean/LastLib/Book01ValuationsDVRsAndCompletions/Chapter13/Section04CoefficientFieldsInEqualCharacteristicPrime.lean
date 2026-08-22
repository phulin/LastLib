import LastLib.Book01ValuationsDVRsAndCompletions.Chapter13.Section03PBasesAndDerivations
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Section02InfiniteDigits
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharP.Quotient
import Mathlib.RingTheory.PowerSeries.Inverse

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter13

open Filter Ideal IsLocalRing
open scoped PowerSeries Topology

noncomputable section

/-! # Book 1, Chapter 13, Section 13.4: Coefficient fields in equal characteristic `p` -/

universe u v

/-- A family of lifts of a `p`-basis in the residue ring. -/
def Chapter13AdmissiblePBaseLiftFamily
    {A : Type u} [CommRing A] [IsLocalRing A]
    (B : Set (Chapter13ResidueRing A)) (a : B → A) : Prop :=
  ∀ b : B, Chapter13ResidueMap A (a b) = (b : Chapter13ResidueRing A)

/-- The type of coefficient fields of a fixed local ring. -/
def Chapter13CoefficientFields
    (A : Type u) [CommRing A] [IsLocalRing A] : Type u :=
  {K : Chapter13Subfield A // Chapter13IsCoefficientField K}

/-- A power-series presentation of a complete equicharacteristic DVR. -/
structure Chapter13PowerSeriesDVRModel
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] (π : A) (u : K →+* A) where
  equiv : PowerSeries K ≃+* A
  maps_constants : equiv.toRingHom.comp (PowerSeries.C : K →+* PowerSeries K) = u
  maps_uniformizer : equiv PowerSeries.X = π
  maps_maximal_ideal :
    (Ideal.span ({PowerSeries.X} : Set (PowerSeries K))).map equiv.toRingHom =
      IsLocalRing.maximalIdeal A

/-- Fixed lifts of a residue `p`-basis determine compatible splittings of all
positive adic quotients. -/
theorem chapter13_compatible_p_basis_splittings
    {A : Type u} [CommRing A] [IsLocalRing A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP A p]
    (B : Set (Chapter13ResidueRing A))
    (hB : Chapter13PBasis
      (Chapter13PthPowerSubfield (Chapter13ResidueRing A) p) B p)
    (a : B → A) (ha : Chapter13AdmissiblePBaseLiftFamily B a) :
    ∃ f : (n : ℕ) → Chapter13ResidueRing A →+*
        A ⧸ (IsLocalRing.maximalIdeal A) ^ (n + 1),
      (∀ n, (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal A)
        (Nat.le_succ (n + 1))).comp (f (n + 1)) = f n) ∧
      (Ideal.Quotient.factor
        (le_of_eq (pow_one (IsLocalRing.maximalIdeal A)))).comp (f 0) =
          RingHom.id _ ∧
      ∀ n (b : B), f n (b : Chapter13ResidueRing A) =
        Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal A) ^ (n + 1)) (a b) := by
  classical
  let I : Ideal A := IsLocalRing.maximalIdeal A
  have hcast (J : Ideal A) (hJ : J ≤ I) :
      ∀ n : ℕ, (n : A) ∈ J → (n : A) = 0 := by
    intro n hn
    by_contra hpn
    have hnotdvd : ¬p ∣ n :=
      fun hdiv => hpn ((CharP.cast_eq_zero_iff A p n).2 hdiv)
    have hunit : IsUnit (n : A) :=
      (CharP.isUnit_natCast_iff (R := A) Fact.out).2 hnotdvd
    exact (IsLocalRing.mem_maximalIdeal (R := A) (n : A)).mp (hJ hn) hunit
  let _ : CharP (Chapter13ResidueRing A) p :=
    CharP.quotient' p I (hcast I le_rfl)
  let X (n : ℕ) :=
    {φ : Chapter13ResidueRing A →+* A ⧸ I ^ (n + 1) //
      ∀ b : B, φ (b : Chapter13ResidueRing A) =
        Ideal.Quotient.mk (I ^ (n + 1)) (a b)}
  let e0 : Chapter13ResidueRing A ≃+* A ⧸ I ^ (0 + 1) :=
    Ideal.quotEquivOfEq (by simp [I])
  let x0 : X 0 := ⟨e0.toRingHom, by
    intro b
    rw [show (b : Chapter13ResidueRing A) = Chapter13ResidueMap A (a b) from
      (ha b).symm]
    simp [e0, Chapter13ResidueMap, Ideal.quotEquivOfEq_mk]⟩
  have hstep (n : ℕ) (x : X n) : ∃ y : X (n + 1),
      (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))).comp y.1 = x.1 := by
    let _ : CharP (A ⧸ I ^ (n + 2)) p :=
      CharP.quotient' p _ (hcast _ (Ideal.pow_le_self (by omega)))
    let q := Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))
    let β : B → A ⧸ I ^ (n + 2) :=
      fun b => Ideal.Quotient.mk (I ^ (n + 2)) (a b)
    have hβ : ∀ b : B, q (β b) = x.1 (b : Chapter13ResidueRing A) := by
      intro b
      rw [x.2 b]
      simp [q, β, Ideal.Quotient.factorPow]
    obtain ⟨φ, hφ, _⟩ :=
      chapter13_char_p_square_zero_lift_surjective p Fact.out B hB q
        (Ideal.Quotient.factor_surjective _)
        (chapter13_factorPow_succ_ker_sq I (n + 1) (by omega)) x.1 β hβ
    exact ⟨⟨φ, hφ.2⟩, hφ.1⟩
  let step (n : ℕ) (x : X n) : X (n + 1) :=
    Classical.choose (hstep n x)
  let xs : (n : ℕ) → X n :=
    fun n => Nat.rec (motive := X) x0 (fun n x => step n x) n
  refine ⟨fun n => (xs n).1, ?_, ?_, ?_⟩
  · intro n
    change (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))).comp
      (xs (n + 1)).1 = (xs n).1
    exact Classical.choose_spec (hstep n (xs n))
  · apply RingHom.ext
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp [xs, x0, e0, I,
      Ideal.quotEquivOfEq_mk]
  · intro n b
    exact (xs n).2 b

/-- Chosen lifts of a `p`-basis determine a unique coefficient-field splitting. -/
theorem chapter13_equal_characteristic_p_coefficient_field_splitting
    {A : Type u} [CommRing A] [IsLocalRing A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP A p]
    (B : Set (Chapter13ResidueRing A))
    (hB : Chapter13PBasis (Chapter13PthPowerSubfield (Chapter13ResidueRing A) p) B p)
    (a : B → A) (ha : Chapter13AdmissiblePBaseLiftFamily B a)
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A) :
    ∃! φ : Chapter13ResidueRing A →+* A,
      (Chapter13ResidueMap A).comp φ = RingHom.id _ ∧
        ∀ b : B, φ (b : Chapter13ResidueRing A) = a b := by
  sorry

/-- Coefficient fields are parametrized by admissible lifts of a residue `p`-basis. -/
theorem chapter13_equal_characteristic_p_coefficient_fields_bijection
    {A : Type u} [CommRing A] [IsLocalRing A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP A p]
    (B : Set (Chapter13ResidueRing A))
    (hB : Chapter13PBasis (Chapter13PthPowerSubfield (Chapter13ResidueRing A) p) B p)
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A) :
    Nonempty
      (Chapter13CoefficientFields A ≃
        {a : B → A // Chapter13AdmissiblePBaseLiftFamily B a}) := by
  sorry

/-- A complete separated local ring containing a field has a coefficient field. -/
theorem chapter13_coefficient_field_exists_when_contains_field
    {A : Type u} [CommRing A] [IsLocalRing A]
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hfield : Chapter13ContainsField A) :
    ∃ K : Chapter13Subfield A,
      Chapter13IsCoefficientField K ∧
        Chapter13CoefficientDecomposition K ∧
        (∀ a : A, ∃! z : K.carrier × A,
          z.2 ∈ IsLocalRing.maximalIdeal A ∧ a = z.1.1 + z.2) := by
  have hdecomp : ∀ (K : Chapter13Subfield A),
      Chapter13IsCoefficientField K →
        ∀ a : A, ∃! z : K.carrier × A,
          z.2 ∈ IsLocalRing.maximalIdeal A ∧ a = z.1.1 + z.2 := by
    intro K hK a
    obtain ⟨k, hk⟩ := hK.2 (Chapter13ResidueMap A a)
    have hzero : Chapter13ResidueMap A (a - K.carrier.subtype k) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hk.symm
    have hm : a - K.carrier.subtype k ∈ IsLocalRing.maximalIdeal A := by
      change Ideal.Quotient.mk _ (a - K.carrier.subtype k) = 0 at hzero
      exact (Ideal.Quotient.eq_zero_iff_mem).mp hzero
    have ha : a = K.carrier.subtype k + (a - K.carrier.subtype k) := by
      simp
    refine ⟨(k, a - K.carrier.subtype k), ⟨hm, ha⟩, ?_⟩
    rintro ⟨k', m'⟩ ⟨hm', ha'⟩
    have hmzero : Chapter13ResidueMap A m' = 0 := by
      change Ideal.Quotient.mk _ m' = 0
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr hm'
    have hkeq : k = k' := by
      have hmapa : Chapter13ResidueMap A a =
          Chapter13ResidueMap A (K.carrier.subtype k') := by
        have hsum : K.carrier.subtype k + (a - K.carrier.subtype k) =
            K.carrier.subtype k' + m' := ha.symm.trans ha'
        apply_fun Chapter13ResidueMap A at hsum
        simpa [map_add, hzero, hmzero] using hsum
      exact hK.1 (hk.trans hmapa)
    have hmeq : a - K.carrier.subtype k = m' := by
      have ha'' : a = K.carrier.subtype k + m' := by
        simpa [hkeq] using ha'
      exact add_left_cancel (ha.symm.trans ha'')
    exact Prod.ext hkeq.symm hmeq.symm
  obtain hcases := (chapter13_contains_field_iff_equal_characteristic (A := A)).mp hfield
  rcases hcases with hzero | ⟨p, hpprime, hpA, hres⟩
  · obtain ⟨⟨K, hK⟩, _, _⟩ :=
      chapter13_coefficient_field_exists_equal_characteristic_zero hA hzero.2 hfield
    exact ⟨K, hK, by
      intro a
      obtain ⟨k, hk⟩ := hK.2 (Chapter13ResidueMap A a)
      let m := a - K.carrier.subtype k
      have hm : m ∈ IsLocalRing.maximalIdeal A := by
        apply (Ideal.Quotient.eq_zero_iff_mem).mp
        change Chapter13ResidueMap A m = 0
        rw [map_sub]
        exact sub_eq_zero.mpr hk.symm
      exact ⟨k, m, hm, by simp [m]⟩, hdecomp K hK⟩
  · let _ : Fact (Nat.Prime p) := ⟨hpprime⟩
    let _ : CharP A p := hpA
    let _ : CharP (Chapter13ResidueRing A) p := hres
    obtain ⟨B, hB⟩ :=
      (chapter13_p_basis_existence (k := Chapter13ResidueRing A) p).2.1
    let a : B → A := fun b =>
      Classical.choose (Ideal.Quotient.mk_surjective (b : Chapter13ResidueRing A))
    have ha : Chapter13AdmissiblePBaseLiftFamily B a := by
      intro b
      exact Classical.choose_spec
        (Ideal.Quotient.mk_surjective (b : Chapter13ResidueRing A))
    obtain ⟨e⟩ := chapter13_equal_characteristic_p_coefficient_fields_bijection
      p B hB hA
    let z : {a : B → A // Chapter13AdmissiblePBaseLiftFamily B a} := ⟨a, ha⟩
    let K : Chapter13Subfield A := (e.symm z).1
    have hK : Chapter13IsCoefficientField K := (e.symm z).2
    exact ⟨K, hK, by
      intro x
      obtain ⟨k, hk⟩ := hK.2 (Chapter13ResidueMap A x)
      have hm : x - K.carrier.subtype k ∈ IsLocalRing.maximalIdeal A := by
        apply (Ideal.Quotient.eq_zero_iff_mem).mp
        change Chapter13ResidueMap A (x - K.carrier.subtype k) = 0
        rw [map_sub]
        exact sub_eq_zero.mpr hk.symm
      exact ⟨k, x - K.carrier.subtype k, hm, by simp⟩,
      hdecomp K hK⟩

/-- The coefficient decomposition is unique. -/
theorem chapter13_coefficient_decomposition_unique
    {A : Type u} [CommRing A] [IsLocalRing A]
    (K : Chapter13Subfield A) (hK : Chapter13IsCoefficientField K) :
    ∀ a : A, ∃! z : K.carrier × A,
      z.2 ∈ IsLocalRing.maximalIdeal A ∧ a = z.1.1 + z.2 := by
  intro a
  obtain ⟨k, hk⟩ := hK.2 (Chapter13ResidueMap A a)
  have hzero : Chapter13ResidueMap A (a - K.carrier.subtype k) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hk.symm
  have hm : a - K.carrier.subtype k ∈ IsLocalRing.maximalIdeal A := by
    change Ideal.Quotient.mk _ (a - K.carrier.subtype k) = 0 at hzero
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hzero
  have ha : a = K.carrier.subtype k + (a - K.carrier.subtype k) := by
    simp
  refine ⟨(k, a - K.carrier.subtype k), ⟨hm, ?_⟩, ?_⟩
  · exact ha
  · rintro ⟨k', m'⟩ ⟨hm', ha'⟩
    have hmzero : Chapter13ResidueMap A m' = 0 := by
      change Ideal.Quotient.mk _ m' = 0
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr hm'
    have hkeq :
        (Chapter13ResidueMap A).comp K.carrier.subtype k =
          (Chapter13ResidueMap A).comp K.carrier.subtype k' := by
      have heq : K.carrier.subtype k + (a - K.carrier.subtype k) =
          K.carrier.subtype k' + m' := ha.symm.trans ha'
      apply_fun Chapter13ResidueMap A at heq
      have hmapa : Chapter13ResidueMap A a =
          Chapter13ResidueMap A (K.carrier.subtype k') := by
        simpa [map_add, hzero, hmzero] using heq
      exact hk.trans hmapa
    have hkeq' : k = k' := hK.1 hkeq
    have hmeq : a - K.carrier.subtype k = m' := by
      have ha'': a = K.carrier.subtype k + m' := by
        simpa [hkeq'] using ha'
      exact add_left_cancel (ha.symm.trans ha'')
    exact Prod.ext hkeq'.symm hmeq.symm

/-- Powers of a perfect residue field give the canonical coefficient field. -/
theorem chapter13_perfect_residue_unique_coefficient_field
    {A : Type u} [CommRing A] [IsLocalRing A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP A p]
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hperfect : Chapter13PerfectAtPrime (Chapter13ResidueRing A) p) :
    ∃! K : Chapter13Subfield A,
      Chapter13IsCoefficientField K ∧
        (K.carrier : Set A) =
          ⋂ n : ℕ, Set.range (fun x : A => x ^ (p ^ n)) := by
  classical
  have hB : Chapter13PBasis
      (Chapter13PthPowerSubfield (Chapter13ResidueRing A) p)
      (∅ : Set (Chapter13ResidueRing A)) p := by
    let _ : CharP (Chapter13ResidueRing A) p := CharP.quotient' p
      (IsLocalRing.maximalIdeal A)
      (by
        intro n hn
        by_contra hpn
        have hnotdvd : ¬p ∣ n := by
          intro hdiv
          exact hpn ((CharP.cast_eq_zero_iff A p n).2 hdiv)
        have hunit : IsUnit (n : A) :=
          (CharP.isUnit_natCast_iff (R := A) (Fact.out : Nat.Prime p)).2
            hnotdvd
        exact (IsLocalRing.mem_maximalIdeal (R := A) (n : A)).mp hn hunit)
    exact chapter13_perfect_field_empty_p_basis p hperfect
  obtain ⟨e⟩ := chapter13_equal_characteristic_p_coefficient_fields_bijection
    p (∅ : Set (Chapter13ResidueRing A)) hB hA
  have hintersection : ∀ K : Chapter13Subfield A,
      Chapter13IsCoefficientField K →
        (K.carrier : Set A) = ⋂ n : ℕ, Set.range (fun x : A => x ^ (p ^ n)) := by
    intro K hK
    let rK : K.carrier →+* Chapter13ResidueRing A :=
      (Chapter13ResidueMap A).comp K.carrier.subtype
    have hroot : ∀ x : K.carrier, ∃ y : K.carrier, y ^ p = x := by
      intro x
      obtain ⟨z, hz⟩ := hperfect (rK x)
      obtain ⟨y, hy⟩ := hK.2 z
      refine ⟨y, ?_⟩
      apply hK.1
      change rK y ^ p = rK x
      calc
        rK y ^ p = z ^ p := by rw [hy]
        _ = rK x := by simpa using hz
    have hpow : ∀ (x : K.carrier) (n : ℕ),
        ∃ y : K.carrier, y ^ (p ^ n) = x := by
      intro x n
      induction n generalizing x with
      | zero => exact ⟨x, by simp⟩
      | succ n ih =>
          obtain ⟨x', hx'⟩ := hroot x
          obtain ⟨y, hy⟩ := ih x'
          refine ⟨y, ?_⟩
          calc
            y ^ (p ^ n * p) = (y ^ (p ^ n)) ^ p := pow_mul y (p ^ n) p
            _ = x' ^ p := by rw [hy]
            _ = x := hx'
    have hhaus : IsHausdorff (IsLocalRing.maximalIdeal A) A := hA.toIsHausdorff
    ext x
    constructor
    · intro hx
      let xK : K.carrier := ⟨x, hx⟩
      refine Set.mem_iInter.mpr ?_
      intro n
      obtain ⟨y, hy⟩ := hpow xK n
      refine ⟨(y : A), congrArg (fun z : K.carrier => (z : A)) hy⟩
    · intro hx
      have hxall : ∀ n : ℕ, x ∈ Set.range (fun y : A => y ^ (p ^ n)) :=
        Set.mem_iInter.mp hx
      obtain ⟨xK, hxK⟩ := hK.2 (Chapter13ResidueMap A x)
      have hzero : x - (xK : A) = 0 := hhaus.haus (x - (xK : A)) (by
        intro n
        obtain ⟨y, hy⟩ := hxall n
        change y ^ (p ^ n) = x at hy
        obtain ⟨yK, hyK⟩ := hK.2 (Chapter13ResidueMap A y)
        have hpowK' : yK ^ (p ^ n) = xK := by
          apply hK.1
          change rK (yK ^ (p ^ n)) = rK xK
          calc
            rK (yK ^ (p ^ n)) = rK yK ^ (p ^ n) := by rw [map_pow]
            _ = (Chapter13ResidueMap A y) ^ (p ^ n) := by rw [hyK]
            _ = Chapter13ResidueMap A (y ^ (p ^ n)) := by
              rw [map_pow]
            _ = Chapter13ResidueMap A x := by rw [hy]
            _ = rK xK := hxK.symm
        have hpowK : (yK : A) ^ (p ^ n) = (xK : A) :=
          congrArg (fun z : K.carrier => (z : A)) hpowK'
        have hdiff : x - (xK : A) = (y - (yK : A)) ^ (p ^ n) := by
          calc
            x - (xK : A) = y ^ (p ^ n) - (xK : A) := by rw [hy]
            _ = y ^ (p ^ n) - (yK : A) ^ (p ^ n) := by rw [hpowK]
            _ = (y - (yK : A)) ^ (p ^ n) :=
              (sub_pow_char_pow (p := p) (n := n) y (yK : A)).symm
        rw [hdiff]
        have hym : y - (yK : A) ∈ IsLocalRing.maximalIdeal A := by
          apply (Ideal.Quotient.eq_zero_iff_mem).mp
          change Chapter13ResidueMap A y - rK yK = 0
          rw [hyK]
          exact sub_self _
        have hnp : n ≤ p ^ n := by
          by_cases hn : n = 0
          · simp [hn]
          · exact le_trans (by
              simpa only [one_mul] using
                Nat.mul_le_mul_right n ((Fact.out : Nat.Prime p).one_le : 1 ≤ p))
              (Nat.mul_le_pow (Fact.out : Nat.Prime p).ne_one n)
        exact SModEq.zero.2 (by
          simpa only [smul_eq_mul, mul_top] using
            (Ideal.pow_le_pow_right hnp) (Ideal.pow_mem_pow hym (p ^ n)))
        )
      have hxeq : x = (xK : A) := sub_eq_zero.mp hzero
      rw [hxeq]
      exact xK.property
  let emptyFamily : {a : (∅ : Set (Chapter13ResidueRing A)) → A //
        Chapter13AdmissiblePBaseLiftFamily (∅ : Set (Chapter13ResidueRing A)) a} :=
    ⟨fun b => b.property.elim, by intro b; exact b.property.elim⟩
  let z : Chapter13CoefficientFields A := e.symm
    emptyFamily
  refine ⟨z.1, ⟨z.2, hintersection z.1 z.2⟩, ?_⟩
  intro K hK
  have heq : e ⟨K, hK.1⟩ = e z := by
    apply Subtype.ext
    funext b
    exact b.property.elim
  have : (⟨K, hK.1⟩ : Chapter13CoefficientFields A) = z := e.injective heq
  exact congrArg Subtype.val this

/-- An equicharacteristic complete DVR is a one-variable power-series ring. -/
theorem chapter13_equicharacteristic_complete_dvr_power_series
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type v} [Field K]
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π})
    (u : K →+* A)
    (hu : IsLocalHom u ∧
      Function.Bijective ((Chapter13ResidueMap A).comp u)) :
    Nonempty (Chapter13PowerSeriesDVRModel A K π u) := by
  let I : Ideal A := IsLocalRing.maximalIdeal A
  let rbar : Chapter13ResidueRing A ≃+* K :=
    (RingEquiv.ofBijective ((Chapter13ResidueMap A).comp u) hu.2).symm
  let r : A →+* K := rbar.toRingHom.comp (Chapter13ResidueMap A)
  let sectionData : LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08CoefficientFieldSection
      A K I :=
    { lift := u
      residue := r
      residue_lift := by
        ext c
        change rbar ((Chapter13ResidueMap A) (u c)) = c
        change (RingEquiv.ofBijective ((Chapter13ResidueMap A).comp u) hu.2).symm
          ((Chapter13ResidueMap A).comp u c) = c
        exact (RingEquiv.ofBijective ((Chapter13ResidueMap A).comp u) hu.2).symm_apply_apply c
      kernel_residue := by
        ext a
        constructor
        · intro ha
          change r a = 0 at ha
          have ha' : Chapter13ResidueMap A a = 0 := by
            apply rbar.injective
            simpa [r] using ha
          have hker : a ∈ RingHom.ker (Chapter13ResidueMap A) :=
            RingHom.mem_ker.mpr ha'
          simpa [I, Chapter13ResidueMap] using hker
        · intro ha
          change r a = 0
          have ha' : Chapter13ResidueMap A a = 0 := by
            apply RingHom.mem_ker.mp
            simpa [I, Chapter13ResidueMap] using ha
          change rbar (Chapter13ResidueMap A a) = 0
          rw [ha']
          exact map_zero rbar
      }
  let hcomplete : IsAdicComplete I A := by simpa [I] using hA
  obtain ⟨model⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.chapter08_equal_characteristic_formal_series_model
      (hcomplete := hcomplete) I π hπ sectionData
  let eA : A ≃+* AdicCompletion I A :=
    (AdicCompletion.ofAlgEquiv I).toRingEquiv
  let e : PowerSeries K ≃+* A := model.equiv.symm.trans eA.symm
  have heC : ∀ c : K, e (PowerSeries.C c) = u c := by
    intro c
    apply eA.injective
    simpa [e, eA, AdicCompletion.ofAlgEquiv_apply,
      AdicCompletion.algebraMap_apply] using
      congrArg model.equiv.symm (model.maps_section c).symm
  have heX : e PowerSeries.X = π := by
    apply eA.injective
    simpa [e, eA, AdicCompletion.ofAlgEquiv_apply,
      AdicCompletion.algebraMap_apply] using
      congrArg model.equiv.symm model.maps_uniformizer.symm
  refine ⟨{
    equiv := e
    maps_constants := by
      ext c
      exact heC c
    maps_uniformizer := heX
    maps_maximal_ideal := by
      rw [Ideal.map_span]
      simp [heX, hπ] }⟩

/-- The coefficient expansion of a complete equicharacteristic DVR is the Cauchy expansion. -/
theorem chapter13_equicharacteristic_dvr_cauchy_expansion
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type v} [Field K]
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π})
    (u : K →+* A) (hu : IsLocalHom u ∧
      Function.Bijective ((Chapter13ResidueMap A).comp u)) :
    ∃ e : PowerSeries K ≃+* A,
      e.toRingHom.comp (PowerSeries.C : K →+* PowerSeries K) = u ∧
        e PowerSeries.X = π := by
  obtain ⟨model⟩ := chapter13_equicharacteristic_complete_dvr_power_series
    hA π hπ u hu
  exact ⟨model.equiv, model.maps_constants, model.maps_uniformizer⟩

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter13
