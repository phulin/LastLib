import LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.Section02EquivalentCharacterizations
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.UniqueFactorization

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter04

open scoped BigOperators Multiplicative PowerSeries WithZero
open Ideal IsLocalRing LinearOrderedCommGroup

noncomputable section

/-!
# Chapter 4: Discrete valuation rings

This chapter formalizes Sections 4.1--4.3 of Book 1.  The
zero-extended multiplicative target `ℤᵐ⁰` is used for Mathlib valuations; its
nonzero part is the additive integer-valued valuation `Kˣ → ℤ` from the prose.
-/

/-! # Book 1, Chapter 4, Section 4.3: Arithmetic and Examples
-/

/-! ## 4.2--4.3. Arithmetic of powers of the maximal ideal -/

/-- Membership in the valuation ring is the valuation inequality `v(x) ≤ 1`
in Mathlib's multiplicative convention. -/
theorem dvr_witness_mem_ring_iff_value_le_one
    (A K : Type*) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (W : Chapter04DVRValuationWitness A K) (x : K) :
    (∃ a : A, algebraMap A K a = x) ↔ W.valuation x ≤ 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    change algebraMap A K a ∈ W.valuation.valuationSubring.toSubring
    rw [W.valuationSubring_eq_image]
    exact Subring.mem_map.mpr ⟨a, by simp, rfl⟩
  · intro hx
    change x ∈ W.valuation.valuationSubring.toSubring at hx
    rw [W.valuationSubring_eq_image] at hx
    obtain ⟨a, _, hax⟩ := Subring.mem_map.mp hx
    exact ⟨a, hax⟩

/-- Membership in the unit group is exactly valuation `0` in additive language,
or value `1` in the multiplicative Mathlib language. -/
theorem dvr_witness_mem_unit_iff_value_one
    (A K : Type*) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (W : Chapter04DVRValuationWitness A K) (x : K) :
    (∃ u : Aˣ, algebraMap A K (u : A) = x) ↔ W.valuation x = 1 := by
  let hvA : W.valuation.Integers A :=
    { hom_inj := IsFractionRing.injective A K
      map_le_one := fun a =>
        (dvr_witness_mem_ring_iff_value_le_one A K W
          (algebraMap A K a)).1 ⟨a, rfl⟩
      exists_of_le_one := fun {r} hz =>
        (dvr_witness_mem_ring_iff_value_le_one A K W r).2 hz }
  constructor
  · rintro ⟨u, rfl⟩
    exact hvA.one_of_isUnit u.isUnit
  · intro hx
    obtain ⟨a, ha⟩ :=
      (dvr_witness_mem_ring_iff_value_le_one A K W x).2 hx.le
    have hunit : IsUnit a := hvA.isUnit_of_one'
      (by simpa [ha] using hx)
    exact ⟨hunit.unit, by simpa only [IsUnit.unit_spec] using ha⟩

/-- The maximal ideal is the strict valuation ball below `1`. -/
theorem dvr_witness_mem_maximal_ideal_iff_value_lt_one
    (A K : Type*) [CommRing A] [IsDomain A] [IsLocalRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (W : Chapter04DVRValuationWitness A K) (a : A) :
    a ∈ IsLocalRing.maximalIdeal A ↔
      W.valuation (algebraMap A K a) < 1 := by
  have hunit :
      (∃ u : Aˣ, algebraMap A K (u : A) = algebraMap A K a) ↔ IsUnit a := by
    constructor
    · rintro ⟨u, hu⟩
      have hEq : (u : A) = a :=
        IsFractionRing.injective A K (hu.trans rfl)
      exact hEq ▸ u.isUnit
    · intro ha
      obtain ⟨u, hu⟩ := ha
      exact ⟨u, by simp only [hu]⟩
  have hle : W.valuation (algebraMap A K a) ≤ 1 :=
    (dvr_witness_mem_ring_iff_value_le_one A K W (algebraMap A K a)).1
      ⟨a, rfl⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← hunit]
  constructor
  · intro h
    exact lt_of_le_of_ne hle (by
      intro heq
      exact h ((dvr_witness_mem_unit_iff_value_one A K W
        (algebraMap A K a)).2 heq))
  · intro hlt hu
    exact (ne_of_lt hlt) ((dvr_witness_mem_unit_iff_value_one A K W
      (algebraMap A K a)).1 hu)

/-- For a uniformizer, powers of the maximal ideal are the corresponding
valuation balls. -/
theorem dvr_witness_mem_maximal_ideal_power_iff_value_le_power
    (A K : Type*) [CommRing A] [IsDomain A] [IsLocalRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (W : Chapter04DVRValuationWitness A K) {π : A}
    (hπ : Chapter04Uniformizer A π) (r : ℕ) (a : A) :
    a ∈ IsLocalRing.maximalIdeal A ^ r ↔
      W.valuation (algebraMap A K a) ≤
        W.valuation (algebraMap A K π) ^ r := by
  let hvA : W.valuation.Integers A :=
    { hom_inj := IsFractionRing.injective A K
      map_le_one := fun a =>
        (dvr_witness_mem_ring_iff_value_le_one A K W
          (algebraMap A K a)).1 ⟨a, rfl⟩
      exists_of_le_one := fun {r} hz =>
        (dvr_witness_mem_ring_iff_value_le_one A K W r).2 hz }
  have : IsDiscreteValuationRing A :=
    (is_discrete_valuation_ring_iff_chapter04_valuation_witness A K).mpr ⟨W⟩
  have hπirr :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π hπ.1 hπ.2
  have hs := hvA.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow hπirr r
  exact Set.ext_iff.mp hs a

/-- The additive Mathlib valuation gives the same power-of-the-maximal-ideal
filtration, including the zero element at value `∞`. -/
theorem dvr_additive_value_mem_maximal_ideal_power_iff
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (a : A) (r : ℕ) :
    (r : ℕ∞) ≤ chapter04AdditiveValue A a ↔
      a ∈ IsLocalRing.maximalIdeal A ^ r := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  change (r : ℕ∞) ≤ IsDiscreteValuationRing.addVal A a ↔
    a ∈ IsLocalRing.maximalIdeal A ^ r
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd,
    hπ.addVal_pow r]

/-- Units are precisely the elements of additive value zero. -/
theorem dvr_additive_value_eq_zero_iff_isUnit
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (a : A) :
    chapter04AdditiveValue A a = 0 ↔ IsUnit a := by
  exact IsDiscreteValuationRing.addVal_eq_zero_iff

/-- Divisibility in a valuation ring is a total relation. -/
theorem dvr_divisibility_is_total
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    ∀ x y : A, x ∣ y ∨ y ∣ x := by
  intro x y
  obtain ⟨z, hz | hz⟩ := PreValuationRing.cond x y
  · exact Or.inl ⟨z, hz.symm⟩
  · exact Or.inr ⟨z, hz.symm⟩

/-- Sums of principal powers use the smaller exponent. -/
theorem dvr_ideal_power_sum_min
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} (hπ : Chapter04Uniformizer A π) (a b : ℕ) :
    chapter04IdealPower A π a ⊔ chapter04IdealPower A π b =
      chapter04IdealPower A π (min a b) := by
  have hp (n : ℕ) :
      chapter04IdealPower A π n = IsLocalRing.maximalIdeal A ^ n := by
      rw [chapter04IdealPower, hπ.2, Ideal.span_singleton_pow]
  rcases le_total a b with hab | hba
  · rw [hp, hp, hp, min_eq_left hab]
    exact sup_eq_left.mpr (Ideal.pow_le_pow_right hab)
  · rw [hp, hp, hp, min_eq_right hba]
    exact sup_eq_right.mpr (Ideal.pow_le_pow_right hba)

/-- Intersections of principal powers use the larger exponent. -/
theorem dvr_ideal_power_inf_max
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} (hπ : Chapter04Uniformizer A π) (a b : ℕ) :
    chapter04IdealPower A π a ⊓ chapter04IdealPower A π b =
      chapter04IdealPower A π (max a b) := by
  have hp (n : ℕ) :
      chapter04IdealPower A π n = IsLocalRing.maximalIdeal A ^ n := by
    rw [chapter04IdealPower, hπ.2, Ideal.span_singleton_pow]
  rcases le_total a b with hab | hba
  · rw [hp, hp, hp, max_eq_right hab]
    exact inf_eq_right.mpr (Ideal.pow_le_pow_right hab)
  · rw [hp, hp, hp, max_eq_left hba]
    exact inf_eq_left.mpr (Ideal.pow_le_pow_right hba)

/-- Products of principal powers add exponents. -/
theorem dvr_ideal_power_mul_add
    (A : Type*) [CommRing A] {π : A} (a b : ℕ) :
    chapter04IdealPower A π a * chapter04IdealPower A π b =
      chapter04IdealPower A π (a + b) := by
  simp [chapter04IdealPower, Ideal.span_singleton_mul_span_singleton, pow_add]

/-- The irreducibles of a DVR are exactly the elements of normalized value `1`. -/
theorem dvr_irreducible_iff_value_one
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (a : A) :
    Irreducible a ↔ chapter04AdditiveValue A a = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπval : IsDiscreteValuationRing.addVal A π = 1 :=
    IsDiscreteValuationRing.addVal_uniformizer hπ
  constructor
  · intro ha
    have hassoc := IsDiscreteValuationRing.associated_of_irreducible A ha
      hπ
    have heq := (IsDiscreteValuationRing.addVal_eq_iff_associated a π).2 hassoc
    simpa [chapter04AdditiveValue] using heq.trans hπval
  · intro ha
    have heq : IsDiscreteValuationRing.addVal A a =
        IsDiscreteValuationRing.addVal A π := ha.trans hπval.symm
    exact ((IsDiscreteValuationRing.addVal_eq_iff_associated a π).mp heq).symm.irreducible
      hπ

/-- All irreducibles in a DVR are associates. -/
theorem dvr_all_irreducibles_are_associates
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {p q : A} (hp : Irreducible p) (hq : Irreducible q) :
    Associated p q := by
  exact IsDiscreteValuationRing.associated_of_irreducible A hp hq

/-! ## 4.3. Principal examples -/

/-- A reusable spelling for localization at a prime ideal. -/
abbrev chapter04AtPrimeLocalization (R : Type*) [CommRing R] (P : Ideal R)
    [P.IsPrime] : Type _ :=
  Localization.AtPrime P

/-- In a Dedekind domain, localization at a nonzero prime is a DVR. -/
theorem dedekind_localization_at_nonzero_prime_is_dvr
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) (hP : P ≠ ⊥) [P.IsPrime] :
    IsDiscreteValuationRing (chapter04AtPrimeLocalization R P) := by
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    R hP (Localization.AtPrime P)

/-- For a prime ideal of `ℤ` generated by a rational prime, the local ring is a
DVR. The displayed `P` records the usual notation `ℤ_(p)`. -/
theorem integer_localization_at_prime_is_dvr
    (p : ℕ) (_hp : Nat.Prime p) (P : Ideal ℤ) [P.IsPrime]
    (_hP : P = Ideal.span ({(p : ℤ)} : Set ℤ)) (hP0 : P ≠ ⊥) :
    IsDiscreteValuationRing (chapter04AtPrimeLocalization ℤ P) := by
  exact dedekind_localization_at_nonzero_prime_is_dvr ℤ P hP0

/-- The uniformizer of `ℤ_(p)` is the image of `p`. -/
theorem integer_localization_uniformizer
    (p : ℕ) (hp : Nat.Prime p) (P : Ideal ℤ) [P.IsPrime]
    (hP : P = Ideal.span ({(p : ℤ)} : Set ℤ)) (_hP0 : P ≠ ⊥) :
    Chapter04Uniformizer (chapter04AtPrimeLocalization ℤ P)
      (algebraMap ℤ (chapter04AtPrimeLocalization ℤ P) (p : ℤ)) := by
  let L := chapter04AtPrimeLocalization ℤ P
  have : IsDiscreteValuationRing L :=
    integer_localization_at_prime_is_dvr p hp P hP _hP0
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have : P.IsMaximal := by
    rw [hP]
    exact Int.ideal_span_isMaximal_of_prime p
  have hp0 : (p : ℤ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hmap0 : algebraMap ℤ L (p : ℤ) ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap ℤ L)
      (IsLocalization.injective L P.primeCompl_le_nonZeroDivisors)).2 hp0
  have hmax :
      IsLocalRing.maximalIdeal L =
        Ideal.span ({algebraMap ℤ L (p : ℤ)} : Set L) := by
    calc
      IsLocalRing.maximalIdeal L = Ideal.map (algebraMap ℤ L) P :=
        (IsLocalization.AtPrime.map_eq_maximalIdeal P L).symm
      _ = Ideal.map (algebraMap ℤ L)
          (Ideal.span ({(p : ℤ)} : Set ℤ)) :=
        congrArg (Ideal.map (algebraMap ℤ L)) hP
      _ = Ideal.span ({algebraMap ℤ L (p : ℤ)} : Set L) := by
        rw [Ideal.map_span]
        simp
  exact ⟨hmap0, hmax⟩

/-- The residue field of `ℤ_(p)` is `𝔽_p`, represented by `ZMod p`. -/
theorem integer_localization_residue_field
    (p : ℕ) (hp : Nat.Prime p) (P : Ideal ℤ) [P.IsPrime]
    (hP : P = Ideal.span ({(p : ℤ)} : Set ℤ)) (_hP0 : P ≠ ⊥) :
    Nonempty (IsLocalRing.ResidueField (chapter04AtPrimeLocalization ℤ P) ≃+* ZMod p) := by
  let L := chapter04AtPrimeLocalization ℤ P
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have : P.IsMaximal := by
    rw [hP]
    exact Int.ideal_span_isMaximal_of_prime p
  change Nonempty (L ⧸ IsLocalRing.maximalIdeal L ≃+* ZMod p)
  let e₁ := (IsLocalization.AtPrime.equivQuotMaximalIdeal P L).symm
  let e₂ : (ℤ ⧸ P) ≃+* (ℤ ⧸ Ideal.span ({(p : ℤ)} : Set ℤ)) :=
    Ideal.quotEquivOfEq hP
  have hn : (p : ℤ).natAbs = p := by
    simp
  refine ⟨e₁.trans (e₂.trans ?_)⟩
  simpa [hn] using (Int.quotientSpanEquivZMod (p : ℤ))

/-- The localization `k[t]_(t)` is a DVR with uniformizer `t`. -/
theorem polynomial_localization_at_X_is_dvr
    (k : Type*) [Field k] (P : Ideal (Polynomial k)) [P.IsPrime]
    (hP : P = Ideal.span ({Polynomial.X} : Set (Polynomial k))) :
    IsDiscreteValuationRing (chapter04AtPrimeLocalization (Polynomial k) P) := by
  have : IsDedekindDomain (Polynomial k) := inferInstance
  have hP0 : P ≠ ⊥ := by
    intro hbot
    have hX0 : (Polynomial.X : Polynomial k) ≠ 0 := Polynomial.X_ne_zero
    exact hX0 (Ideal.span_singleton_eq_bot.mp (hP.symm.trans hbot))
  exact dedekind_localization_at_nonzero_prime_is_dvr (Polynomial k) P hP0

/-- The image of `t` is the uniformizer in `k[t]_(t)`. -/
theorem polynomial_localization_at_X_uniformizer
    (k : Type*) [Field k] (P : Ideal (Polynomial k)) [P.IsPrime]
    (hP : P = Ideal.span ({Polynomial.X} : Set (Polynomial k))) :
    Chapter04Uniformizer (chapter04AtPrimeLocalization (Polynomial k) P)
      (algebraMap (Polynomial k)
        (chapter04AtPrimeLocalization (Polynomial k) P) Polynomial.X) := by
  let L := chapter04AtPrimeLocalization (Polynomial k) P
  have : IsDiscreteValuationRing L :=
    polynomial_localization_at_X_is_dvr k P hP
  have : P.IsMaximal := by
    rw [hP]
    have hXi : Irreducible (Polynomial.X : Polynomial k) :=
      Polynomial.irreducible_X
    exact PrincipalIdealRing.isMaximal_of_irreducible hXi
  have hX0 : (Polynomial.X : Polynomial k) ≠ 0 := Polynomial.X_ne_zero
  have hmap0 : algebraMap (Polynomial k) L Polynomial.X ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap (Polynomial k) L)
      (IsLocalization.injective L P.primeCompl_le_nonZeroDivisors)).2
      hX0
  have hmax :
      IsLocalRing.maximalIdeal L =
        Ideal.span
          ({algebraMap (Polynomial k) L Polynomial.X} : Set L) := by
    calc
      IsLocalRing.maximalIdeal L = Ideal.map (algebraMap (Polynomial k) L) P :=
        (IsLocalization.AtPrime.map_eq_maximalIdeal P L).symm
      _ = Ideal.map (algebraMap (Polynomial k) L)
          (Ideal.span ({Polynomial.X} : Set (Polynomial k))) :=
        congrArg (Ideal.map (algebraMap (Polynomial k) L)) hP
      _ = Ideal.span
          ({algebraMap (Polynomial k) L Polynomial.X} : Set L) := by
        rw [Ideal.map_span]
        simp
  exact ⟨hmap0, hmax⟩

/-- The residue field of `k[t]_(t)` is `k`. -/
theorem polynomial_localization_at_X_residue_field
    (k : Type*) [Field k] (P : Ideal (Polynomial k)) [P.IsPrime]
    (hP : P = Ideal.span ({Polynomial.X} : Set (Polynomial k))) :
    Nonempty (IsLocalRing.ResidueField (chapter04AtPrimeLocalization (Polynomial k) P) ≃+* k) := by
  let L := chapter04AtPrimeLocalization (Polynomial k) P
  have : P.IsMaximal := by
    rw [hP]
    have hXi : Irreducible (Polynomial.X : Polynomial k) :=
      Polynomial.irreducible_X
    exact PrincipalIdealRing.isMaximal_of_irreducible hXi
  change Nonempty (L ⧸ IsLocalRing.maximalIdeal L ≃+* k)
  let e₁ := (IsLocalization.AtPrime.equivQuotMaximalIdeal P L).symm
  let e₂ : (Polynomial k ⧸ P) ≃+* (Polynomial k ⧸
      Ideal.span ({Polynomial.X} : Set (Polynomial k))) :=
    Ideal.quotEquivOfEq hP
  refine ⟨e₁.trans (e₂.trans ?_)⟩
  have hspan : Ideal.span ({Polynomial.X - Polynomial.C (0 : k)} :
      Set (Polynomial k)) = Ideal.span ({Polynomial.X} : Set (Polynomial k)) := by
    simp only [map_zero, sub_zero]
  exact (Ideal.quotEquivOfEq hspan.symm).trans
    (Polynomial.quotientSpanXSubCAlgEquiv (0 : k)).toRingEquiv

/-- For irreducible `P ∈ k[t]`, the local ring `k[t]_(P)` is a DVR with
uniformizer the image of `P`. -/
theorem polynomial_localization_at_irreducible_is_dvr
    (k : Type*) [Field k] (f : Polynomial k) (hf : Irreducible f)
    (P : Ideal (Polynomial k)) [P.IsPrime]
    (hP : P = Ideal.span ({f} : Set (Polynomial k))) :
    IsDiscreteValuationRing (chapter04AtPrimeLocalization (Polynomial k) P) := by
  have : IsDedekindDomain (Polynomial k) := inferInstance
  have hP0 : P ≠ ⊥ := by
    intro hbot
    apply hf.ne_zero
    exact Ideal.span_singleton_eq_bot.mp (hP.symm.trans hbot)
  exact dedekind_localization_at_nonzero_prime_is_dvr (Polynomial k) P hP0

/-- The image of an irreducible polynomial generates the maximal ideal of
`k[t]_(P)`. -/
theorem polynomial_localization_at_irreducible_uniformizer
    (k : Type*) [Field k] (f : Polynomial k) (hf : Irreducible f)
    (P : Ideal (Polynomial k)) [P.IsPrime]
    (hP : P = Ideal.span ({f} : Set (Polynomial k))) :
    Chapter04Uniformizer (chapter04AtPrimeLocalization (Polynomial k) P)
      (algebraMap (Polynomial k)
        (chapter04AtPrimeLocalization (Polynomial k) P) f) := by
  let L := chapter04AtPrimeLocalization (Polynomial k) P
  have : IsDiscreteValuationRing L :=
    polynomial_localization_at_irreducible_is_dvr k f hf P hP
  have : P.IsMaximal := by
    rw [hP]
    exact PrincipalIdealRing.isMaximal_of_irreducible hf
  have hf0 : f ≠ 0 := hf.ne_zero
  have hmap0 : algebraMap (Polynomial k) L f ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap (Polynomial k) L)
      (IsLocalization.injective L P.primeCompl_le_nonZeroDivisors)).2
      hf0
  have hmax :
      IsLocalRing.maximalIdeal L =
        Ideal.span ({algebraMap (Polynomial k) L f} : Set L) := by
    calc
      IsLocalRing.maximalIdeal L = Ideal.map (algebraMap (Polynomial k) L) P :=
        (IsLocalization.AtPrime.map_eq_maximalIdeal P L).symm
      _ = Ideal.map (algebraMap (Polynomial k) L)
          (Ideal.span ({f} : Set (Polynomial k))) :=
        congrArg (Ideal.map (algebraMap (Polynomial k) L)) hP
      _ = Ideal.span ({algebraMap (Polynomial k) L f} : Set L) := by
        rw [Ideal.map_span]
        simp
  exact ⟨hmap0, hmax⟩

/-- The residue field at `(f)` is `k[t]/(f)`. -/
theorem polynomial_localization_at_irreducible_residue_field
    (k : Type*) [Field k] (f : Polynomial k) (hf : Irreducible f)
    (P : Ideal (Polynomial k)) [P.IsPrime]
    (hP : P = Ideal.span ({f} : Set (Polynomial k))) :
    Nonempty
      (IsLocalRing.ResidueField (chapter04AtPrimeLocalization (Polynomial k) P) ≃+*
        (Polynomial k ⧸ (Ideal.span ({f} : Set (Polynomial k))))) := by
  let L := chapter04AtPrimeLocalization (Polynomial k) P
  have : P.IsMaximal := by
    rw [hP]
    exact PrincipalIdealRing.isMaximal_of_irreducible hf
  change Nonempty (L ⧸ IsLocalRing.maximalIdeal L ≃+*
      (Polynomial k ⧸ Ideal.span ({f} : Set (Polynomial k))))
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal P L
  refine ⟨e.symm.trans ?_⟩
  exact Ideal.quotEquivOfEq hP

/-- The formal parameter `t` in a formal power series ring. -/
def chapter04FormalPowerSeriesParameter (k : Type*) [Semiring k] : PowerSeries k :=
  PowerSeries.X

/-- The formal power series residue-field equivalence supplied by Mathlib. -/
def chapter04FormalPowerSeriesResidueEquiv (k : Type*) [Field k] :
    IsLocalRing.ResidueField (PowerSeries k) ≃+* k :=
  PowerSeries.residueFieldOfPowerSeries (k := k)

/-- Every element of `k[[t]]` is a coefficient sequence, i.e. a formal sum
`∑ aₙ tⁿ`. -/
theorem formal_power_series_coefficient_expansion
    (k : Type*) [Semiring k] (f : PowerSeries k) :
    ∃ a : ℕ → k, f = PowerSeries.mk a := by
  refine ⟨fun n => PowerSeries.coeff n f, ?_⟩
  ext n
  simp

/-- A power series over a field is a unit exactly when its constant coefficient
is nonzero. -/
theorem formal_power_series_unit_iff_constant_coefficient_ne_zero
    (k : Type*) [Field k] (f : PowerSeries k) :
    IsUnit f ↔ PowerSeries.constantCoeff f ≠ 0 := by
  rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]

/-- Every nonzero power series is `t^n u` for a unit `u`. -/
theorem formal_power_series_unique_power_unit_factorization
    (k : Type*) [Field k] {f : PowerSeries k} (hf : f ≠ 0) :
    ∃ (n : ℕ) (u : (PowerSeries k)ˣ),
      f = (PowerSeries.X ^ n) * (u : PowerSeries k) ∧
        ∀ (m : ℕ) (w : (PowerSeries k)ˣ),
          f = (PowerSeries.X ^ m) * (w : PowerSeries k) → m = n ∧ w = u := by
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf PowerSeries.X_irreducible
  refine ⟨n, u, ?_, ?_⟩
  · simpa [mul_comm] using hu
  · intro m w hw
    have heq :
        (u : PowerSeries k) * PowerSeries.X ^ n =
          (w : PowerSeries k) * PowerSeries.X ^ m := by
      simpa [mul_comm] using hu.symm.trans hw
    exact ⟨
      (IsDiscreteValuationRing.unit_mul_pow_congr_pow
        PowerSeries.X_irreducible PowerSeries.X_irreducible u w n m heq).symm,
      (IsDiscreteValuationRing.unit_mul_pow_congr_unit
        PowerSeries.X_irreducible u w n m heq).symm⟩

/-- `k[[t]]` is a DVR. -/
theorem formal_power_series_is_dvr
    (k : Type*) [Field k] :
    IsDiscreteValuationRing (PowerSeries k) := by
  infer_instance

/-- The maximal ideal of `k[[t]]` is generated by `t`. -/
theorem formal_power_series_maximal_ideal
    (k : Type*) [Field k] :
    IsLocalRing.maximalIdeal (PowerSeries k) =
      Ideal.span ({PowerSeries.X} : Set (PowerSeries k)) := by
  exact PowerSeries.maximalIdeal_eq_span_X

/-- The residue field of `k[[t]]` is `k`. -/
theorem formal_power_series_residue_field
    (k : Type*) [Field k] :
    Nonempty (IsLocalRing.ResidueField (PowerSeries k) ≃+* k) := by
  exact ⟨chapter04FormalPowerSeriesResidueEquiv k⟩

/-- The fraction field of `k[[t]]` is the Laurent-series field `k((t))`. -/
theorem formal_power_series_fraction_field_is_laurent_series
    (k : Type*) [Field k] :
    IsFractionRing (PowerSeries k) (LaurentSeries k) := by
  infer_instance

/-- Formal power series are complete for the `t`-adic topology. -/
theorem formal_power_series_is_complete
    (k : Type*) [Field k] :
    IsAdicComplete
      (Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) (PowerSeries k) := by
  infer_instance

/-- The local polynomial example and the formal power-series example have the
same uniformizer and residue field, but only the latter is complete. -/
theorem polynomial_localization_and_power_series_comparison
    (k : Type*) [Field k] (P : Ideal (Polynomial k)) [P.IsPrime]
    (hP : P = Ideal.span ({Polynomial.X} : Set (Polynomial k))) :
    Chapter04Uniformizer (chapter04AtPrimeLocalization (Polynomial k) P)
        (algebraMap (Polynomial k)
          (chapter04AtPrimeLocalization (Polynomial k) P) Polynomial.X) ∧
      Chapter04Uniformizer (PowerSeries k) PowerSeries.X ∧
      Nonempty (IsLocalRing.ResidueField (chapter04AtPrimeLocalization (Polynomial k) P) ≃+* k) ∧
      Nonempty (IsLocalRing.ResidueField (PowerSeries k) ≃+* k) ∧
      ¬ IsAdicComplete
          (IsLocalRing.maximalIdeal (chapter04AtPrimeLocalization (Polynomial k) P))
          (chapter04AtPrimeLocalization (Polynomial k) P) ∧
      IsAdicComplete
        (Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) (PowerSeries k) := by
  classical
  have h₁ := polynomial_localization_at_X_uniformizer k P hP
  have h₂ : Chapter04Uniformizer (PowerSeries k) PowerSeries.X := by
    exact ⟨PowerSeries.X_ne_zero, PowerSeries.maximalIdeal_eq_span_X⟩
  have h₃ := polynomial_localization_at_X_residue_field k P hP
  have h₄ : Nonempty (IsLocalRing.ResidueField (PowerSeries k) ≃+* k) :=
    formal_power_series_residue_field k
  have h₆ := formal_power_series_is_complete k
  refine ⟨h₁, h₂, ?_, h₄, ?_, h₆⟩
  · simpa using h₃
  · intro hcomplete
    have : IsAdicComplete
        (IsLocalRing.maximalIdeal (chapter04AtPrimeLocalization (Polynomial k) P))
        (chapter04AtPrimeLocalization (Polynomial k) P) := hcomplete
    have hX : algebraMap (Polynomial k)
        (chapter04AtPrimeLocalization (Polynomial k) P) Polynomial.X ≠ 0 :=
      (polynomial_localization_at_X_uniformizer k P hP).1
    have hpow : ∀ n : ℕ, (algebraMap (Polynomial k)
        (chapter04AtPrimeLocalization (Polynomial k) P) Polynomial.X) ^ n ∈
        IsLocalRing.maximalIdeal (chapter04AtPrimeLocalization (Polynomial k) P) ^ n := by
      intro n
      have hxM : algebraMap (Polynomial k)
          (chapter04AtPrimeLocalization (Polynomial k) P) Polynomial.X ∈
          IsLocalRing.maximalIdeal (chapter04AtPrimeLocalization (Polynomial k) P) := by
        rw [(polynomial_localization_at_X_uniformizer k P hP).2]
        exact Ideal.mem_span_singleton_self _
      exact Ideal.pow_mem_pow hxM n
    have htop : IsLocalRing.maximalIdeal
        (chapter04AtPrimeLocalization (Polynomial k) P) ≠ ⊤ :=
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    have hzero : (⨅ n : ℕ, IsLocalRing.maximalIdeal
        (chapter04AtPrimeLocalization (Polynomial k) P) ^ n) = ⊥ := by
      exact Ideal.iInf_pow_eq_bot_of_isLocalRing
        (IsLocalRing.maximalIdeal _) htop
    have hnotpoly : ¬ IsAdicComplete
        (Ideal.span ({Polynomial.X} : Set (Polynomial k))) (Polynomial k) := by
      intro hpoly
      let I : Ideal (Polynomial k) :=
        Ideal.span ({Polynomial.X} : Set (Polynomial k))
      change IsAdicComplete I (Polynomial k) at hpoly
      let f : ℕ → Polynomial k := fun n =>
        ∑ i ∈ Finset.range n, Polynomial.X ^ i
      have hf : ∀ {m n : ℕ}, m ≤ n →
          f m ≡ f n [SMOD (I ^ m • (⊤ : Submodule (Polynomial k) (Polynomial k)))] := by
        intro m n h
        simp only [f, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
        rw [← add_tsub_cancel_of_le h, Finset.sum_range_add, ← sub_sub, sub_self,
          zero_sub, @neg_mem_iff]
        apply Submodule.sum_mem
        intro j _
        rw [pow_add]
        exact Ideal.mul_mem_right _ (I ^ m)
          (Ideal.pow_mem_pow (by simp [I]) m)
      obtain ⟨L, hL⟩ := IsPrecomplete.prec hpoly.toIsPrecomplete hf
      have hdiff := hL (L.natDegree + 2)
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hdiff
      change f (L.natDegree + 2) - L ∈
        (Ideal.span ({Polynomial.X} : Set (Polynomial k))) ^ (L.natDegree + 2) at hdiff
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hdiff
      have hzero :
          (f (L.natDegree + 2) - L).coeff (L.natDegree + 1) = 0 :=
        (Polynomial.X_pow_dvd_iff.mp hdiff) _ (by omega)
      have hfone :
          (f (L.natDegree + 2) - L).coeff (L.natDegree + 1) = 1 := by
        rw [Polynomial.coeff_sub]
        have hsum :
            (f (L.natDegree + 2)).coeff (L.natDegree + 1) = 1 := by
          simp [f, Polynomial.coeff_X_pow]
        rw [hsum, Polynomial.coeff_natDegree_succ_eq_zero, sub_zero]
      rw [hfone] at hzero
      exact one_ne_zero hzero
    let L := chapter04AtPrimeLocalization (Polynomial k) P
    let M : Ideal L := IsLocalRing.maximalIdeal L
    let I : Ideal (Polynomial k) :=
      Ideal.span ({Polynomial.X} : Set (Polynomial k))
    have : P.IsMaximal := by
      rw [hP]
      exact PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
    change IsAdicComplete M L at hcomplete
    have : IsAdicComplete M L := hcomplete
    let f : ℕ → Polynomial k := fun n =>
      ∑ i ∈ Finset.range n, Polynomial.X ^ (i * i)
    have hX : (Polynomial.X : Polynomial k) ∈ I := by
      exact Ideal.subset_span (by simp)
    have hf : ∀ {m n : ℕ}, m ≤ n →
        (algebraMap (Polynomial k) L (f m)) ≡
          (algebraMap (Polynomial k) L (f n))
            [SMOD (M ^ m • (⊤ : Submodule L L))] := by
      intro m n hmn
      rw [SModEq.sub_mem]
      have hpoly : f m - f n ∈ I ^ m := by
        simp only [f]
        rw [← add_tsub_cancel_of_le hmn, Finset.sum_range_add, ← sub_sub,
          sub_self, zero_sub, @neg_mem_iff]
        apply Submodule.sum_mem
        intro j hj
        have hem : m ≤ (m + j) * (m + j) := by
          by_cases hm : m = 0
          · simp [hm]
          · have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
            exact le_trans (Nat.le_mul_self m)
              (Nat.mul_le_mul (Nat.le_add_right m j) (Nat.le_add_right m j))
        have heq : (m + j) * (m + j) =
            m + ((m + j) * (m + j) - m) :=
          (Nat.add_sub_of_le hem).symm
        rw [heq, pow_add]
        exact Ideal.mul_mem_right _ (I ^ m) (Ideal.pow_mem_pow hX m)
      have hmap : Ideal.map (algebraMap (Polynomial k) L) (I ^ m) = M ^ m := by
        rw [show I = P by simpa [I] using hP.symm, Ideal.map_pow]
        exact (IsLocalization.AtPrime.map_eq_maximalIdeal P L).symm ▸ rfl
      have hmem : algebraMap (Polynomial k) L (f m - f n) ∈ M ^ m := by
        rw [← hmap]
        exact Ideal.mem_map_of_mem (algebraMap (Polynomial k) L) hpoly
      simpa [map_sub, smul_eq_mul, Ideal.mul_top] using hmem
    obtain ⟨L₀, hL⟩ := IsPrecomplete.prec (I := M) (M := L)
      inferInstance hf
    obtain ⟨q, s, hs⟩ := IsLocalization.exists_mk'_eq P.primeCompl L₀
    have hsrel : algebraMap (Polynomial k) L (s : Polynomial k) * L₀ =
        algebraMap (Polynomial k) L q := by
      simpa [hs] using
        (IsLocalization.mk'_spec' L q s)
    have hsnotP : (s : Polynomial k) ∉ P := s.property
    have hsnotI : (s : Polynomial k) ∉ I := by
      simpa [I, hP] using hsnotP
    have hs0 : (s : Polynomial k).coeff 0 ≠ 0 := by
      intro hs0
      apply hsnotI
      rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
      exact hs0
    let r := (s : Polynomial k).natDegree + q.natDegree + 2
    have hrpos : 1 ≤ r := by
      dsimp [r]
      omega
    have hrfac : (s : Polynomial k).natDegree ≤ r - 1 := by
      dsimp [r]
      omega
    have hqdeg : q.natDegree < r * r := by
      dsimp [r]
      nlinarith
    let N := r * r + 1
    have hLN : algebraMap (Polynomial k) L (f N) - L₀ ∈ M ^ N := by
      simpa [smul_eq_mul, Ideal.mul_top] using (SModEq.sub_mem.mp (hL N))
    have hclear : algebraMap (Polynomial k) L
          ((s : Polynomial k) * f N - q) ∈ M ^ N := by
      have hmul : algebraMap (Polynomial k) L (s : Polynomial k) *
          (algebraMap (Polynomial k) L (f N) - L₀) ∈ M ^ N :=
        (M ^ N).mul_mem_left _ hLN
      rw [mul_sub, hsrel] at hmul
      simpa [map_sub, map_mul, mul_sub, mul_assoc, mul_comm, mul_left_comm] using hmul
    have hpolyN : (s : Polynomial k) * f N - q ∈ P ^ N := by
      have hmem : (s : Polynomial k) * f N - q ∈
          (M ^ N).under (Polynomial k) := by
        rw [Ideal.mem_under]
        exact hclear
      rw [← IsLocalization.AtPrime.under_maximalIdeal_pow P L N]
      exact hmem
    have hdivN : (Polynomial.X : Polynomial k) ^ N ∣
        (s : Polynomial k) * f N - q := by
      have hpolyNI : (s : Polynomial k) * f N - q ∈ I ^ N := by
        change (s : Polynomial k) * f N - q ∈
          (Ideal.span {(Polynomial.X : Polynomial k)}) ^ N
        rw [← hP]
        exact hpolyN
      rw [show I = Ideal.span {(Polynomial.X : Polynomial k)} by rfl,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hpolyNI
      exact hpolyNI
    have hcoeffzero : ((s : Polynomial k) * f N - q).coeff (r * r) = 0 :=
      (Polynomial.X_pow_dvd_iff.mp hdivN) _ (by dsimp [N]; omega)
    have hcoeffprod : ((s : Polynomial k) * f N).coeff (r * r) =
        (s : Polynomial k).coeff 0 := by
      simp only [f, Finset.mul_sum, Polynomial.finsetSum_coeff]
      simp_rw [Polynomial.coeff_mul_X_pow']
      have hsum :
          (∑ i ∈ Finset.range N,
            if i * i ≤ r * r then (s : Polynomial k).coeff (r * r - i * i)
            else 0) =
            (if r * r ≤ r * r then (s : Polynomial k).coeff (r * r - r * r)
            else 0) := by
        apply Finset.sum_eq_single r
        · intro i hi hir
          by_cases hir' : i < r
          · have hi2 : i * i ≤ (r - 1) * (r - 1) := by
              apply Nat.mul_le_mul
              · exact Nat.le_pred_of_lt hir'
              · exact Nat.le_pred_of_lt hir'
            have hbound : (s : Polynomial k).natDegree + i * i < r * r := by
              have hbase : (s : Polynomial k).natDegree + (r - 1) * (r - 1) <
                  r * r := by
                dsimp [r]
                nlinarith
              omega
            have hzero : (s : Polynomial k).coeff (r * r - i * i) = 0 :=
              Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
            simp [Nat.mul_le_mul hir'.le hir'.le, hzero]
          · have hri : r < i := Nat.lt_of_le_of_ne
                (Nat.le_of_not_gt hir') (Ne.symm hir)
            have hi2 : r * r < i * i := by
              calc
                r * r < r * i := Nat.mul_lt_mul_of_pos_left hri (by omega)
                _ < i * i := Nat.mul_lt_mul_of_pos_right hri (by omega)
            simp [not_le.mpr hi2]
        · intro hrnot
          have hriN : r < N := by
            dsimp [N]
            have hrle : r ≤ r * r := by
              simpa using Nat.mul_le_mul_left r hrpos
            omega
          exact (hrnot (Finset.mem_range.mpr hriN)).elim
      simpa using hsum
    have hcoeffq : q.coeff (r * r) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hqdeg
    have : (s : Polynomial k).coeff 0 = 0 := by
      rw [Polynomial.coeff_sub, hcoeffprod, hcoeffq] at hcoeffzero
      exact sub_eq_zero.mp hcoeffzero
    exact hs0 this

/-! ## 4.3. Failure examples -/

/-- The coefficient description of `k[[t²,t³]]`: the coefficient of `t` is
zero, while all degrees `0` and at least `2` are allowed. -/
def chapter04CuspPowerSeriesSubring (k : Type*) [CommRing k] :
    Subring (PowerSeries k) := by
  refine
    { carrier := {f | PowerSeries.coeff 1 f = 0}
      zero_mem' := by simp
      add_mem' := by
        intro f g hf hg
        change PowerSeries.coeff 1 f = 0 at hf
        change PowerSeries.coeff 1 g = 0 at hg
        change PowerSeries.coeff 1 (f + g) = 0
        simp [map_add, hf, hg]
      one_mem' := by simp
      mul_mem' := by
        intro f g hf hg
        change PowerSeries.coeff 1 f = 0 at hf
        change PowerSeries.coeff 1 g = 0 at hg
        change PowerSeries.coeff 1 (f * g) = 0
        rw [PowerSeries.coeff_one_mul]
        simp [hf, hg]
      neg_mem' := by
        intro f hf
        change PowerSeries.coeff 1 f = 0 at hf
        change PowerSeries.coeff 1 (-f) = 0
        simp [map_neg, hf] }

/-- The `t²` generator of the cusp power-series ring. -/
def chapter04CuspPowerSeriesT2 (k : Type*) [CommRing k] :
    chapter04CuspPowerSeriesSubring k := by
  refine ⟨PowerSeries.X ^ 2, ?_⟩
  change PowerSeries.coeff 1 (PowerSeries.X ^ 2) = 0
  simp

/-- The `t³` generator of the cusp power-series ring. -/
def chapter04CuspPowerSeriesT3 (k : Type*) [CommRing k] :
    chapter04CuspPowerSeriesSubring k := by
  refine ⟨PowerSeries.X ^ 3, ?_⟩
  change PowerSeries.coeff 1 (PowerSeries.X ^ 3) = 0
  simp

/-- The maximal ideal `(t²,t³)` in the cusp power-series ring. -/
def chapter04CuspPowerSeriesMaximalIdeal (k : Type*) [Field k] :
    Ideal (chapter04CuspPowerSeriesSubring k) := by
  exact Ideal.span
    ({chapter04CuspPowerSeriesT2 k, chapter04CuspPowerSeriesT3 k} :
      Set (chapter04CuspPowerSeriesSubring k))

/-- The ambient parameter `t`, which is absent from `k[[t²,t³]]`. -/
def chapter04CuspAmbientParameter (k : Type*) [CommRing k] : PowerSeries k :=
  PowerSeries.X

/-- `k[[t²,t³]]` is a complete one-dimensional domain but is not normal. -/
theorem cusp_power_series_is_complete_one_dimensional_non_normal
    (k : Type*) [Field k] :
    IsDomain (chapter04CuspPowerSeriesSubring k) ∧
      IsLocalRing (chapter04CuspPowerSeriesSubring k) ∧
      IsAdicComplete
        (chapter04CuspPowerSeriesMaximalIdeal k)
        (chapter04CuspPowerSeriesSubring k) ∧
      ringKrullDim (chapter04CuspPowerSeriesSubring k) = 1 ∧
      ¬ IsIntegrallyClosed (chapter04CuspPowerSeriesSubring k) := by
  classical
  let S := chapter04CuspPowerSeriesSubring k
  let M := chapter04CuspPowerSeriesMaximalIdeal k
  have hdom : IsDomain S := by infer_instance
  have : IsDomain S := hdom
  have hunit : ∀ (x : PowerSeries k) (hx : x ∈ S), IsUnit x →
      IsUnit (⟨x, hx⟩ : S) := by
    intro x hx hu
    rcases hu with ⟨u, rfl⟩
    change PowerSeries.coeff 1 (u : PowerSeries k) = 0 at hx
    have hcc : PowerSeries.constantCoeff (u : PowerSeries k) ≠ 0 :=
      isUnit_iff_ne_zero.mp
        ((PowerSeries.isUnit_iff_constantCoeff).mp u.isUnit)
    have hc := congrArg (PowerSeries.coeff 1) u.val_inv
    have hc' : PowerSeries.coeff 1 (↑(u⁻¹) : PowerSeries k) *
        PowerSeries.constantCoeff (u : PowerSeries k) = 0 := by
      rw [PowerSeries.coeff_one_mul] at hc
      simpa [hx] using hc
    have hcoeff : PowerSeries.coeff 1 (↑(u⁻¹) : PowerSeries k) = 0 :=
      (mul_eq_zero.mp hc').resolve_right hcc
    let us : Sˣ :=
      { val := ⟨(u : PowerSeries k), hx⟩
        inv := ⟨(↑(u⁻¹) : PowerSeries k), hcoeff⟩
        val_inv := by
          apply Subtype.ext
          exact u.val_inv
        inv_val := by
          apply Subtype.ext
          exact u.inv_val }
    exact ⟨us, rfl⟩
  have hlocal : IsLocalRing S := by
    exact Subring.isLocalRing_of_unit S hunit
  have : IsLocalRing S := hlocal
  let I : Ideal (PowerSeries k) :=
    Ideal.span ({PowerSeries.X} : Set (PowerSeries k))
  have hMmap : Ideal.map S.subtype M ≤ I ^ 2 := by
    change Ideal.map S.subtype
        (Ideal.span ({chapter04CuspPowerSeriesT2 k,
          chapter04CuspPowerSeriesT3 k} : Set S)) ≤ I ^ 2
    rw [Ideal.map_span]
    apply Ideal.span_le.2
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with rfl | rfl
    · change (PowerSeries.X : PowerSeries k) ^ 2 ∈ I ^ 2
      exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) 2
    · change (PowerSeries.X : PowerSeries k) ^ 3 ∈ I ^ 2
      have hX2 : (PowerSeries.X : PowerSeries k) ^ 2 ∈ I ^ 2 :=
        Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) 2
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
        (I ^ 2).mul_mem_left (PowerSeries.X : PowerSeries k) hX2
  have hpowmap : ∀ n : ℕ,
      Ideal.map S.subtype (M ^ n) ≤ I ^ (2 * n) := by
    intro n
    rw [Ideal.map_pow, pow_mul]
    exact Ideal.pow_right_mono hMmap n
  have hkey : ∀ (n : ℕ) (x : S),
      (x : PowerSeries k) ∈ I ^ (2 * n) → x ∈ M ^ n := by
    intro n x hx
    by_cases hn : n = 0
    · subst n
      simp
    have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    let N := n
    have hxspan : (x : PowerSeries k) ∈
        Ideal.span ({(PowerSeries.X : PowerSeries k) ^ (2 * N)} :
          Set (PowerSeries k)) := by
      simpa [I, N, Ideal.span_singleton_pow] using hx
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hxspan
    let q : PowerSeries k :=
      g - PowerSeries.C (PowerSeries.coeff 0 g) -
        PowerSeries.C (PowerSeries.coeff 1 g) * PowerSeries.X
    have hq : PowerSeries.coeff 1 q = 0 := by
      dsimp [q]
      rw [map_sub, map_sub, PowerSeries.coeff_one_mul]
      simp
    let qS : S := ⟨q, hq⟩
    let c0S : S :=
      ⟨PowerSeries.C (PowerSeries.coeff 0 g), by
        change PowerSeries.coeff 1 (PowerSeries.C _) = 0
        exact PowerSeries.coeff_C_of_ne_zero (by omega)⟩
    let c1S : S :=
      ⟨PowerSeries.C (PowerSeries.coeff 1 g), by
        change PowerSeries.coeff 1 (PowerSeries.C _) = 0
        exact PowerSeries.coeff_C_of_ne_zero (by omega)⟩
    have hdecomp : g = PowerSeries.C (PowerSeries.coeff 0 g) +
        PowerSeries.C (PowerSeries.coeff 1 g) * PowerSeries.X + q := by
      dsimp [q]
      ring
    have hT2pow :
        ((chapter04CuspPowerSeriesT2 k : S) : PowerSeries k) ^ N =
          PowerSeries.X ^ (2 * N) := by
      simp [chapter04CuspPowerSeriesT2, ← pow_mul]
    have hT2T3 :
        ((chapter04CuspPowerSeriesT2 k : S) : PowerSeries k) ^ (n - 1) *
          ((chapter04CuspPowerSeriesT3 k : S) : PowerSeries k) =
          PowerSeries.X ^ (2 * (n - 1) + 3) := by
      simp [chapter04CuspPowerSeriesT2, chapter04CuspPowerSeriesT3,
        ← pow_mul, ← pow_add]
    have hthird :
        PowerSeries.X ^ (2 * N) *
            (PowerSeries.C (PowerSeries.coeff 1 g) * PowerSeries.X) =
              PowerSeries.X ^ (2 * (n - 1) + 3) *
            PowerSeries.C (PowerSeries.coeff 1 g) := by
      calc
        PowerSeries.X ^ (2 * N) *
              (PowerSeries.C (PowerSeries.coeff 1 g) * PowerSeries.X) =
            (PowerSeries.X ^ (2 * N) * PowerSeries.X) *
              PowerSeries.C (PowerSeries.coeff 1 g) := by ring
        _ = PowerSeries.X ^ (2 * N + 1) *
              PowerSeries.C (PowerSeries.coeff 1 g) := by
            rw [pow_succ]
        _ = PowerSeries.X ^ (2 * (n - 1) + 3) *
              PowerSeries.C (PowerSeries.coeff 1 g) := by
            congr 2
            dsimp [N]
            omega
    have hx_eq : x =
        chapter04CuspPowerSeriesT2 k ^ N * qS +
          chapter04CuspPowerSeriesT2 k ^ N * c0S +
          (chapter04CuspPowerSeriesT2 k ^ (n - 1) *
            chapter04CuspPowerSeriesT3 k) * c1S := by
      apply Subtype.ext
      dsimp [qS, c0S, c1S]
      rw [hg]
      conv_lhs => rw [hdecomp]
      rw [hT2pow, hT2T3]
      calc
        _ = PowerSeries.X ^ (2 * N) * q +
            PowerSeries.X ^ (2 * N) * PowerSeries.C (PowerSeries.coeff 0 g) +
            PowerSeries.X ^ (2 * N) *
              (PowerSeries.C (PowerSeries.coeff 1 g) * PowerSeries.X) := by
          ring
        _ = _ := by rw [hthird]
    have hT2 : chapter04CuspPowerSeriesT2 k ∈ M := by
      exact Ideal.subset_span (by simp)
    have hT3 : chapter04CuspPowerSeriesT3 k ∈ M := by
      exact Ideal.subset_span (by simp)
    have hT2pow' : chapter04CuspPowerSeriesT2 k ^ N ∈ M ^ N :=
      Ideal.pow_mem_pow hT2 N
    have hqmem : chapter04CuspPowerSeriesT2 k ^ N * qS ∈ M ^ N := by
      simpa [mul_comm] using (M ^ N).mul_mem_left qS hT2pow'
    have hc0mem : chapter04CuspPowerSeriesT2 k ^ N * c0S ∈ M ^ N := by
      simpa [mul_comm] using (M ^ N).mul_mem_left c0S hT2pow'
    have hmix : ∀ r : ℕ,
        chapter04CuspPowerSeriesT2 k ^ r *
            chapter04CuspPowerSeriesT3 k ∈ M ^ (r + 1) := by
      intro r
      induction r with
      | zero => simpa using hT3
      | succ r ihr =>
          simpa [pow_succ, M.pow_succ, mul_assoc, mul_comm, mul_left_comm] using
            (Ideal.mul_mem_mul hT2 ihr)
    have hc1mem :
        (chapter04CuspPowerSeriesT2 k ^ (n - 1) *
          chapter04CuspPowerSeriesT3 k) * c1S ∈ M ^ N := by
      have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
      have hmixN : chapter04CuspPowerSeriesT2 k ^ (n - 1) *
          chapter04CuspPowerSeriesT3 k ∈ M ^ N := by
        simpa [N, hnsub] using hmix (n - 1)
      simpa [mul_comm] using (M ^ N).mul_mem_left c1S hmixN
    rw [hx_eq]
    exact (M ^ N).add_mem ((M ^ N).add_mem hqmem hc0mem) hc1mem
  have hmax : IsLocalRing.maximalIdeal S = M := by
    apply le_antisymm
    · intro x hx
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
      have hx0 : PowerSeries.constantCoeff (x : PowerSeries k) = 0 := by
        by_contra hx0
        apply hx
        apply hunit (x : PowerSeries k) x.property
        rw [PowerSeries.isUnit_iff_constantCoeff]
        exact isUnit_iff_ne_zero.mpr hx0
      have hx1 : PowerSeries.coeff 1 (x : PowerSeries k) = 0 := x.property
      have hxdiv : (PowerSeries.X : PowerSeries k) ^ 2 ∣
          (x : PowerSeries k) := by
        rw [PowerSeries.X_pow_dvd_iff]
        intro i hi
        interval_cases i <;> simp_all [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      have hxI : (x : PowerSeries k) ∈ I ^ 2 := by
        change (x : PowerSeries k) ∈
          (Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) ^ 2
        rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        exact hxdiv
      simpa using hkey 1 x hxI
    · apply Ideal.span_le.2
      intro x hx
      rcases hx with rfl | rfl
      · change ¬ IsUnit (chapter04CuspPowerSeriesT2 k)
        intro hu
        have hc := PowerSeries.isUnit_iff_constantCoeff.mp (IsUnit.map S.subtype hu)
        simp [chapter04CuspPowerSeriesT2] at hc
      · change ¬ IsUnit (chapter04CuspPowerSeriesT3 k)
        intro hu
        have hc := PowerSeries.isUnit_iff_constantCoeff.mp (IsUnit.map S.subtype hu)
        simp [chapter04CuspPowerSeriesT3] at hc
  have hcomplete : IsAdicComplete M S := by
    refine { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
    · constructor
      intro x hx
      apply Subtype.ext
      apply PowerSeries.ext
      intro d
      have hmem : x ∈ M ^ (d + 1) := by
        simpa [smul_eq_mul, Ideal.mul_top] using
          (SModEq.sub_mem.mp (hx (d + 1)))
      have hmemI : (x : PowerSeries k) ∈ I ^ (2 * (d + 1)) :=
        (hpowmap (d + 1)) (Ideal.mem_map_of_mem S.subtype hmem)
      have hdiv : (PowerSeries.X : PowerSeries k) ^ (2 * (d + 1)) ∣
          (x : PowerSeries k) := by
        rw [← Ideal.mem_span_singleton]
        simpa [I, Ideal.span_singleton_pow] using hmemI
      exact (PowerSeries.X_pow_dvd_iff.mp hdiv) d (by omega)
    · constructor
      intro f hf
      have hambient : ∀ {m n : ℕ}, m ≤ n →
          (f m : PowerSeries k) ≡ (f n : PowerSeries k)
            [SMOD (I ^ m • (⊤ : Submodule (PowerSeries k) (PowerSeries k)))] := by
        intro m n hmn
        have hmem : f m - f n ∈ M ^ m := by
          simpa [smul_eq_mul, Ideal.mul_top] using (SModEq.sub_mem.mp (hf hmn))
        have hmem2 : ((f m - f n : S) : PowerSeries k) ∈ I ^ (2 * m) :=
          (hpowmap m) (Ideal.mem_map_of_mem S.subtype hmem)
        have hle : I ^ (2 * m) ≤ I ^ m := by
          rw [show 2 * m = m + m by omega, pow_add]
          exact Ideal.mul_le_left
        rw [SModEq.sub_mem]
        simpa [smul_eq_mul, Ideal.mul_top] using hle hmem2
      have : IsAdicComplete I (PowerSeries k) := by infer_instance
      obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := PowerSeries k)
        inferInstance hambient
      have hLprop : PowerSeries.coeff 1 L = 0 := by
        have hmem : (f 2 : PowerSeries k) - L ∈ I ^ 2 := by
          simpa [smul_eq_mul, Ideal.mul_top] using (SModEq.sub_mem.mp (hL 2))
        have hdiv : (PowerSeries.X : PowerSeries k) ^ 2 ∣
            (f 2 : PowerSeries k) - L := by
          rw [← Ideal.mem_span_singleton]
          simpa [I, Ideal.span_singleton_pow] using hmem
        have hc := PowerSeries.X_pow_dvd_iff.mp hdiv 1 (by omega)
        have hf2 : PowerSeries.coeff 1 (f 2 : PowerSeries k) = 0 := f 2 |>.property
        rw [map_sub, hf2, zero_sub] at hc
        simpa using hc
      let Ls : S := ⟨L, hLprop⟩
      refine ⟨Ls, ?_⟩
      intro n
      rw [SModEq.sub_mem]
      have hfirst : ((f n - f (2 * n) : S) : PowerSeries k) ∈ I ^ (2 * n) := by
        have hmem : f n - f (2 * n) ∈ M ^ n := by
          simpa [smul_eq_mul, Ideal.mul_top] using (SModEq.sub_mem.mp
            (hf (by omega : n ≤ 2 * n)))
        exact (hpowmap n) (Ideal.mem_map_of_mem S.subtype hmem)
      have hsecond : (f (2 * n) : PowerSeries k) - L ∈ I ^ (2 * n) := by
        simpa [smul_eq_mul, Ideal.mul_top] using (SModEq.sub_mem.mp (hL (2 * n)))
      have hdiff : ((f n - Ls : S) : PowerSeries k) ∈ I ^ (2 * n) := by
        change (f n : PowerSeries k) - L ∈ I ^ (2 * n)
        rw [← sub_add_sub_cancel (f n : PowerSeries k) (f (2 * n) : PowerSeries k) L]
        exact (I ^ (2 * n)).add_mem hfirst hsecond
      exact by
        simpa [smul_eq_mul, Ideal.mul_top] using hkey n (f n - Ls) hdiff
  have hdim : ringKrullDim S = 1 := by
    apply (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain (R := S)).2
    constructor
    · intro hfield
      have : IsField S := hfield
      have hT20 : (chapter04CuspPowerSeriesT2 k : S) ≠ 0 := by
        intro h
        have h' := congrArg Subtype.val h
        simp [chapter04CuspPowerSeriesT2] at h'
      have hT2unit : IsUnit (chapter04CuspPowerSeriesT2 k : S) := by
        rcases hfield.mul_inv_cancel hT20 with ⟨y, hy⟩
        apply isUnit_iff_exists.mpr
        exact ⟨y, hy, by simpa [hfield.mul_comm] using hy⟩
      have hT2nonunit : ¬ IsUnit (chapter04CuspPowerSeriesT2 k : S) := by
        intro hu
        have hc := PowerSeries.isUnit_iff_constantCoeff.mp
          (IsUnit.map S.subtype hu)
        simp [chapter04CuspPowerSeriesT2] at hc
      exact hT2nonunit hT2unit
    · intro x hx
      by_cases hu : IsUnit x
      · rw [Ideal.span_singleton_eq_top.mpr hu, Ideal.radical_top]
        exact le_top
      · have hx0 : PowerSeries.constantCoeff (x : PowerSeries k) = 0 := by
          by_contra hx0
          apply hu
          apply hunit (x : PowerSeries k) x.property
          rw [PowerSeries.isUnit_iff_constantCoeff]
          exact isUnit_iff_ne_zero.mpr hx0
        have hxne : (x : PowerSeries k) ≠ 0 := by
          intro h
          apply hx
          exact Subtype.ext h
        let d := (x : PowerSeries k).order.toNat
        let u : (PowerSeries k)ˣ :=
          PowerSeries.Unit_of_divided_by_X_pow_order (x : PowerSeries k)
        have hfactor : (x : PowerSeries k) =
            PowerSeries.X ^ d * (u : PowerSeries k) := by
          dsimp [d]
          simpa [u, PowerSeries.Unit_of_divided_by_X_pow_order_nonzero hxne] using
            (PowerSeries.X_pow_order_mul_divXPowOrder
              (f := (x : PowerSeries k))).symm
        let gPS : PowerSeries k :=
          PowerSeries.X ^ (d + 2) * (↑(u⁻¹) : PowerSeries k)
        have hg1 : PowerSeries.coeff 1 gPS = 0 := by
          dsimp [gPS]
          rw [PowerSeries.coeff_X_pow_mul']
          simp
        let gS : S := ⟨gPS, hg1⟩
        have hprod : x * gS =
            (chapter04CuspPowerSeriesT2 k) ^ (d + 1) := by
          apply Subtype.ext
          change (x : PowerSeries k) * gPS = _
          calc
            (x : PowerSeries k) * gPS =
                PowerSeries.X ^ d * (u : PowerSeries k) *
                  (PowerSeries.X ^ (d + 2) * (↑(u⁻¹) : PowerSeries k)) := by
                    rw [hfactor]
            _ = PowerSeries.X ^ d * PowerSeries.X ^ (d + 2) *
                  ((u : PowerSeries k) * (↑(u⁻¹) : PowerSeries k)) := by ring
            _ = PowerSeries.X ^ (d + (d + 2)) := by
                  have huinv : (u : PowerSeries k) *
                      (↑(u⁻¹) : PowerSeries k) = 1 := u.val_inv
                  rw [huinv, mul_one]
                  rw [← pow_add]
            _ = ((PowerSeries.X : PowerSeries k) ^ 2) ^ (d + 1) := by
                  rw [← pow_mul]
                  congr 1
                  omega
            _ = ((chapter04CuspPowerSeriesT2 k) ^ (d + 1) : S) := by
                  rfl
        have hT2pow :
            (chapter04CuspPowerSeriesT2 k) ^ (d + 1) ∈
              Ideal.span ({x} : Set S) := by
          rw [← hprod]
          exact (Ideal.span ({x} : Set S)).mul_mem_right gS
            (Ideal.mem_span_singleton_self x)
        have hT2rad : chapter04CuspPowerSeriesT2 k ∈
            (Ideal.span ({x} : Set S)).radical :=
          Ideal.mem_radical_of_pow_mem
            ((Ideal.le_radical (I := Ideal.span ({x} : Set S))) hT2pow)
        have hT2sq : (chapter04CuspPowerSeriesT2 k) ^ 2 ∈
            (Ideal.span ({x} : Set S)).radical := by
          simpa [pow_succ, mul_comm] using
            (Ideal.radical (Ideal.span ({x} : Set S))).mul_mem_left
              (chapter04CuspPowerSeriesT2 k) hT2rad
        have hT2cube : (chapter04CuspPowerSeriesT2 k) ^ 3 ∈
            (Ideal.span ({x} : Set S)).radical := by
          simpa [pow_succ, mul_comm] using
            (Ideal.radical (Ideal.span ({x} : Set S))).mul_mem_left
              (chapter04CuspPowerSeriesT2 k) hT2sq
        have hrel :
            (chapter04CuspPowerSeriesT3 k) ^ 2 =
              (chapter04CuspPowerSeriesT2 k) ^ 3 := by
          apply Subtype.ext
          simp [chapter04CuspPowerSeriesT2, chapter04CuspPowerSeriesT3]
          ring
        have hT3sq : (chapter04CuspPowerSeriesT3 k) ^ 2 ∈
            (Ideal.span ({x} : Set S)).radical := by
          rw [hrel]
          exact hT2cube
        have hT3rad : chapter04CuspPowerSeriesT3 k ∈
            (Ideal.span ({x} : Set S)).radical :=
          Ideal.mem_radical_of_pow_mem
            hT3sq
        rw [hmax]
        apply Ideal.span_le.2
        rintro y (rfl | rfl)
        · exact hT2rad
        · exact hT3rad
  have hnon : ¬ IsIntegrallyClosed S := by
    intro hnormal
    let T2 : S := chapter04CuspPowerSeriesT2 k
    let T3 : S := chapter04CuspPowerSeriesT3 k
    have hT2 : T2 ≠ 0 := by
      intro h
      have hp : (PowerSeries.X : PowerSeries k) ^ 2 = 0 := by
        have := congrArg Subtype.val h
        simp [T2, chapter04CuspPowerSeriesT2] at this
      exact (pow_ne_zero 2 PowerSeries.X_ne_zero) hp
    have hrel : T3 ^ 2 = T2 ^ 3 := by
      apply Subtype.ext
      simp [T2, T3, chapter04CuspPowerSeriesT2,
        chapter04CuspPowerSeriesT3]
      ring
    have ht2 : IsIntegral S
        (algebraMap S (PowerSeries k) T2) := by
      exact isIntegral_algebraMap
    have hpow : IsIntegral S (chapter04CuspAmbientParameter k ^ 2) := by
      change IsIntegral S (algebraMap S (PowerSeries k) T2)
      exact ht2
    have hint : IsIntegral S (chapter04CuspAmbientParameter k) :=
      IsIntegral.of_pow (by norm_num) hpow
    let a : FractionRing S := algebraMap S (FractionRing S) T2
    let b : FractionRing S := algebraMap S (FractionRing S) T3
    have ha : a ≠ 0 := by
      intro ha0
      apply hT2
      apply (IsFractionRing.injective S (FractionRing S))
      simpa [a] using ha0
    have hab : b ^ 2 = a ^ 3 := by
      simpa [a, b] using congrArg (algebraMap S (FractionRing S)) hrel
    let z : FractionRing S := b / a
    have hzpow : z ^ 2 = a := by
      dsimp [z]
      rw [div_pow]
      apply (div_eq_iff (pow_ne_zero 2 ha)).2
      simpa [pow_succ, mul_assoc] using hab
    have haint : IsIntegral S a := by
      simpa [a] using
        (isIntegral_algebraMap :
          IsIntegral S (algebraMap S (FractionRing S) T2))
    have hzint : IsIntegral S z := by
      have hzpowint : IsIntegral S (z ^ 2) := by
        simpa [hzpow] using haint
      exact IsIntegral.of_pow (x := z) (by norm_num) hzpowint
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S)).mp hzint
    let g : S →+* LaurentSeries k :=
      (algebraMap (PowerSeries k) (LaurentSeries k)).comp S.subtype
    have hg : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      apply (IsFractionRing.injective (PowerSeries k) (LaurentSeries k))
      simpa [g] using hxy
    let f : FractionRing S →+* LaurentSeries k := IsFractionRing.lift hg
    have hfz : f z = ((PowerSeries.X : PowerSeries k) : LaurentSeries k) := by
      dsimp [f, z, a, b, g]
      simp only [map_div₀, IsFractionRing.lift_algebraMap, RingHom.coe_comp,
        Function.comp_apply, Subring.coe_subtype]
      change
        (algebraMap (PowerSeries k) (LaurentSeries k)
            ((PowerSeries.X : PowerSeries k) ^ 3)) /
          (algebraMap (PowerSeries k) (LaurentSeries k)
            ((PowerSeries.X : PowerSeries k) ^ 2)) =
          algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X : PowerSeries k)
      rw [map_pow, map_pow]
      field_simp
    have hgy : g y = f z := by
      calc
        g y = f (algebraMap S (FractionRing S) y) := by
          symm
          exact IsFractionRing.lift_algebraMap hg y
        _ = f z := by rw [hy]
    have hgyX : g y = ((PowerSeries.X : PowerSeries k) : LaurentSeries k) :=
      hgy.trans hfz
    have hPS : (y : PowerSeries k) = PowerSeries.X := by
      apply (IsFractionRing.injective (PowerSeries k) (LaurentSeries k))
      simpa [g] using hgyX
    have hy0 : PowerSeries.coeff 1 (y : PowerSeries k) = 0 := by
      exact y.property
    rw [hPS] at hy0
    simp at hy0
  exact ⟨hdom, hlocal, hcomplete, hdim, hnon⟩

/-- The missing parameter `t` is integral over `k[[t²,t³]]` but is not an
element of that ring. -/
theorem cusp_parameter_is_integral_but_absent
    (k : Type*) [Field k] :
    IsIntegral (chapter04CuspPowerSeriesSubring k)
        (chapter04CuspAmbientParameter k) ∧
      chapter04CuspAmbientParameter k ∉
        (chapter04CuspPowerSeriesSubring k : Set (PowerSeries k)) := by
  constructor
  · have ht2 : IsIntegral (chapter04CuspPowerSeriesSubring k)
        (algebraMap (chapter04CuspPowerSeriesSubring k) (PowerSeries k)
          (chapter04CuspPowerSeriesT2 k)) := by
      exact isIntegral_algebraMap
    have hpow : IsIntegral (chapter04CuspPowerSeriesSubring k)
        ((chapter04CuspAmbientParameter k) ^ 2) := by
      change IsIntegral (chapter04CuspPowerSeriesSubring k)
        (algebraMap (chapter04CuspPowerSeriesSubring k) (PowerSeries k)
          (chapter04CuspPowerSeriesT2 k))
      exact ht2
    exact IsIntegral.of_pow (by norm_num) hpow
  · change ¬ PowerSeries.coeff 1 (PowerSeries.X : PowerSeries k) = 0
    simp

/-- Consequently the cusp power-series ring is not a DVR. -/
theorem cusp_power_series_is_not_a_dvr
    (k : Type*) [Field k] :
    ¬ IsDiscreteValuationRing (chapter04CuspPowerSeriesSubring k) := by
  intro hDVR
  have hnormal : IsIntegrallyClosed (chapter04CuspPowerSeriesSubring k) := by
    have : IsDiscreteValuationRing (chapter04CuspPowerSeriesSubring k) := hDVR
    infer_instance
  exact (cusp_power_series_is_complete_one_dimensional_non_normal k).2.2.2.2 hnormal

/-- The maximal ideal `(x,y)` in the two-variable polynomial ring. -/
def chapter04TwoVariablePolynomialMaximalIdeal (k : Type*) [Field k] :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
    Set (MvPolynomial (Fin 2) k))

/-- The local ring `k[x,y]_(x,y)` is normal and two-dimensional, hence not a
DVR. -/
theorem two_variable_polynomial_localization_is_integrally_closed_two_dimensional
    (k : Type*) [Field k] (P : Ideal (MvPolynomial (Fin 2) k)) [P.IsPrime]
    (hP : P = chapter04TwoVariablePolynomialMaximalIdeal k) :
    IsIntegrallyClosed (chapter04AtPrimeLocalization (MvPolynomial (Fin 2) k) P) ∧
      IsLocalRing (chapter04AtPrimeLocalization (MvPolynomial (Fin 2) k) P) ∧
      ringKrullDim (chapter04AtPrimeLocalization (MvPolynomial (Fin 2) k) P) = 2 ∧
      IsLocalRing.maximalIdeal (chapter04AtPrimeLocalization (MvPolynomial (Fin 2) k) P) =
        Ideal.map
          (algebraMap (MvPolynomial (Fin 2) k)
            (chapter04AtPrimeLocalization (MvPolynomial (Fin 2) k) P)) P ∧
      ¬ IsDiscreteValuationRing
        (chapter04AtPrimeLocalization (MvPolynomial (Fin 2) k) P) := by
  classical
  let R := MvPolynomial (Fin 2) k
  let L := chapter04AtPrimeLocalization R P
  have : IsRegularRing R := MvPolynomial.isRegularRing_of_isRegularRing k
  have hlocal : IsLocalRing L := by
    exact IsLocalization.AtPrime.isLocalRing L P
  have : IsIntegrallyClosed R := by infer_instance
  have hnormal : IsIntegrallyClosed L := by
    exact isIntegrallyClosed_of_isLocalization L P.primeCompl
      P.primeCompl_le_nonZeroDivisors
  have hmax : IsLocalRing.maximalIdeal L = Ideal.map (algebraMap R L) P := by
    exact (IsLocalization.AtPrime.map_eq_maximalIdeal P L).symm
  have hdim : ringKrullDim L = 2 := by
    have hRdim : ringKrullDim R = 2 := by
      simp [R]
    have hPh : P.height = 2 := by
      let q : Ideal R := Ideal.span ({MvPolynomial.X 0} : Set R)
      have hqprime : q.IsPrime := by
        dsimp [q]
        exact Ideal.isPrime_span_singleton_of_prime MvPolynomial.X_prime
      have : q.IsPrime := hqprime
      have hqP : q < P := by
        rw [hP]
        constructor
        · exact Ideal.span_le.2 (by
            intro x hx
            rcases hx with rfl
            exact Ideal.subset_span (by simp))
        · intro hle
          have hx1q : MvPolynomial.X 1 ∈ q := by
            exact hle (Ideal.subset_span (by simp))
          change MvPolynomial.X 1 ∈ Ideal.span
            ({MvPolynomial.X 0} : Set R) at hx1q
          rw [Ideal.mem_span_singleton] at hx1q
          have h01 : (0 : Fin 2) = 1 :=
            (MvPolynomial.X_dvd_X (R := k)).mp hx1q
          exact Fin.zero_ne_one h01
      have hbotq : (⊥ : Ideal R) < q := by
        apply lt_of_le_of_ne bot_le
        intro hqbot
        have hx0q : MvPolynomial.X 0 ∈ q := Ideal.subset_span (by simp)
        have hx0bot : MvPolynomial.X 0 ∈ (⊥ : Ideal R) := hqbot ▸ hx0q
        have hx0zero : (MvPolynomial.X 0 : R) = 0 := by
          simp at hx0bot
        exact MvPolynomial.X_ne_zero 0 hx0zero
      have hqheight : (1 : ℕ∞) ≤ q.height := by
        apply WithBot.coe_le_coe.mp
        simpa using (Ideal.height_add_one_le_of_lt_of_isPrime hbotq)
      have hPheight : (2 : ℕ∞) ≤ P.height := by
        calc
          (2 : ℕ∞) = 1 + 1 := by norm_num
          _ ≤ 1 + q.height := add_le_add_right hqheight 1
          _ = q.height + 1 := by rw [add_comm]
          _ ≤ P.height := by
            exact (Ideal.height_add_one_le_of_lt_of_isPrime hqP)
      have hPupper : P.height ≤ 2 := by
        have h := Ideal.height_le_ringKrullDim_of_isPrime (I := P)
        apply WithBot.coe_le_coe.mp
        simpa [hRdim] using h
      exact le_antisymm hPupper hPheight
    calc
      ringKrullDim L = P.height :=
        IsLocalization.AtPrime.ringKrullDim_eq_height P L
      _ = 2 := by
        simpa using congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hPh
  have hnot : ¬ IsDiscreteValuationRing L := by
    intro hDVR
    have : IsDiscreteValuationRing L := hDVR
    have := IsDiscreteValuationRing.ringKrullDim_eq_one L
    rw [hdim] at this
    norm_num at this
  exact ⟨hnormal, hlocal, hdim, hmax, hnot⟩

/-- The `p`-adic power-series ring `ℤ_p[[t]]`. -/
abbrev chapter04PadicPowerSeries (p : ℕ) [Fact (Nat.Prime p)] :=
  PowerSeries (PadicInt p)

/-- Its maximal ideal `(p,t)`, written with the constant power series `C p`. -/
def chapter04PadicPowerSeriesMaximalIdeal (p : ℕ) [Fact (Nat.Prime p)] :
    Ideal (chapter04PadicPowerSeries p) :=
  Ideal.span ({PowerSeries.C (p : PadicInt p), PowerSeries.X} :
    Set (chapter04PadicPowerSeries p))

/-- The complete regular local ring `ℤ_p[[t]]` has dimension two and is not a
DVR. -/
theorem padic_power_series_is_complete_regular_local_two_dimensional
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsAdicComplete (chapter04PadicPowerSeriesMaximalIdeal p)
        (chapter04PadicPowerSeries p) ∧
      IsRegularLocalRing (chapter04PadicPowerSeries p) ∧
      ringKrullDim (chapter04PadicPowerSeries p) = 2 ∧
      IsLocalRing.maximalIdeal (chapter04PadicPowerSeries p) =
        chapter04PadicPowerSeriesMaximalIdeal p ∧
      ¬ IsDiscreteValuationRing (chapter04PadicPowerSeries p) := by
  classical
  let R := PadicInt p
  let A := chapter04PadicPowerSeries p
  have hmax : IsLocalRing.maximalIdeal A =
      chapter04PadicPowerSeriesMaximalIdeal p := by
    let J : Ideal A := Ideal.span
      ({PowerSeries.C (p : PadicInt p), PowerSeries.X} : Set A)
    change IsLocalRing.maximalIdeal A = J
    apply le_antisymm
    · intro f hf
      rw [IsLocalRing.mem_maximalIdeal] at hf
      have hcf : PowerSeries.constantCoeff f ∈
          IsLocalRing.maximalIdeal R := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hc
        apply (mem_nonunits_iff.mp hf)
        rw [PowerSeries.isUnit_iff_constantCoeff]
        simpa using hc
      rw [PadicInt.maximalIdeal_eq_span_p] at hcf
      obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton.mp hcf)
      rw [PowerSeries.eq_X_mul_shift_add_const f, ha]
      apply J.add_mem
      · exact J.mul_mem_right _ (Ideal.subset_span (by simp))
      · rw [map_mul]
        exact J.mul_mem_right _ (Ideal.subset_span (by simp))
    · apply Ideal.span_le.2
      intro x hx
      rcases hx with rfl | rfl
      · change PowerSeries.C (p : PadicInt p) ∈ IsLocalRing.maximalIdeal A
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hc
        have hp : (p : PadicInt p) ∈ nonunits (PadicInt p) :=
          PadicInt.p_nonunit
        exact (mem_nonunits_iff.mp hp) (by
          simpa using (PowerSeries.isUnit_iff_constantCoeff.mp hc))
      · change (PowerSeries.X : A) ∈ IsLocalRing.maximalIdeal A
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hc
        exact not_isUnit_zero (M₀ := PadicInt p) (by
          simpa using (PowerSeries.isUnit_iff_constantCoeff.mp hc))
  have hcomplete : IsAdicComplete (chapter04PadicPowerSeriesMaximalIdeal p) A := by
    let Ip : Ideal R := Ideal.span {(p : R)}
    let J : Ideal A := Ideal.span
      ({PowerSeries.C (p : R), PowerSeries.X} : Set A)
    have hIp : IsAdicComplete Ip R := by
      have hIp' : Ip = IsLocalRing.maximalIdeal R := by
        dsimp [Ip]
        exact (PadicInt.maximalIdeal_eq_span_p (p := p)).symm
      rw [hIp']
      infer_instance
    have hmapIp : Ideal.map (PowerSeries.C : R →+* A) Ip ≤ J := by
      dsimp [Ip]
      rw [Ideal.map_span, Set.image_singleton]
      apply Ideal.span_le.2
      intro x hx
      rcases hx with rfl
      change PowerSeries.C (p : R) ∈
        Ideal.span ({PowerSeries.C (p : R), PowerSeries.X} : Set A)
      exact Ideal.subset_span (by simp)
    have hmapIpPow : ∀ q : ℕ,
        Ideal.map (PowerSeries.C : R →+* A) (Ip ^ q) ≤ J ^ q := by
      intro q
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono hmapIp q
    let K : ℕ → Ideal A := fun n =>
      { carrier := {f | ∀ i, i < n → PowerSeries.coeff i f ∈ Ip ^ (n - i)}
        zero_mem' := by
          intro i hi
          simp
        add_mem' := by
          intro f g hf hg i hi
          simpa using (Ip ^ (n - i)).add_mem (hf i hi) (hg i hi)
        smul_mem' := by
          intro c f hf
          change ∀ i, i < n → PowerSeries.coeff i (c * f) ∈ Ip ^ (n - i)
          intro i hi
          rw [PowerSeries.coeff_mul]
          apply Ideal.sum_mem
          intro z hz
          have hz2 : z.2 ≤ i :=
            Finset.HasAntidiagonal.antidiagonal.snd_le hz
          have hfz : PowerSeries.coeff z.2 f ∈ Ip ^ (n - z.2) :=
            hf z.2 (by omega)
          have hpow : Ip ^ (n - z.2) ≤ Ip ^ (n - i) :=
            Ideal.pow_le_pow_right (I := Ip) (by omega)
          exact (Ip ^ (n - i)).mul_mem_left _ (hpow hfz) }
    have hCstep : ∀ n (a : A), a ∈ K n →
        a * PowerSeries.C (p : R) ∈ K (n + 1) := by
      intro n a ha
      change ∀ i, i < n + 1 →
        PowerSeries.coeff i (a * PowerSeries.C (p : R)) ∈ Ip ^ (n + 1 - i)
      intro i hi
      by_cases hil : i < n
      · rw [PowerSeries.coeff_mul_C]
        have hai : PowerSeries.coeff i a ∈ Ip ^ (n - i) := ha i hil
        have hp : (p : R) ∈ Ip := Ideal.subset_span (by simp)
        have he : n + 1 - i = (n - i) + 1 := by omega
        rw [he, pow_succ]
        exact Ideal.mul_mem_mul hai hp
      · have hieq : i = n := by omega
        subst i
        rw [PowerSeries.coeff_mul_C]
        have hp : (p : R) ∈ Ip := Ideal.subset_span (by simp)
        simpa using Ip.mul_mem_left _ hp
    have hXstep : ∀ n (a : A), a ∈ K n →
        a * (PowerSeries.X : A) ∈ K (n + 1) := by
      intro n a ha
      change ∀ i, i < n + 1 →
        PowerSeries.coeff i (a * (PowerSeries.X : A)) ∈ Ip ^ (n + 1 - i)
      intro i hi
      cases i with
      | zero => simp
      | succ j =>
          have haj : PowerSeries.coeff j a ∈ Ip ^ (n - j) := ha j (by omega)
          have he : n + 1 - (j + 1) = n - j := by omega
          rw [← pow_one (PowerSeries.X : A), PowerSeries.coeff_mul_X_pow, he]
          exact haj
    have hKstep : ∀ n, K n * J ≤ K (n + 1) := by
      intro n
      apply Ideal.mul_le.2
      intro a ha b hb
      change b ∈ Ideal.span
        ({PowerSeries.C (p : R), PowerSeries.X} : Set A) at hb
      rcases Ideal.mem_span_pair.mp hb with ⟨u, v, hb⟩
      rw [← hb, mul_add]
      exact (K (n + 1)).add_mem
        (by simpa [mul_assoc] using
          hCstep n (a * u) ((K n).mul_mem_right u ha))
        (by simpa [mul_assoc] using
          hXstep n (a * v) ((K n).mul_mem_right v ha))
    have hKpow : ∀ n, J ^ n ≤ K n := by
      intro n
      induction n with
      | zero =>
          intro f hf
          change ∀ i, i < 0 → PowerSeries.coeff i f ∈ Ip ^ (0 - i)
          intro i hi
          omega
      | succ n ih =>
          rw [pow_succ]
          exact (Ideal.mul_mono ih le_rfl).trans (hKstep n)
    have hcoeff_mem (n : ℕ) (f : A) (hf : f ∈ J ^ n) (i : ℕ) (hi : i < n) :
        PowerSeries.coeff i f ∈ Ip ^ (n - i) :=
      hKpow n hf i hi
    have hX : (PowerSeries.X : A) ∈ J := by
      exact Ideal.subset_span (by simp)
    have hcoeff_to_mem : ∀ n (f : A),
        (∀ i, i < n → PowerSeries.coeff i f ∈ Ip ^ (n - i)) → f ∈ J ^ n := by
      intro n f hf
      have htrunc : (PowerSeries.trunc n f : A) ∈ J ^ n := by
        rw [PowerSeries.trunc_apply, Nat.Ico_zero_eq_range]
        change Polynomial.coeToPowerSeries.ringHom
          (∑ i ∈ Finset.range n,
            Polynomial.monomial i (PowerSeries.coeff i f)) ∈ J ^ n
        rw [map_sum]
        apply Ideal.sum_mem
        intro i hi
        simp only [Polynomial.coeToPowerSeries.ringHom_apply,
          Polynomial.coe_monomial]
        rw [PowerSeries.monomial_eq_C_mul_X_pow]
        have hi_lt : i < n := by simpa using hi
        have hi_le : i ≤ n := hi_lt.le
        have hCcoeff : PowerSeries.C (PowerSeries.coeff i f) ∈ J ^ (n - i) :=
          hmapIpPow (n - i) (Ideal.mem_map_of_mem
            (PowerSeries.C : R →+* A) (hf i hi_lt))
        have hprod := Ideal.mul_mem_mul
          hCcoeff
          (Ideal.pow_mem_pow hX i)
        simpa [← pow_add, Nat.sub_add_cancel hi_le] using hprod
      have hshift :
          PowerSeries.X ^ n * PowerSeries.mk
              (fun i => PowerSeries.coeff (i + n) f) ∈ J ^ n :=
        by
          simpa [mul_comm] using
            (J ^ n).mul_mem_left
              (PowerSeries.mk (fun i => PowerSeries.coeff (i + n) f))
              (Ideal.pow_mem_pow hX n)
      rw [PowerSeries.eq_X_pow_mul_shift_add_trunc n f]
      exact (J ^ n).add_mem hshift htrunc
    have hhaus : IsHausdorff J A := by
      refine ⟨?_⟩
      intro x hx
      apply PowerSeries.ext
      intro d
      have hcoeff : ∀ q : ℕ, PowerSeries.coeff d x ∈ Ip ^ q := by
        intro q
        have hxmem : x ∈ J ^ (d + q) := by
          simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using hx (d + q)
        by_cases hq : q = 0
        · subst q
          simp
        · simpa [Nat.add_sub_cancel_left] using
            hcoeff_mem (d + q) x hxmem d (by omega)
      have hd : PowerSeries.coeff d x = 0 := by
        apply IsHausdorff.haus hIp.toIsHausdorff
        intro q
        rw [SModEq.zero]
        simpa [smul_eq_mul, Ideal.mul_top] using hcoeff q
      simpa using hd
    have hpre : IsPrecomplete J A := by
      refine ⟨?_⟩
      intro f hf
      let g : ℕ → ℕ → R := fun d n => PowerSeries.coeff d (f (n + d))
      have hg : ∀ d, ∀ {m n : ℕ}, m ≤ n →
          g d m ≡ g d n [SMOD (Ip ^ m • (⊤ : Submodule R R))] := by
        intro d m n hmn
        by_cases hm : m = 0
        · subst m
          simp [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        rw [SModEq.sub_mem]
        have hfdiff : f (m + d) - f (n + d) ∈ J ^ (m + d) := by
          simpa [smul_eq_mul, Ideal.mul_top] using
            (SModEq.sub_mem.mp (hf (by omega : m + d ≤ n + d)))
        have hcoeff := hcoeff_mem (m + d) (f (m + d) - f (n + d)) hfdiff d
          (by omega)
        simpa [g, map_sub, smul_eq_mul, Ideal.mul_top] using hcoeff
      have hconv : ∀ d, ∃ a : R, ∀ n,
          g d n ≡ a [SMOD (Ip ^ n • (⊤ : Submodule R R))] := by
        intro d
        exact IsPrecomplete.prec hIp.toIsPrecomplete (hg d)
      choose a ha using hconv
      let L : A := PowerSeries.mk a
      have hmem : ∀ n, f n - L ∈ J ^ n := by
        intro n
        apply hcoeff_to_mem n (f n - L)
        intro d hd
        have hda := SModEq.sub_mem.mp (ha d (n - d))
        have hda' : g d (n - d) - a d ∈ Ip ^ (n - d) := by
          simpa [smul_eq_mul, Ideal.mul_top] using hda
        simpa [g, L, map_sub, PowerSeries.coeff_mk,
          Nat.sub_add_cancel (Nat.le_of_lt hd)] using hda'
      refine ⟨L, ?_⟩
      intro n
      rw [SModEq.sub_mem]
      simpa [smul_eq_mul, Ideal.mul_top] using hmem n
    have hcompleteJ : IsAdicComplete J A :=
      { toIsHausdorff := hhaus, toIsPrecomplete := hpre }
    have hJ : J = chapter04PadicPowerSeriesMaximalIdeal p := by
      rfl
    rw [← hJ]
    exact hcompleteJ
  have hdim : ringKrullDim A = 2 := by
    have hupper : ringKrullDim A ≤ 2 := by
      have hspan : (IsLocalRing.maximalIdeal A).spanFinrank ≤ 2 := by
        rw [hmax]
        apply le_trans
          (Submodule.spanFinrank_span_le_ncard_of_finite
            ((Set.finite_singleton _).insert _))
        simpa using Set.ncard_insert_le
          (PowerSeries.C (p : PadicInt p)) ({PowerSeries.X} : Set A)
      exact le_trans (ringKrullDim_le_spanFinrank_maximalIdeal A)
        (WithBot.coe_le_coe.mpr (by exact_mod_cast hspan))
    have hlower : 2 ≤ ringKrullDim A := by
      have h := ringKrullDim_succ_le_ringKrullDim_powerseries (R := R)
      have hRdim : ringKrullDim R = 1 :=
        IsDiscreteValuationRing.ringKrullDim_eq_one R
      change 2 ≤ ringKrullDim (PowerSeries R)
      simpa [hRdim, one_add_one_eq_two] using h
    exact le_antisymm hupper hlower
  have hregular : IsRegularLocalRing A := by
    have hspan : (IsLocalRing.maximalIdeal A).spanFinrank ≤ 2 := by
      rw [hmax]
      apply le_trans
        (Submodule.spanFinrank_span_le_ncard_of_finite
          ((Set.finite_singleton _).insert _))
      simpa using Set.ncard_insert_le
        (PowerSeries.C (p : PadicInt p)) ({PowerSeries.X} : Set A)
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le A
    simpa [hdim] using hspan
  have hnot : ¬ IsDiscreteValuationRing A := by
    intro hDVR
    have : IsDiscreteValuationRing A := hDVR
    have := IsDiscreteValuationRing.ringKrullDim_eq_one A
    rw [hdim] at this
    norm_num at this
  exact ⟨hcomplete, hregular, hdim, hmax, hnot⟩

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter04
