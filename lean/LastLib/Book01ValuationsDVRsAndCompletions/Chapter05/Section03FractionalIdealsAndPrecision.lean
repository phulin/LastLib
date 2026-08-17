import LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.Section04LocalizationsOfDedekindDomains
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.Section02EquivalentCharacterizations
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.Section03ArithmeticAndExamples
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime.Extension
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter05

open LastLib.Book01ValuationsDVRsAndCompletions.Chapter01
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter04
open IsLocalRing
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped BigOperators DirectSum nonZeroDivisors WithZero

noncomputable section

/-!
# Chapter 5: The valuation filtration

This file is a statement-generation pass for Chapter 5 of *Valuations, DVRs, and
Completions*.  The declarations are deliberately self-contained: the DVR and
local-ring notions used below are Mathlib notions, while the few constructions
which are not exposed by Mathlib are recorded as chapter-local interfaces.
-/

/-! # Book 1, Chapter 5, Section 5.3: Fractional Ideals and Precision
-/

section FractionalIdealsAndPrecision

variable (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
variable (π : A) (hπ : Irreducible π)

/-- Book §5.3: the valuation filtration extended to all integer indices. -/
def chapterFractionalFiltration (n : ℤ) :
    FractionalIdeal (nonZeroDivisors A) K :=
  FractionalIdeal.spanSingleton (nonZeroDivisors A)
    ((algebraMap A K π) ^ n)

include hπ in
/-- Book §5.3: nonnegative filtration levels recover the integral powers. -/
theorem chapter_fractional_filtration_natCast_eq (n : ℕ) :
    chapterFractionalFiltration (A := A) (K := K) π n =
      ((IsLocalRing.maximalIdeal A ^ n : Ideal A) :
        FractionalIdeal (nonZeroDivisors A) K) := by
  rw [chapterFractionalFiltration, zpow_natCast,
    ← map_pow, ← FractionalIdeal.coeIdeal_span_singleton]
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]

include hπ in
/-- Book §5.3: every nonzero fractional ideal has a unique integer level. -/
theorem chapter_nonzero_fractional_ideal_unique_level
    (I : FractionalIdeal (nonZeroDivisors A) K) (hI : I ≠ 0) :
    ∃! n : ℤ,
      I = chapterFractionalFiltration (A := A) (K := K) π n := by
  classical
  have hπK : algebraMap A K π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    apply IsFractionRing.injective A K
    simpa using h
  let g : K := Submodule.IsPrincipal.generator (I : Submodule A K)
  have hg : g ≠ 0 := by
    intro hg
    apply hI
    have hg' : Submodule.IsPrincipal.generator (I : Submodule A K) = 0 := by
      simpa [g] using hg
    rw [FractionalIdeal.eq_spanSingleton_of_principal I, hg',
      FractionalIdeal.spanSingleton_zero]
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hg
  have hgen : I = FractionalIdeal.spanSingleton (nonZeroDivisors A)
      ((algebraMap A K π) ^ n) := by
    have hgen0 : I = FractionalIdeal.spanSingleton (nonZeroDivisors A) g := by
      simpa [g] using FractionalIdeal.eq_spanSingleton_of_principal I
    calc
      I = FractionalIdeal.spanSingleton (nonZeroDivisors A) g := hgen0
      _ = FractionalIdeal.spanSingleton (nonZeroDivisors A)
          (u • (algebraMap A K π) ^ n) := by rw [hu]
      _ = FractionalIdeal.spanSingleton (nonZeroDivisors A)
          ((algebraMap A K π) ^ n) := by
        apply (FractionalIdeal.spanSingleton_eq_spanSingleton).2
        exact ⟨u⁻¹, by simp [smul_smul]⟩
  refine ⟨n, ?_, ?_⟩
  · simpa [chapterFractionalFiltration] using hgen
  · intro m hm
    have hpow :
        FractionalIdeal.spanSingleton (nonZeroDivisors A)
            ((algebraMap A K π) ^ n) =
          FractionalIdeal.spanSingleton (nonZeroDivisors A)
            ((algebraMap A K π) ^ m) := by
      simpa [chapterFractionalFiltration] using hgen.symm.trans hm
    obtain ⟨u', hu'⟩ :=
      (FractionalIdeal.spanSingleton_eq_spanSingleton).1 hpow
    let v : IsDedekindDomain.HeightOneSpectrum A :=
      { asIdeal := IsLocalRing.maximalIdeal A
        isPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
        ne_bot := by
          rw [hπ.maximalIdeal_eq]
          exact fun h => hπ.ne_zero (Ideal.span_singleton_eq_bot.mp h) }
    let w : Valuation K ℤᵐ⁰ := v.valuation K
    have hwπ : w (algebraMap A K π) = WithZero.exp (-1 : ℤ) := by
      dsimp [w]
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        v.intValuation_singleton hπ.ne_zero
          hπ.maximalIdeal_eq]
      rfl
    have hnm : n = m := by
      have huval : w (algebraMap A K (u' : A)) = 1 := by
        dsimp [w]
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          v.intValuation_eq_one_iff.mpr]
        exact (IsLocalRing.notMem_maximalIdeal).2 u'.isUnit
      have hval := congrArg (fun z : K => w z) hu'
      have hnmz : (-(n : ℤ)) = -(m : ℤ) := by
        have hpow : (WithZero.exp (-1 : ℤ)) ^ n =
            (WithZero.exp (-1 : ℤ)) ^ m := by
          simpa [Units.smul_def, Algebra.smul_def, huval, hwπ, map_zpow] using hval
        apply WithZero.exp_injective
        simpa [← WithZero.exp_zsmul] using hpow
      exact neg_injective hnmz
    exact hnm.symm

/- The actual group of nonzero fractional ideals; its operation is supplied
   below rather than replacing the ideals by an isomorphic copy of `ℤ`. -/
def chapterNonzeroFractionalIdealGroup : Type _ :=
  {I : FractionalIdeal (nonZeroDivisors A) K // I ≠ 0}

/-- The group operations are the multiplication and inverse of fractional ideals,
restricted to the nonzero ideals. -/
noncomputable instance chapterNonzeroFractionalIdealGroup.instGroup :
    Group (chapterNonzeroFractionalIdealGroup (A := A) (K := K)) where
  mul I J := ⟨I.1 * J.1, by
    exact mul_ne_zero I.2 J.2⟩
  one := ⟨1, by simp⟩
  inv I := ⟨I.1⁻¹, by
    exact inv_ne_zero I.2⟩
  mul_assoc := by
    intro a b c
    apply Subtype.ext
    exact mul_assoc _ _ _
  one_mul := by
    intro a
    apply Subtype.ext
    exact one_mul _
  mul_one := by
    intro a
    apply Subtype.ext
    exact mul_one _
  div I J := ⟨I.1 / J.1, by
    exact div_ne_zero I.2 J.2⟩
  div_eq_mul_inv := by
    intro a b
    apply Subtype.ext
    exact div_eq_mul_inv _ _
  inv_mul_cancel := by
    intro a
    apply Subtype.ext
    exact inv_mul_cancel₀ a.2

/-- The image of `Aˣ` in `Kˣ`. -/
def chapterRingUnitImage : Subgroup Kˣ :=
  (Units.map (algebraMap A K).toMonoidHom).range

/-- The quotient `Kˣ/Aˣ`. -/
abbrev chapterFieldUnitQuotient : Type _ :=
  Kˣ ⧸ chapterRingUnitImage (A := A) (K := K)

noncomputable def chapterNonzeroFractionalIdealGroupEquivInt' :
    chapterNonzeroFractionalIdealGroup (A := A) (K := K) ≃* Multiplicative ℤ := by
  classical
  have hπK : algebraMap A K π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    apply IsFractionRing.injective A K
    simpa using h
  let F : ℤ → chapterNonzeroFractionalIdealGroup (A := A) (K := K) := fun n =>
    ⟨chapterFractionalFiltration (A := A) (K := K) π n, by
      apply FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      exact zpow_ne_zero n hπK⟩
  let level : chapterNonzeroFractionalIdealGroup (A := A) (K := K) → ℤ := fun I =>
    Classical.choose (chapter_nonzero_fractional_ideal_unique_level
      (A := A) (K := K) π hπ I.1 I.2)
  have hlevel (I : chapterNonzeroFractionalIdealGroup (A := A) (K := K)) :
      I.1 = (F (level I)).1 := by
    exact (Classical.choose_spec (chapter_nonzero_fractional_ideal_unique_level
      (A := A) (K := K) π hπ I.1 I.2)
      ).1
  have hFmul (n m : ℤ) : F n * F m = F (n + m) := by
    apply Subtype.ext
    change FractionalIdeal.spanSingleton (nonZeroDivisors A) ((algebraMap A K π) ^ n) *
        FractionalIdeal.spanSingleton (nonZeroDivisors A) ((algebraMap A K π) ^ m) =
      FractionalIdeal.spanSingleton (nonZeroDivisors A)
        ((algebraMap A K π) ^ (n + m))
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton, ← zpow_add₀ hπK]
  have hlevel_mul (I J : chapterNonzeroFractionalIdealGroup (A := A) (K := K)) :
      level (I * J) = level I + level J := by
    have huniq := chapter_nonzero_fractional_ideal_unique_level
      (A := A) (K := K) π hπ (I * J).1 (I * J).2
    apply huniq.unique (hlevel (I * J))
    change I.1 * J.1 = (F (level I + level J)).1
    rw [hlevel I, hlevel J]
    exact congrArg Subtype.val (hFmul (level I) (level J))
  have hlevel_F (n : ℤ) : level (F n) = n := by
    have huniq := chapter_nonzero_fractional_ideal_unique_level
      (A := A) (K := K) π hπ (F n).1 (F n).2
    apply huniq.unique (hlevel (F n))
    rfl
  exact
    { toFun := level
      invFun := fun n => F (Multiplicative.toAdd n)
      left_inv := by
        intro I
        apply Subtype.ext
        exact (hlevel I).symm
      right_inv := by
        intro n
        apply congrArg Multiplicative.ofAdd
        exact hlevel_F (Multiplicative.toAdd n)
      map_mul' := by
        intro I J
        exact congrArg Multiplicative.ofAdd (hlevel_mul I J) }

include hπ in
/-- Book §5.3: the nonzero fractional ideals form an infinite cyclic group. -/
theorem chapter_nonzero_fractional_ideal_group_is_infinite_cyclic :
    IsCyclic (chapterNonzeroFractionalIdealGroup (A := A) (K := K)) ∧
      Infinite (chapterNonzeroFractionalIdealGroup (A := A) (K := K)) := by
  let e := chapterNonzeroFractionalIdealGroupEquivInt' (A := A) (K := K) π hπ
  exact ⟨e.isCyclic.mpr inferInstance,
    Infinite.of_injective e.symm e.symm.injective⟩

include hπ in
/-- Book §5.3: the fractional-ideal group is another copy of `ℤ`. -/
theorem chapter_nonzero_fractional_ideal_group_equiv_int :
    Nonempty (chapterNonzeroFractionalIdealGroup (A := A) (K := K) ≃* Multiplicative ℤ) := by
  exact ⟨chapterNonzeroFractionalIdealGroupEquivInt' (A := A) (K := K) π hπ⟩

include hπ in
/-- Book §5.3, displayed quotient assertion `Kˣ/Aˣ ≅ ℤ`. -/
noncomputable def chapter_field_unit_quotient_equiv_int :
    chapterFieldUnitQuotient (A := A) (K := K) ≃* Multiplicative ℤ := by
  classical
  have hπK : algebraMap A K π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    apply IsFractionRing.injective A K
    simpa using h
  let φ : Kˣ →* chapterNonzeroFractionalIdealGroup (A := A) (K := K) :=
    MonoidHom.mk' (fun x =>
      ⟨FractionalIdeal.spanSingleton (nonZeroDivisors A) (x : K),
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.ne_zero⟩) (by
      intro x y
      apply Subtype.ext
      change FractionalIdeal.spanSingleton (nonZeroDivisors A) ((x * y : K)) =
        FractionalIdeal.spanSingleton (nonZeroDivisors A) (x : K) *
          FractionalIdeal.spanSingleton (nonZeroDivisors A) (y : K)
      simpa only [Units.val_mul] using
        (FractionalIdeal.spanSingleton_mul_spanSingleton
          (S := nonZeroDivisors A) (x : K) (y : K)).symm)
  have hφ_apply (x : Kˣ) :
      (φ x).1 = FractionalIdeal.spanSingleton (nonZeroDivisors A) (x : K) := by
    rfl
  have hker : chapterRingUnitImage (A := A) (K := K) = φ.ker := by
    ext x
    constructor
    · intro hx
      rcases (MonoidHom.mem_range).1 hx with ⟨u, rfl⟩
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have hspan :
          FractionalIdeal.spanSingleton (nonZeroDivisors A)
              ((Units.map (algebraMap A K).toMonoidHom u : Kˣ) : K) =
            FractionalIdeal.spanSingleton (nonZeroDivisors A) (1 : K) := by
        apply (FractionalIdeal.spanSingleton_eq_spanSingleton).2
        refine ⟨u⁻¹, ?_⟩
        simp [Units.smul_def, Algebra.smul_def]
      rw [hφ_apply]
      change FractionalIdeal.spanSingleton (nonZeroDivisors A)
          ((Units.map (algebraMap A K).toMonoidHom u : Kˣ) : K) =
        (1 : FractionalIdeal (nonZeroDivisors A) K)
      simpa only [FractionalIdeal.spanSingleton_one] using hspan
    · intro hx
      have hφ : φ x =
          (1 : chapterNonzeroFractionalIdealGroup (A := A) (K := K)) :=
        MonoidHom.mem_ker.1 hx
      have hx' : FractionalIdeal.spanSingleton (nonZeroDivisors A) (x : K) =
          (1 : FractionalIdeal (nonZeroDivisors A) K) := by
        have hxval := congrArg Subtype.val hφ
        rw [hφ_apply] at hxval
        change FractionalIdeal.spanSingleton (nonZeroDivisors A) (x : K) =
          (1 : FractionalIdeal (nonZeroDivisors A) K) at hxval
        exact hxval
      have hx'' : FractionalIdeal.spanSingleton (nonZeroDivisors A) (x : K) =
          FractionalIdeal.spanSingleton (nonZeroDivisors A) (1 : K) := by
        simpa using hx'
      obtain ⟨u, hu⟩ :=
        (FractionalIdeal.spanSingleton_eq_spanSingleton).1 hx''
      have hu' : (algebraMap A K (u : A)) * (x : K) = 1 := by
        simpa [Units.smul_def, Algebra.smul_def] using hu
      have hu'' : ((Units.map (algebraMap A K).toMonoidHom u : Kˣ) : K) *
          (x : K) = 1 := by
        simpa using hu'
      have hxinv : (x : K) =
          ((Units.map (algebraMap A K).toMonoidHom u)⁻¹ : K) := by
        simpa only [Units.val_inv_eq_inv_val] using
          (Units.eq_inv_of_mul_eq_one_left hu'')
      apply (MonoidHom.mem_range).2
      refine ⟨u⁻¹, ?_⟩
      apply Units.ext
      simpa using hxinv.symm
  have hφsurj : Function.Surjective φ := by
    intro I
    obtain ⟨n, hn, _⟩ :=
      chapter_nonzero_fractional_ideal_unique_level
        (A := A) (K := K) π hπ I.1 I.2
    let uπ : Kˣ := Units.mk0 (algebraMap A K π) hπK
    refine ⟨uπ ^ n, ?_⟩
    apply Subtype.ext
    change FractionalIdeal.spanSingleton (nonZeroDivisors A)
        ((uπ ^ n : Kˣ) : K) = I.1
    rw [Units.val_zpow_eq_zpow_val]
    change FractionalIdeal.spanSingleton (nonZeroDivisors A)
        ((algebraMap A K π) ^ n) = I.1
    simpa [chapterFractionalFiltration] using hn.symm
  exact
    (QuotientGroup.liftEquiv (N := chapterRingUnitImage (A := A) (K := K))
      hφsurj hker).trans
      (chapterNonzeroFractionalIdealGroupEquivInt' (A := A) (K := K) π hπ)

/-- A unit of the fraction field associated with a DVR integer unit. -/
def chapterMappedRingUnit (u : Aˣ) : Kˣ :=
  Units.map (algebraMap A K).toMonoidHom u

/- The chapter uses the integer part of the standard Mathlib valuation.  The
   valuation witness and its normalization are supplied by Chapter 4; only
   this conversion from `ℤᵐ⁰` to `ℤ` is chapter-specific. -/
def chapterValuationValue
    (v : Chapter04DVRValuationWitness A K) (x : K) (_hx : x ≠ 0) : ℤ :=
  -WithZero.log (v.valuation x)

/-- Book §5.3: the DVR supplies the normalized valuation witness. -/
theorem chapter_exists_integer_valuation :
    Nonempty (Chapter04DVRValuationWitness A K) := by
  exact (is_discrete_valuation_ring_iff_chapter04_valuation_witness A K).mp
    (inferInstance : IsDiscreteValuationRing A)

include hπ in
/-- Book §5.3, displayed precision-shift formula. -/
theorem chapter_fractional_filtration_shift
    (v : Chapter04DVRValuationWitness A K)
    (x : K) (hx : x ≠ 0) (n : ℤ) :
    chapterPrincipalFractionalIdeal (A := A) (K := K) x *
    chapterFractionalFiltration (A := A) (K := K) π n =
    chapterFractionalFiltration (A := A) (K := K) π
        (n + chapterValuationValue (A := A) (K := K) v x hx) := by
  let hvA : v.valuation.Integers A :=
    { hom_inj := IsFractionRing.injective A K
      map_le_one := fun a => by
        change algebraMap A K a ∈ v.valuation.valuationSubring.toSubring
        rw [v.valuationSubring_eq_image]
        exact Subring.mem_map.mpr ⟨a, by simp, rfl⟩
      exists_of_le_one := fun {r} hr => by
        change r ∈ v.valuation.valuationSubring.toSubring at hr
        rw [v.valuationSubring_eq_image] at hr
        obtain ⟨a, _, hax⟩ := Subring.mem_map.mp hr
        exact ⟨a, hax⟩ }
  have hπval : v.valuation (algebraMap A K π) = WithZero.exp (-1 : ℤ) := by
    have hq0 : v.valuation (algebraMap A K π) ≠ 0 :=
      v.valuation.ne_zero_iff.mpr (by simpa using hπ.ne_zero)
    have hq_lt : v.valuation (algebraMap A K π) < 1 :=
      hvA.valuation_irreducible_lt_one hπ
    have hmax := hvA.maximalIdeal_eq_setOfPred_le_v_algebraMap hπ
    obtain ⟨y, hy⟩ := v.surjective (WithZero.exp (-1 : ℤ))
    obtain ⟨a, ha⟩ :=
      hvA.exists_of_le_one (r := y) (by
        rw [hy]
        apply (WithZero.exp_le_exp).2
        omega)
    have ha_max : a ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hau
      have hauv := hvA.one_of_isUnit hau
      rw [ha, hy] at hauv
      simp at hauv
    have hle : WithZero.exp (-1 : ℤ) ≤
        v.valuation (algebraMap A K π) := by
      have hle' := (Set.ext_iff.mp hmax a).1 ha_max
      simpa [ha, hy] using hle'
    have hlog : WithZero.log (v.valuation (algebraMap A K π)) ≤ (-1 : ℤ) := by
      have hlt : WithZero.log (v.valuation (algebraMap A K π)) < (0 : ℤ) := by
        apply (WithZero.exp_lt_exp).mp
        simpa [WithZero.exp_log hq0] using hq_lt
      omega
    apply le_antisymm
    · rw [← WithZero.exp_log hq0]
      exact (WithZero.exp_le_exp).2 hlog
    · exact hle
  have hπu : Chapter04Uniformizer A π :=
    ⟨hπ.ne_zero, hπ.maximalIdeal_eq⟩
  obtain ⟨k, u, hxrep, _⟩ :=
    dvr_fraction_field_unique_normal_form A K hπu hx
  have huval : v.valuation (algebraMap A K (u : A)) = 1 :=
    hvA.one_of_isUnit u.isUnit
  have hxval : v.valuation x = WithZero.exp (-k : ℤ) := by
    rw [hxrep, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀,
      huval, hπval]
    rw [← WithZero.exp_zsmul]
    simp
  have hlevel : chapterValuationValue (A := A) (K := K) v x hx = k := by
    simp [chapterValuationValue, hxval]
  rw [chapterPrincipalFractionalIdeal, chapterFractionalFiltration,
    FractionalIdeal.spanSingleton_mul_spanSingleton]
  apply (FractionalIdeal.spanSingleton_eq_spanSingleton).2
  refine ⟨u⁻¹, ?_⟩
  simp only [hlevel]
  rw [hxrep]
  have hπK : algebraMap A K π ≠ 0 := by
    simpa using hπ.ne_zero
  simp [Units.smul_def, Algebra.smul_def, zpow_add₀ hπK,
    mul_comm, mul_left_comm]

omit [IsDiscreteValuationRing A] in
/-- Book §5.3: units have value zero. -/
theorem chapter_mapped_ring_unit_has_value_zero
    (v : Chapter04DVRValuationWitness A K) (u : Aˣ) :
    chapterValuationValue (A := A) (K := K) v
        (chapterMappedRingUnit (A := A) (K := K) u : K)
        (Units.ne_zero _) = 0 := by
  have huval : v.valuation (algebraMap A K (u : A)) = 1 := by
    exact (dvr_witness_mem_unit_iff_value_one A K v
      (algebraMap A K (u : A))).1 ⟨u, rfl⟩
  simp [chapterValuationValue, chapterMappedRingUnit, huval]

/-- Book §5.3: multiplication by a unit preserves precision. -/
theorem chapter_unit_preserves_precision
    (u : Aˣ) (n : ℤ) :
    chapterPrincipalFractionalIdeal (A := A) (K := K)
        (chapterMappedRingUnit (A := A) (K := K) u : K) *
        chapterFractionalFiltration (A := A) (K := K) π n =
      chapterFractionalFiltration (A := A) (K := K) π n := by
  rw [chapterPrincipalFractionalIdeal, chapterFractionalFiltration,
    FractionalIdeal.spanSingleton_mul_spanSingleton]
  apply (FractionalIdeal.spanSingleton_eq_spanSingleton).2
  refine ⟨u⁻¹, ?_⟩
  simp [Units.smul_def, Algebra.smul_def, chapterMappedRingUnit]

include hπ in
/-- Book §5.3: a nonzero maximal-ideal element gains positive precision. -/
theorem chapter_maximalIdeal_element_gains_precision
    (v : Chapter04DVRValuationWitness A K)
    {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A)
    (haK : algebraMap A K a ≠ 0) (n : ℤ) :
    0 < chapterValuationValue (A := A) (K := K) v
        (algebraMap A K a) haK ∧
      n < n + chapterValuationValue (A := A) (K := K) v
        (algebraMap A K a) haK ∧
      chapterPrincipalFractionalIdeal (A := A) (K := K) (algebraMap A K a) *
          chapterFractionalFiltration (A := A) (K := K) π n =
        chapterFractionalFiltration (A := A) (K := K) π
          (n + chapterValuationValue (A := A) (K := K) v
            (algebraMap A K a) haK) := by
  have hq0 : v.valuation (algebraMap A K a) ≠ 0 :=
    v.valuation.ne_zero_iff.mpr (by simpa using haK)
  have hq_lt : v.valuation (algebraMap A K a) < 1 :=
    (dvr_witness_mem_maximal_ideal_iff_value_lt_one A K v a).1 ha
  have hlog_lt : WithZero.log (v.valuation (algebraMap A K a)) < (0 : ℤ) := by
    apply (WithZero.exp_lt_exp).mp
    simpa [WithZero.exp_log hq0] using hq_lt
  have hpositive :
      0 < chapterValuationValue (A := A) (K := K) v
          (algebraMap A K a) haK := by
    simp [chapterValuationValue]
    omega
  refine ⟨hpositive, ?_, ?_⟩
  · omega
  · exact chapter_fractional_filtration_shift (A := A) (K := K) π hπ v
      (algebraMap A K a) haK n

include hπ in
/-- Book §5.3: a negative-valued element loses digits. -/
theorem chapter_negative_valued_element_loses_precision
    (v : Chapter04DVRValuationWitness A K)
    {x : K} (hx : x ≠ 0)
    (hv : chapterValuationValue (A := A) (K := K) v x hx < 0) (n : ℤ) :
    n + chapterValuationValue (A := A) (K := K) v x hx < n ∧
      chapterPrincipalFractionalIdeal (A := A) (K := K) x *
          chapterFractionalFiltration (A := A) (K := K) π n =
        chapterFractionalFiltration (A := A) (K := K) π
          (n + chapterValuationValue (A := A) (K := K) v x hx) := by
  refine ⟨by omega, ?_⟩
  exact chapter_fractional_filtration_shift (A := A) (K := K) π hπ v x hx n

end FractionalIdealsAndPrecision

section DedekindLocalizationProjection

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The global exponent vector of a fractional ideal. -/
def chapterGlobalIdealExponent (v : HeightOneSpectrum R)
    (I : FractionalIdeal (nonZeroDivisors R) K) : ℤ :=
  FractionalIdeal.count K v I

/-- The full global exponent vector `v ↦ val_v(I)`. -/
def chapterGlobalIdealExponentVector
    (I : FractionalIdeal (nonZeroDivisors R) K) : HeightOneSpectrum R → ℤ :=
  fun v => chapterGlobalIdealExponent (R := R) (K := K) v I

/-- Extension of a fractional ideal to the localization at a height-one prime.
The underlying submodule is the localized span inside the common fraction
field. -/
noncomputable def chapterLocalizeFractionalIdealAtPrime
    (v : HeightOneSpectrum R)
    [Algebra (Localization.AtPrime v.asIdeal) K]
    [IsScalarTower R (Localization.AtPrime v.asIdeal) K]
    (I : FractionalIdeal (nonZeroDivisors R) K) :
    FractionalIdeal (nonZeroDivisors (Localization.AtPrime v.asIdeal)) K :=
  ⟨Submodule.span (Localization.AtPrime v.asIdeal) (I : Set K), by
    rw [FractionalIdeal.isFractional_span_iff]
    obtain ⟨a, ha, haI⟩ := I.isFractional
    refine ⟨algebraMap R (Localization.AtPrime v.asIdeal) a,
      mem_nonZeroDivisors_iff_ne_zero.mpr
        (IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors
          (Localization.AtPrime v.asIdeal)
          v.asIdeal.primeCompl_le_nonZeroDivisors ha), ?_⟩
    intro b hb
    rcases haI b hb with ⟨r, hr⟩
    refine ⟨algebraMap R (Localization.AtPrime v.asIdeal) r, ?_⟩
    simpa [Algebra.smul_def, IsScalarTower.algebraMap_apply R
      (Localization.AtPrime v.asIdeal) K] using hr⟩

/-- The local fractional-ideal filtration attached to a chosen local
uniformizer. -/
def chapterLocalizedFractionalFiltrationAtPrime
    (v : HeightOneSpectrum R)
    [Algebra (Localization.AtPrime v.asIdeal) K]
    (ϖ : Localization.AtPrime v.asIdeal) (_hϖ : Irreducible ϖ) (n : ℤ) :
    FractionalIdeal (nonZeroDivisors (Localization.AtPrime v.asIdeal)) K :=
  ⟨Submodule.span (Localization.AtPrime v.asIdeal)
      ({(algebraMap (Localization.AtPrime v.asIdeal) K ϖ) ^ n} : Set K), by
    rw [FractionalIdeal.isFractional_span_iff]
    cases n with
    | ofNat k =>
        refine ⟨1, mem_nonZeroDivisors_iff_ne_zero.mpr one_ne_zero, ?_⟩
        intro b hb
        subst b
        rw [one_smul]
        exact ⟨ϖ ^ k, by simp⟩
    | negSucc k =>
        refine ⟨ϖ ^ (k + 1), mem_nonZeroDivisors_iff_ne_zero.mpr
          (pow_ne_zero _ _hϖ.ne_zero), ?_⟩
        intro b hb
        subst b
        by_cases hz : algebraMap (Localization.AtPrime v.asIdeal) K ϖ = 0
        · refine ⟨0, ?_⟩
          simp [Algebra.smul_def, hz]
        · have hpow : (algebraMap (Localization.AtPrime v.asIdeal) K ϖ) ^ (k + 1) ≠ 0 :=
            pow_ne_zero _ hz
          refine ⟨1, ?_⟩
          simp [Algebra.smul_def, hpow]⟩

/-- Book §5.3: for a fractional ideal, localization at a height-one prime
projects the global exponent vector to that prime's coordinate. -/
theorem chapter_localization_projects_global_fractional_exponent
    (v : HeightOneSpectrum R)
    [Algebra (Localization.AtPrime v.asIdeal) K]
    [IsFractionRing (Localization.AtPrime v.asIdeal) K]
    [IsScalarTower R (Localization.AtPrime v.asIdeal) K]
    [IsDiscreteValuationRing (Localization.AtPrime v.asIdeal)]
    (I : FractionalIdeal (nonZeroDivisors R) K) (hI : I ≠ 0)
    (ϖ : Localization.AtPrime v.asIdeal) (hϖ : Irreducible ϖ) :
    chapterLocalizeFractionalIdealAtPrime (R := R) (K := K) v I =
      chapterLocalizedFractionalFiltrationAtPrime (R := R) (K := K) v ϖ hϖ
        (chapterGlobalIdealExponentVector (R := R) (K := K) I v) := by
  classical
  let L := Localization.AtPrime v.asIdeal
  have hf : nonZeroDivisors R ≤
      (nonZeroDivisors L).comap (algebraMap R L) :=
    IsLocalization.nonZeroDivisors_le_comap v.asIdeal.primeCompl L
  have hmap :
      IsLocalization.map (S := K) K (algebraMap R L) hf = RingHom.id K := by
    apply IsFractionRing.ringHom_ext (A := R)
    intro r
    rw [IsLocalization.map_eq]
    exact (IsScalarTower.algebraMap_apply R L K r).symm
  have hext :
      chapterLocalizeFractionalIdealAtPrime (R := R) (K := K) v I =
        FractionalIdeal.extended K hf I := by
    apply FractionalIdeal.coeToSubmodule_injective
    change Submodule.span L (I : Set K) =
      Submodule.span L ((IsLocalization.map (S := K) K (algebraMap R L) hf) '' I)
    rw [hmap]
    congr 1
    ext x
    simp
  have hcoe (w : HeightOneSpectrum R) :
      FractionalIdeal.extendedHom K L
          (w.asIdeal : FractionalIdeal (nonZeroDivisors R) K) =
        (w.asIdeal.map (algebraMap R L) :
          FractionalIdeal (nonZeroDivisors L) K) :=
    FractionalIdeal.extendedHom_coeIdeal_eq_map K L w.asIdeal
  have hextHom :
      FractionalIdeal.extended K hf I =
        FractionalIdeal.extendedHom K L I := by
    rfl
  have hmapideal (w : HeightOneSpectrum R) (hw : w ≠ v) :
      w.asIdeal.map (algebraMap R L) = (⊤ : Ideal L) := by
    rw [IsLocalization.AtPrime.map_eq_top_of_not_le (S := L) (p := v.asIdeal)]
    intro hle
    have heq : w.asIdeal = v.asIdeal :=
      (w.isPrime.isMaximal w.ne_bot).eq_of_le
        (v.isPrime.isMaximal v.ne_bot).ne_top hle
    exact hw (HeightOneSpectrum.ext heq)
  have hbase (w : HeightOneSpectrum R) :
      FractionalIdeal.extendedHom K L
          (w.asIdeal : FractionalIdeal (nonZeroDivisors R) K) =
        if w = v then
          (IsLocalRing.maximalIdeal L :
            FractionalIdeal (nonZeroDivisors L) K)
        else 1 := by
    by_cases hw : w = v
    · simp only [if_pos hw]
      subst w
      rw [hcoe v, Localization.AtPrime.map_eq_maximalIdeal]
    · simp only [if_neg hw]
      rw [hcoe w, hmapideal w hw]
      simp
  have hfinite :
      Function.HasFiniteMulSupport
        (fun w : HeightOneSpectrum R =>
          (w.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^
            (FractionalIdeal.count K w I)) := by
    rw [Function.HasFiniteMulSupport]
    apply (Filter.eventually_cofinite.mp
      (FractionalIdeal.finite_factors (K := K) I)).subset
    intro w hw
    change (w.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^
        (FractionalIdeal.count K w I) ≠ 1 at hw
    by_contra hc
    have hc' : FractionalIdeal.count K w I = 0 := not_not.mp hc
    exact hw (by rw [hc']; simp)
  have hmapfactor :
      FractionalIdeal.extendedHom K L
          (∏ᶠ w : HeightOneSpectrum R,
            (w.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^
              (FractionalIdeal.count K w I)) =
        ∏ᶠ w : HeightOneSpectrum R,
          FractionalIdeal.extendedHom K L
            ((w.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^
              (FractionalIdeal.count K w I)) := by
    exact map_finprod
      (f := fun w : HeightOneSpectrum R =>
        (w.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^
          (FractionalIdeal.count K w I))
      (FractionalIdeal.extendedHom K L) hfinite
  have hterm (w : HeightOneSpectrum R) (n : ℤ) :
      FractionalIdeal.extendedHom K L
          ((w.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ n) =
        (FractionalIdeal.extendedHom K L
          (w.asIdeal : FractionalIdeal (nonZeroDivisors R) K)) ^ n := by
    exact map_zpow₀ (FractionalIdeal.extendedHom K L)
      (w.asIdeal : FractionalIdeal (nonZeroDivisors R) K) n
  have hsingle :
      (∏ᶠ w : HeightOneSpectrum R,
          FractionalIdeal.extendedHom K L
            ((w.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^
              (FractionalIdeal.count K w I))) =
        (FractionalIdeal.extendedHom K L
          (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K)) ^
            (FractionalIdeal.count K v I) := by
    simp_rw [hterm]
    apply finprod_eq_single _ v
    intro w hw
    rw [hbase]
    simp [hw]
  have hmax :
      (IsLocalRing.maximalIdeal L :
        FractionalIdeal (nonZeroDivisors L) K) =
      FractionalIdeal.spanSingleton (nonZeroDivisors L)
        (algebraMap L K ϖ) := by
    rw [hϖ.maximalIdeal_eq, FractionalIdeal.coeIdeal_span_singleton]
  have hpow (n : ℤ) :
      (IsLocalRing.maximalIdeal L :
        FractionalIdeal (nonZeroDivisors L) K) ^ n =
      FractionalIdeal.spanSingleton (nonZeroDivisors L)
        ((algebraMap L K ϖ) ^ n) := by
    rw [hmax]
    cases n with
    | ofNat k =>
        simp [FractionalIdeal.spanSingleton_pow]
    | negSucc k =>
        simp [zpow_negSucc, FractionalIdeal.spanSingleton_pow,
          FractionalIdeal.spanSingleton_inv]
  have hfil (n : ℤ) :
      chapterLocalizedFractionalFiltrationAtPrime (R := R) (K := K) v ϖ hϖ n =
        FractionalIdeal.spanSingleton (nonZeroDivisors L)
          ((algebraMap L K ϖ) ^ n) := by
    apply FractionalIdeal.coeToSubmodule_injective
    change Submodule.span L
        ({(algebraMap L K ϖ) ^ n} : Set K) =
      (FractionalIdeal.spanSingleton (nonZeroDivisors L)
        ((algebraMap L K ϖ) ^ n) : Submodule L K)
    rw [FractionalIdeal.coe_spanSingleton]
  have hfactor :
      (∏ᶠ w : HeightOneSpectrum R,
          (w.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^
            (FractionalIdeal.count K w I)) = I :=
    FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K) hI
  calc
    chapterLocalizeFractionalIdealAtPrime (R := R) (K := K) v I =
        FractionalIdeal.extendedHom K L I := hext.trans hextHom
    _ = FractionalIdeal.extendedHom K L
          (∏ᶠ w : HeightOneSpectrum R,
            (w.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^
              (FractionalIdeal.count K w I)) := by rw [hfactor]
    _ = ∏ᶠ w : HeightOneSpectrum R,
          FractionalIdeal.extendedHom K L
            ((w.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^
              (FractionalIdeal.count K w I)) := hmapfactor
    _ = (FractionalIdeal.extendedHom K L
          (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K)) ^
            (FractionalIdeal.count K v I) := hsingle
    _ = (IsLocalRing.maximalIdeal L :
          FractionalIdeal (nonZeroDivisors L) K) ^
            (FractionalIdeal.count K v I) := by
          rw [hbase v]
          simp
    _ = FractionalIdeal.spanSingleton (nonZeroDivisors L)
          ((algebraMap L K ϖ) ^
            (FractionalIdeal.count K v I)) := hpow _
    _ = chapterLocalizedFractionalFiltrationAtPrime (R := R) (K := K)
          v ϖ hϖ (chapterGlobalIdealExponentVector (R := R) (K := K) I v) := by
          symm
          apply hfil

/-- Localization of an integral ideal at a height-one prime. -/
def chapterLocalizeIdealAtPrime (v : HeightOneSpectrum R) (I : Ideal R) :
    Ideal (Localization.AtPrime v.asIdeal) :=
  I.map (algebraMap R (Localization.AtPrime v.asIdeal))

/-- The local exponent of an ideal after localization at a height-one prime.

This is defined independently of the global exponent: it says that the
localized ideal is a power of the local maximal ideal and records that power
as an integer. -/
def chapterLocalizedIdealExponentAtPrime (v : HeightOneSpectrum R)
    (J : Ideal (Localization.AtPrime v.asIdeal)) (n : ℤ) : Prop :=
  ∃ m : ℕ, n = (m : ℤ) ∧
    J = IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) ^ m

/-- Book §5.3: integral-ideal localization projects the global exponent vector
    to its `𝔭` coordinate. -/
theorem chapter_localization_projects_global_exponent
    (v : HeightOneSpectrum R) (I : Ideal R) (hI : I ≠ ⊥) :
    chapterLocalizedIdealExponentAtPrime (R := R) v
        (chapterLocalizeIdealAtPrime (R := R) v I)
        (chapterGlobalIdealExponentVector (R := R) (K := K)
          (I : FractionalIdeal (nonZeroDivisors R) K) v) := by
  classical
  have hv0 : v.asIdeal ≠ ⊥ := v.ne_bot
  let hvmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal hv0
  obtain ⟨J, hcop, hfactor⟩ :=
    Ideal.eq_prime_pow_mul_coprime (hpm := hvmax) hI v.asIdeal
  have hJnot : ¬ J ≤ v.asIdeal := by
    intro hJ
    have htop : v.asIdeal = ⊤ := by
      calc
        v.asIdeal = v.asIdeal ⊔ J := (sup_eq_left.mpr hJ).symm
        _ = ⊤ := hcop
    exact hvmax.ne_top htop
  have hcount :
      chapterGlobalIdealExponentVector (R := R) (K := K)
          (I : FractionalIdeal (nonZeroDivisors R) K) v =
        (Multiset.count v.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors I) : ℤ) := by
    unfold chapterGlobalIdealExponentVector chapterGlobalIdealExponent
    rw [FractionalIdeal.count_coe K v hI,
      Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot]
  have hlocal :
      chapterLocalizeIdealAtPrime (R := R) v I =
        IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) ^
          Multiset.count v.asIdeal
            (UniqueFactorizationMonoid.normalizedFactors I) := by
    let m : ℕ := Multiset.count v.asIdeal
      (UniqueFactorizationMonoid.normalizedFactors I)
    have hmap :
        I.map (algebraMap R (Localization.AtPrime v.asIdeal)) =
          IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) ^ m := by
      rw [hfactor, Ideal.map_mul, Ideal.map_pow,
        IsLocalization.AtPrime.map_eq_top_of_not_le
          (S := Localization.AtPrime v.asIdeal) (p := v.asIdeal) hJnot,
        Ideal.mul_top, Localization.AtPrime.map_eq_maximalIdeal]
    simpa [chapterLocalizeIdealAtPrime, m] using hmap
  refine ⟨Multiset.count v.asIdeal
    (UniqueFactorizationMonoid.normalizedFactors I), hcount, ?_⟩
  exact hlocal

/-- The projection statement written directly as `val_𝔭(I)`. -/
theorem chapter_localization_exponent_is_p_coordinate
    (v : HeightOneSpectrum R) (I : Ideal R) (hI : I ≠ ⊥) :
    ∃ m : ℕ,
      chapterGlobalIdealExponentVector (R := R) (K := K)
          (I : FractionalIdeal (nonZeroDivisors R) K) v = (m : ℤ) ∧
        chapterLocalizeIdealAtPrime (R := R) v I =
          IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) ^ m := by
  rcases chapter_localization_projects_global_exponent
      (R := R) (K := K) v I hI with ⟨m, hm, hlocal⟩
  exact ⟨m, hm, hlocal⟩

end DedekindLocalizationProjection

section RamificationShift

variable {R S : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S]

omit [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S] in
/-- Book §5.3: ramification index as the length of the localized quotient. -/
theorem chapter_ramification_index_length_formula
  (q : Ideal S) [q.IsPrime] :
    let Sq := Localization.AtPrime q;
      q.ramificationIdx R =
      (Module.length Sq
        (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat := by
  exact Ideal.ramificationIdx_def q R

omit [Module.Finite R S] in
/-- Book §5.3: the ramification index is the shift between the two local filtrations. -/
theorem chapter_ramification_index_is_filtration_shift
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    [Module.IsTorsionFree R S]
    (hp : p ≠ ⊥) :
    let Sq := Localization.AtPrime q;
    p.map (algebraMap R Sq) =
        IsLocalRing.maximalIdeal Sq ^ q.ramificationIdx R ∧
      ∀ n : ℕ,
        p.map (algebraMap R Sq) * IsLocalRing.maximalIdeal Sq ^ n =
          IsLocalRing.maximalIdeal Sq ^ (n + q.ramificationIdx R) := by
  classical
  dsimp
  have hpS : p.map (algebraMap R S) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hp
  have hq0 : q ≠ ⊥ :=
    ne_bot_of_le_ne_bot hpS
      (Ideal.map_le_of_le_comap (q.over_def p).le)
  let hqmax : q.IsMaximal := (inferInstance : q.IsPrime).isMaximal hq0
  obtain ⟨I, hqI, hfactor⟩ :=
    Ideal.eq_prime_pow_mul_coprime (hpm := hqmax) hpS q
  replace hqI : ¬ I ≤ q := by
    contrapose! hqI
    rw [sup_of_le_left hqI]
    exact (inferInstance : q.IsPrime).ne_top
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
    p q hpS] at hfactor
  have hmap : p.map (algebraMap R (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ q.ramificationIdx R := by
    apply_fun (Ideal.map (algebraMap S (Localization.AtPrime q))) at hfactor
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, Ideal.map_mul, Ideal.map_pow,
      IsLocalization.AtPrime.map_eq_top_of_not_le
        (S := Localization.AtPrime q) (p := q) hqI, Ideal.mul_top,
      Localization.AtPrime.map_eq_maximalIdeal] at hfactor
    exact hfactor
  refine ⟨hmap, ?_⟩
  intro n
  rw [hmap, ← pow_add, add_comm]

end RamificationShift

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter05
