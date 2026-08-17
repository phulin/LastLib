import Mathlib.Algebra.CharP.Defs
import Mathlib.RingTheory.HahnSeries.Basic
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter03

open Set
open scoped BigOperators WithZero LaurentSeries PowerSeries

/-!
# Chapter 3: Valuation rings and divisibility

Mathlib uses multiplicative valuations, so bounded elements are written `v x ≤ 1`.
The additive convention in the book is recorded below with `AddValuation`; under the
usual sign change, `v x ≤ 1` is the same assertion as `0 ≤ v x`.
-/

universe u v w

/-! # Book 1, Chapter 3, Section 3.1: Bounded Elements
-/

section BoundedElements

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-! ### 3.1. Bounded elements -/

/-- The valuation ring attached to a multiplicative Mathlib valuation. -/
abbrev valuationRingOf (v : Valuation K Γ) : Subring K :=
  v.integer

/-- The maximal ideal of the valuation ring. -/
def maximalIdealOf (v : Valuation K Γ) : Ideal (valuationRingOf v) :=
  IsLocalRing.maximalIdeal (valuationRingOf v)

/-- The residue field of the valuation ring. -/
abbrev residueFieldOf (v : Valuation K Γ) :=
  IsLocalRing.ResidueField (valuationRingOf v)

/-- The reduction map to the residue field. -/
def residueMapOf (v : Valuation K Γ) : valuationRingOf v →+* residueFieldOf v :=
  IsLocalRing.residue _

/-- The characteristic of the residue field of a valuation. -/
noncomputable abbrev residueCharacteristic (v : Valuation K Γ) : ℕ :=
  ringChar (residueFieldOf v)

/-- The valued field has equal characteristic when its field and residue field
    have the same characteristic. -/
def IsEqualCharacteristic (v : Valuation K Γ) : Prop :=
  ringChar K = residueCharacteristic v

/-- The valued field has mixed characteristic `(0, p)`. -/
def IsMixedCharacteristic (v : Valuation K Γ) (p : ℕ) : Prop :=
  ringChar K = 0 ∧ residueCharacteristic v = p ∧ p.Prime

theorem residueCharacteristic_isPrime_or_zero (v : Valuation K Γ) :
    Nat.Prime (residueCharacteristic v) ∨ residueCharacteristic v = 0 := by
  exact CharP.char_is_prime_or_zero (residueFieldOf v)
    (ringChar (residueFieldOf v))

theorem equal_or_mixed_characteristic (v : Valuation K Γ) :
    IsEqualCharacteristic v ∨ ∃ p, IsMixedCharacteristic v p := by
  by_cases h : ringChar K = residueCharacteristic v
  · exact Or.inl h
  · have hK : ringChar K = 0 := by
      rcases CharP.char_is_prime_or_zero K (ringChar K) with hprime | hzero
      · have hcastK : (ringChar K : K) = 0 := ringChar.Nat.cast_ringChar
        have hcastV : (ringChar K : valuationRingOf v) = 0 := by
          apply Subtype.ext
          exact hcastK
        have hcastResidue : (ringChar K : residueFieldOf v) = 0 := by
          calc
            (ringChar K : residueFieldOf v) =
                residueMapOf v (ringChar K : valuationRingOf v) := by
                  rw [map_natCast]
            _ = residueMapOf v 0 := by rw [hcastV]
            _ = 0 := map_zero _
        have hdiv : residueCharacteristic v ∣ ringChar K :=
          ringChar.dvd hcastResidue
        have hres_ne_one : residueCharacteristic v ≠ 1 := by
          exact CharP.ringChar_ne_one (R := residueFieldOf v)
        have hres_eq : residueCharacteristic v = ringChar K :=
          (Nat.dvd_prime hprime).mp hdiv |>.resolve_left hres_ne_one
        exact False.elim (h hres_eq.symm)
      · exact hzero
    have hres_ne_zero : residueCharacteristic v ≠ 0 := by
      intro hzero
      apply h
      exact hK.trans hzero.symm
    have hres_prime : (residueCharacteristic v).Prime :=
      CharP.char_prime_of_ne_zero (R := residueFieldOf v) hres_ne_zero
    refine Or.inr ⟨residueCharacteristic v, ?_⟩
    exact ⟨hK, rfl, hres_prime⟩

/-- The maximal ideal viewed as a subset of the ambient field. -/
def maximalIdealImageOf (v : Valuation K Γ) : Set K :=
  (algebraMap (valuationRingOf v) K) '' (maximalIdealOf v : Set (valuationRingOf v))

/- The basic numerical descriptions of bounded elements and infinitesimals. -/

theorem mem_valuationRingOf_iff (v : Valuation K Γ) (x : K) :
    x ∈ valuationRingOf v ↔ v x ≤ 1 := by
  exact v.mem_integer_iff x

theorem valuationRingOf_isSubring (v : Valuation K Γ) :
    IsDomain (valuationRingOf v) ∧ ValuationRing (valuationRingOf v) := by
  exact ⟨inferInstance, inferInstance⟩

theorem valuationRingOf_isLocal (v : Valuation K Γ) :
    IsLocalRing (valuationRingOf v) := by
  infer_instance

theorem mem_maximalIdealOf_iff (v : Valuation K Γ) (x : valuationRingOf v) :
    x ∈ maximalIdealOf v ↔ v (x : K) < 1 := by
  change x ∈ IsLocalRing.maximalIdeal (v.integer) ↔ _
  rw [IsLocalRing.mem_maximalIdeal]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem mem_maximalIdealImageOf_iff (v : Valuation K Γ) (x : K) :
    x ∈ maximalIdealImageOf v ↔ v x < 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_maximalIdealOf_iff v y).mp hy
  · intro hx
    let y : valuationRingOf v :=
      ⟨x, (mem_valuationRingOf_iff v x).2 hx.le⟩
    exact ⟨y, (mem_maximalIdealOf_iff v y).2 hx, rfl⟩

theorem valuationRingOf_isUnit_iff (v : Valuation K Γ) (x : valuationRingOf v) :
    IsUnit x ↔ v (x : K) = 1 := by
  exact (Valuation.integer.integers v).isUnit_iff_valuation_eq_one

theorem maximalIdealOf_eq_nonunits (v : Valuation K Γ) :
    (maximalIdealOf v : Set (valuationRingOf v)) = nonunits (valuationRingOf v) := by
  ext x
  change x ∈ IsLocalRing.maximalIdeal (v.integer) ↔ _
  rw [IsLocalRing.mem_maximalIdeal]

theorem maximalIdealOf_unique (v : Valuation K Γ) (I : Ideal (valuationRingOf v)) :
    I.IsMaximal ↔ I = maximalIdealOf v := by
  simpa [maximalIdealOf] using
    (IsLocalRing.isMaximal_iff (R := valuationRingOf v) (I := I))

theorem residueMapOf_eq_iff_difference_mem (v : Valuation K Γ)
    (x y : valuationRingOf v) :
    residueMapOf v x = residueMapOf v y ↔
      (x - y : valuationRingOf v) ∈ maximalIdealOf v := by
  change IsLocalRing.residue (valuationRingOf v) x =
      IsLocalRing.residue (valuationRingOf v) y ↔
      (x - y : valuationRingOf v) ∈ IsLocalRing.maximalIdeal (valuationRingOf v)
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]

theorem residueMapOf_eq_iff_difference_small (v : Valuation K Γ)
    (x y : valuationRingOf v) :
    residueMapOf v x = residueMapOf v y ↔ v ((x : K) - (y : K)) < 1 := by
  rw [residueMapOf_eq_iff_difference_mem, mem_maximalIdealOf_iff]
  rfl

/- The same definitions in the additive convention used by the prose. -/

variable {A : Type*} [LinearOrderedAddCommGroupWithTop A]

/-- The bounded ring of an additive valuation, expressed through Mathlib's integers. -/
abbrev additiveValuationRingOf (v : AddValuation K A) : Subring K :=
  (AddValuation.toValuation v).integer

/-- The strictly positive part of an additive valuation ring. -/
def additiveMaximalIdealOf (v : AddValuation K A) :
    Ideal (additiveValuationRingOf v) :=
  IsLocalRing.maximalIdeal (additiveValuationRingOf v)

theorem mem_additiveValuationRingOf_iff (v : AddValuation K A) (x : K) :
    x ∈ additiveValuationRingOf v ↔ 0 ≤ v x := by
  change (AddValuation.toValuation v) x ≤ 1 ↔ _
  change Multiplicative.ofAdd (OrderDual.toDual (v x)) ≤
      Multiplicative.ofAdd (OrderDual.toDual 0) ↔ _
  rw [Multiplicative.ofAdd_le, OrderDual.toDual_le_toDual]

theorem mem_additiveMaximalIdealOf_iff (v : AddValuation K A)
    (x : additiveValuationRingOf v) :
    x ∈ additiveMaximalIdealOf v ↔ 0 < v (x : K) := by
  change x ∈ IsLocalRing.maximalIdeal ((AddValuation.toValuation v).integer) ↔ _
  rw [IsLocalRing.mem_maximalIdeal]
  change ¬ IsUnit x ↔ _
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change Multiplicative.ofAdd (OrderDual.toDual (v (x : K))) <
      Multiplicative.ofAdd (OrderDual.toDual 0) ↔ _
  rw [Multiplicative.ofAdd_lt, OrderDual.toDual_lt_toDual]

theorem additiveValuationRingOf_isLocal (v : AddValuation K A) :
    IsLocalRing (additiveValuationRingOf v) := by
  infer_instance

/- Absolute-value language for the same bounded/infinitesimal distinction. -/

/-- Elements of absolute value at most one. -/
def absoluteValueBoundedSet (f : AbsoluteValue K ℝ) : Set K :=
  {x | f x ≤ 1}

/- Elements of absolute value strictly less than one. -/
def absoluteValueInfinitesimalSet (f : AbsoluteValue K ℝ) : Set K :=
  {x | f x < 1}

/-- A normalized contracting absolute-value presentation of a valuation ring. -/
structure ContractingAbsoluteValuePresentation (v : Valuation K Γ)
    (f : AbsoluteValue K ℝ) : Type _ where
  valueMap : Γ →*₀ ℝ
  valueMap_order_iff : ∀ {a b : Γ}, a ≠ 0 → b ≠ 0 →
    (a ≤ b ↔ valueMap a ≤ valueMap b)
  valueMap_pos : ∀ {a : Γ}, a ≠ 0 → 0 < valueMap a
  valueMap_eq : ∀ x : K, f x = valueMap (v x)
  bounded_iff : ∀ x : K, x ∈ valuationRingOf v ↔ f x ≤ 1
  infinitesimal_iff : ∀ x : K, x ∈ maximalIdealImageOf v ↔ f x < 1

theorem residue_forgets_infinitesimals (v : Valuation K Γ)
    (x y : valuationRingOf v) :
    residueMapOf v x = residueMapOf v y ↔
      (x : K) - (y : K) ∈ maximalIdealImageOf v := by
  rw [residueMapOf_eq_iff_difference_mem]
  constructor
  · intro h
    exact ⟨x - y, h, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    have hsub : z = x - y := by
      apply Subtype.ext
      change (z : K) = (x : K) - (y : K) at hzy
      exact hzy
    simpa [hsub] using hz

/- The two standard examples in the chapter. -/

/-- The prime ideal `(p)` of `ℤ`. -/
def pPrimeIdeal (p : ℕ) : Ideal ℤ :=
  Ideal.span ({(p : ℤ)} : Set ℤ)

instance pPrimeIdeal_isPrime (p : ℕ) [Fact p.Prime] : (pPrimeIdeal p).IsPrime := by
  apply Ideal.isPrime_span_singleton_of_prime
  exact Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))

/-- The localization `ℤ_(p)`, represented as localization at `(p)`. -/
abbrev pLocalIntegers (p : ℕ) [Fact p.Prime] : Type :=
  Localization.AtPrime (pPrimeIdeal p)

/-- The maximal ideal of `ℤ_(p)`. -/
def pLocalMaximalIdeal (p : ℕ) [Fact p.Prime] : Ideal (pLocalIntegers p) :=
  IsLocalRing.maximalIdeal _

/-- The ideal generated by `p` in `ℤ_(p)`. -/
def pLocalPrincipalIdeal (p : ℕ) [Fact p.Prime] : Ideal (pLocalIntegers p) :=
  Ideal.span {algebraMap ℤ (pLocalIntegers p) (p : ℤ)}

/-- The `p`-adic valuation on `ℚ`. -/
def pValuation (p : ℕ) [Fact p.Prime] : Valuation ℚ ℤᵐ⁰ :=
  Rat.padicValuation p

/-- Its valuation ring. -/
def pValuationRing (p : ℕ) [Fact p.Prime] : Subring ℚ :=
  valuationRingOf (pValuation p)

/-- Its maximal ideal. -/
def pValuationMaximalIdeal (p : ℕ) [Fact p.Prime] : Ideal (pValuationRing p) :=
  maximalIdealOf (pValuation p)

noncomputable def pValuationRingEquiv (p : ℕ) [Fact p.Prime] :
    pValuationRing p ≃+* pLocalIntegers p := by
  letI : IsLocalization ((pPrimeIdeal p).primeCompl) (pValuationRing p) :=
    { map_units := by
        rintro ⟨y, hy⟩
        have hnot : ¬ (p : ℤ) ∣ y := by
          intro hdiv
          apply hy
          change y ∈ Ideal.span ({(p : ℤ)} : Set ℤ)
          exact Ideal.mem_span_singleton.mpr hdiv
        apply (valuationRingOf_isUnit_iff (pValuation p)
          (algebraMap ℤ (pValuationRing p) y)).2
        change Rat.padicValuation p (y : ℚ) = 1
        rw [Rat.padicValuation_cast]
        exact Int.padicValuation_eq_one_iff.mpr hnot
      surj z := by
        have hden : ¬ p ∣ z.1.den := (Rat.padicValuation_le_one_iff).1 z.2
        have hden' : ¬ (p : ℤ) ∣ (z.1.den : ℤ) := by
          intro hdiv
          apply hden
          exact_mod_cast hdiv
        have hden'' : (z.1.den : ℤ) ∉ pPrimeIdeal p := by
          intro hmem
          apply hden'
          exact Ideal.mem_span_singleton.mp (by simpa [pPrimeIdeal] using hmem)
        let d : (pPrimeIdeal p).primeCompl :=
          ⟨(z.1.den : ℤ), hden''⟩
        refine ⟨(z.1.num, d), ?_⟩
        apply Subtype.ext
        change z.1 * (z.1.den : ℚ) = (z.1.num : ℚ)
        calc
          z.1 * (z.1.den : ℚ) =
              ((z.1.num : ℚ) / (z.1.den : ℚ)) * (z.1.den : ℚ) := by
                rw [z.1.num_div_den]
          _ = (z.1.num : ℚ) := by field_simp [Rat.den_nz]
      exists_of_eq := by
        intro x y hxy
        refine ⟨1, ?_⟩
        simpa using hxy }
  exact (IsLocalization.algEquiv ((pPrimeIdeal p).primeCompl)
    (pValuationRing p) (pLocalIntegers p)).toRingEquiv

theorem pValuationRing_is_pLocal (p : ℕ) [Fact p.Prime] :
    Nonempty (pValuationRing p ≃+* pLocalIntegers p) := by
  exact ⟨pValuationRingEquiv p⟩

theorem pValuationMaximalIdeal_is_generated_by_p (p : ℕ) [Fact p.Prime] :
    ∃ e : pValuationRing p ≃+* pLocalIntegers p,
      Ideal.map e.toRingHom (pValuationMaximalIdeal p) = pLocalPrincipalIdeal p := by
  let : IsLocalRing (pValuationRing p) := valuationRingOf_isLocal (pValuation p)
  let e := pValuationRingEquiv p
  refine ⟨e, ?_⟩
  have hmax : Ideal.map e.toRingHom (pValuationMaximalIdeal p) =
      IsLocalRing.maximalIdeal (pLocalIntegers p) := by
    exact IsLocalRing.map_ringEquiv_maximalIdeal e
  have hp : pLocalPrincipalIdeal p = IsLocalRing.maximalIdeal (pLocalIntegers p) := by
    rw [pLocalPrincipalIdeal, ← IsLocalization.AtPrime.map_eq_maximalIdeal
      (pPrimeIdeal p) (pLocalIntegers p)]
    simp [pPrimeIdeal, Ideal.map_span]
  exact hmax.trans hp.symm

abbrev pValuationResidueField (p : ℕ) [Fact p.Prime] :=
  residueFieldOf (pValuation p)

theorem pValuationResidueField_equiv_finiteField (p : ℕ) [Fact p.Prime] :
    Nonempty (pValuationResidueField p ≃+* ZMod p) := by
  let : IsLocalRing (pValuationRing p) := valuationRingOf_isLocal (pValuation p)
  let : (pPrimeIdeal p).IsMaximal := by
    change (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal
    infer_instance
  let e := pValuationRingEquiv p
  let q := IsLocalization.AtPrime.equivQuotMaximalIdeal
    (pPrimeIdeal p) (pLocalIntegers p)
  exact ⟨(IsLocalRing.ResidueField.mapEquiv e).trans
    (q.symm.trans (Int.quotientSpanNatEquivZMod p))⟩

/- The rational-function example `k[t]_(t) ⊂ k(t)`. -/

noncomputable def tPrimeIdeal (k : Type*) [Field k] : Ideal (Polynomial k) :=
  Ideal.span ({Polynomial.X} : Set (Polynomial k))

instance tPrimeIdeal_isPrime (k : Type*) [Field k] : (tPrimeIdeal k).IsPrime := by
  rw [tPrimeIdeal]
  apply Ideal.isPrime_span_singleton_of_prime
  exact Polynomial.prime_X

abbrev tLocalPolynomialRing (k : Type*) [Field k] : Type _ :=
  Localization.AtPrime (tPrimeIdeal k)

noncomputable def tLocalMaximalIdeal (k : Type*) [Field k] :
    Ideal (tLocalPolynomialRing k) :=
  IsLocalRing.maximalIdeal _

noncomputable def tLocalPrincipalIdeal (k : Type*) [Field k] :
    Ideal (tLocalPolynomialRing k) :=
  Ideal.span {algebraMap (Polynomial k) (tLocalPolynomialRing k) Polynomial.X}

/-- The `t`-adic valuation on the rational function field `k(t)`. -/
noncomputable def tValuation (k : Type*) [Field k] : Valuation (RatFunc k) ℤᵐ⁰ :=
  (Polynomial.idealX k).valuation _

noncomputable abbrev tValuationRing (k : Type*) [Field k] : Subring (RatFunc k) :=
  valuationRingOf (tValuation k)

noncomputable def tValuationMaximalIdeal (k : Type*) [Field k] :
    Ideal (tValuationRing k) :=
  maximalIdealOf (tValuation k)

noncomputable def tParameterInValuationRing (k : Type*) [Field k] : tValuationRing k :=
  ⟨algebraMap (Polynomial k) (RatFunc k) Polynomial.X, by
    rw [mem_valuationRingOf_iff, tValuation]
    rw [RatFunc.algebraMap_X, Polynomial.valuation_X_eq_neg_one]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num⟩

noncomputable def tParameterInLocalPolynomialRing (k : Type*) [Field k] :
    tLocalPolynomialRing k :=
  algebraMap (Polynomial k) (tLocalPolynomialRing k) Polynomial.X

theorem tValuationRing_is_tLocal (k : Type*) [Field k] :
    ∃ e : tValuationRing k ≃+* tLocalPolynomialRing k,
      e (tParameterInValuationRing k) =
        tParameterInLocalPolynomialRing k ∧
      ∀ f : Polynomial k,
        e ⟨algebraMap (Polynomial k) (RatFunc k) f, by
          rw [mem_valuationRingOf_iff, tValuation]
          exact (Polynomial.idealX k).valuation_le_one f⟩ =
          algebraMap (Polynomial k) (tLocalPolynomialRing k) f := by
  classical
  let A := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
    (RatFunc k) (Polynomial.idealX k)
  have hAeq : A = (tValuation k).valuationSubring := by
    exact IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
      (K := RatFunc k) (v := Polynomial.idealX k)
  have hA : A.toSubring = tValuationRing k := by
    rw [hAeq]
    rfl
  have hle : tValuationRing k ≤ A.toSubring := by
    rw [hA]
  let eSub : tValuationRing k ≃+* A := by
    let f : tValuationRing k →+* A :=
      { toFun := fun x => ⟨(x : RatFunc k), hle x.property⟩
        map_one' := rfl
        map_mul' := by intro x y; rfl
        map_zero' := rfl
        map_add' := by intro x y; rfl }
    refine RingEquiv.ofBijective f ?_
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : A => (z : RatFunc k)) hxy
    · intro y
      have hy : (y : RatFunc k) ∈ tValuationRing k := by
        rw [← hA]
        exact y.property
      exact ⟨⟨y, hy⟩, rfl⟩
  have hP : tPrimeIdeal k = (Polynomial.idealX k).asIdeal := by
    rfl
  let : IsLocalization (tPrimeIdeal k).primeCompl A := by
    let : (Polynomial.idealX k).asIdeal.IsPrime :=
      (Polynomial.idealX k).isPrime
    change IsLocalization
      ((Polynomial.idealX k).asIdeal.primeCompl)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
        (RatFunc k) (Polynomial.idealX k))
    infer_instance
  let eLoc : A ≃ₐ[Polynomial k] tLocalPolynomialRing k :=
    IsLocalization.algEquiv (tPrimeIdeal k).primeCompl A
      (tLocalPolynomialRing k)
  let e := eSub.trans eLoc.toRingEquiv
  refine ⟨e, ?_, ?_⟩
  · have hsub : eSub (tParameterInValuationRing k) =
        algebraMap (Polynomial k) A Polynomial.X := by
      apply Subtype.ext
      rfl
    rw [show e (tParameterInValuationRing k) =
        eLoc (eSub (tParameterInValuationRing k)) by rfl, hsub]
    exact eLoc.commutes Polynomial.X
  · intro f
    have hsub : eSub ⟨algebraMap (Polynomial k) (RatFunc k) f, by
          rw [mem_valuationRingOf_iff, tValuation]
          exact (Polynomial.idealX k).valuation_le_one f⟩ =
        algebraMap (Polynomial k) A f := by
      apply Subtype.ext
      rfl
    rw [show e _ = eLoc (eSub _) by rfl, hsub]
    exact eLoc.commutes f

noncomputable def tEvaluationAtZero (k : Type*) [Field k] :
    tLocalPolynomialRing k →+* k :=
  IsLocalization.lift (M := (tPrimeIdeal k).primeCompl)
    (g := Polynomial.evalRingHom (0 : k)) (by
      intro y
      have hy0 : Polynomial.eval 0 (y : Polynomial k) ≠ 0 := by
        intro hzero
        apply y.property
        change (y : Polynomial k) ∈ Ideal.span ({Polynomial.X} : Set (Polynomial k))
        rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
        simpa [Polynomial.coeff_zero_eq_eval_zero] using hzero
      exact (isUnit_iff_ne_zero.mpr hy0))

theorem tLocalMaximalIdeal_is_generated_by_t (k : Type*) [Field k] :
    tLocalMaximalIdeal k = Ideal.span {tParameterInLocalPolynomialRing k} := by
  classical
  change IsLocalRing.maximalIdeal (tLocalPolynomialRing k) =
    Ideal.span {tParameterInLocalPolynomialRing k}
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
    (tPrimeIdeal k) (tLocalPolynomialRing k)]
  simp [tPrimeIdeal, tParameterInLocalPolynomialRing,
    Ideal.map_span]

theorem tValuationMaximalIdeal_is_generated_by_t (k : Type*) [Field k] :
    tValuationMaximalIdeal k =
      Ideal.span {tParameterInValuationRing k} := by
  classical
  let : IsLocalRing (tValuationRing k) := valuationRingOf_isLocal (tValuation k)
  obtain ⟨e, heparam, _hepoly⟩ := tValuationRing_is_tLocal k
  have hmap : Ideal.map e.toRingHom (tValuationMaximalIdeal k) =
      Ideal.map e.toRingHom (Ideal.span {tParameterInValuationRing k}) := by
    rw [show tValuationMaximalIdeal k = IsLocalRing.maximalIdeal (tValuationRing k) by rfl]
    have hmax : Ideal.map e.toRingHom
        (IsLocalRing.maximalIdeal (tValuationRing k)) =
        IsLocalRing.maximalIdeal (tLocalPolynomialRing k) :=
      IsLocalRing.map_ringEquiv_maximalIdeal e
    rw [hmax]
    simp only [Ideal.map_span, Set.image_singleton]
    change IsLocalRing.maximalIdeal (tLocalPolynomialRing k) =
      Ideal.span {e (tParameterInValuationRing k)}
    rw [heparam]
    rw [← tLocalMaximalIdeal_is_generated_by_t k]
    rfl
  calc
    tValuationMaximalIdeal k =
        Ideal.comap e.toRingHom (Ideal.map e.toRingHom (tValuationMaximalIdeal k)) := by
          symm
          exact Ideal.comap_map_of_bijective (f := e.toRingHom) e.bijective
    _ = Ideal.comap e.toRingHom
        (Ideal.map e.toRingHom (Ideal.span {tParameterInValuationRing k})) := by
          rw [hmap]
    _ = Ideal.span {tParameterInValuationRing k} := by
      exact Ideal.comap_map_of_bijective (f := e.toRingHom) e.bijective

theorem tValuationResidueField_is_the_coefficient_field (k : Type*) [Field k] :
    Nonempty (residueFieldOf (tValuation k) ≃+* k) := by
  classical
  let : IsLocalRing (tValuationRing k) := valuationRingOf_isLocal (tValuation k)
  let : (tPrimeIdeal k).IsMaximal := by
    change (Ideal.span ({Polynomial.X} : Set (Polynomial k))).IsMaximal
    refine (Ideal.Quotient.maximal_ideal_iff_isField_quotient
      (Ideal.span ({Polynomial.X} : Set (Polynomial k)))).mpr ?_
    have hX : Ideal.span ({Polynomial.X} : Set (Polynomial k)) =
        Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k)) := by
      simp
    rw [hX]
    exact (Polynomial.quotientSpanXSubCAlgEquiv (0 : k)).toMulEquiv.isField
      (Field.toIsField k)
  obtain ⟨e, _heparam, _hepoly⟩ := tValuationRing_is_tLocal k
  let q := IsLocalization.AtPrime.equivQuotMaximalIdeal
    (tPrimeIdeal k) (tLocalPolynomialRing k)
  have hX : tPrimeIdeal k =
      Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k)) := by
    simp [tPrimeIdeal]
  let : (Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k))).IsMaximal :=
    hX ▸ (inferInstance : (tPrimeIdeal k).IsMaximal)
  let : Field (Polynomial k ⧸ tPrimeIdeal k) := Ideal.Quotient.field _
  let : Field (Polynomial k ⧸ Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k))) :=
    Ideal.Quotient.field _
  let : (tPrimeIdeal k).IsPrime := inferInstance
  let : (Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k))).IsMaximal :=
    hX ▸ (inferInstance : (tPrimeIdeal k).IsMaximal)
  let : (Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k))).IsPrime :=
    inferInstance
  let : Field (Polynomial k ⧸ tPrimeIdeal k) := Ideal.Quotient.field _
  let : Field (Polynomial k ⧸ Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k))) :=
    Ideal.Quotient.field _
  let qpoly := Ideal.quotEquivOfEq hX
  let r := q.symm.trans
    (qpoly.trans (Polynomial.quotientSpanXSubCAlgEquiv (0 : k)).toRingEquiv)
  exact ⟨(IsLocalRing.ResidueField.mapEquiv e).trans r⟩

theorem tResidue_is_evaluation_at_zero (k : Type*) [Field k] :
    ∃ e : IsLocalRing.ResidueField (tLocalPolynomialRing k) ≃+* k,
      ∀ x : tLocalPolynomialRing k,
        e (IsLocalRing.residue (tLocalPolynomialRing k) x) = tEvaluationAtZero k x := by
  classical
  let : (tPrimeIdeal k).IsMaximal := by
    change (Ideal.span ({Polynomial.X} : Set (Polynomial k))).IsMaximal
    refine (Ideal.Quotient.maximal_ideal_iff_isField_quotient
      (Ideal.span ({Polynomial.X} : Set (Polynomial k)))).mpr ?_
    have hX : Ideal.span ({Polynomial.X} : Set (Polynomial k)) =
        Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k)) := by
      simp
    rw [hX]
    exact (Polynomial.quotientSpanXSubCAlgEquiv (0 : k)).toMulEquiv.isField
      (Field.toIsField k)
  let q := IsLocalization.AtPrime.equivQuotMaximalIdeal
    (tPrimeIdeal k) (tLocalPolynomialRing k)
  have hX : tPrimeIdeal k =
      Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k)) := by
    simp [tPrimeIdeal]
  let : (Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k))).IsMaximal :=
    hX ▸ (inferInstance : (tPrimeIdeal k).IsMaximal)
  let : Field (Polynomial k ⧸ tPrimeIdeal k) := Ideal.Quotient.field _
  let : Field (Polynomial k ⧸ Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k))) :=
    Ideal.Quotient.field _
  let qpoly := Ideal.quotEquivOfEq hX
  let e := q.symm.trans
    (qpoly.trans (Polynomial.quotientSpanXSubCAlgEquiv (0 : k)).toRingEquiv)
  refine ⟨e, ?_⟩
  intro x
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (tPrimeIdeal k).primeCompl x
  rw [IsLocalRing.residue_def]
  change (Polynomial.quotientSpanXSubCAlgEquiv (0 : k))
      (Ideal.quotEquivOfEq hX
        ((IsLocalization.AtPrime.equivQuotMaximalIdeal
          (tPrimeIdeal k) (tLocalPolynomialRing k)).symm
          (Ideal.Quotient.mk _ (IsLocalization.mk' (tLocalPolynomialRing k) a s)))) =
    tEvaluationAtZero k (IsLocalization.mk' (tLocalPolynomialRing k) a s)
  rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_symm_apply_mk]
  have hs0 : Polynomial.eval 0 (s : Polynomial k) ≠ 0 := by
    intro hs
    apply s.property
    change (s : Polynomial k) ∈ Ideal.span ({Polynomial.X} : Set (Polynomial k))
    rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hs
  rw [map_mul]
  simp only [Ideal.quotEquivOfEq_mk]
  rw [map_mul]
  change (Polynomial.quotientSpanXSubCAlgEquiv (0 : k))
      (Ideal.Quotient.mk _ a) *
      (Polynomial.quotientSpanXSubCAlgEquiv (0 : k))
        ((Ideal.quotEquivOfEq hX)
          ((Ideal.Quotient.mk _ (s : Polynomial k))⁻¹)) = _
  have hqinv := map_inv₀ (Ideal.quotEquivOfEq hX)
    (Ideal.Quotient.mk _ (s : Polynomial k))
  have hQinv := map_inv₀ (Polynomial.quotientSpanXSubCAlgEquiv (0 : k))
    ((Ideal.quotEquivOfEq hX) (Ideal.Quotient.mk _ (s : Polynomial k)))
  rw [hqinv, hQinv, Ideal.quotEquivOfEq_mk,
    Polynomial.quotientSpanXSubCAlgEquiv_mk]
  rw [tEvaluationAtZero, IsLocalization.lift_mk']
  simp [IsUnit.coe_liftRight]

end BoundedElements

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter03
