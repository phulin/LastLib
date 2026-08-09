import Mathlib

namespace ValuationsBook.Chapter03

open Set
open scoped BigOperators WithZero LaurentSeries PowerSeries

/-!
# Chapter 3: Valuation rings and divisibility

Mathlib uses multiplicative valuations, so bounded elements are written `v x ≤ 1`.
The additive convention in the book is recorded below with `AddValuation`; under the
usual sign change, `v x ≤ 1` is the same assertion as `0 ≤ v x`.
-/

universe u v w

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
  letI : IsLocalRing (pValuationRing p) := valuationRingOf_isLocal (pValuation p)
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
  letI : IsLocalRing (pValuationRing p) := valuationRingOf_isLocal (pValuation p)
  letI : (pPrimeIdeal p).IsMaximal := by
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
  letI : IsLocalization (tPrimeIdeal k).primeCompl A := by
    letI : (Polynomial.idealX k).asIdeal.IsPrime :=
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
  simp [tPrimeIdeal, tLocalPrincipalIdeal, tParameterInLocalPolynomialRing,
    Ideal.map_span]

theorem tValuationMaximalIdeal_is_generated_by_t (k : Type*) [Field k] :
    tValuationMaximalIdeal k =
      Ideal.span {tParameterInValuationRing k} := by
  classical
  letI : IsLocalRing (tValuationRing k) := valuationRingOf_isLocal (tValuation k)
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
  letI : IsLocalRing (tValuationRing k) := valuationRingOf_isLocal (tValuation k)
  letI : (tPrimeIdeal k).IsMaximal := by
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
  letI : (Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k))).IsMaximal :=
    hX ▸ (inferInstance : (tPrimeIdeal k).IsMaximal)
  letI : Field (Polynomial k ⧸ tPrimeIdeal k) := Ideal.Quotient.field _
  letI : Field (Polynomial k ⧸ Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k))) :=
    Ideal.Quotient.field _
  letI : (tPrimeIdeal k).IsPrime := inferInstance
  letI : (Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k))).IsMaximal :=
    hX ▸ (inferInstance : (tPrimeIdeal k).IsMaximal)
  letI : (Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k))).IsPrime :=
    inferInstance
  letI : Field (Polynomial k ⧸ tPrimeIdeal k) := Ideal.Quotient.field _
  letI : Field (Polynomial k ⧸ Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k))) :=
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
  letI : (tPrimeIdeal k).IsMaximal := by
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
  letI : (Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k))).IsMaximal :=
    hX ▸ (inferInstance : (tPrimeIdeal k).IsMaximal)
  letI : Field (Polynomial k ⧸ tPrimeIdeal k) := Ideal.Quotient.field _
  letI : Field (Polynomial k ⧸ Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k))) :=
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
  simp [IsUnit.coe_liftRight, hs0]

end BoundedElements

section IntrinsicCriterion

variable {K : Type*} [Field K]

/-! ### 3.2. The intrinsic characterization -/

/-- A subring is a valuation ring of some valuation on its fraction field. -/
def IsValuationRingSubring (V : Subring K) : Prop :=
  ∃ A : ValuationSubring K, V = A.toSubring

/-- The second condition in the valuation-ring criterion. -/
def HasValuationSubringCriterion (V : Subring K) : Prop :=
  ∀ x : K, x ∈ V ∨ x⁻¹ ∈ V

/- A principal fractional ideal `xV`, represented as a subset of the field. -/
def principalFractionalSet (V : Subring K) (x : K) : Set K :=
  {z | ∃ a : V, z = (a : K) * x}

/- Total comparability of principal fractional ideals. -/
def PrincipalFractionalIdealsComparable (V : Subring K) : Prop :=
  ∀ x y : K, x ≠ 0 → y ≠ 0 →
    principalFractionalSet V x ⊆ principalFractionalSet V y ∨
      principalFractionalSet V y ⊆ principalFractionalSet V x

theorem principalFractionalSet_le_iff (V : Subring K) {x y : K} (hy : y ≠ 0) :
    principalFractionalSet V x ⊆ principalFractionalSet V y ↔ x / y ∈ V := by
  constructor
  · intro h
    have hmem : x ∈ principalFractionalSet V y := by
      apply h
      exact ⟨1, by simp [principalFractionalSet]⟩
    rcases hmem with ⟨a, ha⟩
    change x = (a : K) * y at ha
    have hxy : x / y = (a : K) := by
      rw [ha]
      field_simp [hy]
    rw [hxy]
    exact a.property
  · intro h z hz
    rcases hz with ⟨a, rfl⟩
    refine ⟨⟨(a : K) * (x / y), V.mul_mem a.property h⟩, ?_⟩
    field_simp [hy]

theorem principalFractionalSet_comparison_iff (V : Subring K) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    principalFractionalSet V x ⊆ principalFractionalSet V y ∨
        principalFractionalSet V y ⊆ principalFractionalSet V x ↔
      x / y ∈ V ∨ y / x ∈ V := by
  rw [principalFractionalSet_le_iff V hy, principalFractionalSet_le_iff V hx]

theorem valuationRingCriterion_tfae (V : Subring K) :
    List.TFAE
      [IsValuationRingSubring V,
        HasValuationSubringCriterion V,
        PrincipalFractionalIdealsComparable V] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · rintro ⟨A, rfl⟩ x
      exact A.mem_or_inv_mem x
    · intro hV
      let A := ValuationSubring.ofSubring V hV
      refine ⟨A, ?_⟩
      rfl
  tfae_have 2 ↔ 3 := by
    constructor
    · intro hV x y hx hy
      apply (principalFractionalSet_comparison_iff V hx hy).2
      rcases hV (x / y) with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa [div_eq_mul_inv] using h)
    · intro hC x
      by_cases hx : x = 0
      · exact Or.inl (by simpa [hx] using V.zero_mem)
      rcases hC x 1 hx one_ne_zero with h | h
      · exact Or.inl (by simpa using
          (principalFractionalSet_le_iff V one_ne_zero).1 h)
      · exact Or.inr (by simpa [one_div] using
          (principalFractionalSet_le_iff V hx).1 h)
  tfae_finish

theorem valuationRingCriterion (V : Subring K) :
    IsValuationRingSubring V ↔ HasValuationSubringCriterion V ∧
      PrincipalFractionalIdealsComparable V := by
  have hT := valuationRingCriterion_tfae V
  have h12 : IsValuationRingSubring V ↔ HasValuationSubringCriterion V :=
    hT.out 0 1
  have h23 : HasValuationSubringCriterion V ↔
      PrincipalFractionalIdealsComparable V := hT.out 1 2
  constructor
  · intro h
    exact ⟨h12.mp h, h23.mp (h12.mp h)⟩
  · rintro ⟨hV, _⟩
    exact h12.mpr hV

/- Reconstruction by quotienting the multiplicative group by the unit group. -/

def criterionValuationSubring (V : Subring K) (hV : HasValuationSubringCriterion V) :
    ValuationSubring K :=
  ValuationSubring.ofSubring V hV

abbrev criterionValueGroup (V : Subring K) (hV : HasValuationSubringCriterion V) :=
  (criterionValuationSubring V hV).ValueGroup

noncomputable def criterionReconstructedValuation (V : Subring K)
    (hV : HasValuationSubringCriterion V) :
    Valuation K (criterionValueGroup V hV) :=
  (criterionValuationSubring V hV).valuation

theorem criterionReconstructedValuation_integer (V : Subring K)
    (hV : HasValuationSubringCriterion V) :
    (criterionReconstructedValuation V hV).integer = V := by
  change (criterionValuationSubring V hV).valuation.integer =
    (criterionValuationSubring V hV).toSubring
  exact ValuationSubring.integer_valuation (criterionValuationSubring V hV)

def criterionUnitSubgroup (V : Subring K) : Subgroup Kˣ :=
  (Units.map V.subtype.toMonoidHom).range

abbrev criterionUnitQuotient (V : Subring K) :=
  Kˣ ⧸ criterionUnitSubgroup V

theorem criterionValueGroup_is_quotient_by_units (V : Subring K)
    (hV : HasValuationSubringCriterion V) :
    Nonempty ((criterionValueGroup V hV)ˣ ≃* criterionUnitQuotient V) := by
  classical
  let A := criterionValuationSubring V hV
  let φ : Kˣ →* (A.ValueGroup)ˣ :=
    Units.map A.valuation.toMonoidWithZeroHom.toMonoidHom
  have hφ : Function.Surjective φ := by
    intro u
    obtain ⟨x, hx⟩ := Quotient.exists_rep (u : A.ValueGroup)
    have hx0 : x ≠ 0 := by
      intro hx0
      apply u.ne_zero
      rw [← hx, hx0]
      rfl
    refine ⟨Units.mk0 x hx0, ?_⟩
    apply Units.ext
    change A.valuation x = (u : A.ValueGroup)
    exact hx
  have hker : φ.ker = criterionUnitSubgroup V := by
    ext a
    constructor
    · intro ha
      have hφa : φ a = 1 := MonoidHom.mem_ker.mp ha
      have hval : A.valuation (a : K) = 1 := by
        have hv := congrArg Units.val hφa
        simpa [φ] using hv
      have haA : (a : K) ∈ A :=
        A.mem_of_valuation_le_one (a : K) hval.le
      have haV : (a : K) ∈ V := by
        apply (ValuationSubring.mem_ofSubring V hV (a : K)).mp
        simpa [A, criterionValuationSubring] using haA
      have hainvval : A.valuation (a⁻¹ : K) = 1 := by
        rw [map_inv₀, hval, inv_one]
      have hainvA : (a⁻¹ : K) ∈ A :=
        A.mem_of_valuation_le_one (a⁻¹ : K) hainvval.le
      have hainvV : (a⁻¹ : K) ∈ V := by
        apply (ValuationSubring.mem_ofSubring V hV (a⁻¹ : K)).mp
        simpa [A, criterionValuationSubring] using hainvA
      let u : Vˣ :=
        { val := ⟨(a : K), haV⟩
          inv := ⟨(a⁻¹ : K), hainvV⟩
          val_inv := by apply Subtype.ext; simp
          inv_val := by apply Subtype.ext; simp }
      change a ∈ (Units.map V.subtype.toMonoidHom).range
      exact ⟨u, by apply Units.ext; rfl⟩
    · intro ha
      change a ∈ (Units.map V.subtype.toMonoidHom).range at ha
      rcases ha with ⟨u, rfl⟩
      have huA : (u : K) ∈ A := by
        apply (ValuationSubring.mem_ofSubring V hV (u : K)).mpr
        exact u.val.property
      have huinv : (u⁻¹ : K) = (u.inv : K) := by
        exact (eq_inv_of_mul_eq_one_left
          (congrArg (fun z : V => (z : K)) u.inv_val)).symm
      have huinvA : (u⁻¹ : K) ∈ A := by
        rw [huinv]
        apply (ValuationSubring.mem_ofSubring V hV (u.inv : K)).mpr
        exact u.inv.property
      let uA : Aˣ :=
        { val := ⟨(u : K), huA⟩
          inv := ⟨(u⁻¹ : K), huinvA⟩
          val_inv := by apply Subtype.ext; simp
          inv_val := by apply Subtype.ext; simp }
      change φ (Units.map V.subtype.toMonoidHom u) = 1
      apply Units.ext
      have huval : A.valuation (u : K) = 1 := by
        simpa [uA] using A.valuation_unit uA
      simpa [φ] using huval
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  exact ⟨e.symm.trans (QuotientGroup.quotientMulEquivOfEq hker)⟩

def criterionComparison (V : Subring K) (hV : HasValuationSubringCriterion V)
    (x y : K) : Prop :=
  x / y ∈ V

theorem criterionComparison_unit_invariant (V : Subring K)
    (hV : HasValuationSubringCriterion V) (x y : K) (a b : Vˣ) :
    criterionComparison V hV
        (((a : V) : K) * x) (((b : V) : K) * y) ↔
      criterionComparison V hV x y := by
  classical
  change (((a : V) : K) * x) / (((b : V) : K) * y) ∈ V ↔ x / y ∈ V
  have ha0 : ((a : V) : K) ≠ 0 := by
    intro h
    apply a.ne_zero
    exact Subtype.ext h
  have hb0 : ((b : V) : K) ≠ 0 := by
    intro h
    apply b.ne_zero
    exact Subtype.ext h
  have habV : ((a : V) : K) / ((b : V) : K) ∈ V := by
    have hmem : (((a : V) * ((b⁻¹ : Vˣ) : V) : V) : K) ∈ V :=
      SetLike.coe_mem _
    change ((a : V) : K) * (((b⁻¹ : Vˣ) : V) : K) ∈ V at hmem
    have hbinv : (((b⁻¹ : Vˣ) : V) : K) * ((b : V) : K) = 1 := by
      exact congrArg (fun z : V => (z : K)) b.inv_val
    rw [eq_inv_of_mul_eq_one_left hbinv] at hmem
    simpa [div_eq_mul_inv] using hmem
  have hbaV : ((b : V) : K) / ((a : V) : K) ∈ V := by
    have hmem : (((b : V) * ((a⁻¹ : Vˣ) : V) : V) : K) ∈ V :=
      SetLike.coe_mem _
    change ((b : V) : K) * (((a⁻¹ : Vˣ) : V) : K) ∈ V at hmem
    have hainv : (((a⁻¹ : Vˣ) : V) : K) * ((a : V) : K) = 1 := by
      exact congrArg (fun z : V => (z : K)) a.inv_val
    rw [eq_inv_of_mul_eq_one_left hainv] at hmem
    simpa [div_eq_mul_inv] using hmem
  constructor
  · intro h
    have hxy : x / y = (((b : V) : K) / ((a : V) : K)) *
        ((((a : V) : K) * x) / (((b : V) : K) * y)) := by
      field_simp [ha0, hb0]
    rw [hxy]
    exact V.mul_mem hbaV h
  · intro h
    have hxy : (((a : V) : K) * x) / (((b : V) : K) * y) =
        (((a : V) : K) / ((b : V) : K)) * (x / y) := by
      field_simp [ha0, hb0]
    rw [hxy]
    exact V.mul_mem habV h

theorem criterionComparison_total (V : Subring K)
    (hV : HasValuationSubringCriterion V) (x y : K) :
    criterionComparison V hV x y ∨ criterionComparison V hV y x := by
  change x / y ∈ V ∨ y / x ∈ V
  rcases hV (x / y) with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa [div_eq_mul_inv] using h)

theorem criterionReconstructedValuation_addition_inequality (V : Subring K)
    (hV : HasValuationSubringCriterion V) (x y : K) :
    criterionReconstructedValuation V hV (x + y) ≤
      max (criterionReconstructedValuation V hV x)
        (criterionReconstructedValuation V hV y) := by
  exact map_add_le_max (criterionReconstructedValuation V hV) x y

theorem criterionNormalizedAddition (V : Subring K)
    (hV : HasValuationSubringCriterion V) {x y : K} (hx : x ≠ 0)
    (hle : criterionReconstructedValuation V hV y ≤
      criterionReconstructedValuation V hV x) :
    (x + y) / x = 1 + y / x ∧
      (x + y) / x ∈ V := by
  constructor
  · field_simp [hx]
  · have hyx : criterionReconstructedValuation V hV (y / x) ≤ 1 := by
      rw [map_div₀, div_le_one₀
        ((criterionReconstructedValuation V hV).pos_iff.mpr hx)]
      exact hle
    have hyxV : y / x ∈ V := by
      change y / x ∈ criterionValuationSubring V hV
      exact (ValuationSubring.valuation_le_one_iff
        (criterionValuationSubring V hV) (y / x)).mp hyx
    rw [show (x + y) / x = 1 + y / x by field_simp [hx]]
    exact V.add_mem V.one_mem hyxV

theorem valuationRing_determines_equivalence
    {Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ₁]
    [LinearOrderedCommGroupWithZero Γ₂]
    (v₁ : Valuation K Γ₁) (v₂ : Valuation K Γ₂)
    (h : v₁.integer = v₂.integer) : v₁.IsEquiv v₂ := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  rw [← v₁.mem_integer_iff x, h, v₂.mem_integer_iff x]

theorem valuationRing_determines_additive_equivalence
    {A₁ A₂ : Type*} [LinearOrderedAddCommGroupWithTop A₁]
    [LinearOrderedAddCommGroupWithTop A₂]
    (v₁ : AddValuation K A₁) (v₂ : AddValuation K A₂)
    (h : additiveValuationRingOf v₁ = additiveValuationRingOf v₂) :
    v₁.IsEquiv v₂ := by
  change (AddValuation.toValuation v₁).IsEquiv (AddValuation.toValuation v₂)
  apply valuationRing_determines_equivalence
  simpa [additiveValuationRingOf] using h

end IntrinsicCriterion

section OrderedIdeals

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

/-! ### 3.3. Ideals are ordered -/

theorem ideals_totally_ordered : @Std.Total (Ideal R) (· ≤ ·) := by
  exact PreValuationRing.iff_ideal_total.mp inferInstance

theorem ideals_comparable_from_principal_ideals (I J : Ideal R) :
    I ≤ J ∨ J ≤ I := by
  exact ideals_totally_ordered.total I J

theorem noncomparable_ideals_choose_crossing_elements (I J : Ideal R)
    (hIJ : ¬ I ≤ J) (hJI : ¬ J ≤ I) :
    ∃ x ∈ I, x ∉ J ∧ ∃ y ∈ J, y ∉ I := by
  have hIJ' : ∃ x, x ∈ I ∧ x ∉ J := by
    by_contra h
    apply hIJ
    intro x hx
    by_contra hxJ
    exact h ⟨x, hx, hxJ⟩
  have hJI' : ∃ y, y ∈ J ∧ y ∉ I := by
    by_contra h
    apply hJI
    intro y hy
    by_contra hyI
    exact h ⟨y, hy, hyI⟩
  exact ⟨hIJ'.choose, hIJ'.choose_spec.1, hIJ'.choose_spec.2,
    hJI'.choose, hJI'.choose_spec.1, hJI'.choose_spec.2⟩

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem principal_ideal_order_reverses_valuation (v : Valuation K Γ)
    (x y : valuationRingOf v) :
    Ideal.span ({x} : Set (valuationRingOf v)) ≤ Ideal.span {y} ↔
      v (x : K) ≤ v (y : K) := by
  rw [Ideal.span_singleton_le_span_singleton]
  exact (Valuation.integer.integers v).le_iff_dvd.symm

theorem valuationRingOf_isBezout (v : Valuation K Γ) :
    IsBezout (valuationRingOf v) := by
  infer_instance

theorem valuationRingOf_finitely_generated_ideal_is_principal (v : Valuation K Γ)
    (I : Ideal (valuationRingOf v)) (hI : I.FG) : I.IsPrincipal := by
  exact IsBezout.isPrincipal_of_FG I hI

theorem valuationRingOf_need_not_be_principal_ideal_ring (v : Valuation K Γ)
    (I : Ideal (valuationRingOf v)) (hI : ¬ I.IsPrincipal) :
    ¬ IsPrincipalIdealRing (valuationRingOf v) := by
  intro hPIR
  letI : IsPrincipalIdealRing (valuationRingOf v) := hPIR
  exact hI (IsPrincipalIdealRing.principal I)

/- Value sets of ideals, in the additive sign convention. -/

variable {A : Type*} [AddCommGroup A] [LinearOrder A]
  [IsOrderedAddMonoid A]

def additiveValueSet (v : AddValuation K (WithTop A))
    (I : Ideal (additiveValuationRingOf v)) : Set A :=
  {γ | ∃ x : additiveValuationRingOf v,
      x ∈ I ∧ x ≠ 0 ∧ v (x : K) = (γ : WithTop A)}

def hasLeastValue (S : Set A) : Prop :=
  ∃ γ, γ ∈ S ∧ ∀ δ, δ ∈ S → γ ≤ δ

theorem additiveValueSet_nonnegative (v : AddValuation K (WithTop A))
    (I : Ideal (additiveValuationRingOf v)) :
    additiveValueSet v I ⊆ Set.Ici 0 := by
  rintro γ ⟨x, hxI, hx0, hv⟩
  have hnon : 0 ≤ v (x : K) :=
    (mem_additiveValuationRingOf_iff v (x : K)).1 x.property
  rw [hv] at hnon
  simpa using hnon

theorem additiveValueSet_upward_closed_on_realized_values
    (v : AddValuation K (WithTop A)) (I : Ideal (additiveValuationRingOf v))
    {γ δ : A} (hγ : γ ∈ additiveValueSet v I)
    (hδ : ∃ z : K, z ≠ 0 ∧ v z = (δ : WithTop A)) (hγδ : γ ≤ δ) :
    δ ∈ additiveValueSet v I := by
  rcases hγ with ⟨x, hxI, hx0, hxv⟩
  rcases hδ with ⟨z, hz0, hzv⟩
  have hzx : 0 ≤ v (z / (x : K)) := by
    rw [AddValuation.map_div, hzv, hxv,
      ← WithTop.LinearOrderedAddCommGroup.coe_sub]
    norm_cast
    exact sub_nonneg.mpr hγδ
  let c : additiveValuationRingOf v :=
    ⟨z / (x : K), (mem_additiveValuationRingOf_iff v _).2 hzx⟩
  have hγ0 : 0 ≤ γ := by
    have hxnon : 0 ≤ v (x : K) :=
      (mem_additiveValuationRingOf_iff v (x : K)).1 x.property
    rw [hxv] at hxnon
    exact WithTop.coe_nonneg.mp hxnon
  have hδ0 : 0 ≤ δ := hγ0.trans hγδ
  let z' : additiveValuationRingOf v :=
    ⟨z, (mem_additiveValuationRingOf_iff v _).2 (by
      rw [hzv]
      exact WithTop.coe_nonneg.mpr hδ0)⟩
  have hz'0 : z' ≠ 0 := by
    intro h
    apply hz0
    exact congrArg Subtype.val h
  refine ⟨z', ?_, hz'0, hzv⟩
  have hmul := I.mul_mem_left c hxI
  have hcx : c * x = z' := by
    apply Subtype.ext
    change (z / (x : K)) * (x : K) = z
    field_simp [hx0]
  rw [← hcx]
  exact hmul

/- An upward-closed, nonnegative value cut and the ideal it determines. -/

structure AdditiveValueCut (A : Type*) [AddCommGroup A] [LinearOrder A]
    [IsOrderedAddMonoid A] where
  carrier : Set A
  nonnegative : ∀ {γ}, γ ∈ carrier → 0 ≤ γ
  upward : ∀ {γ δ}, γ ∈ carrier → γ ≤ δ → δ ∈ carrier
  add_nonnegative : ∀ {γ δ}, γ ∈ carrier → 0 ≤ δ → γ + δ ∈ carrier

noncomputable def idealOfValueCut (v : AddValuation K (WithTop A))
    (S : AdditiveValueCut A)
    (hreal : ∀ {γ}, γ ∈ S.carrier → ∃ x : K, x ≠ 0 ∧
      v x = (γ : WithTop A)) : Ideal (additiveValuationRingOf v) :=
  { carrier := {x : additiveValuationRingOf v | x = 0 ∨
        ∃ γ, γ ∈ S.carrier ∧ v (x : K) = (γ : WithTop A)}
    zero_mem' := by
      exact Or.inl rfl
    add_mem' := by
      intro a b ha hb
      change a = 0 ∨ ∃ γ, γ ∈ S.carrier ∧ v (a : K) = (γ : WithTop A) at ha
      change b = 0 ∨ ∃ γ, γ ∈ S.carrier ∧ v (b : K) = (γ : WithTop A) at hb
      rcases ha with rfl | ⟨γ, hγ, hav⟩
      · simpa using hb
      rcases hb with rfl | ⟨δ, hδ, hbv⟩
      · simpa using Or.inr ⟨γ, hγ, hav⟩
      by_cases hab : a + b = 0
      · exact Or.inl hab
      right
      have habK : ((a + b : additiveValuationRingOf v) : K) ≠ 0 := by
        intro hzero
        apply hab
        exact Subtype.ext hzero
      obtain ⟨ε, hε⟩ := WithTop.ne_top_iff_exists.mp
        (v.ne_top_iff.mpr habK)
      rcases AddValuation.map_add' v a b with h | h
      · have hγε : γ ≤ ε := by
          apply WithTop.coe_le_coe.mp
          rw [← hav, hε]
          exact h
        exact ⟨ε, S.upward hγ hγε, hε.symm⟩
      · have hδε : δ ≤ ε := by
          apply WithTop.coe_le_coe.mp
          rw [← hbv, hε]
          exact h
        exact ⟨ε, S.upward hδ hδε, hε.symm⟩
    smul_mem' := by
      intro c a ha
      change a = 0 ∨ ∃ γ, γ ∈ S.carrier ∧ v (a : K) = (γ : WithTop A) at ha
      change c * a = 0 ∨ ∃ γ, γ ∈ S.carrier ∧
        v ((c * a : additiveValuationRingOf v) : K) = (γ : WithTop A)
      rcases ha with rfl | ⟨γ, hγ, hav⟩
      · simp
      by_cases hc : c = 0
      · simp [hc]
      have hcK : (c : K) ≠ 0 := by
        intro hzero
        apply hc
        exact Subtype.ext hzero
      obtain ⟨δ, hδ⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr hcK)
      have hc0 : 0 ≤ δ := by
        have hcv : 0 ≤ v (c : K) := (mem_additiveValuationRingOf_iff v (c : K)).1 c.property
        rw [← hδ] at hcv
        exact WithTop.coe_nonneg.mp hcv
      right
      refine ⟨γ + δ, S.add_nonnegative hγ hc0, ?_⟩
      change v ((c : K) * (a : K)) = (↑(γ + δ) : WithTop A)
      rw [AddValuation.map_mul, ← hδ, hav, ← WithTop.coe_add]
      simp [add_comm]
  }

theorem idealOfValueCut_mem_iff (v : AddValuation K (WithTop A))
    (S : AdditiveValueCut A)
    (hreal : ∀ {γ}, γ ∈ S.carrier → ∃ x : K, x ≠ 0 ∧
      v x = (γ : WithTop A)) (x : additiveValuationRingOf v) :
    x ∈ idealOfValueCut v S hreal ↔
      x = 0 ∨ ∃ γ, γ ∈ S.carrier ∧ v (x : K) = (γ : WithTop A) := by
  rfl

theorem idealOfValueCut_valueSet (v : AddValuation K (WithTop A))
    (S : AdditiveValueCut A)
    (hreal : ∀ {γ}, γ ∈ S.carrier → ∃ x : K, x ≠ 0 ∧
      v x = (γ : WithTop A)) :
    additiveValueSet v (idealOfValueCut v S hreal) = S.carrier := by
  classical
  ext γ
  constructor
  · rintro ⟨x, hxI, hx0, hxv⟩
    rcases (idealOfValueCut_mem_iff v S hreal x).1 hxI with hzero | ⟨δ, hδ, hxδ⟩
    · exact False.elim (hx0 hzero)
    · have hγδ : γ = δ := WithTop.coe_eq_coe.mp (hxv.symm.trans hxδ)
      simpa [hγδ] using hδ
  · intro hγ
    rcases hreal hγ with ⟨z, hz0, hzv⟩
    have hzV : 0 ≤ v z := by
      rw [hzv]
      exact WithTop.coe_nonneg.mpr (S.nonnegative hγ)
    let x : additiveValuationRingOf v := ⟨z, hzV⟩
    refine ⟨x, ?_, ?_, hzv⟩
    · exact (idealOfValueCut_mem_iff v S hreal x).2
        (Or.inr ⟨γ, hγ, hzv⟩)
    · intro hx
      apply hz0
      exact congrArg Subtype.val hx

theorem principal_additiveValueSet_has_least
    (v : AddValuation K (WithTop A)) (x : additiveValuationRingOf v)
    (hx : x ≠ 0) :
    hasLeastValue (additiveValueSet v (Ideal.span ({x} : Set (additiveValuationRingOf v)))) := by
  classical
  have hxK : (x : K) ≠ 0 := by
    intro h
    apply hx
    exact Subtype.ext h
  obtain ⟨γ, hγ⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr hxK)
  refine ⟨γ, ?_, ?_⟩
  · exact ⟨x, Ideal.mem_span_singleton.mpr ⟨1, by simp⟩, hx, hγ.symm⟩
  · intro δ hδ
    rcases hδ with ⟨z, hzI, hz0, hzv⟩
    rcases Ideal.mem_span_singleton'.mp hzI with ⟨c, hcz⟩
    have hczK : (c : K) * (x : K) = (z : K) :=
      congrArg (fun q : additiveValuationRingOf v => (q : K)) hcz
    have hcv : 0 ≤ v (c : K) :=
      (mem_additiveValuationRingOf_iff v (c : K)).1 c.property
    have hvle : v (x : K) ≤ v (z : K) := by
      rw [← hczK, AddValuation.map_mul]
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hcv (v (x : K))
    rw [← hγ, hzv] at hvle
    exact WithTop.coe_le_coe.mp hvle

theorem valueCut_without_least_gives_nonprincipal_ideal
    (v : AddValuation K (WithTop A)) (S : AdditiveValueCut A)
    (hreal : ∀ {γ}, γ ∈ S.carrier → ∃ x : K, x ≠ 0 ∧
      v x = (γ : WithTop A)) (hne : S.carrier.Nonempty)
    (hleast : ¬ hasLeastValue S.carrier) :
    ¬ (idealOfValueCut v S hreal).IsPrincipal := by
  classical
  intro hP
  rcases hP with ⟨x, hxI⟩
  have hx0 : x ≠ 0 := by
    intro hx
    obtain ⟨γ, hγ⟩ := hne
    have hγ' : γ ∈ additiveValueSet v (idealOfValueCut v S hreal) := by
      rw [idealOfValueCut_valueSet v S hreal]
      exact hγ
    rcases hγ' with ⟨z, hzI, hz0, _⟩
    rw [hxI, hx] at hzI
    exact hz0 (by simpa using hzI)
  obtain ⟨γ, hγ, hγleast⟩ :=
    principal_additiveValueSet_has_least v x hx0
  apply hleast
  refine ⟨γ, ?_, ?_⟩
  · rw [← idealOfValueCut_valueSet v S hreal]
    rw [hxI]
    exact hγ
  · intro δ hδ
    apply hγleast
    have hδI : δ ∈ additiveValueSet v (idealOfValueCut v S hreal) := by
      rw [idealOfValueCut_valueSet v S hreal]
      exact hδ
    simpa only [hxI] using hδI

theorem integer_upward_closed_nonnegative_set_has_least (S : Set ℤ)
    (hne : S.Nonempty) (hnonneg : S ⊆ Set.Ici 0)
    (hup : ∀ {a b : ℤ}, a ∈ S → a ≤ b → b ∈ S) :
    hasLeastValue S := by
  classical
  rcases Int.exists_least_of_bdd
      (P := fun z : ℤ => z ∈ S)
      ⟨0, fun z hz => hnonneg hz⟩ hne with ⟨lb, hlb, hleast⟩
  exact ⟨lb, hlb, hleast⟩
theorem discrete_additive_valuation_nonzero_ideal_is_principal
    (v : AddValuation K (WithTop ℤ)) (I : Ideal (additiveValuationRingOf v))
    (hI : I ≠ ⊥) :
    ∃ x : additiveValuationRingOf v, x ≠ 0 ∧
      I = Ideal.span ({x} : Set (additiveValuationRingOf v)) := by
  classical
  have hnonzero : ∃ x : additiveValuationRingOf v, x ∈ I ∧ x ≠ 0 := by
    by_contra h
    apply hI
    ext z
    constructor
    · intro hz
      have hz0 : z = 0 := by
        by_contra hz0
        exact h ⟨z, hz, hz0⟩
      simpa [hz0]
    · intro hz
      have hz0 : z = 0 := by simpa using hz
      simpa [hz0]
  have hne : (additiveValueSet v I).Nonempty := by
    obtain ⟨x, hxI, hx0⟩ := hnonzero
    obtain ⟨γ, hγ⟩ := WithTop.ne_top_iff_exists.mp
      (v.ne_top_iff.mpr (by
        intro hxK
        apply hx0
        exact Subtype.ext hxK))
    exact ⟨γ, ⟨x, hxI, hx0, hγ.symm⟩⟩
  have hnonneg : additiveValueSet v I ⊆ Set.Ici 0 := by
    intro γ hγ
    rcases hγ with ⟨x, hxI, hx0, hxv⟩
    change 0 ≤ γ
    apply WithTop.coe_nonneg.mp
    rw [← hxv]
    exact (mem_additiveValuationRingOf_iff v (x : K)).1 x.property
  obtain ⟨γ, hγ, hγleast⟩ := Int.exists_least_of_bdd
      (P := fun z : ℤ => z ∈ additiveValueSet v I)
      ⟨0, fun z hz => hnonneg hz⟩ hne
  rcases hγ with ⟨x, hxI, hx0, hxv⟩
  refine ⟨x, hx0, ?_⟩
  apply le_antisymm
  · intro z hzI
    by_cases hz0 : z = 0
    · simpa [hz0]
    obtain ⟨δ, hδ⟩ := WithTop.ne_top_iff_exists.mp
      (v.ne_top_iff.mpr (by
        intro hzK
        apply hz0
        exact Subtype.ext hzK))
    have hδmem : δ ∈ additiveValueSet v I := ⟨z, hzI, hz0, hδ.symm⟩
    have hγδ : γ ≤ δ := hγleast δ hδmem
    have hxK : (x : K) ≠ 0 := by
      intro hxK
      apply hx0
      exact Subtype.ext hxK
    have hdiv : 0 ≤ v ((z : K) / (x : K)) := by
      rw [AddValuation.map_div, ← hδ, hxv,
        ← WithTop.LinearOrderedAddCommGroup.coe_sub]
      norm_cast
      exact sub_nonneg.mpr hγδ
    let c : additiveValuationRingOf v :=
      ⟨(z : K) / (x : K), hdiv⟩
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨c, ?_⟩
    apply Subtype.ext
    change ((z : K) / (x : K)) * (x : K) = (z : K)
    exact div_mul_cancel₀ _ hxK
  · exact I.span_singleton_le_iff_mem.mpr hxI

def strictUpperValueCut (α : A) (hα : 0 ≤ α) : AdditiveValueCut A :=
  { carrier := {γ | α < γ}
    nonnegative := by
      intro γ hγ
      exact hα.trans hγ.le
    upward := by
      intro γ δ hγ hγδ
      exact lt_of_lt_of_le hγ hγδ
    add_nonnegative := by
      intro γ δ hγ hδ
      exact lt_of_lt_of_le hγ (le_add_of_nonneg_right hδ) }
theorem dense_strict_cut_has_no_least {A : Type*} [LinearOrder A] [DenselyOrdered A]
    (α : A) (hne : ({γ : A | α < γ}).Nonempty) :
    ¬ hasLeastValue {γ : A | α < γ} := by
  rintro ⟨γ, hγ, hleast⟩
  obtain ⟨δ, hαδ, hδγ⟩ := exists_between hγ
  exact (not_lt_of_ge (hleast δ hαδ)) hδγ

theorem strictUpperRationalValueCut_is_nonprincipal
    (v : AddValuation K (WithTop ℚ)) (α : ℚ) (hα : 0 ≤ α)
    (hne : ({γ : ℚ | α < γ}).Nonempty)
    (hreal : ∀ {γ}, γ ∈ (strictUpperValueCut α hα).carrier → ∃ x : K, x ≠ 0 ∧
      v x = (γ : WithTop ℚ)) :
    ¬ (idealOfValueCut v (strictUpperValueCut α hα) hreal).IsPrincipal := by
  classical
  apply valueCut_without_least_gives_nonprincipal_ideal v
    (strictUpperValueCut α hα) hreal hne
  exact dense_strict_cut_has_no_least α hne
theorem rational_dense_value_cut_is_nonprincipal
    (v : AddValuation K (WithTop ℚ)) (S : AdditiveValueCut ℚ)
    (hreal : ∀ {γ}, γ ∈ S.carrier → ∃ x : K, x ≠ 0 ∧
      v x = (γ : WithTop ℚ)) (hne : S.carrier.Nonempty)
    (hleast : ¬ hasLeastValue S.carrier) :
    ¬ (idealOfValueCut v S hreal).IsPrincipal := by
  classical
  exact valueCut_without_least_gives_nonprincipal_ideal v S hreal hne hleast

end OrderedIdeals

section PrimeIdealsAndRank

variable {K : Type*} [Field K]

/-! ### 3.4. Prime ideals and rank -/

/-- A chapter-local interface for a convex additive subgroup of an ordered group. -/
structure ChapterConvexAddSubgroup (G : Type*) [AddCommGroup G] [LinearOrder G] where
  carrier : AddSubgroup G
  convex : ∀ {a b c : G}, a ≤ b → b ≤ c → a ∈ carrier → c ∈ carrier → b ∈ carrier

noncomputable def valuationPrimeSpectrum_orderEquiv (A : ValuationSubring K) :
    (PrimeSpectrum A)ᵒᵈ ≃o {S : ValuationSubring K // A ≤ S} :=
  ValuationSubring.primeSpectrumOrderEquiv A

noncomputable def valuationPrimeSpectrum_equiv_coarsenings (A : ValuationSubring K) :
    PrimeSpectrum A ≃ {S : ValuationSubring K // A ≤ S} :=
  ValuationSubring.primeSpectrumEquiv A

theorem convex_scales_correspond_to_prime_ideals (A : ValuationSubring K) :
    Nonempty ((PrimeSpectrum A)ᵒᵈ ≃o {S : ValuationSubring K // A ≤ S}) :=
  ⟨valuationPrimeSpectrum_orderEquiv A⟩

/- Rank one is the nontrivial Archimedean case. -/

def IsRankOneValuation {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) : Prop :=
  Nonempty (Valuation.RankOne v)

theorem isRankOneValuation_iff_archimedean_valueGroup
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [v.IsNontrivial] :
    IsRankOneValuation v ↔
      MulArchimedean (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v)) := by
  change Nonempty (Valuation.RankOne v) ↔ _
  exact Valuation.nonempty_rankOne_iff_mulArchimedean

private theorem rankOne_prime_bot_or_maximal
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (hrank : IsRankOneValuation v)
    (P : Ideal (valuationRingOf v)) (hP : P.IsPrime) :
    P = ⊥ ∨ P = maximalIdealOf v := by
  classical
  letI : P.IsPrime := hP
  have harch : MulArchimedean
      (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v)) := by
    letI : v.IsNontrivial := by
      exact hrank.some.toIsNontrivial
    exact (isRankOneValuation_iff_archimedean_valueGroup v).mp hrank
  letI : MulArchimedean
      (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v)) := harch
  by_cases hP0 : P = ⊥
  · exact Or.inl hP0
  right
  apply le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime P)
  have hnonzero : ∃ x : valuationRingOf v, x ∈ P ∧ x ≠ 0 := by
    by_contra h
    apply hP0
    apply le_antisymm
    · intro z hz
      have hz0 : z = 0 := by
        by_contra hz0
        exact h ⟨z, hz, hz0⟩
      simpa [hz0]
    · exact bot_le
  obtain ⟨x, hxP, hx0⟩ := hnonzero
  intro y hymax
  by_cases hy0 : y = 0
  · simpa [hy0] using P.zero_mem
  have hylt : v.restrict (y : K) < 1 := by
    rw [Valuation.restrict_lt_one_iff]
    exact (mem_maximalIdealOf_iff v y).mp hymax
  have hxK : (x : K) ≠ 0 := by
    intro hzero
    apply hx0
    exact Subtype.ext hzero
  have hxpos : 0 < v.restrict (x : K) := by
    rw [Valuation.restrict_pos_iff]
    exact v.pos_iff.mpr hxK
  have hypos : 0 < v.restrict (y : K) := by
    rw [Valuation.restrict_pos_iff]
    exact v.pos_iff.mpr (by
      exact fun hzero => hy0 (Subtype.ext hzero))
  have hyinv : 1 < (v.restrict (y : K))⁻¹ :=
    (one_lt_inv₀ hypos).2 hylt
  obtain ⟨n, hn⟩ := harch.arch (v.restrict (x : K))⁻¹ hyinv
  have hpowR : (v.restrict (y : K)) ^ n ≤ v.restrict (x : K) := by
    apply (inv_le_inv₀ hxpos (pow_pos hypos n)).mp
    simpa [inv_pow] using hn
  have hpow : v ((y : K) ^ n) ≤ v (x : K) := by
    rw [← Valuation.restrict_le_iff]
    simpa [v.map_pow] using hpowR
  have hcval : v ((y : K) ^ n / (x : K)) ≤ 1 := by
    rw [v.map_div, div_le_iff₀ (v.pos_iff.mpr hxK)]
    simpa using hpow
  let c : valuationRingOf v :=
    ⟨(y : K) ^ n / (x : K), (mem_valuationRingOf_iff v _).2 hcval⟩
  have hcy : (c : K) * (x : K) = (y : K) ^ n := by
    dsimp [c]
    field_simp [hxK]
  have hpowP : y ^ n ∈ P := by
    have hmul : c * x ∈ P := P.mul_mem_left c hxP
    convert hmul using 1
    apply Subtype.ext
    exact hcy.symm
  exact hP.mem_of_pow_mem n hpowP

private theorem nonarch_valuation_has_intermediate_prime
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ)
    (hnotarch : ¬ MulArchimedean
      (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v))) :
    ∃ P : Ideal (valuationRingOf v), P.IsPrime ∧ P ≠ ⊥ ∧
      P ≠ maximalIdealOf v := by
  classical
  let G₀ := MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v)
  have hforall : ¬ (∀ α : G₀, ∀ β : G₀, 1 < β →
      ∃ n : ℕ, α ≤ β ^ n) := by
    intro h
    apply hnotarch
    exact ⟨by
      intro α β hβ
      exact h α β hβ⟩
  obtain ⟨α, hα⟩ := not_forall.mp hforall
  obtain ⟨β, hβnot⟩ := not_forall.mp hα
  obtain ⟨hβ, hbad⟩ := Classical.not_imp.mp hβnot
  have hα1 : 1 < α := by
    have hbad0 : ¬ α ≤ β ^ 0 := by
      intro h
      exact hbad ⟨0, h⟩
    simpa using (lt_of_not_ge hbad0)
  have hαpos : 0 < α := zero_lt_one.trans hα1
  have hβpos : 0 < β := zero_lt_one.trans hβ
  have hmq : ∀ n : ℕ, α⁻¹ < (β⁻¹) ^ n := by
    intro n
    have hbadn : ¬ α ≤ β ^ n := by
      intro h
      exact hbad ⟨n, h⟩
    have hba : β ^ n < α := lt_of_not_ge hbadn
    have hinv : α⁻¹ < (β ^ n)⁻¹ :=
      (inv_lt_inv₀ hαpos (pow_pos hβpos n)).2 hba
    simpa [inv_pow] using hinv
  have hqpos : 0 < β⁻¹ := inv_pos.mpr hβpos
  have hq_lt : β⁻¹ < 1 := inv_lt_one_of_one_lt₀ hβ
  let f := MonoidWithZeroHom.ofClass v
  obtain ⟨xm, hxm⟩ :=
    MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective f (α⁻¹)
  obtain ⟨xq, hxq⟩ :=
    MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective f (β⁻¹)
  have hxmR : v.restrict xm = α⁻¹ := by
    simpa [Valuation.restrict_def, f] using hxm
  have hxqR : v.restrict xq = β⁻¹ := by
    simpa [Valuation.restrict_def, f] using hxq
  have hxm_lt : v xm < 1 := by
    rw [← Valuation.restrict_lt_one_iff, hxmR]
    exact inv_lt_one_of_one_lt₀ hα1
  have hxq_lt : v xq < 1 := by
    rw [← Valuation.restrict_lt_one_iff, hxqR]
    exact hq_lt
  let xmA : valuationRingOf v :=
    ⟨xm, (mem_valuationRingOf_iff v xm).2 hxm_lt.le⟩
  let xqA : valuationRingOf v :=
    ⟨xq, (mem_valuationRingOf_iff v xq).2 hxq_lt.le⟩
  let P : Ideal (valuationRingOf v) :=
    { carrier := {x | ∀ n : ℕ, v.restrict (x : K) < (β⁻¹) ^ n}
      zero_mem' := by
        intro n
        simpa using (pow_pos hqpos n)
      add_mem' := by
        intro x y hx hy n
        change v.restrict ((x : K) + (y : K)) < (β⁻¹) ^ n
        exact v.restrict.map_add_lt (hx n) (hy n)
      smul_mem' := by
        intro r x hx
        change ∀ n : ℕ, v.restrict ((r : K) * (x : K)) < (β⁻¹) ^ n
        intro n
        rw [v.restrict.map_mul]
        have hr : v.restrict (r : K) ≤ 1 := by
          rw [Valuation.restrict_le_one_iff]
          exact (mem_valuationRingOf_iff v (r : K)).mp r.property
        exact (mul_le_of_le_one_left' hr).trans_lt (hx n) }
  have hxm_mem : xmA ∈ P := by
    change ∀ n : ℕ, v.restrict xm < (β⁻¹) ^ n
    rw [hxmR]
    exact hmq
  have hxm_ne : xmA ≠ 0 := by
    intro hzero
    have hz' : v.restrict (xmA : K) = v.restrict (0 : K) :=
      congrArg (fun z : valuationRingOf v => v.restrict (z : K)) hzero
    have hz : v.restrict xm = 0 := by
      simpa [xmA] using hz'
    rw [hxmR] at hz
    exact (inv_ne_zero hαpos.ne') hz
  have hxq_not_mem : xqA ∉ P := by
    intro hmem
    change ∀ n : ℕ, v.restrict xq < (β⁻¹) ^ n at hmem
    have hone := hmem 1
    rw [hxqR, pow_one] at hone
    exact (lt_irrefl _ hone)
  have hP_ne_top : P ≠ ⊤ := by
    intro htop
    apply hxq_not_mem
    rw [htop]
    trivial
  have hP_prime : P.IsPrime := by
    refine ⟨hP_ne_top, ?_⟩
    intro x y hxy
    by_cases hx : x ∈ P
    · exact Or.inl hx
    by_cases hy : y ∈ P
    · exact Or.inr hy
    exfalso
    change ¬ (∀ n : ℕ, v.restrict (x : K) < (β⁻¹) ^ n) at hx
    change ¬ (∀ n : ℕ, v.restrict (y : K) < (β⁻¹) ^ n) at hy
    obtain ⟨m, hm⟩ := not_forall.mp hx
    obtain ⟨n, hn⟩ := not_forall.mp hy
    have hm' : (β⁻¹) ^ m ≤ v.restrict (x : K) := le_of_not_gt hm
    have hn' : (β⁻¹) ^ n ≤ v.restrict (y : K) := le_of_not_gt hn
    have hlow : (β⁻¹) ^ (m + n) ≤
        v.restrict (x : K) * v.restrict (y : K) := by
      rw [pow_add]
      exact mul_le_mul_of_nonneg hm' hn'
        (pow_pos hqpos m).le ((pow_pos hqpos n).le.trans hn')
    change ∀ n : ℕ, v.restrict ((x * y : valuationRingOf v) : K) <
      (β⁻¹) ^ n at hxy
    have hxy' := hxy (m + n)
    have hxy'' : v.restrict (x : K) * v.restrict (y : K) <
        (β⁻¹) ^ (m + n) := by
      simpa [v.restrict.map_mul] using hxy'
    exact (not_lt_of_ge hlow) hxy''
  have hP_le_max : P ≤ maximalIdealOf v := by
    intro z hz
    apply (mem_maximalIdealOf_iff v z).2
    change ∀ n : ℕ, v.restrict (z : K) < (β⁻¹) ^ n at hz
    have hz0 := hz 0
    exact (Valuation.restrict_lt_one_iff (v := v)).mp (by simpa using hz0)
  have hxq_max : xqA ∈ maximalIdealOf v :=
    (mem_maximalIdealOf_iff v xqA).2 hxq_lt
  have hP_ne_max : P ≠ maximalIdealOf v := by
    intro heq
    apply hxq_not_mem
    rw [heq]
    exact hxq_max
  have hP_ne_bot : P ≠ ⊥ := by
    intro hbot
    have hzero : xmA ∈ (⊥ : Ideal (valuationRingOf v)) := by
      rw [← hbot]
      exact hxm_mem
    have : xmA = 0 := by simpa using hzero
    exact hxm_ne this
  exact ⟨P, hP_prime, hP_ne_bot, hP_ne_max⟩


 theorem valuationRing_rankOne_iff_krullDim_one
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (hnontrivial : v.IsNontrivial) :
    IsRankOneValuation v ↔ ringKrullDim (valuationRingOf v) = 1 := by
  classical
  letI : v.IsNontrivial := hnontrivial
  constructor
  · intro hrank
    have hradical_of_nonzero_proper : ∀ (I : Ideal (valuationRingOf v)),
        I ≠ ⊥ → I ≠ ⊤ → Ideal.radical I = maximalIdealOf v := by
      intro I hI0 hItop
      have hle : Ideal.radical I ≤ maximalIdealOf v := by
        apply (Ideal.IsPrime.radical_le_iff
          (IsLocalRing.maximalIdeal.isMaximal (valuationRingOf v)).isPrime).2
        exact IsLocalRing.le_maximalIdeal hItop
      have hge : maximalIdealOf v ≤ Ideal.radical I := by
        rw [Ideal.radical_eq_sInf]
        refine le_sInf (fun J hJ => ?_)
        rcases rankOne_prime_bot_or_maximal v hrank J hJ.2 with hbot | hmax
        · exfalso
          apply hI0
          apply le_antisymm
          · simpa [hbot] using hJ.1
          · exact bot_le
        · simpa [hmax]
      exact le_antisymm hle hge
    apply (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain).2
    constructor
    · intro hfield
      letI : IsField (valuationRingOf v) := hfield
      have hbot : maximalIdealOf v = ⊥ :=
        (IsLocalRing.isField_iff_maximalIdeal_eq).mp hfield
      obtain ⟨z, hz0, hz1⟩ := hnontrivial.exists_val_nontrivial
      obtain hz | hz := Valuation.val_le_one_or_val_inv_le_one v z
      · have hzlt : v z < 1 := lt_of_le_of_ne hz hz1
        let hzA : valuationRingOf v :=
          ⟨z, (mem_valuationRingOf_iff v z).2 hz⟩
        have hzm : hzA ∈ maximalIdealOf v :=
          (mem_maximalIdealOf_iff v hzA).2 (by simpa [hzA] using hzlt)
        have hzbot : hzA ∈ (⊥ : Ideal (valuationRingOf v)) := by
          rw [← hbot]
          exact hzm
        have hzero : hzA = 0 := by simpa using hzbot
        have hzeroK : (hzA : K) = 0 := congrArg Subtype.val hzero
        dsimp [hzA] at hzeroK
        exact hz0 (by rw [hzeroK, map_zero])
      · have hz1' : v z⁻¹ ≠ 1 := by
          intro h
          apply hz1
          have hinv : (v z)⁻¹ = 1 := by simpa [v.map_inv] using h
          exact inv_eq_one.mp hinv
        have hzlt : v z⁻¹ < 1 := lt_of_le_of_ne hz hz1'
        let hzA : valuationRingOf v :=
          ⟨z⁻¹, (mem_valuationRingOf_iff v z⁻¹).2 hz⟩
        have hzm : hzA ∈ maximalIdealOf v :=
          (mem_maximalIdealOf_iff v hzA).2 (by simpa [hzA] using hzlt)
        have hzbot : hzA ∈ (⊥ : Ideal (valuationRingOf v)) := by
          rw [← hbot]
          exact hzm
        have hzero : hzA = 0 := by simpa using hzbot
        have hzeroK : (hzA : K) = 0 := congrArg Subtype.val hzero
        dsimp [hzA] at hzeroK
        have hzzero : z = 0 := inv_eq_zero.mp hzeroK
        exact hz0 (by rw [hzzero, map_zero])
    · intro x hx
      have hradical_span :
          maximalIdealOf v ≤ Ideal.radical (Ideal.span ({x} : Set (valuationRingOf v))) := by
        by_cases hxM : x ∈ maximalIdealOf v
        · have hspan0 : Ideal.span ({x} : Set (valuationRingOf v)) ≠ ⊥ := by
            intro hzero
            apply hx
            have hxbot : x ∈ (⊥ : Ideal (valuationRingOf v)) := by
              rw [← hzero]
              exact Ideal.subset_span (by simp)
            simpa using hxbot
          have hspanTop : Ideal.span ({x} : Set (valuationRingOf v)) ≠ ⊤ := by
            intro htop
            have hunit : IsUnit x := Ideal.span_singleton_eq_top.mp htop
            have hxnot : x ∉ maximalIdealOf v := by
              intro hxmax
              have hxlt := (mem_maximalIdealOf_iff v x).mp hxmax
              have hxeq := (valuationRingOf_isUnit_iff v x).mp hunit
              exact (ne_of_gt hxlt) hxeq.symm
            exact hxnot hxM
          rw [hradical_of_nonzero_proper _ hspan0 hspanTop]
        · have hunit : IsUnit x := by
            apply (valuationRingOf_isUnit_iff v x).2
            apply le_antisymm ((mem_valuationRingOf_iff v (x : K)).mp x.property)
            apply le_of_not_gt
            intro hxlt
            exact hxM ((mem_maximalIdealOf_iff v x).2 hxlt)
          have htop : Ideal.span ({x} : Set (valuationRingOf v)) = ⊤ :=
            Ideal.span_singleton_eq_top.mpr hunit
          rw [htop, Ideal.radical_top]
          exact le_top
      exact hradical_span
  · intro hdim
    have harch : MulArchimedean
        (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v)) := by
      by_contra hnotarch
      obtain ⟨P, hP, hP0, hPmax⟩ :=
        nonarch_valuation_has_intermediate_prime v hnotarch
      letI : Ring.KrullDimLE 1 (valuationRingOf v) := by
        apply Ring.krullDimLE_iff.mpr
        simpa [hdim]
      have hPm : P.IsMaximal := hP.isMaximal_of_ne_bot hP0
      have hPeq : P = maximalIdealOf v :=
        (maximalIdealOf_unique v P).mp hPm
      exact hPmax hPeq
    exact (isRankOneValuation_iff_archimedean_valueGroup v).2 harch

theorem rankOne_valuationRing_only_prime_ideals
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (hrank : IsRankOneValuation v)
    (hnontrivial : v.IsNontrivial) (P : Ideal (valuationRingOf v))
    (hP : P.IsPrime) :
    P = ⊥ ∨ P = maximalIdealOf v := by
  exact rankOne_prime_bot_or_maximal v hrank P hP

theorem rankOne_nonzero_proper_ideal_radical
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (hrank : IsRankOneValuation v)
    (hnontrivial : v.IsNontrivial) (I : Ideal (valuationRingOf v))
    (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤) :
    Ideal.radical I = maximalIdealOf v := by
  classical
  letI : v.IsNontrivial := hnontrivial
  have hle : Ideal.radical I ≤ maximalIdealOf v := by
    apply (Ideal.IsPrime.radical_le_iff
      (IsLocalRing.maximalIdeal.isMaximal (valuationRingOf v)).isPrime).2
    exact IsLocalRing.le_maximalIdeal hItop
  have hge : maximalIdealOf v ≤ Ideal.radical I := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf (fun J hJ => ?_)
    rcases rankOne_prime_bot_or_maximal v hrank J hJ.2 with hbot | hmax
    · exfalso
      apply hI0
      apply le_antisymm
      · simpa [hbot] using hJ.1
      · exact bot_le
    · simpa [hmax]
  exact le_antisymm hle hge

theorem rankOne_power_divisibility
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (hrank : IsRankOneValuation v)
    (a b : valuationRingOf v) (ha : a ≠ 0) (hb : b ≠ 0)
    (ha_m : a ∈ maximalIdealOf v) (hb_m : b ∈ maximalIdealOf v) :
    ∃ n : ℕ, v ((a : K) ^ n) ≤ v (b : K) ∧
      a ^ n ∈ Ideal.span ({b} : Set (valuationRingOf v)) := by
  classical
  letI : v.IsNontrivial := by
    exact hrank.some.toIsNontrivial
  have harch : MulArchimedean
      (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v)) := by
    exact (isRankOneValuation_iff_archimedean_valueGroup v).mp hrank
  letI : MulArchimedean
      (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v)) := harch
  have hav : v (a : K) < 1 := (mem_maximalIdealOf_iff v a).mp ha_m
  have hbv : 0 < v.restrict (b : K) := by
    rw [Valuation.restrict_pos_iff]
    exact v.pos_iff.mpr (by
      intro hzero
      apply hb
      exact Subtype.ext hzero)
  have havpos : 0 < v.restrict (a : K) := by
    rw [Valuation.restrict_pos_iff]
    exact v.pos_iff.mpr (by
      exact fun hzero => ha (Subtype.ext hzero))
  have havR : v.restrict (a : K) < 1 := by
    rw [Valuation.restrict_lt_one_iff]
    exact hav
  have havinv : 1 < (v.restrict (a : K))⁻¹ := (one_lt_inv₀ havpos).2 havR
  obtain ⟨n, hn⟩ := harch.arch (v.restrict (b : K))⁻¹ havinv
  have hpowR : (v.restrict (a : K)) ^ n ≤ v.restrict (b : K) := by
    apply (inv_le_inv₀ hbv (pow_pos havpos n)).mp
    simpa [inv_pow] using hn
  have hpow : v ((a : K) ^ n) ≤ v (b : K) := by
    rw [← Valuation.restrict_le_iff]
    simpa [v.map_pow] using hpowR
  have hdiv : v ((a : K) ^ n / (b : K)) ≤ 1 := by
    rw [v.map_div, div_le_iff₀ (v.pos_iff.mpr (by
      intro hzero
      apply hb
      exact Subtype.ext hzero))]
    simpa using hpow
  let c : valuationRingOf v :=
    ⟨(a : K) ^ n / (b : K), (mem_valuationRingOf_iff v _).2 hdiv⟩
  have hcb : (c : K) * (b : K) = (a : K) ^ n := by
    dsimp [c]
    field_simp [hb]
  refine ⟨n, hpow, ?_⟩
  exact Ideal.mem_span_singleton'.mpr ⟨c, by
    apply Subtype.ext
    exact hcb⟩

/- The two-scale lexicographic example. -/

abbrev LexicographicIntegerPair := Lex (ℤ × ℤ)

def lexicographicPair (a b : ℤ) : LexicographicIntegerPair :=
  toLex (a, b)

def lexicographicInfinitesimal (n : ℕ) : LexicographicIntegerPair :=
  lexicographicPair 0 n

def lexicographicDominant : LexicographicIntegerPair :=
  lexicographicPair 1 0

theorem lexicographic_infinitesimals_are_all_below_dominant (n : ℕ) :
    lexicographicInfinitesimal n < lexicographicDominant := by
  change Prod.Lex (fun a b : ℤ => a < b) (fun a b : ℤ => a < b)
    (0, (n : ℤ)) (1, 0)
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by norm_num))

def ChapterArchimedean (A : Type*) [AddCommGroup A] [LinearOrder A] : Prop :=
  ∀ a b : A, 0 < a → 0 < b → ∃ n : ℕ, b ≤ n • a

theorem lexicographic_integer_pair_is_not_archimedean :
    ¬ ChapterArchimedean LexicographicIntegerPair := by
  intro h
  have ha : (0 : LexicographicIntegerPair) <
      lexicographicPair (0 : ℤ) (1 : ℤ) := by
    change Prod.Lex (fun a b : ℤ => a < b) (fun a b : ℤ => a < b)
      (0, 0) (0, 1)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, by norm_num⟩)
  have hb : (0 : LexicographicIntegerPair) <
      lexicographicPair (1 : ℤ) (0 : ℤ) := by
    change Prod.Lex (fun a b : ℤ => a < b) (fun a b : ℤ => a < b)
      (0, 0) (1, 0)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by norm_num))
  obtain ⟨n, hn⟩ := h (lexicographicPair (0 : ℤ) (1 : ℤ))
      (lexicographicPair (1 : ℤ) (0 : ℤ)) ha hb
  have hn' : lexicographicPair (1 : ℤ) (0 : ℤ) ≤
      n • lexicographicPair (0 : ℤ) (1 : ℤ) := hn
  have hnsmul : n • lexicographicPair (0 : ℤ) (1 : ℤ) =
      lexicographicPair (0 : ℤ) (n : ℤ) := by
    clear hn hn'
    induction n with
    | zero =>
        change (0, (0 : ℤ)) = (0, (0 : ℤ))
        rfl
    | succ n ih =>
        rw [succ_nsmul, ih]
        change (0, (n : ℤ) + 1) = (0, (n.succ : ℤ))
        simp
  rw [hnsmul] at hn'
  have hlex := (Prod.Lex.toLex_le_toLex.mp hn')
  have : False := by
    rcases hlex with hfirst | ⟨heq, _⟩ <;> omega
  exact this

theorem lexicographic_two_scale_has_intermediate_prime
    {K : Type*} [Field K]
    (v : Valuation K (WithZero (Multiplicative LexicographicIntegerPair)))
    (hsurj : Function.Surjective v) :
    ∃ P : Ideal (valuationRingOf v), P.IsPrime ∧ P ≠ ⊥ ∧
      P ≠ maximalIdealOf v := by
  classical
  have htarget_not : ¬ MulArchimedean
      (WithZero (Multiplicative LexicographicIntegerPair)) := by
    intro htarget
    have hpair : ∀ n : ℕ, ¬ lexicographicPair (1 : ℤ) (0 : ℤ) ≤
        n • lexicographicPair (0 : ℤ) (1 : ℤ) := by
      intro n hn
      have hnsmul : n • lexicographicPair (0 : ℤ) (1 : ℤ) =
          lexicographicPair (0 : ℤ) (n : ℤ) := by
        clear hn
        induction n with
        | zero =>
            change (0, (0 : ℤ)) = (0, (0 : ℤ))
            rfl
        | succ n ih =>
            rw [succ_nsmul, ih]
            change (0, (n : ℤ) + 1) = (0, (n.succ : ℤ))
            simp
      rw [hnsmul] at hn
      rcases Prod.Lex.toLex_le_toLex.mp hn with hfirst | ⟨heq, _⟩ <;> omega
    let X : WithZero (Multiplicative LexicographicIntegerPair) :=
      WithZero.exp (lexicographicPair (1 : ℤ) (0 : ℤ))
    let Y : WithZero (Multiplicative LexicographicIntegerPair) :=
      WithZero.exp (lexicographicPair (0 : ℤ) (1 : ℤ))
    have hsmall : (0 : LexicographicIntegerPair) <
        lexicographicPair (0 : ℤ) (1 : ℤ) :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, by norm_num⟩)
    have hY : 1 < Y := by
      dsimp [Y]
      rw [← WithZero.exp_zero]
      change (↑(Multiplicative.ofAdd (0 : LexicographicIntegerPair)) :
        WithZero (Multiplicative LexicographicIntegerPair)) <
        ↑(Multiplicative.ofAdd (lexicographicPair (0 : ℤ) (1 : ℤ)))
      exact WithZero.coe_lt_coe.mpr (Multiplicative.ofAdd_lt.mpr hsmall)
    obtain ⟨n, hn⟩ := htarget.arch X hY
    dsimp [X, Y] at hn
    change (↑(Multiplicative.ofAdd (lexicographicPair (1 : ℤ) (0 : ℤ))) :
        WithZero (Multiplicative LexicographicIntegerPair)) ≤
        ↑(Multiplicative.ofAdd (n • lexicographicPair (0 : ℤ) (1 : ℤ))) at hn
    apply hpair n
    exact Multiplicative.ofAdd_le.mp (WithZero.coe_le_coe.mp hn)
  have hgroup_not : ¬ MulArchimedean
      (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v)) := by
    intro hgroup
    apply htarget_not
    exact ⟨by
      intro x y hy
      obtain ⟨a, ha⟩ := hsurj x
      obtain ⟨b, hb⟩ := hsurj y
      have hvb : 1 < v b := by simpa [hb] using hy
      have hyR : 1 < v.restrict b := by
        apply lt_of_not_ge
        intro hle
        have hle' : v b ≤ 1 := by
          rw [← Valuation.restrict_le_one_iff]
          exact hle
        exact (not_le_of_gt hvb) hle'
      obtain ⟨n, hn⟩ := hgroup.arch (v.restrict a) hyR
      have hn' : v.restrict a ≤ v.restrict (b ^ n) := by
        simpa [v.restrict.map_pow] using hn
      have hn'' : v a ≤ v (b ^ n) :=
        (Valuation.restrict_le_iff (v := v)).mp hn'
      exact ⟨n, by simpa [ha, hb, v.map_pow] using hn''⟩⟩
  exact nonarch_valuation_has_intermediate_prime v hgroup_not

end PrimeIdealsAndRank

section IntegralityAndMaximality

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-! ### 3.5. Integrality and maximality -/

theorem valuationRingOf_isIntegrallyClosed (v : Valuation K Γ) :
    IsIntegrallyClosed (valuationRingOf v) := by
  infer_instance

theorem integral_element_outside_ring_has_inverse_in_maximalIdeal
    (v : Valuation K Γ) {x : K} (hxV : x ∉ valuationRingOf v) :
    x⁻¹ ∈ valuationRingOf v ∧
      ∃ y : valuationRingOf v, y ∈ maximalIdealOf v ∧ (y : K) = x⁻¹ := by
  have hx0 : x ≠ 0 := by
    intro hx
    apply hxV
    simpa [hx]
  obtain hxinv | hxinv := Valuation.val_le_one_or_val_inv_le_one v x
  · exact False.elim (hxV ((mem_valuationRingOf_iff v x).2 hxinv))
  · refine ⟨(mem_valuationRingOf_iff v x⁻¹).2 hxinv, ?_⟩
    refine ⟨⟨x⁻¹, (mem_valuationRingOf_iff v x⁻¹).2 hxinv⟩, ?_, rfl⟩
    apply (mem_maximalIdealOf_iff v _).2
    apply (Valuation.one_lt_val_iff v hx0).mp
    exact lt_of_not_ge (fun h => hxV ((mem_valuationRingOf_iff v x).2 h))

theorem monic_relation_divide_by_top_power
    (v : Valuation K Γ) (p : Polynomial (valuationRingOf v)) {x : K}
    (hx : x ≠ 0) (hp : p.Monic)
    (hroot : p.eval₂ (algebraMap (valuationRingOf v) K) x = 0) :
    1 + ∑ i ∈ Finset.range p.natDegree,
      (algebraMap (valuationRingOf v) K (p.coeff i) * x ^ i) / x ^ p.natDegree = 0 := by
  have hsum :
      (∑ i ∈ Finset.range p.natDegree,
        algebraMap (valuationRingOf v) K (p.coeff i) * x ^ i) + x ^ p.natDegree = 0 := by
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ,
      hp.coeff_natDegree, map_one, one_mul] at hroot
    exact hroot
  have hdiv := congrArg (fun z : K => z / x ^ p.natDegree) hsum
  field_simp [hx] at hdiv
  calc
    1 + ∑ i ∈ Finset.range p.natDegree,
        (algebraMap (valuationRingOf v) K (p.coeff i) * x ^ i) / x ^ p.natDegree =
      ((∑ i ∈ Finset.range p.natDegree,
        algebraMap (valuationRingOf v) K (p.coeff i) * x ^ i) + x ^ p.natDegree) /
        x ^ p.natDegree := by
          rw [add_div, Finset.sum_div]
          simp [hx, add_comm]
    _ = 0 := by rw [hsum, zero_div]

theorem monic_relation_divided_tail_is_infinitesimal
    (v : Valuation K Γ) (p : Polynomial (valuationRingOf v)) {x : K}
    (hx : x ≠ 0) (hp : p.Monic) (hxV : x ∉ valuationRingOf v)
    (hroot : p.eval₂ (algebraMap (valuationRingOf v) K) x = 0) :
    ∀ i ∈ Finset.range p.natDegree,
      (algebraMap (valuationRingOf v) K (p.coeff i) * x ^ i) / x ^ p.natDegree ∈
        maximalIdealImageOf v := by
  intro i hi
  let z : K :=
    (algebraMap (valuationRingOf v) K (p.coeff i) * x ^ i) / x ^ p.natDegree
  have hcoeff : v (algebraMap (valuationRingOf v) K (p.coeff i)) ≤ 1 :=
    (mem_valuationRingOf_iff v _).1 (p.coeff i).property
  have hxgt : 1 < v x :=
    lt_of_not_ge (fun h => hxV ((mem_valuationRingOf_iff v x).2 h))
  have hpow : v x ^ i < v x ^ p.natDegree :=
    pow_lt_pow_right₀ hxgt (Finset.mem_range.mp hi)
  have hz : v z < 1 := by
    dsimp [z]
    rw [v.map_div]
    apply (div_lt_one₀ (v.pos_iff.mpr (pow_ne_zero _ hx))).2
    rw [v.map_mul, v.map_pow, v.map_pow]
    exact mul_lt_of_le_one_of_lt hcoeff hpow
  have hzV : z ∈ valuationRingOf v := (mem_valuationRingOf_iff v z).2 hz.le
  refine ⟨⟨z, hzV⟩, (mem_maximalIdealOf_iff v ⟨z, hzV⟩).2 hz, ?_⟩
  rfl

theorem local_sum_of_maximal_ideal_terms_ne_neg_one
    {R : Type*} [CommRing R] [IsLocalRing R]
    {ι : Type*} (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, f i ∈ IsLocalRing.maximalIdeal R) :
    (∑ i ∈ s, f i) ≠ -1 := by
  intro hsum
  have hmem : (∑ i ∈ s, f i) ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.maximalIdeal R).sum_mem (fun i hi => hf i hi)
  have hneg := (IsLocalRing.maximalIdeal R).neg_mem hmem
  rw [hsum] at hneg
  exact (Ideal.ne_top_iff_one _).mp
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top (by simpa using hneg)

theorem integral_element_outside_valuationRing_contradiction
    (v : Valuation K Γ) {x : K} (hx : IsIntegral (valuationRingOf v) x)
    (hxV : x ∉ valuationRingOf v) : False := by
  have hxle : v x ≤ 1 :=
    (Valuation.Integers.isIntegral_iff_v_le_one
      (Valuation.integer.integers v)).mp hx
  exact hxV ((mem_valuationRingOf_iff v x).2 hxle)

theorem integral_element_mem_valuationRing
    (v : Valuation K Γ) {x : K} (hx : IsIntegral (valuationRingOf v) x) :
    x ∈ valuationRingOf v := by
  apply (mem_valuationRingOf_iff v x).2
  exact (Valuation.Integers.isIntegral_iff_v_le_one
    (Valuation.integer.integers v)).mp hx

/- Maximality among local subrings dominated by the same place. -/

def contractedMaximalIdeal {V W : Subring K} (hVW : V ≤ W) [IsLocalRing W] : Ideal V :=
  (IsLocalRing.maximalIdeal W).comap (Subring.inclusion hVW)

theorem local_subring_inverse_obstruction
    (v : Valuation K Γ) (W : Subring K) [IsLocalRing W]
    (hVW : valuationRingOf v ≤ W)
    (hcontract : contractedMaximalIdeal hVW = maximalIdealOf v)
    {x : K} (hxW : x ∈ W) (hxV : x ∉ valuationRingOf v) : False := by
  have hx0 : x ≠ 0 := by
    intro hx
    apply hxV
    simpa [hx]
  obtain ⟨hxiV, ⟨y, hyM, hyx⟩⟩ :=
    integral_element_outside_ring_has_inverse_in_maximalIdeal v hxV
  have hxiM : (⟨x⁻¹, hxiV⟩ : valuationRingOf v) ∈ maximalIdealOf v := by
    convert hyM using 1
    apply Subtype.ext
    exact hyx.symm
  have hxiW : x⁻¹ ∈ W := hVW hxiV
  have hxiMWV : (⟨x⁻¹, hxiV⟩ : valuationRingOf v) ∈ contractedMaximalIdeal hVW := by
    rw [hcontract]
    exact hxiM
  have hxiMW : (⟨x⁻¹, hxiW⟩ : W) ∈ IsLocalRing.maximalIdeal W := by
    exact hxiMWV
  have hunit : IsUnit (⟨x⁻¹, hxiW⟩ : W) := by
    apply IsUnit.of_mul_eq_one (⟨x, hxW⟩ : W)
    apply Subtype.ext
    simp [hx0]
  rw [IsLocalRing.mem_maximalIdeal] at hxiMW
  exact hxiMW hunit

theorem valuationRingOf_maximal_among_dominated_local_subrings
    (v : Valuation K Γ) (W : Subring K) [IsLocalRing W]
    (hVW : valuationRingOf v ≤ W)
    (hcontract : contractedMaximalIdeal hVW = maximalIdealOf v) :
    W = valuationRingOf v := by
  apply le_antisymm
  · intro x hxW
    by_contra hxV
    exact local_subring_inverse_obstruction v W hVW hcontract hxW hxV
  · exact hVW

end IntegralityAndMaximality

section ResiduesAndAngularComponents

variable {K : Type*} [Field K]

/-! ### 3.6. Residues and leading coefficients -/

/-- A discrete valuation normalized so that a uniformizer has value `exp (-1)`. -/
def IsUniformizerFor (v : Valuation K ℤᵐ⁰) (π : K) : Prop :=
  π ≠ 0 ∧ v π = WithZero.exp (-1 : ℤ)

/-- The integer value of a nonzero element for a `ℤᵐ⁰`-valued valuation. -/
def discreteUnitValue (v : Valuation K ℤᵐ⁰) (x : Kˣ) : ℤ :=
  -WithZero.log (v (x : K))

theorem discreteUnitValue_mul (v : Valuation K ℤᵐ⁰) (x y : Kˣ) :
    discreteUnitValue v (x * y) = discreteUnitValue v x + discreteUnitValue v y := by
  simp [discreteUnitValue, WithZero.log_mul]
  abel

theorem discreteUnitValue_inv (v : Valuation K ℤᵐ⁰) (x : Kˣ) :
    discreteUnitValue v x⁻¹ = -discreteUnitValue v x := by
  simp [discreteUnitValue]

/-- The normalized value-zero representative `π⁻ᵛ x`. -/
noncomputable def normalizedElement (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) (x : K) (hx : x ≠ 0) : valuationRingOf v := by
  refine ⟨π ^ (-discreteUnitValue v (Units.mk0 x hx)) * x, ?_⟩
  have hxv0 : v x ≠ 0 := v.ne_zero_iff.mpr hx
  apply (mem_valuationRingOf_iff v _).2
  rw [v.map_mul, map_zpow₀, hπ.2, ← WithZero.exp_zsmul,
    ← WithZero.exp_log hxv0]
  simp [discreteUnitValue, WithZero.exp_add]

/-- The angular component, with zero sent to zero. -/
noncomputable def angularComponent (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) (x : K) : residueFieldOf v := by
  classical
  exact if hx : x = 0 then 0 else
    residueMapOf v (normalizedElement v π hπ x hx)

theorem angularComponent_zero (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) : angularComponent v π hπ 0 = 0 := by
  unfold angularComponent
  simp

theorem discrete_uniformizer_decomposition (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) {x : K} (hx : x ≠ 0) :
    ∃! u : (valuationRingOf v)ˣ,
      x = π ^ discreteUnitValue v (Units.mk0 x hx) * ((u : valuationRingOf v) : K) := by
  classical
  let d := discreteUnitValue v (Units.mk0 x hx)
  let n : valuationRingOf v := normalizedElement v π hπ x hx
  have hnval : v (n : K) = 1 := by
    dsimp [n, normalizedElement]
    rw [v.map_mul, map_zpow₀, hπ.2, ← WithZero.exp_zsmul,
      ← WithZero.exp_log (v.ne_zero_iff.mpr hx)]
    simp [discreteUnitValue]
  have hnunit : IsUnit n := (valuationRingOf_isUnit_iff v n).2 hnval
  let u := hnunit.unit
  have hu : (u : valuationRingOf v) = n := IsUnit.unit_spec hnunit
  have hdecomp : x = π ^ d * (n : K) := by
    dsimp [n, normalizedElement]
    calc
      x = 1 * x := by simp
      _ = (π ^ d * π ^ (-d)) * x := by
        rw [← zpow_add₀ hπ.1, add_neg_cancel, zpow_zero]
      _ = π ^ d * (π ^ (-d) * x) := by ring
  refine ⟨u, ?_, ?_⟩
  · change x = π ^ d * ((u : valuationRingOf v) : K)
    rw [hu]
    exact hdecomp
  · intro u' hu'
    apply Units.ext
    apply Subtype.ext
    apply mul_left_cancel₀ (zpow_ne_zero _ hπ.1)
    calc
      π ^ d * ((u' : valuationRingOf v) : K) = x := by
        exact hu'.symm
      _ = π ^ d * (n : K) := hdecomp
      _ = π ^ d * ((u : valuationRingOf v) : K) := by rw [hu]

theorem angularComponent_eq_reduction_of_normalizedElement
    (v : Valuation K ℤᵐ⁰) (π : K) (hπ : IsUniformizerFor v π) {x : K} (hx : x ≠ 0) :
    angularComponent v π hπ x = residueMapOf v (normalizedElement v π hπ x hx) := by
  simp only [angularComponent, dif_neg hx]

theorem angularComponent_mul (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) (x y : K) :
    angularComponent v π hπ (x * y) =
      angularComponent v π hπ x * angularComponent v π hπ y := by
  classical
  by_cases hx : x = 0
  · subst x
    simp [angularComponent_zero]
  by_cases hy : y = 0
  · subst y
    simp [angularComponent_zero]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hunit : Units.mk0 (x * y) hxy = Units.mk0 x hx * Units.mk0 y hy := by
    apply Units.ext
    rfl
  have hnorm : normalizedElement v π hπ (x * y) hxy =
      normalizedElement v π hπ x hx * normalizedElement v π hπ y hy := by
    apply Subtype.ext
    dsimp [normalizedElement]
    rw [hunit, discreteUnitValue_mul, neg_add, zpow_add₀ hπ.1]
    ring
  rw [angularComponent_eq_reduction_of_normalizedElement v π hπ hxy,
    angularComponent_eq_reduction_of_normalizedElement v π hπ hx,
    angularComponent_eq_reduction_of_normalizedElement v π hπ hy,
    hnorm, map_mul]

noncomputable def residueUnitOf (v : Valuation K ℤᵐ⁰) (u : (valuationRingOf v)ˣ) :
    (residueFieldOf v)ˣ :=
  Units.map (residueMapOf v).toMonoidHom u

theorem angularComponent_parameter_change
    (v : Valuation K ℤᵐ⁰) (π : K) (hπ : IsUniformizerFor v π)
    (u : (valuationRingOf v)ˣ)
    (hπ' : IsUniformizerFor v (((u : valuationRingOf v) : K) * π))
    {x : K} (hx : x ≠ 0) :
    angularComponent v (((u : valuationRingOf v) : K) * π) hπ' x =
      (residueUnitOf v u) ^ (-discreteUnitValue v (Units.mk0 x hx)) *
        angularComponent v π hπ x := by
  classical
  let d := discreteUnitValue v (Units.mk0 x hx)
  have hpow :
      (((u : valuationRingOf v) : K) * π) ^ (-d) =
        ((u : valuationRingOf v) : K) ^ (-d) * π ^ (-d) := by
    let U : Kˣ := Units.map (algebraMap (valuationRingOf v) K).toMonoidHom u
    let P : Kˣ := Units.mk0 π hπ.1
    calc
      (((u : valuationRingOf v) : K) * π) ^ (-d) =
          ((U * P : Kˣ) : K) ^ (-d) := by rfl
      _ = (((U * P) ^ (-d) : Kˣ) : K) := by
        rw [Units.val_zpow_eq_zpow_val]
      _ = (((U ^ (-d) * P ^ (-d) : Kˣ) : Kˣ) : K) := by
        rw [mul_zpow]
      _ = ((u : valuationRingOf v) : K) ^ (-d) * π ^ (-d) := by
        have hU : (U : K) = ((u : valuationRingOf v) : K) := by
          rfl
        have hP : (P : K) = π := by
          rfl
        rw [Units.val_mul, Units.val_zpow_eq_zpow_val,
          Units.val_zpow_eq_zpow_val, hU, hP]
  have hnorm : normalizedElement v (((u : valuationRingOf v) : K) * π) hπ' x hx =
      ((u ^ (-d) : (valuationRingOf v)ˣ) : valuationRingOf v) *
        normalizedElement v π hπ x hx := by
    apply Subtype.ext
    dsimp [normalizedElement]
    have hu_pow :
        (((u ^ (-d) : (valuationRingOf v)ˣ) : valuationRingOf v) : K) =
          ((u : valuationRingOf v) : K) ^ (-d) := by
      let U : Kˣ := Units.map (algebraMap (valuationRingOf v) K).toMonoidHom u
      calc
        (((u ^ (-d) : (valuationRingOf v)ˣ) : valuationRingOf v) : K) =
            ((Units.map (algebraMap (valuationRingOf v) K).toMonoidHom
              (u ^ (-d) : (valuationRingOf v)ˣ) : Kˣ) : K) := by
          rfl
        _ = ((U ^ (-d) : Kˣ) : K) := by
          rw [map_zpow]
        _ = ((u : valuationRingOf v) : K) ^ (-d) := by
          rw [Units.val_zpow_eq_zpow_val]
          rw [show (U : K) = ((u : valuationRingOf v) : K) by rfl]
    rw [hpow, hu_pow]
    ring
  have hres : residueMapOf v
      (((u ^ (-d) : (valuationRingOf v)ˣ) : valuationRingOf v)) =
    (residueUnitOf v u : residueFieldOf v) ^ (-d) := by
    change
      (Units.map (residueMapOf v).toMonoidHom
          (u ^ (-d) : (valuationRingOf v)ˣ) : residueFieldOf v) =
        (Units.map (residueMapOf v).toMonoidHom u : residueFieldOf v) ^ (-d)
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rw [angularComponent_eq_reduction_of_normalizedElement v _ hπ' hx,
    angularComponent_eq_reduction_of_normalizedElement v π hπ hx,
    hnorm, map_mul, hres]

/- A local associated-graded-symbol interface records the coordinate change above. -/

def leadingTermCoordinateRelation (v : Valuation K ℤᵐ⁰)
    (p q : ℤ × residueFieldOf v) : Prop :=
  p.1 = q.1 ∧ ∃ u : (residueFieldOf v)ˣ,
    q.2 = (u : residueFieldOf v) ^ (-p.1) * p.2

noncomputable def leadingTermCoordinateSetoid (v : Valuation K ℤᵐ⁰) :
    Setoid (ℤ × residueFieldOf v) :=
  { r := leadingTermCoordinateRelation v
    iseqv := by
      constructor
      · rintro ⟨a, b⟩
        exact ⟨rfl, 1, by simp⟩
      · rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨ha, u, hu⟩
        refine ⟨ha.symm, u⁻¹, ?_⟩
        rw [hu, ← ha]
        have hpow : ((u⁻¹ : (residueFieldOf v)ˣ) : residueFieldOf v) ^ (-(a : ℤ)) *
            (u : residueFieldOf v) ^ (-(a : ℤ)) = 1 := by
          calc
            ((u⁻¹ : (residueFieldOf v)ˣ) : residueFieldOf v) ^ (-(a : ℤ)) *
                (u : residueFieldOf v) ^ (-(a : ℤ)) =
                (((u⁻¹ : (residueFieldOf v)ˣ) ^ (-(a : ℤ)) *
                    u ^ (-(a : ℤ)) : (residueFieldOf v)ˣ) : residueFieldOf v) := by
              rw [Units.val_mul, Units.val_zpow_eq_zpow_val,
                Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val]
            _ = 1 := by
              rw [← mul_zpow]
              simp
        rw [← mul_assoc, hpow, one_mul]
      · rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨a'', b''⟩ ⟨ha, u, hu⟩ ⟨ha', w, hw⟩
        refine ⟨ha.trans ha', w * u, ?_⟩
        change a = a' at ha
        change a' = a'' at ha'
        rw [hw, hu, ← ha]
        simp [mul_zpow, mul_assoc, mul_comm, mul_left_comm]
  }

abbrev intrinsicLeadingTermClass (v : Valuation K ℤᵐ⁰) :=
  Quotient (leadingTermCoordinateSetoid v)

noncomputable def leadingTermCoordinate (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) (x : Kˣ) : ℤ × residueFieldOf v :=
  (discreteUnitValue v x, angularComponent v π hπ (x : K))

noncomputable def associatedGradedSymbol (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) (x : Kˣ) : intrinsicLeadingTermClass v :=
  Quotient.mk (leadingTermCoordinateSetoid v)
    (leadingTermCoordinate v π hπ x)

theorem associatedGradedSymbol_parameter_independent
    (v : Valuation K ℤᵐ⁰) (π₁ π₂ : K)
    (hπ₁ : IsUniformizerFor v π₁) (hπ₂ : IsUniformizerFor v π₂) (x : Kˣ) :
    associatedGradedSymbol v π₁ hπ₁ x = associatedGradedSymbol v π₂ hπ₂ x := by
  classical
  have hπ₁0 : π₁ ≠ 0 := hπ₁.1
  have hπ₂0 : π₂ ≠ 0 := hπ₂.1
  have hr0 : π₂ / π₁ ≠ 0 := div_ne_zero hπ₂0 hπ₁0
  have hrval : v (π₂ / π₁) = 1 := by
    rw [v.map_div, hπ₂.2, hπ₁.2]
    simp
  let rA : valuationRingOf v :=
    ⟨π₂ / π₁, (mem_valuationRingOf_iff v _).2 hrval.le⟩
  have hrunit : IsUnit rA :=
    (valuationRingOf_isUnit_iff v rA).2 (by simpa [rA] using hrval)
  let u := hrunit.unit
  have hu : ((u : valuationRingOf v) : K) = π₂ / π₁ := by
    have h := IsUnit.unit_spec hrunit
    exact congrArg Subtype.val h
  have hπrel : π₂ = ((u : valuationRingOf v) : K) * π₁ := by
    rw [hu]
    field_simp [hπ₁0]
  have hπ₂' : IsUniformizerFor v (((u : valuationRingOf v) : K) * π₁) := by
    rw [← hπrel]
    exact hπ₂
  apply Quotient.sound
  dsimp [associatedGradedSymbol, leadingTermCoordinate]
  refine ⟨rfl, residueUnitOf v u, ?_⟩
  have hmk : Units.mk0 (x : K) x.ne_zero = x := by
    apply Units.ext
    rfl
  have hangle :
      angularComponent v π₂ hπ₂ (x : K) =
        angularComponent v (((u : valuationRingOf v) : K) * π₁) hπ₂' (x : K) := by
    simpa only [hπrel]
  rw [hangle]
  simpa [hmk] using
    (angularComponent_parameter_change v π₁ hπ₁ u hπ₂' (x := (x : K)) x.ne_zero)

/- The Laurent-series realization: first nonzero coefficient and angular component. -/

noncomputable def laurentSeriesValuation (k : Type*) [Field k] :
    Valuation (LaurentSeries k) ℤᵐ⁰ :=
  Valued.v

noncomputable def laurentSeriesValuationRingEquiv (k : Type*) [Field k] :
    k⟦X⟧ ≃+* valuationRingOf (laurentSeriesValuation k) := by
  letI : IsLocalRing (valuationRingOf (laurentSeriesValuation k)) :=
    valuationRingOf_isLocal (laurentSeriesValuation k)
  let e : k⟦X⟧ →+* valuationRingOf (laurentSeriesValuation k) :=
    (HahnSeries.ofPowerSeries ℤ k).codRestrict
      (valuationRingOf (laurentSeriesValuation k)) (fun F =>
        (mem_valuationRingOf_iff (laurentSeriesValuation k)
          (F : LaurentSeries k)).2 (by
            simpa [laurentSeriesValuation] using
              (LaurentSeries.val_le_one_iff_eq_coe k (F : LaurentSeries k)).2 ⟨F, rfl⟩))
  apply RingEquiv.ofBijective e
  constructor
  · intro F G hFG
    apply PowerSeries.ext
    intro n
    have hFG' := congrArg
      (fun z : valuationRingOf (laurentSeriesValuation k) => (z : LaurentSeries k)) hFG
    simpa [e] using congrArg (fun z : LaurentSeries k => z.coeff n) hFG'
  · intro z
    have hz : Valued.v (z : LaurentSeries k) ≤ (1 : ℤᵐ⁰) := by
      simpa [laurentSeriesValuation] using
        (mem_valuationRingOf_iff (laurentSeriesValuation k)
          (z : LaurentSeries k)).mp z.property
    obtain ⟨F, hF⟩ := (LaurentSeries.val_le_one_iff_eq_coe k
      (z : LaurentSeries k)).mp hz
    refine ⟨F, ?_⟩
    apply Subtype.ext
    exact hF

noncomputable def laurentSeriesResidueEquiv (k : Type*) [Field k] :
    residueFieldOf (laurentSeriesValuation k) ≃+* k := by
  letI : IsLocalRing (valuationRingOf (laurentSeriesValuation k)) :=
    valuationRingOf_isLocal (laurentSeriesValuation k)
  exact (IsLocalRing.ResidueField.mapEquiv
    (laurentSeriesValuationRingEquiv k)).symm.trans
      PowerSeries.residueFieldOfPowerSeries

theorem laurentSeriesResidueEquiv_exists (k : Type*) [Field k] :
    Nonempty (residueFieldOf (laurentSeriesValuation k) ≃+* k) := by
  exact ⟨laurentSeriesResidueEquiv k⟩

theorem laurentSeries_value_is_first_nonzero_coefficient
    (k : Type*) [Field k] (f : LaurentSeries k) (hf : f ≠ 0) :
    ∃ N : ℤ, f.order = N ∧ f.coeff N ≠ 0 ∧
      (∀ n : ℤ, n < N → f.coeff n = 0) ∧
      laurentSeriesValuation k f = WithZero.exp (-N) := by
  classical
  refine ⟨f.order, rfl, ?_, ?_, ?_⟩
  · intro hzero
    exact hf ((HahnSeries.coeff_order_eq_zero).mp hzero)
  · intro n hn
    exact HahnSeries.coeff_eq_zero_of_lt_order hn
  · have hvne : laurentSeriesValuation k f ≠ 0 :=
      (Valuation.ne_zero_iff (laurentSeriesValuation k)).2 hf
    have hle : laurentSeriesValuation k f ≤ WithZero.exp (-f.order) := by
      apply (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero k).2
      exact fun n hn => HahnSeries.coeff_eq_zero_of_lt_order hn
    have hlog_le : WithZero.log (laurentSeriesValuation k f) ≤ -f.order := by
      apply (WithZero.exp_le_exp).mp
      rw [WithZero.exp_log hvne]
      exact hle
    have hlog_ge : -f.order ≤ WithZero.log (laurentSeriesValuation k f) := by
      apply le_of_not_gt
      intro hlt
      have hnext : WithZero.log (laurentSeriesValuation k f) ≤ -(f.order + 1) := by
        omega
      have hvalnext : laurentSeriesValuation k f ≤
          WithZero.exp (-(f.order + 1)) := by
        rw [← WithZero.exp_log hvne, WithZero.exp_le_exp]
        exact hnext
      have hcoeff :=
        (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero k).mp hvalnext
          f.order (by omega)
      exact (show f.coeff f.order ≠ 0 from by
        intro hzero
        exact hf ((HahnSeries.coeff_order_eq_zero).mp hzero)) hcoeff
    have hlog : WithZero.log (laurentSeriesValuation k f) = -f.order :=
      le_antisymm hlog_le hlog_ge
    rw [← WithZero.exp_log hvne, hlog]

noncomputable def laurentSeriesUniformizer (k : Type*) [Field k] : LaurentSeries k :=
  HahnSeries.single 1 1

theorem laurentSeriesUniformizer_isUniformizer (k : Type*) [Field k] :
    IsUniformizerFor (laurentSeriesValuation k) (laurentSeriesUniformizer k) := by
  refine ⟨HahnSeries.single_ne_zero one_ne_zero, ?_⟩
  simpa [laurentSeriesValuation, laurentSeriesUniformizer] using
    (LaurentSeries.valuation_single_zpow (K := k) (1 : ℤ))

theorem laurentSeries_angularComponent_is_first_coefficient
    (k : Type*) [Field k] {f : LaurentSeries k} (hf : f ≠ 0) :
    (laurentSeriesResidueEquiv k)
        (angularComponent (laurentSeriesValuation k)
          (laurentSeriesUniformizer k)
          (laurentSeriesUniformizer_isUniformizer k) f) =
      f.coeff f.order := by
  classical
  have hvalue := laurentSeries_value_is_first_nonzero_coefficient k f hf
  have hd : discreteUnitValue (laurentSeriesValuation k) (Units.mk0 f hf) = f.order := by
    unfold discreteUnitValue
    change -WithZero.log (laurentSeriesValuation k f) = f.order
    have hN : hvalue.choose = f.order := hvalue.choose_spec.1.symm
    have hval : laurentSeriesValuation k f = WithZero.exp (-f.order) := by
      calc
        laurentSeriesValuation k f = WithZero.exp (-hvalue.choose) :=
          hvalue.choose_spec.2.2.2
        _ = WithZero.exp (-f.order) := by rw [hN]
    rw [hval]
    simp
  let F0 : valuationRingOf (laurentSeriesValuation k) :=
    ⟨(f.powerSeriesPart : LaurentSeries k),
      (mem_valuationRingOf_iff (laurentSeriesValuation k)
        (f.powerSeriesPart : LaurentSeries k)).2 (by
          simpa [laurentSeriesValuation] using
            (LaurentSeries.val_le_one_iff_eq_coe k
              (f.powerSeriesPart : LaurentSeries k)).2
              ⟨f.powerSeriesPart, rfl⟩)⟩
  have hnorm :
      normalizedElement (laurentSeriesValuation k) (laurentSeriesUniformizer k)
        (laurentSeriesUniformizer_isUniformizer k) f hf = F0 := by
    apply Subtype.ext
    dsimp [normalizedElement]
    rw [hd, laurentSeriesUniformizer, ← RatFunc.single_zpow (F := k) (-f.order)]
    exact (LaurentSeries.ofPowerSeries_powerSeriesPart f).symm
  rw [angularComponent_eq_reduction_of_normalizedElement
    (laurentSeriesValuation k) (laurentSeriesUniformizer k)
    (laurentSeriesUniformizer_isUniformizer k) hf, hnorm]
  change PowerSeries.residueFieldOfPowerSeries
      ((IsLocalRing.ResidueField.mapEquiv (laurentSeriesValuationRingEquiv k)).symm
        (residueMapOf (laurentSeriesValuation k) F0)) = f.coeff f.order
  have hresidue :
      (IsLocalRing.ResidueField.mapEquiv (laurentSeriesValuationRingEquiv k)).symm
          (residueMapOf (laurentSeriesValuation k) F0) =
        IsLocalRing.residue k⟦X⟧ f.powerSeriesPart := by
    apply (IsLocalRing.ResidueField.mapEquiv
      (laurentSeriesValuationRingEquiv k)).injective
    calc
      (IsLocalRing.ResidueField.mapEquiv (laurentSeriesValuationRingEquiv k))
          ((IsLocalRing.ResidueField.mapEquiv
            (laurentSeriesValuationRingEquiv k)).symm
            (residueMapOf (laurentSeriesValuation k) F0)) =
          residueMapOf (laurentSeriesValuation k) F0 :=
        (IsLocalRing.ResidueField.mapEquiv
          (laurentSeriesValuationRingEquiv k)).apply_symm_apply _
      _ = (IsLocalRing.ResidueField.mapEquiv
          (laurentSeriesValuationRingEquiv k))
          (IsLocalRing.residue k⟦X⟧ f.powerSeriesPart) := by
        change residueMapOf (laurentSeriesValuation k) F0 =
          residueMapOf (laurentSeriesValuation k)
            (laurentSeriesValuationRingEquiv k f.powerSeriesPart)
        congr 1
  rw [hresidue]
  change
    ((Ideal.quotEquivOfEq (PowerSeries.ker_coeff_eq_max_ideal (k := k)).symm).trans
      (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj))
        (Ideal.Quotient.mk _ f.powerSeriesPart) = f.coeff f.order
  simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    LaurentSeries.powerSeriesPart_coeff]
  simp

/- The rational p-adic realization. -/

theorem padicResidueEquiv_exists (p : ℕ) [Fact p.Prime] :
    Nonempty (residueFieldOf (pValuation p) ≃+* ZMod p) := by
  exact pValuationResidueField_equiv_finiteField p
noncomputable def padicResidueEquiv (p : ℕ) [Fact p.Prime] :
    residueFieldOf (pValuation p) ≃+* ZMod p :=
  letI : IsLocalRing (pValuationRing p) := valuationRingOf_isLocal (pValuation p)
  letI : (pPrimeIdeal p).IsMaximal := by
    change (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal
    infer_instance
  let e := pValuationRingEquiv p
  let q := IsLocalization.AtPrime.equivQuotMaximalIdeal
    (pPrimeIdeal p) (pLocalIntegers p)
  (IsLocalRing.ResidueField.mapEquiv e).trans
    (q.symm.trans (Int.quotientSpanNatEquivZMod p))

theorem padic_angularComponent_formula (p : ℕ) [Fact p.Prime]
    (hp : IsUniformizerFor (pValuation p) (p : ℚ))
    (n : ℤ) (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b) :
    padicResidueEquiv p
        (angularComponent (pValuation p) (p : ℚ) hp
          (((p : ℚ) ^ n) * (a : ℚ) / (b : ℚ))) =
      (a : ZMod p) * (b : ZMod p)⁻¹ := by
  classical
  letI : IsLocalRing (pValuationRing p) := valuationRingOf_isLocal (pValuation p)
  letI : (pPrimeIdeal p).IsMaximal := by
    change (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal
    infer_instance
  let e := pValuationRingEquiv p
  let q := IsLocalization.AtPrime.equivQuotMaximalIdeal
    (pPrimeIdeal p) (pLocalIntegers p)
  letI : Field (ℤ ⧸ pPrimeIdeal p) := Ideal.Quotient.field _
  have hres_int (z : ℤ) :
      padicResidueEquiv p
          (residueMapOf (pValuation p)
            (algebraMap ℤ (valuationRingOf (pValuation p)) z)) =
        (z : ZMod p) := by
    change (Int.quotientSpanNatEquivZMod p)
        (q.symm ((IsLocalRing.ResidueField.mapEquiv e)
          (residueMapOf (pValuation p)
            (algebraMap ℤ (valuationRingOf (pValuation p)) z)))) =
      (z : ZMod p)
    have hq : q.symm
        (IsLocalRing.residue (pLocalIntegers p)
          (algebraMap ℤ (pLocalIntegers p) z)) =
        Ideal.Quotient.mk (pPrimeIdeal p) z := by
      rw [IsLocalRing.residue_def,
        ← IsLocalization.mk'_one (M := (pPrimeIdeal p).primeCompl)
          (S := pLocalIntegers p) z]
      rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_symm_apply_mk]
      change (Ideal.Quotient.mk (pPrimeIdeal p) z) *
          (Ideal.Quotient.mk (pPrimeIdeal p) (1 : ℤ))⁻¹ = _
      rw [map_one, inv_one, mul_one]
    rw [show (IsLocalRing.ResidueField.mapEquiv e)
          (residueMapOf (pValuation p)
            (algebraMap ℤ (valuationRingOf (pValuation p)) z)) =
          IsLocalRing.residue (pLocalIntegers p)
            (algebraMap ℤ (pLocalIntegers p) z) by
          change IsLocalRing.ResidueField.map (e :
              pValuationRing p →+* pLocalIntegers p)
              (IsLocalRing.residue (pValuationRing p)
              (algebraMap ℤ (pValuationRing p) z)) = _
          rw [IsLocalRing.ResidueField.map_residue]
          congr 1
          simp [e, pValuationRingEquiv, AlgEquiv.commutes]
          ]
    rw [hq]
    change (Int.quotientSpanNatEquivZMod p)
        (Ideal.Quotient.mk (Ideal.span ({(p : ℤ)} : Set ℤ)) z) =
      (z : ZMod p)
    exact congrArg (fun f : ℤ →+* ZMod p => f z)
      (Int.quotientSpanNatEquivZMod_comp_Quotient_mk p)
  have hp0 : (p : ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have ha0 : (a : ℚ) ≠ 0 := by
    exact_mod_cast ha
  have hb0 : (b : ℚ) ≠ 0 := by
    exact_mod_cast hb
  have hvp : pValuation p (p : ℚ) = WithZero.exp (-1 : ℤ) := by
    simpa [pValuation] using Rat.padicValuation_self p
  have hva : pValuation p (a : ℚ) = 1 := by
    change Rat.padicValuation p (a : ℚ) = 1
    rw [Rat.padicValuation_cast]
    exact Int.padicValuation_eq_one_iff.mpr hpa
  have hvb : pValuation p (b : ℚ) = 1 := by
    change Rat.padicValuation p (b : ℚ) = 1
    rw [Rat.padicValuation_cast]
    exact Int.padicValuation_eq_one_iff.mpr hpb
  let x : ℚ := ((p : ℚ) ^ n) * (a : ℚ) / (b : ℚ)
  have hx : x ≠ 0 := by
    dsimp [x]
    exact div_ne_zero (mul_ne_zero (zpow_ne_zero n hp0) ha0) hb0
  have hvx : pValuation p x = WithZero.exp (-n : ℤ) := by
    dsimp [x]
    rw [map_div₀, map_mul, map_zpow₀, hvp, hva, hvb]
    simp [← WithZero.exp_zsmul]
  have hd : discreteUnitValue (pValuation p) (Units.mk0 x hx) = n := by
    unfold discreteUnitValue
    change -WithZero.log (pValuation p x) = n
    rw [hvx]
    simp
  have hqval : pValuation p ((a : ℚ) / (b : ℚ)) = 1 := by
    rw [map_div₀, hva, hvb]
    simp
  let qA : valuationRingOf (pValuation p) :=
    ⟨(a : ℚ) / (b : ℚ), (mem_valuationRingOf_iff (pValuation p) _).2 hqval.le⟩
  have hbunit : IsUnit (algebraMap ℤ (valuationRingOf (pValuation p)) b) := by
    apply (valuationRingOf_isUnit_iff (pValuation p) _).2
    exact hvb
  let qinv : valuationRingOf (pValuation p) :=
    (((IsUnit.unit hbunit)⁻¹).val)
  have hqinv : (qinv : ℚ) = (b : ℚ)⁻¹ := by
    have h := congrArg (fun y : valuationRingOf (pValuation p) => (y : ℚ))
      (IsUnit.mul_val_inv hbunit)
    have h' : (b : ℚ) * (qinv : ℚ) = 1 := by
      change (b : ℚ) * (qinv : ℚ) = 1 at h
      exact h
    calc
      (qinv : ℚ) = (qinv : ℚ) * 1 := by rw [mul_one]
      _ = (qinv : ℚ) * ((b : ℚ) * (b : ℚ)⁻¹) := by
        rw [mul_inv_cancel₀ hb0]
      _ = ((b : ℚ) * (qinv : ℚ)) * (b : ℚ)⁻¹ := by ring
      _ = (1 : ℚ) * (b : ℚ)⁻¹ := by rw [h']
      _ = (b : ℚ)⁻¹ := by rw [one_mul]
  have hqrepr : qA =
      algebraMap ℤ (valuationRingOf (pValuation p)) a *
        qinv := by
    apply Subtype.ext
    dsimp [qA]
    change (a : ℚ) / (b : ℚ) = (a : ℚ) * (qinv : ℚ)
    rw [hqinv]
    field_simp [hb0]
  have hmap_inv :
      residueMapOf (pValuation p)
          qinv =
        (residueMapOf (pValuation p)
          (algebraMap ℤ (valuationRingOf (pValuation p)) b))⁻¹ := by
    change (residueMapOf (pValuation p)).toMonoidHom
        (((IsUnit.unit hbunit)⁻¹ : (valuationRingOf (pValuation p))ˣ) :
          valuationRingOf (pValuation p)) = _
    rw [map_units_inv]
    congr 1
  have hres_q :
      padicResidueEquiv p (residueMapOf (pValuation p) qA) =
        (a : ZMod p) * (b : ZMod p)⁻¹ := by
    calc
      padicResidueEquiv p (residueMapOf (pValuation p) qA) =
          padicResidueEquiv p
            (residueMapOf (pValuation p)
              (algebraMap ℤ (valuationRingOf (pValuation p)) a * qinv)) := by
        rw [hqrepr]
      _ = padicResidueEquiv p
          (residueMapOf (pValuation p)
            (algebraMap ℤ (valuationRingOf (pValuation p)) a) *
            residueMapOf (pValuation p) qinv) := by
        rw [map_mul, map_mul]
      _ = padicResidueEquiv p
          (residueMapOf (pValuation p)
            (algebraMap ℤ (valuationRingOf (pValuation p)) a)) *
            padicResidueEquiv p (residueMapOf (pValuation p) qinv) := by
        simp only [map_mul]
      _ = (a : ZMod p) * (b : ZMod p)⁻¹ := by
        rw [hmap_inv, map_inv₀, hres_int a, hres_int b]
  have hnorm :
      normalizedElement (pValuation p) (p : ℚ) hp x hx = qA := by
    apply Subtype.ext
    change (p : ℚ) ^ (-discreteUnitValue (pValuation p) (Units.mk0 x hx)) * x =
      (a : ℚ) / (b : ℚ)
    rw [hd]
    dsimp [x]
    calc
      (p : ℚ) ^ (-n) * ((p : ℚ) ^ n * (a : ℚ) / (b : ℚ)) =
          ((p : ℚ) ^ (-n) * (p : ℚ) ^ n) * ((a : ℚ) / (b : ℚ)) := by ring
      _ = (a : ℚ) / (b : ℚ) := by
        rw [← zpow_add₀ hp0, neg_add_cancel, zpow_zero, one_mul]
  have hangular :
      padicResidueEquiv p
          (angularComponent (pValuation p) (p : ℚ) hp x) =
        (a : ZMod p) * (b : ZMod p)⁻¹ := by
    rw [angularComponent_eq_reduction_of_normalizedElement
      (pValuation p) (p : ℚ) hp hx, hnorm]
    exact hres_q
  simpa [x] using hangular

end ResiduesAndAngularComponents

end ValuationsBook.Chapter03
