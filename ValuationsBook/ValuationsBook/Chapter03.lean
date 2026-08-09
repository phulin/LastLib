import Mathlib

namespace ValuationsBook.Chapter03

open Set
open scoped BigOperators WithZero LaurentSeries

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
  sorry

theorem valuationRingOf_isSubring (v : Valuation K Γ) :
    IsDomain (valuationRingOf v) ∧ ValuationRing (valuationRingOf v) := by
  sorry

theorem valuationRingOf_isLocal (v : Valuation K Γ) :
    IsLocalRing (valuationRingOf v) := by
  sorry

theorem mem_maximalIdealOf_iff (v : Valuation K Γ) (x : valuationRingOf v) :
    x ∈ maximalIdealOf v ↔ v (x : K) < 1 := by
  sorry

theorem valuationRingOf_isUnit_iff (v : Valuation K Γ) (x : valuationRingOf v) :
    IsUnit x ↔ v (x : K) = 1 := by
  sorry

theorem maximalIdealOf_eq_nonunits (v : Valuation K Γ) :
    (maximalIdealOf v : Set (valuationRingOf v)) = nonunits (valuationRingOf v) := by
  sorry

theorem maximalIdealOf_unique (v : Valuation K Γ) (I : Ideal (valuationRingOf v)) :
    I.IsMaximal ↔ I = maximalIdealOf v := by
  sorry

theorem residueMapOf_eq_iff_difference_mem (v : Valuation K Γ)
    (x y : valuationRingOf v) :
    residueMapOf v x = residueMapOf v y ↔
      (x - y : valuationRingOf v) ∈ maximalIdealOf v := by
  sorry

theorem residueMapOf_eq_iff_difference_small (v : Valuation K Γ)
    (x y : valuationRingOf v) :
    residueMapOf v x = residueMapOf v y ↔ v ((x : K) - (y : K)) < 1 := by
  sorry

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
  sorry

theorem mem_additiveMaximalIdealOf_iff (v : AddValuation K A)
    (x : additiveValuationRingOf v) :
    x ∈ additiveMaximalIdealOf v ↔ 0 < v (x : K) := by
  sorry

theorem additiveValuationRingOf_isLocal (v : AddValuation K A) :
    IsLocalRing (additiveValuationRingOf v) := by
  sorry

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
  sorry

/- The two standard examples in the chapter. -/

/-- The prime ideal `(p)` of `ℤ`. -/
def pPrimeIdeal (p : ℕ) : Ideal ℤ :=
  Ideal.span ({(p : ℤ)} : Set ℤ)

instance pPrimeIdeal_isPrime (p : ℕ) [Fact p.Prime] : (pPrimeIdeal p).IsPrime := by
  sorry

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

theorem pValuationRing_is_pLocal (p : ℕ) [Fact p.Prime] :
    Nonempty (pValuationRing p ≃+* pLocalIntegers p) := by
  sorry

theorem pValuationMaximalIdeal_is_generated_by_p (p : ℕ) [Fact p.Prime] :
    ∃ e : pValuationRing p ≃+* pLocalIntegers p,
      Ideal.map e.toRingHom (pValuationMaximalIdeal p) = pLocalPrincipalIdeal p := by
  sorry

abbrev pValuationResidueField (p : ℕ) [Fact p.Prime] :=
  residueFieldOf (pValuation p)

theorem pValuationResidueField_equiv_finiteField (p : ℕ) [Fact p.Prime] :
    Nonempty (pValuationResidueField p ≃+* ZMod p) := by
  sorry

/- The rational-function example `k[t]_(t) ⊂ k(t)`. -/

noncomputable def tPrimeIdeal (k : Type*) [Field k] : Ideal (Polynomial k) :=
  Ideal.span ({Polynomial.X} : Set (Polynomial k))

instance tPrimeIdeal_isPrime (k : Type*) [Field k] : (tPrimeIdeal k).IsPrime := by
  sorry

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
  ⟨algebraMap (Polynomial k) (RatFunc k) Polynomial.X, by sorry⟩

noncomputable def tParameterInLocalPolynomialRing (k : Type*) [Field k] :
    tLocalPolynomialRing k :=
  algebraMap (Polynomial k) (tLocalPolynomialRing k) Polynomial.X

theorem tValuationRing_is_tLocal (k : Type*) [Field k] :
    ∃ e : tValuationRing k ≃+* tLocalPolynomialRing k,
      e (tParameterInValuationRing k) =
        tParameterInLocalPolynomialRing k ∧
      ∀ f : Polynomial k,
        e ⟨algebraMap (Polynomial k) (RatFunc k) f, by sorry⟩ =
          algebraMap (Polynomial k) (tLocalPolynomialRing k) f := by
  sorry

theorem tValuationMaximalIdeal_is_generated_by_t (k : Type*) [Field k] :
    tValuationMaximalIdeal k =
      Ideal.span {tParameterInValuationRing k} := by
  sorry

theorem tLocalMaximalIdeal_is_generated_by_t (k : Type*) [Field k] :
    tLocalMaximalIdeal k = Ideal.span {tParameterInLocalPolynomialRing k} := by
  sorry

theorem tValuationResidueField_is_the_coefficient_field (k : Type*) [Field k] :
    Nonempty (residueFieldOf (tValuation k) ≃+* k) := by
  sorry
noncomputable def tEvaluationAtZero (k : Type*) [Field k] :
    tLocalPolynomialRing k →+* k :=
  IsLocalization.lift (M := (tPrimeIdeal k).primeCompl)
    (g := Polynomial.evalRingHom (0 : k)) (by
      intro y
      sorry)
theorem tResidue_is_evaluation_at_zero (k : Type*) [Field k] :
    ∃ e : IsLocalRing.ResidueField (tLocalPolynomialRing k) ≃+* k,
      ∀ x : tLocalPolynomialRing k,
        e (IsLocalRing.residue (tLocalPolynomialRing k) x) = tEvaluationAtZero k x := by
  sorry

end BoundedElements

section IntrinsicCriterion

variable {K : Type*} [Field K]

/-! ### 3.2. The intrinsic characterization -/

/-- A subring is a valuation ring of some valuation on its fraction field. -/
def IsValuationRingSubring (V : Subring K) : Prop :=
  ∃ (Γ : Type*) (_ : LinearOrderedCommGroupWithZero Γ),
    ∃ v : Valuation K Γ, V = v.integer

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
  sorry

theorem principalFractionalSet_comparison_iff (V : Subring K) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    principalFractionalSet V x ⊆ principalFractionalSet V y ∨
        principalFractionalSet V y ⊆ principalFractionalSet V x ↔
      x / y ∈ V ∨ y / x ∈ V := by
  sorry

theorem valuationRingCriterion_tfae (V : Subring K) :
    List.TFAE
      [IsValuationRingSubring V,
        HasValuationSubringCriterion V,
        PrincipalFractionalIdealsComparable V] := by
  sorry

theorem valuationRingCriterion (V : Subring K) :
    IsValuationRingSubring V ↔ HasValuationSubringCriterion V ∧
      PrincipalFractionalIdealsComparable V := by
  sorry

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
  sorry

def criterionUnitSubgroup (V : Subring K) : Subgroup Kˣ :=
  (Units.map V.subtype.toMonoidHom).range

abbrev criterionUnitQuotient (V : Subring K) :=
  Kˣ ⧸ criterionUnitSubgroup V

theorem criterionValueGroup_is_quotient_by_units (V : Subring K)
    (hV : HasValuationSubringCriterion V) :
    Nonempty ((criterionValueGroup V hV)ˣ ≃* criterionUnitQuotient V) := by
  sorry

def criterionComparison (V : Subring K) (hV : HasValuationSubringCriterion V)
    (x y : K) : Prop :=
  x / y ∈ V

theorem criterionComparison_unit_invariant (V : Subring K)
    (hV : HasValuationSubringCriterion V) (x y : K) (a b : Vˣ) :
    criterionComparison V hV
        (((a : V) : K) * x) (((b : V) : K) * y) ↔
      criterionComparison V hV x y := by
  sorry

theorem criterionComparison_total (V : Subring K)
    (hV : HasValuationSubringCriterion V) (x y : K) :
    criterionComparison V hV x y ∨ criterionComparison V hV y x := by
  sorry

theorem criterionReconstructedValuation_addition_inequality (V : Subring K)
    (hV : HasValuationSubringCriterion V) (x y : K) :
    criterionReconstructedValuation V hV (x + y) ≤
      max (criterionReconstructedValuation V hV x)
        (criterionReconstructedValuation V hV y) := by
  sorry

theorem criterionNormalizedAddition (V : Subring K)
    (hV : HasValuationSubringCriterion V) {x y : K} (hx : x ≠ 0)
    (hle : criterionReconstructedValuation V hV y ≤
      criterionReconstructedValuation V hV x) :
    (x + y) / x = 1 + y / x ∧
      (x + y) / x ∈ V := by
  sorry

theorem valuationRing_determines_equivalence
    {Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ₁]
    [LinearOrderedCommGroupWithZero Γ₂]
    (v₁ : Valuation K Γ₁) (v₂ : Valuation K Γ₂)
    (h : v₁.integer = v₂.integer) : v₁.IsEquiv v₂ := by
  sorry

theorem valuationRing_determines_additive_equivalence
    {A₁ A₂ : Type*} [LinearOrderedAddCommGroupWithTop A₁]
    [LinearOrderedAddCommGroupWithTop A₂]
    (v₁ : AddValuation K A₁) (v₂ : AddValuation K A₂)
    (h : additiveValuationRingOf v₁ = additiveValuationRingOf v₂) :
    v₁.IsEquiv v₂ := by
  sorry

end IntrinsicCriterion

section OrderedIdeals

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

/-! ### 3.3. Ideals are ordered -/

theorem ideals_totally_ordered : @Std.Total (Ideal R) (· ≤ ·) := by
  sorry

theorem ideals_comparable_from_principal_ideals (I J : Ideal R) :
    I ≤ J ∨ J ≤ I := by
  sorry

theorem noncomparable_ideals_choose_crossing_elements (I J : Ideal R)
    (hIJ : ¬ I ≤ J) (hJI : ¬ J ≤ I) :
    ∃ x ∈ I, x ∉ J ∧ ∃ y ∈ J, y ∉ I := by
  sorry

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem principal_ideal_order_reverses_valuation (v : Valuation K Γ)
    (x y : valuationRingOf v) :
    Ideal.span ({x} : Set (valuationRingOf v)) ≤ Ideal.span {y} ↔
      v (x : K) ≤ v (y : K) := by
  sorry

theorem valuationRingOf_isBezout (v : Valuation K Γ) :
    IsBezout (valuationRingOf v) := by
  sorry

theorem valuationRingOf_finitely_generated_ideal_is_principal (v : Valuation K Γ)
    (I : Ideal (valuationRingOf v)) (hI : I.FG) : I.IsPrincipal := by
  sorry

theorem valuationRingOf_need_not_be_principal_ideal_ring (v : Valuation K Γ)
    (I : Ideal (valuationRingOf v)) (hI : ¬ I.IsPrincipal) :
    ¬ IsPrincipalIdealRing (valuationRingOf v) := by
  sorry

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
  sorry

theorem additiveValueSet_upward_closed_on_realized_values
    (v : AddValuation K (WithTop A)) (I : Ideal (additiveValuationRingOf v))
    {γ δ : A} (hγ : γ ∈ additiveValueSet v I)
    (hδ : ∃ z : K, z ≠ 0 ∧ v z = (δ : WithTop A)) (hγδ : γ ≤ δ) :
    δ ∈ additiveValueSet v I := by
  sorry

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
  { carrier := {x | x = 0 ∨
        ∃ γ, γ ∈ S.carrier ∧ v (x : K) = (γ : WithTop A)}
    zero_mem' := by sorry
    add_mem' := by sorry
    smul_mem' := by sorry }

theorem idealOfValueCut_mem_iff (v : AddValuation K (WithTop A))
    (S : AdditiveValueCut A)
    (hreal : ∀ {γ}, γ ∈ S.carrier → ∃ x : K, x ≠ 0 ∧
      v x = (γ : WithTop A)) (x : additiveValuationRingOf v) :
    x ∈ idealOfValueCut v S hreal ↔
      x = 0 ∨ ∃ γ, γ ∈ S.carrier ∧ v (x : K) = (γ : WithTop A) := by
  sorry

theorem idealOfValueCut_valueSet (v : AddValuation K (WithTop A))
    (S : AdditiveValueCut A)
    (hreal : ∀ {γ}, γ ∈ S.carrier → ∃ x : K, x ≠ 0 ∧
      v x = (γ : WithTop A)) :
    additiveValueSet v (idealOfValueCut v S hreal) = S.carrier := by
  sorry

theorem principal_additiveValueSet_has_least
    (v : AddValuation K (WithTop A)) (x : additiveValuationRingOf v)
    (hx : x ≠ 0) :
    hasLeastValue (additiveValueSet v (Ideal.span ({x} : Set (additiveValuationRingOf v)))) := by
  sorry

theorem valueCut_without_least_gives_nonprincipal_ideal
    (v : AddValuation K (WithTop A)) (S : AdditiveValueCut A)
    (hreal : ∀ {γ}, γ ∈ S.carrier → ∃ x : K, x ≠ 0 ∧
      v x = (γ : WithTop A)) (hleast : ¬ hasLeastValue S.carrier) :
    ¬ (idealOfValueCut v S hreal).IsPrincipal := by
  sorry

theorem integer_upward_closed_nonnegative_set_has_least (S : Set ℤ)
    (hne : S.Nonempty) (hnonneg : S ⊆ Set.Ici 0)
    (hup : ∀ {a b : ℤ}, a ∈ S → a ≤ b → b ∈ S) :
    hasLeastValue S := by
  sorry
theorem discrete_additive_valuation_nonzero_ideal_is_principal
    (v : AddValuation K (WithTop ℤ)) (I : Ideal (additiveValuationRingOf v))
    (hI : I ≠ ⊥) :
    ∃ x : additiveValuationRingOf v, x ≠ 0 ∧
      I = Ideal.span ({x} : Set (additiveValuationRingOf v)) := by
  sorry

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
  sorry

theorem strictUpperRationalValueCut_is_nonprincipal
    (v : AddValuation K (WithTop ℚ)) (α : ℚ) (hα : 0 ≤ α)
    (hne : ({γ : ℚ | α < γ}).Nonempty)
    (hreal : ∀ {γ}, γ ∈ (strictUpperValueCut α hα).carrier → ∃ x : K, x ≠ 0 ∧
      v x = (γ : WithTop ℚ)) :
    ¬ (idealOfValueCut v (strictUpperValueCut α hα) hreal).IsPrincipal := by
  sorry
theorem rational_dense_value_cut_is_nonprincipal
    (v : AddValuation K (WithTop ℚ)) (S : AdditiveValueCut ℚ)
    (hreal : ∀ {γ}, γ ∈ S.carrier → ∃ x : K, x ≠ 0 ∧
      v x = (γ : WithTop ℚ)) (hleast : ¬ hasLeastValue S.carrier) :
    ¬ (idealOfValueCut v S hreal).IsPrincipal := by
  sorry

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
  sorry


theorem valuationRing_rankOne_iff_krullDim_one
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (hnontrivial : v.IsNontrivial) :
    IsRankOneValuation v ↔ ringKrullDim (valuationRingOf v) = 1 := by
  sorry

theorem rankOne_valuationRing_only_prime_ideals
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (hrank : IsRankOneValuation v)
    (hnontrivial : v.IsNontrivial) (P : Ideal (valuationRingOf v))
    (hP : P.IsPrime) :
    P = ⊥ ∨ P = maximalIdealOf v := by
  sorry

theorem rankOne_nonzero_proper_ideal_radical
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (hrank : IsRankOneValuation v)
    (hnontrivial : v.IsNontrivial) (I : Ideal (valuationRingOf v))
    (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤) :
    Ideal.radical I = maximalIdealOf v := by
  sorry

theorem rankOne_power_divisibility
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (hrank : IsRankOneValuation v)
    (a b : valuationRingOf v) (ha : a ≠ 0) (hb : b ≠ 0)
    (ha_m : a ∈ maximalIdealOf v) (hb_m : b ∈ maximalIdealOf v) :
    ∃ n : ℕ, v ((a : K) ^ n) ≤ v (b : K) ∧
      a ^ n ∈ Ideal.span ({b} : Set (valuationRingOf v)) := by
  sorry

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
  sorry

def ChapterArchimedean (A : Type*) [AddCommGroup A] [LinearOrder A] : Prop :=
  ∀ a b : A, 0 < a → 0 < b → ∃ n : ℕ, b ≤ n • a

theorem lexicographic_integer_pair_is_not_archimedean :
    ¬ ChapterArchimedean LexicographicIntegerPair := by
  sorry

theorem lexicographic_two_scale_has_intermediate_prime
    {K : Type*} [Field K]
    (v : Valuation K (WithZero (Multiplicative LexicographicIntegerPair)))
    (hsurj : Function.Surjective v) :
    ∃ P : Ideal (valuationRingOf v), P.IsPrime ∧ P ≠ ⊥ ∧
      P ≠ maximalIdealOf v := by
  sorry

end PrimeIdealsAndRank

section IntegralityAndMaximality

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-! ### 3.5. Integrality and maximality -/

theorem valuationRingOf_isIntegrallyClosed (v : Valuation K Γ) :
    IsIntegrallyClosed (valuationRingOf v) := by
  sorry

theorem integral_element_outside_ring_has_inverse_in_maximalIdeal
    (v : Valuation K Γ) {x : K} (hxV : x ∉ valuationRingOf v) :
    x⁻¹ ∈ valuationRingOf v ∧
      ∃ y : valuationRingOf v, y ∈ maximalIdealOf v ∧ (y : K) = x⁻¹ := by
  sorry

theorem monic_relation_divide_by_top_power
    (v : Valuation K Γ) (p : Polynomial (valuationRingOf v)) {x : K}
    (hx : x ≠ 0) (hp : p.Monic)
    (hroot : p.eval₂ (algebraMap (valuationRingOf v) K) x = 0) :
    1 + ∑ i ∈ Finset.range p.natDegree,
      (algebraMap (valuationRingOf v) K (p.coeff i) * x ^ i) / x ^ p.natDegree = 0 := by
  sorry

theorem monic_relation_divided_tail_is_infinitesimal
    (v : Valuation K Γ) (p : Polynomial (valuationRingOf v)) {x : K}
    (hx : x ≠ 0) (hp : p.Monic) (hxV : x ∉ valuationRingOf v)
    (hroot : p.eval₂ (algebraMap (valuationRingOf v) K) x = 0) :
    ∀ i ∈ Finset.range p.natDegree,
      (algebraMap (valuationRingOf v) K (p.coeff i) * x ^ i) / x ^ p.natDegree ∈
        maximalIdealImageOf v := by
  sorry

theorem local_sum_of_maximal_ideal_terms_ne_neg_one
    {R : Type*} [CommRing R] [IsLocalRing R]
    {ι : Type*} (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, f i ∈ IsLocalRing.maximalIdeal R) :
    (∑ i ∈ s, f i) ≠ -1 := by
  sorry

theorem integral_element_outside_valuationRing_contradiction
    (v : Valuation K Γ) {x : K} (hx : IsIntegral (valuationRingOf v) x)
    (hxV : x ∉ valuationRingOf v) : False := by
  sorry

theorem integral_element_mem_valuationRing
    (v : Valuation K Γ) {x : K} (hx : IsIntegral (valuationRingOf v) x) :
    x ∈ valuationRingOf v := by
  sorry

/- Maximality among local subrings dominated by the same place. -/

def contractedMaximalIdeal {V W : Subring K} (hVW : V ≤ W) [IsLocalRing W] : Ideal V :=
  (IsLocalRing.maximalIdeal W).comap (Subring.inclusion hVW)

theorem local_subring_inverse_obstruction
    (v : Valuation K Γ) (W : Subring K) [IsLocalRing W]
    (hVW : valuationRingOf v ≤ W)
    (hcontract : contractedMaximalIdeal hVW = maximalIdealOf v)
    {x : K} (hxW : x ∈ W) (hxV : x ∉ valuationRingOf v) : False := by
  sorry

theorem valuationRingOf_maximal_among_dominated_local_subrings
    (v : Valuation K Γ) (W : Subring K) [IsLocalRing W]
    (hVW : valuationRingOf v ≤ W)
    (hcontract : contractedMaximalIdeal hVW = maximalIdealOf v) :
    W = valuationRingOf v := by
  sorry

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
  sorry

theorem discreteUnitValue_inv (v : Valuation K ℤᵐ⁰) (x : Kˣ) :
    discreteUnitValue v x⁻¹ = -discreteUnitValue v x := by
  sorry

/-- The normalized value-zero representative `π⁻ᵛ x`. -/
noncomputable def normalizedElement (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) (x : K) (hx : x ≠ 0) : valuationRingOf v := by
  refine ⟨π ^ (-discreteUnitValue v (Units.mk0 x hx)) * x, ?_⟩
  sorry

/-- The angular component, with zero sent to zero. -/
noncomputable def angularComponent (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) (x : K) : residueFieldOf v := by
  classical
  exact if hx : x = 0 then 0 else
    residueMapOf v (normalizedElement v π hπ x hx)

theorem angularComponent_zero (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) : angularComponent v π hπ 0 = 0 := by
  sorry

theorem discrete_uniformizer_decomposition (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) {x : K} (hx : x ≠ 0) :
    ∃! u : (valuationRingOf v)ˣ,
      x = π ^ discreteUnitValue v (Units.mk0 x hx) * ((u : valuationRingOf v) : K) := by
  sorry

theorem angularComponent_eq_reduction_of_normalizedElement
    (v : Valuation K ℤᵐ⁰) (π : K) (hπ : IsUniformizerFor v π) {x : K} (hx : x ≠ 0) :
    angularComponent v π hπ x = residueMapOf v (normalizedElement v π hπ x hx) := by
  sorry

theorem angularComponent_mul (v : Valuation K ℤᵐ⁰) (π : K)
    (hπ : IsUniformizerFor v π) (x y : K) :
    angularComponent v π hπ (x * y) =
      angularComponent v π hπ x * angularComponent v π hπ y := by
  sorry

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
  sorry

/- A local associated-graded-symbol interface records the coordinate change above. -/

def leadingTermCoordinateRelation (v : Valuation K ℤᵐ⁰)
    (p q : ℤ × residueFieldOf v) : Prop :=
  p.1 = q.1 ∧ ∃ u : (residueFieldOf v)ˣ,
    q.2 = (u : residueFieldOf v) ^ (-p.1) * p.2

noncomputable def leadingTermCoordinateSetoid (v : Valuation K ℤᵐ⁰) :
    Setoid (ℤ × residueFieldOf v) :=
  { r := leadingTermCoordinateRelation v
    iseqv := by exact ⟨by sorry, by sorry, by sorry⟩ }

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
  sorry

/- The Laurent-series realization: first nonzero coefficient and angular component. -/

noncomputable def laurentSeriesValuation (k : Type*) [Field k] :
    Valuation (LaurentSeries k) ℤᵐ⁰ :=
  Valued.v

theorem laurentSeriesResidueEquiv_exists (k : Type*) [Field k] :
    Nonempty (residueFieldOf (laurentSeriesValuation k) ≃+* k) := by
  sorry
noncomputable def laurentSeriesResidueEquiv (k : Type*) [Field k] :
    residueFieldOf (laurentSeriesValuation k) ≃+* k :=
  Classical.choice (laurentSeriesResidueEquiv_exists k)

theorem laurentSeries_value_is_first_nonzero_coefficient
    (k : Type*) [Field k] (f : LaurentSeries k) (hf : f ≠ 0) :
    ∃ N : ℤ, f.order = N ∧ f.coeff N ≠ 0 ∧
      (∀ n : ℤ, n < N → f.coeff n = 0) ∧
      laurentSeriesValuation k f = WithZero.exp (-N) := by
  sorry

theorem laurentSeries_angularComponent_is_first_coefficient
    (k : Type*) [Field k] (π : LaurentSeries k)
    (hπ : IsUniformizerFor (laurentSeriesValuation k) π) {f : LaurentSeries k} (hf : f ≠ 0) :
    (laurentSeriesResidueEquiv k)
        (angularComponent (laurentSeriesValuation k) π hπ f) =
      f.coeff f.order := by
  sorry

/- The rational p-adic realization. -/

theorem padicResidueEquiv_exists (p : ℕ) [Fact p.Prime] :
    Nonempty (residueFieldOf (pValuation p) ≃+* ZMod p) := by
  sorry
noncomputable def padicResidueEquiv (p : ℕ) [Fact p.Prime] :
    residueFieldOf (pValuation p) ≃+* ZMod p :=
  Classical.choice (padicResidueEquiv_exists p)

theorem padic_angularComponent_formula (p : ℕ) [Fact p.Prime]
    (hp : IsUniformizerFor (pValuation p) (p : ℚ))
    (n : ℤ) (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b) :
    padicResidueEquiv p
        (angularComponent (pValuation p) (p : ℚ) hp
          (((p : ℚ) ^ n) * (a : ℚ) / (b : ℚ))) =
      (a : ZMod p) * (b : ZMod p)⁻¹ := by
  sorry

end ResiduesAndAngularComponents

end ValuationsBook.Chapter03
