import Mathlib

namespace ValuationsBook.Chapter02

/-!
# Chapter 2: Valuations

This file is a statement-generation pass for Chapter 2 of *Valuations, DVRs,
and Completions*.  The declarations are deliberately self-contained: they
use Mathlib's `AddValuation` where it has the required interface and introduce
chapter-local names for the constructions that are specific to the exposition.
-/

noncomputable section

open Set Function
open scoped BigOperators LaurentSeries
open HahnSeries Polynomial

/-! ## 2.1. Why values form a group -/

/-- The finite part of an extended value group. -/
abbrev Chapter02FiniteValueGroup (Γ : Type*) := Γ

/-- Adjoin the value `⊤`, representing zero, to a finite value group. -/
abbrev Chapter02ExtendedValueGroup (Γ : Type*) := WithTop Γ

/- The top element is absorbing for addition in the extended group. -/
theorem chapter02_top_add_value
    {Γ : Type*} [Add Γ] (γ : Γ) :
    (γ : WithTop Γ) + ⊤ = ⊤ := by
  sorry

theorem chapter02_add_value_top
    {Γ : Type*} [Add Γ] (γ : Γ) :
    (⊤ : WithTop Γ) + γ = ⊤ := by
  sorry

/-- The ordered-group formulation of the rank-one/Archimedean condition. -/
theorem chapter02_finite_values_are_translation_ordered
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (α β γ : Γ) (h : α ≤ β) : α + γ ≤ β + γ := by
  sorry

theorem chapter02_every_finite_value_is_below_infinity
    {Γ : Type*} [LinearOrder Γ] (γ : Γ) : (γ : WithTop Γ) < ⊤ := by
  sorry

def Chapter02ArchimedeanValueGroup (Γ : Type*)
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] : Prop :=
  ∀ α β : Γ, 0 < α → 0 < β → ∃ n : ℕ, 1 ≤ n ∧ β ≤ n • α

theorem chapter02_archimedean_value_group_iff
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] :
    Chapter02ArchimedeanValueGroup Γ ↔ Archimedean Γ := by
  sorry

theorem chapter02_archimedean_values_embed_in_reals
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (hΓ : Chapter02ArchimedeanValueGroup Γ) :
    ∃ f : Γ →+o ℝ, Function.Injective f := by
  sorry

/-- A convenient name for the lexicographically ordered copy of `ℤ × ℤ`. -/
abbrev Chapter02LexicographicIntegers := ℤ ×ₗ ℤ

theorem chapter02_lexicographic_order_formula (a b c d : ℤ) :
    toLex (a, b) < toLex (c, d) ↔
      a < c ∨ (a = c ∧ b < d) := by
  sorry

theorem chapter02_lex_second_coordinate_refines_first (n : ℤ) :
    toLex (0, 1) < toLex (1, n) := by
  sorry

theorem chapter02_lexicographic_integers_nonarchimedean :
    ¬ Chapter02ArchimedeanValueGroup Chapter02LexicographicIntegers := by
  sorry

theorem chapter02_lexicographic_integers_have_coarse_and_refining_coordinates :
    ∃ q : Chapter02LexicographicIntegers →+o ℤ,
      (∀ a b : ℤ, q (toLex (a, b)) = a) ∧
      (∀ n : ℤ, q (toLex (0, n)) = 0) := by
  sorry

/-- The subgroup `ℤ + √2 ℤ` of the real line. -/
def Chapter02SqrtTwoIntegerSubgroup : AddSubgroup ℝ :=
  AddSubgroup.closure ({(1 : ℝ), Real.sqrt 2} : Set ℝ)

theorem chapter02_sqrt_two_integer_subgroup_is_archimedean :
    Chapter02ArchimedeanValueGroup (↥Chapter02SqrtTwoIntegerSubgroup) := by
  sorry

theorem chapter02_rank_one_need_not_be_discrete :
    Chapter02ArchimedeanValueGroup ℚ ∧
      DenselyOrdered ℚ ∧
      ¬ ∃ d : ℚ, 0 < d ∧ ∀ x : ℚ, 0 < x → d ≤ x := by
  sorry

theorem chapter02_lexicographic_group_has_no_real_order_embedding :
    ¬ ∃ f : Chapter02LexicographicIntegers →+o ℝ, Function.Injective f := by
  sorry

/-! ## 2.2. Additive valuations -/

/-- Chapter 2's additive valuation interface, using Mathlib's definition. -/
abbrev Chapter02AdditiveValuation (R Γ : Type*) [Ring R]
    [LinearOrderedAddCommMonoidWithTop Γ] := AddValuation R Γ

theorem chapter02_additive_valuation_axioms
    {R Γ : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) :
    v 0 = (⊤ : Γ) ∧
      v 1 = 0 ∧
      (∀ x y : R, v (x * y) = v x + v y) ∧
      (∀ x y : R, min (v x) (v y) ≤ v (x + y)) := by
  sorry

theorem chapter02_additive_valuation_zero_is_infinity
    {R Γ : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) : v 0 = (⊤ : Γ) := by
  sorry

theorem chapter02_additive_valuation_one_is_zero
    {R Γ : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) : v 1 = 0 := by
  sorry

def Chapter02Support {R Γ : Type*} [CommRing R]
    [LinearOrderedAddCommMonoidWithTop Γ] (v : AddValuation R Γ) : Ideal R :=
  AddValuation.supp v

theorem chapter02_support_characterization
    {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) (x : R) :
    x ∈ Chapter02Support v ↔ v x = (⊤ : Γ) := by
  sorry

theorem chapter02_support_closed_under_addition
    {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) {x y : R}
    (hx : x ∈ Chapter02Support v) (hy : y ∈ Chapter02Support v) :
    x + y ∈ Chapter02Support v := by
  sorry

theorem chapter02_support_absorbs_multiplication
    {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) {x y : R}
    (hx : x ∈ Chapter02Support v) :
    x * y ∈ Chapter02Support v := by
  sorry

theorem chapter02_support_product_characterization
    {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    [Nontrivial (Multiplicative Γᵒᵈ)] [NoZeroDivisors (Multiplicative Γᵒᵈ)]
    (v : AddValuation R Γ) (x y : R) :
    x * y ∈ Chapter02Support v ↔
      x ∈ Chapter02Support v ∨ y ∈ Chapter02Support v := by
  sorry

theorem chapter02_support_is_prime
    {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    [Nontrivial (Multiplicative Γᵒᵈ)] [NoZeroDivisors (Multiplicative Γᵒᵈ)]
    (v : AddValuation R Γ) :
    (Chapter02Support v).IsPrime := by
  sorry

theorem chapter02_field_support_is_zero
    {K Γ : Type*} [Field K] [LinearOrderedAddCommMonoidWithTop Γ]
    [Nontrivial (Multiplicative Γᵒᵈ)] [NoZeroDivisors (Multiplicative Γᵒᵈ)]
    (v : AddValuation K Γ) : Chapter02Support v = ⊥ := by
  sorry

/-- The finite value read from a nonzero element of a valued field. -/
def Chapter02FiniteValueOfNonzero
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] [Nontrivial Γ]
    (v : AddValuation K (WithTop Γ)) (x : K) (hx : x ≠ 0) : Γ :=
  (v x).untop ((AddValuation.ne_top_iff v).2 hx)

/-- Restriction of a field valuation to `Kˣ`; the codomain is multiplicative
notation for the additive value group. -/
noncomputable def Chapter02FieldUnitValueHom
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] [Nontrivial Γ]
    (v : AddValuation K (WithTop Γ)) : Kˣ →* Multiplicative Γ :=
  { toFun := fun u =>
      Multiplicative.ofAdd
        (Chapter02FiniteValueOfNonzero v (u : K) (Units.ne_zero u))
    map_one' := by sorry
    map_mul' := by sorry }

def Chapter02UnitHomSumInequality
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (φ : Kˣ →* Multiplicative Γ) : Prop :=
  ∀ (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0),
    min (Multiplicative.toAdd (φ (Units.mk0 x hx)))
        (Multiplicative.toAdd (φ (Units.mk0 y hy))) ≤
      Multiplicative.toAdd (φ (Units.mk0 (x + y) hxy))

def Chapter02ExtensionValue
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (φ : Kˣ →* Multiplicative Γ) (x : K) :
    WithTop Γ := by
  classical
  exact if hx : x = 0 then ⊤
  else ((Multiplicative.toAdd (φ (Units.mk0 x hx)) : Γ) : WithTop Γ)

theorem chapter02_field_valuation_restricts_to_units
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] [Nontrivial Γ]
    (v : AddValuation K (WithTop Γ)) :
    ∃ φ : Kˣ →* Multiplicative Γ, ∀ (x : K) (hx : x ≠ 0),
      Multiplicative.toAdd (φ (Units.mk0 x hx)) =
        Chapter02FiniteValueOfNonzero v x hx := by
  sorry

theorem chapter02_unit_hom_converse
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (φ : Kˣ →* Multiplicative Γ)
    (hφ : Chapter02UnitHomSumInequality φ) :
    ∃! v : AddValuation K (WithTop Γ),
      ∀ x : K, v x = Chapter02ExtensionValue φ x := by
  sorry

theorem chapter02_field_valuation_is_a_group_hom_on_nonzero_elements
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] [Nontrivial Γ]
    (v : AddValuation K (WithTop Γ)) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    Chapter02FiniteValueOfNonzero v (x * y) (mul_ne_zero hx hy) =
      Chapter02FiniteValueOfNonzero v x hx +
        Chapter02FiniteValueOfNonzero v y hy := by
  sorry

def Chapter02SupportQuotientValuation
    {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) :
    AddValuation (R ⧸ Chapter02Support v) Γ := by
  exact AddValuation.onQuot v (by
    simpa [Chapter02Support])

theorem chapter02_support_quotient_is_a_domain
    {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    [Nontrivial (Multiplicative Γᵒᵈ)] [NoZeroDivisors (Multiplicative Γᵒᵈ)]
    (v : AddValuation R Γ) :
    IsDomain (R ⧸ Chapter02Support v) := by
  sorry

theorem chapter02_valuation_factors_through_support
    {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) :
    ∀ x : R, v x = Chapter02SupportQuotientValuation v (Ideal.Quotient.mk _ x) := by
  sorry

theorem chapter02_fraction_field_extension
    {A Γ : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (v : AddValuation A (WithTop Γ)) :
    ∃! w : AddValuation (FractionRing A) (WithTop Γ),
      (∀ a : A, w (algebraMap A (FractionRing A) a) = v a) ∧
      (∀ (a b : A) (hb : b ≠ 0),
        w (algebraMap A (FractionRing A) a /
            algebraMap A (FractionRing A) b) = v a - v b) := by
  sorry

def Chapter02SurjectiveValuation
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) : Prop :=
  ∀ γ : Γ, ∃ x : K, x ≠ 0 ∧ v x = (γ : WithTop Γ)

def Chapter02AttainedValueSet
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) : Set Γ :=
  {γ | ∃ x : K, x ≠ 0 ∧ v x = (γ : WithTop Γ)}

noncomputable def Chapter02ValueGroup
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) : AddSubgroup Γ :=
  AddSubgroup.closure (Chapter02AttainedValueSet v)

theorem chapter02_value_group_carrier
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) :
    (Chapter02ValueGroup v : Set Γ) = Chapter02AttainedValueSet v := by
  sorry

theorem chapter02_surjective_iff_value_group_is_ambient
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) :
    Chapter02SurjectiveValuation v ↔ Chapter02ValueGroup v = ⊤ := by
  sorry

/-! ## 2.3. The decisive equality -/

theorem chapter02_unequal_values_do_not_cancel
    {R Γ : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) {x y : R} (hxy : v x ≠ v y) :
    v (x + y) = min (v x) (v y) := by
  sorry

theorem chapter02_strictly_smallest_term_controls_finite_sum
    {R Γ ι : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    [DecidableEq ι] (v : AddValuation R Γ) (s : Finset ι) (f : ι → R) (j : ι)
    (hj : j ∈ s)
    (hmin : ∀ i ∈ s, i ≠ j → v (f j) < v (f i)) :
    v (∑ i ∈ s, f i) = v (f j) := by
  sorry

theorem chapter02_zero_finite_sum_has_repeated_minimum
    {R Γ ι : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    [DecidableEq ι] (v : AddValuation R Γ) (s : Finset ι) (f : ι → R)
    (hs : s.Nonempty) (hz : ∑ i ∈ s, f i = 0)
    (hnz : ∀ i ∈ s, f i ≠ 0) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧
      v (f i) = v (f j) ∧ ∀ k ∈ s, v (f i) ≤ v (f k) := by
  sorry

theorem chapter02_minimum_occurs_twice_in_zero_sum
    {R Γ ι : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    [DecidableEq ι] (v : AddValuation R Γ) (s : Finset ι) (f : ι → R)
    (hz : ∑ i ∈ s, f i = 0) (hunique : ∃ j ∈ s,
      ∀ i ∈ s, i ≠ j → v (f j) < v (f i)) :
    ¬ (∀ i ∈ s, f i ≠ 0) := by
  sorry

/-! ## 2.4. Equivalence and normalization -/

def Chapter02EquivalentValuations
    {R Γ Δ : Type*} [Ring R]
    [LinearOrderedAddCommMonoidWithTop Γ]
    [LinearOrderedAddCommMonoidWithTop Δ]
    (v : AddValuation R Γ) (w : AddValuation R Δ) : Prop :=
  AddValuation.IsEquiv v w

theorem chapter02_equivalent_iff_same_comparisons
    {R Γ Δ : Type*} [Ring R]
    [LinearOrderedAddCommMonoidWithTop Γ]
    [LinearOrderedAddCommMonoidWithTop Δ]
    (v : AddValuation R Γ) (w : AddValuation R Δ) :
    Chapter02EquivalentValuations v w ↔
      ∀ x y : R, v x ≤ v y ↔ w x ≤ w y := by
  sorry

def Chapter02OrderRelabelValue
    {Γ Δ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    (e : Γ ≃+o Δ) (γ : WithTop Γ) : WithTop Δ :=
  if hγ : γ = ⊤ then ⊤ else (e (γ.untop hγ) : WithTop Δ)

def Chapter02EquivalentByOrderedRelabeling
    {K Γ Δ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    (v : AddValuation K (WithTop Γ))
    (w : AddValuation K (WithTop Δ)) : Prop :=
  ∃ e : Γ ≃+o Δ, ∀ x : K, w x = Chapter02OrderRelabelValue e (v x)

theorem chapter02_order_relabeling_implies_equivalence
    {K Γ Δ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    {v : AddValuation K (WithTop Γ)} {w : AddValuation K (WithTop Δ)}
    (h : Chapter02EquivalentByOrderedRelabeling v w) :
    Chapter02EquivalentValuations v w := by
  sorry

theorem chapter02_equivalence_and_surjectivity_give_order_relabeling
    {K Γ Δ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    {v : AddValuation K (WithTop Γ)} {w : AddValuation K (WithTop Δ)}
    (hv : Chapter02SurjectiveValuation v)
    (hw : Chapter02SurjectiveValuation w)
    (he : Chapter02EquivalentValuations v w) :
    Chapter02EquivalentByOrderedRelabeling v w := by
  sorry

def Chapter02DiscreteValueGroup (Γ : Type*)
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] : Prop :=
  Nonempty (Γ ≃+o ℤ)

theorem chapter02_discrete_value_group_has_unique_smallest_positive
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (hΓ : Chapter02DiscreteValueGroup Γ) :
    ∃! π : Γ, 0 < π ∧ ∀ γ : Γ, 0 < γ → π ≤ γ := by
  sorry

noncomputable def Chapter02NormalizedValuation
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (e : Γ ≃+o ℤ) (v : AddValuation K (WithTop Γ)) :
    AddValuation K (WithTop ℤ) := by
  exact v.map (AddMonoidHom.withTopMap (e : Γ →+ ℤ)) (by simp) (by sorry)

theorem chapter02_normalized_valuation_uses_unit_step
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (e : Γ ≃+o ℤ) (v : AddValuation K (WithTop Γ))
    {x : K} {π : Γ} (hx : x ≠ 0)
    (hπ : 0 < π) (hleast : ∀ γ : Γ, 0 < γ → π ≤ γ)
    (hv : v x = (π : WithTop Γ)) :
    Chapter02NormalizedValuation e v x = (1 : WithTop ℤ) := by
  sorry

noncomputable def Chapter02TwiceValuation
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : AddValuation K (WithTop ℤ) :=
  AddValuation.of (fun x => 2 • v x) (by sorry) (by simp)
    (by sorry) (by sorry)

theorem chapter02_twice_valuation_formula
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) (x : K) :
    Chapter02TwiceValuation v x = 2 • v x := by
  sorry

def Chapter02ValuationRing
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) : Subring K :=
  { carrier := {x | 0 ≤ v x}
    zero_mem' := by sorry
    one_mem' := by sorry
    add_mem' := by sorry
    mul_mem' := by sorry
    neg_mem' := by sorry
  }

theorem chapter02_equivalent_scalings_have_same_valuation_ring
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) :
    Chapter02ValuationRing (Chapter02TwiceValuation v) =
      Chapter02ValuationRing v := by
  sorry

theorem chapter02_ramification_labels_depend_on_normalization
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
    {x : K} (hx : v x = (1 : WithTop ℤ)) :
    Chapter02TwiceValuation v x = (2 : WithTop ℤ) ∧
      Chapter02TwiceValuation v x ≠ v x := by
  sorry

def Chapter02ConvexAddSubgroup
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (H : AddSubgroup Γ) : Prop :=
  ∀ ⦃a b c : Γ⦄, a ≤ b → b ≤ c → a ∈ H → c ∈ H → b ∈ H

def Chapter02ConvexQuotientInterface
    {Γ Λ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (H : AddSubgroup Γ) (q : Γ →+o Λ) : Prop :=
  Function.Surjective q ∧
    (∀ γ : Γ, q γ = 0 ↔ γ ∈ H) ∧
    ∀ {Ω : Type*} [AddCommGroup Ω] [LinearOrder Ω]
      [IsOrderedAddMonoid Ω] (f : Γ →+o Ω),
      (∀ h : Γ, h ∈ H → f h = 0) →
        ∃! g : Λ →+o Ω, f = g.comp q

def Chapter02CoarsenedValuation
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (q : Γ →+o Λ) (v : AddValuation K (WithTop Γ)) :
    AddValuation K (WithTop Λ) := by
  exact v.map (AddMonoidHom.withTopMap (q : Γ →+ Λ)) (by simp) (by sorry)

theorem chapter02_convex_subgroup_gives_ordered_quotient
    {Γ Λ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (H : AddSubgroup Γ) (hH : Chapter02ConvexAddSubgroup H)
    (q : Γ →+o Λ) (hq : Function.Surjective q)
    (hker : ∀ γ : Γ, q γ = 0 ↔ γ ∈ H)
    (horder : ∀ a b : Γ, q a ≤ q b ↔
      ∃ h : H, a ≤ b + (h : Γ)) :
    Chapter02ConvexQuotientInterface H q := by
  sorry

theorem chapter02_coarsening_is_composition_with_quotient
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (H : AddSubgroup Γ) (q : Γ →+o Λ)
    (hQ : Chapter02ConvexQuotientInterface H q)
    (v : AddValuation K (WithTop Γ)) :
    ∀ x : K, Chapter02CoarsenedValuation q v x =
      (if h : v x = ⊤ then ⊤ else (q ((v x).untop h) : WithTop Λ)) := by
  sorry

def Chapter02LexSecondCoordinateSubgroup :
    AddSubgroup Chapter02LexicographicIntegers :=
  { carrier := {p | (ofLex p).1 = 0}
    zero_mem' := by simp
    add_mem' := by
      intro p q hp hq
      simp_all
    neg_mem' := by
      intro p hp
      simp_all }

def Chapter02LexFirstCoordinate :
    Chapter02LexicographicIntegers →+o ℤ :=
  { toFun := fun p => (ofLex p).1
    map_zero' := by simp
    map_add' := by
      intro p q
      simp
    monotone' := Prod.Lex.monotone_fst_ofLex }

theorem chapter02_lex_second_coordinate_is_convex :
    Chapter02ConvexAddSubgroup Chapter02LexSecondCoordinateSubgroup := by
  sorry

theorem chapter02_lex_quotient_remembers_first_coordinate :
    Function.Surjective Chapter02LexFirstCoordinate ∧
      ∀ p : Chapter02LexicographicIntegers,
        Chapter02LexFirstCoordinate p = 0 ↔
          p ∈ Chapter02LexSecondCoordinateSubgroup := by
  sorry

theorem chapter02_discrete_rank_one_has_no_proper_coarsening
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (hΓ : Chapter02DiscreteValueGroup Γ) (H : AddSubgroup Γ)
    (hH : Chapter02ConvexAddSubgroup H) : H = ⊥ ∨ H = ⊤ := by
  sorry

/-! ## 2.5. From additive values to multiplicative absolute values -/

def Chapter02RealSizeFromValuation
    {K : Type*} [Field K] (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (v : AddValuation K (WithTop ℝ)) (x : K) : ℝ :=
  if hx : v x = ⊤ then 0 else Real.rpow c ((v x).untop hx)

theorem chapter02_real_size_of_zero
    {K : Type*} [Field K] {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (v : AddValuation K (WithTop ℝ)) :
    Chapter02RealSizeFromValuation c hc hc1 v 0 = 0 := by
  sorry

theorem chapter02_real_size_of_one
    {K : Type*} [Field K] {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (v : AddValuation K (WithTop ℝ)) :
    Chapter02RealSizeFromValuation c hc hc1 v 1 = 1 := by
  sorry

theorem chapter02_real_size_is_multiplicative
    {K : Type*} [Field K] {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (v : AddValuation K (WithTop ℝ)) (x y : K) :
    Chapter02RealSizeFromValuation c hc hc1 v (x * y) =
      Chapter02RealSizeFromValuation c hc hc1 v x *
        Chapter02RealSizeFromValuation c hc hc1 v y := by
  sorry

theorem chapter02_real_size_is_ultrametric
    {K : Type*} [Field K] {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (v : AddValuation K (WithTop ℝ)) (x y : K) :
    Chapter02RealSizeFromValuation c hc hc1 v (x + y) ≤
      max (Chapter02RealSizeFromValuation c hc hc1 v x)
        (Chapter02RealSizeFromValuation c hc hc1 v y) := by
  sorry

def Chapter02PadicAdditiveValuation (p : ℕ) [Fact p.Prime] :
    AddValuation ℚ (WithTop ℤ) :=
  AddValuation.of
    (fun x : ℚ => if x = 0 then ⊤ else (padicValRat p x : WithTop ℤ))
    (by simp) (by simp) (by sorry) (by sorry)

def Chapter02PadicAbsoluteValue (p : ℕ) [Fact p.Prime] (x : ℚ) : ℝ :=
  if x = 0 then 0 else Real.rpow (p : ℝ) (-(padicValRat p x : ℝ))
theorem chapter02_padic_value_of_p
    (p : ℕ) [Fact p.Prime] :
    Chapter02PadicAdditiveValuation p p = (1 : WithTop ℤ) := by
  sorry

theorem chapter02_padic_absolute_value_of_p
    (p : ℕ) [Fact p.Prime] :
    Chapter02PadicAbsoluteValue p p = (p : ℝ)⁻¹ := by
  sorry


theorem chapter02_padic_absolute_value_of_p_pow_times_prime_to_p
    (p n : ℕ) [Fact p.Prime] (a b : ℤ) (hb : b ≠ 0)
    (ha : ¬ (p : ℤ) ∣ a) (hbp : ¬ (p : ℤ) ∣ b) :
    Chapter02PadicAbsoluteValue p
        (((p : ℚ) ^ n) * (a : ℚ) / (b : ℚ)) =
      Real.rpow (p : ℝ) (-(n : ℝ)) := by
  sorry

def Chapter02IsUltrametricAbsoluteValue {K : Type*} [Ring K]
    (f : K → ℝ) : Prop :=
  ∀ x y : K, f (x + y) ≤ max (f x) (f y)

def Chapter02LogarithmicValueFromAbsoluteValue
    {K : Type*} [Field K] (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (f : K → ℝ) (x : K) : WithTop ℝ := by
  classical
  exact if hx : x = 0 then ⊤ else (Real.log (f x) / Real.log c : ℝ)

theorem chapter02_ultrametric_absolute_value_gives_additive_value
    {K : Type*} [Field K] (f : AbsoluteValue K ℝ)
    (hf : Chapter02IsUltrametricAbsoluteValue (f : K → ℝ))
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ∃! v : AddValuation K (WithTop ℝ),
      ∀ x : K, v x =
        Chapter02LogarithmicValueFromAbsoluteValue c hc hc1 (f : K → ℝ) x := by
  sorry

def Chapter02PositiveValueRescaling
    {K : Type*} [Field K] (v w : K → WithTop ℝ) : Prop := by
  classical
  exact ∃ r : ℝ, 0 < r ∧ ∀ x : K,
    w x = if h : v x = ⊤ then ⊤ else (r * (v x).untop h : WithTop ℝ)

theorem chapter02_changing_the_base_rescales_values
    {K : Type*} [Field K] (f : AbsoluteValue K ℝ)
    (hf : Chapter02IsUltrametricAbsoluteValue (f : K → ℝ))
    {c d : ℝ} (hc : 0 < c) (hc1 : c < 1) (hd : 0 < d) (hd1 : d < 1) :
    Chapter02PositiveValueRescaling
      (fun x => Chapter02LogarithmicValueFromAbsoluteValue c hc hc1 (f : K → ℝ) x)
      (fun x => Chapter02LogarithmicValueFromAbsoluteValue d hd hd1 (f : K → ℝ) x) := by
  sorry

theorem chapter02_positive_rescaling_preserves_comparisons
    {K : Type*} [Field K] (v w : K → WithTop ℝ)
    (h : Chapter02PositiveValueRescaling v w) (x y : K) :
    v x ≤ v y ↔ w x ≤ w y := by
  sorry

/-! ## 2.6. Trivial valuations and a failure of the ordinary absolute value -/

def Chapter02TrivialAdditiveValuation {K : Type*} [Field K] :
    AddValuation K (WithTop ℤ) := by
  classical
  exact AddValuation.of (fun x : K => if x = 0 then ⊤ else 0)
    (by simp) (by simp) (by sorry) (by sorry)

theorem chapter02_trivial_valuation_ring_is_the_whole_field
    {K : Type*} [Field K] :
    Chapter02ValuationRing (Chapter02TrivialAdditiveValuation :
      AddValuation K (WithTop ℤ)) = (⊤ : Subring K) := by
  sorry

def Chapter02TrivialAbsoluteValue {K : Type*} [Field K] (x : K) : ℝ := by
  classical
  exact if x = 0 then 0 else 1

theorem chapter02_trivial_absolute_value_is_one_off_zero
    {K : Type*} [Field K] {x : K} (hx : x ≠ 0) :
    Chapter02TrivialAbsoluteValue x = 1 := by
  sorry

def Chapter02TrivialDistance {K : Type*} [Field K] (x y : K) : ℝ := by
  classical
  exact if x = y then 0 else 1

theorem chapter02_trivial_distance_characterization
    {K : Type*} [Field K] (x y : K) :
    Chapter02TrivialDistance x y = 0 ↔ x = y := by
  sorry

theorem chapter02_trivial_distance_of_distinct_points
    {K : Type*} [Field K] {x y : K} (hxy : x ≠ y) :
    Chapter02TrivialDistance x y = 1 := by
  sorry

def Chapter02OrdinaryRationalAbsoluteValue (x : ℚ) : ℝ :=
  |(x : ℝ)|

theorem chapter02_ordinary_absolute_value_fails_ultrametricity :
    ¬ Chapter02IsUltrametricAbsoluteValue Chapter02OrdinaryRationalAbsoluteValue := by
  sorry

theorem chapter02_ordinary_absolute_value_one_plus_one :
    Chapter02OrdinaryRationalAbsoluteValue (1 + 1) = 2 ∧
      Chapter02OrdinaryRationalAbsoluteValue 1 = 1 := by
  sorry

theorem chapter02_rational_completion_is_real_model :
    Nonempty (UniformSpace.Completion ℚ ≃ₜ ℝ) := by
  sorry

def Chapter02UltrametricDistance {K : Type*} [Ring K]
    (f : K → ℝ) (x y : K) : ℝ := f (x - y)

theorem chapter02_ultrametric_longest_side
    {K : Type*} [Ring K] (f : K → ℝ)
    (hf : Chapter02IsUltrametricAbsoluteValue f) (x y z : K) :
    Chapter02UltrametricDistance f x z ≤
      max (Chapter02UltrametricDistance f x y)
        (Chapter02UltrametricDistance f y z) := by
  sorry

theorem chapter02_ultrametric_series_criterion
    {K : Type*} [NormedAddCommGroup K] [CompleteSpace K]
    (htri : ∀ x y : K, ‖x + y‖ ≤ max ‖x‖ ‖y‖) (u : ℕ → K)
    (hu : Filter.Tendsto (fun n => ‖u n‖) atTop (nhds 0)) :
    Summable u := by
  sorry

/-! ## 2.7. Gauss valuations and two-stage examples -/

def Chapter02WeightedCoefficientValue
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ)
    (a : K) (i : ℕ) : WithTop Λ :=
  if ha : v a = ⊤ then ⊤
  else (e ((v a).untop ha) + i • α : Λ)

def Chapter02GaussValuationFunction
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ)
    (f : Polynomial K) : WithTop Λ :=
  if hf : f.support.Nonempty then
    f.support.inf' hf (fun i => Chapter02WeightedCoefficientValue v e α (f.coeff i) i)
  else ⊤

theorem chapter02_gauss_valuation_sum_inequality
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ)
    (f g : Polynomial K) :
    min (Chapter02GaussValuationFunction v e α f)
        (Chapter02GaussValuationFunction v e α g) ≤
      Chapter02GaussValuationFunction v e α (f + g) := by
  sorry

theorem chapter02_gauss_valuation_is_multiplicative
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ)
    (f g : Polynomial K) :
    Chapter02GaussValuationFunction v e α (f * g) =
      Chapter02GaussValuationFunction v e α f +
        Chapter02GaussValuationFunction v e α g := by
  sorry

noncomputable def Chapter02GaussValuationOnRationalFunctions
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ) :
    RatFunc K → WithTop Λ := by
  classical
  exact fun x => if hx : x = 0 then ⊤ else
    Chapter02GaussValuationFunction v e α x.num -
      Chapter02GaussValuationFunction v e α x.denom

theorem chapter02_gauss_valuation_on_quotients
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ)
    (f g : Polynomial K) (hg : g ≠ 0) :
    Chapter02GaussValuationOnRationalFunctions v e α
        (algebraMap (Polynomial K) (RatFunc K) f /
          algebraMap (Polynomial K) (RatFunc K) g) =
      Chapter02GaussValuationFunction v e α f -
        Chapter02GaussValuationFunction v e α g := by
  sorry

theorem chapter02_gauss_at_zero_is_coefficient_minimum
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (f : Polynomial K) :
    Chapter02GaussValuationFunction v e 0 f =
      if hf : f.support.Nonempty then
        f.support.inf' hf (fun i =>
          if ha : v (f.coeff i) = ⊤ then ⊤
          else (e ((v (f.coeff i)).untop ha) : WithTop Λ))
      else ⊤ := by
  sorry

theorem chapter02_gauss_variable_has_prescribed_value
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ) :
    Chapter02GaussValuationFunction v e α Polynomial.X = (α : WithTop Λ) := by
  sorry

theorem chapter02_gauss_positive_parameter_makes_the_variable_small
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) {α : Λ} (hα : 0 < α) :
    0 < Chapter02GaussValuationFunction v e α Polynomial.X := by
  sorry

def Chapter02GaussMinimalIndices
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ)
    (f : Polynomial K) : Set ℕ :=
  {i | i ∈ f.support ∧
    Chapter02WeightedCoefficientValue v e α (f.coeff i) i =
      Chapter02GaussValuationFunction v e α f}

theorem chapter02_gauss_minimum_is_attained
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ)
    {f : Polynomial K} (hf : f ≠ 0) :
    (Chapter02GaussMinimalIndices v e α f).Nonempty := by
  sorry

abbrev Chapter02ValuationSubring
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) : Subring K :=
  (AddValuation.toValuation v).integer

def Chapter02ValuationMaximalIdeal
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) :
    Ideal (Chapter02ValuationSubring v) :=
  IsLocalRing.maximalIdeal (Chapter02ValuationSubring v)

abbrev Chapter02ResidueField
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) :=
  (Chapter02ValuationSubring v) ⧸ Chapter02ValuationMaximalIdeal v

noncomputable def Chapter02ResidueOfIntegral
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) (x : K) (hx : 0 ≤ v x) :
    Chapter02ResidueField v :=
  Ideal.Quotient.mk _ ⟨x, by sorry⟩

theorem chapter02_gauss_residue_remembers_scaled_polynomial
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ)
    {f : Polynomial K} (hf : f ≠ 0) :
    ∃ i ∈ f.support,
      (∀ j : ℕ, j ∈ f.support →
        v (f.coeff i) ≤ v (f.coeff j)) ∧
      Chapter02WeightedCoefficientValue v e 0 (f.coeff i) i =
        Chapter02GaussValuationFunction v e 0 f ∧
      ∃ g : Polynomial (Chapter02ResidueField v),
        g.coeff i = 1 ∧
        g.support ⊆ f.support ∧
        ∀ j : ℕ, j ∈ f.support →
          g.coeff j = Chapter02ResidueOfIntegral v
            ((f.coeff j) / (f.coeff i)) (by sorry) := by
  sorry

theorem chapter02_gauss_residue_construction_requires_a_unit_coefficient
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) {a : K} (ha : a ≠ 0) :
    ∃ s : K, s ≠ 0 ∧ v (s * a) = 0 ∧ v s + v a = 0 := by
  sorry

/-! ### Two-stage valuation on Laurent series -/

abbrev Chapter02TwoStageValueGroup (Γ : Type*) := ℤ ×ₗ Γ

def Chapter02TwoStageLaurentValuation
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ]
    (v : AddValuation K (WithTop Γ)) :
    LaurentSeries K → WithTop (Chapter02TwoStageValueGroup Γ) := by
  classical
  exact fun f => if hf : f = 0 then ⊤ else
    ((toLex
      (f.order, (v f.leadingCoeff).untop (by
        exact (AddValuation.ne_top_iff v).2
          (HahnSeries.leadingCoeff_ne_zero.mpr hf))) :
      Chapter02TwoStageValueGroup Γ) :
      WithTop (Chapter02TwoStageValueGroup Γ))

theorem chapter02_two_stage_value_of_zero
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ)) :
    Chapter02TwoStageLaurentValuation v 0 = ⊤ := by
  sorry

theorem chapter02_two_stage_value_is_multiplicative
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ))
    (f g : LaurentSeries K) :
    Chapter02TwoStageLaurentValuation v (f * g) =
      Chapter02TwoStageLaurentValuation v f +
        Chapter02TwoStageLaurentValuation v g := by
  sorry

theorem chapter02_two_stage_value_satisfies_sum_inequality
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ))
    (f g : LaurentSeries K) :
    min (Chapter02TwoStageLaurentValuation v f)
        (Chapter02TwoStageLaurentValuation v g) ≤
      Chapter02TwoStageLaurentValuation v (f + g) := by
  sorry

theorem chapter02_positive_T_order_outweighs_every_coefficient_value
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    {n : ℤ} (hn : 0 < n) (γ : Γ) :
    toLex (0, γ) < toLex (n, 0) := by
  sorry

theorem chapter02_two_stage_order_is_lexicographic
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ))
    {f : LaurentSeries K} (hf : f ≠ 0) :
    ∃ n : ℤ, ∃ a : K, a ≠ 0 ∧ n = f.order ∧ a = f.leadingCoeff ∧
      Chapter02TwoStageLaurentValuation v f =
        ((toLex (n, (v a).untop (by
          exact (AddValuation.ne_top_iff v).2 (by sorry))) :
          Chapter02TwoStageValueGroup Γ) :
          WithTop (Chapter02TwoStageValueGroup Γ)) := by
  sorry

def Chapter02LaurentTAdicOrder {K : Type*} [Zero K]
    (f : LaurentSeries K) : WithTop ℤ := by
  classical
  exact if hf : f = 0 then ⊤ else (f.order : WithTop ℤ)

theorem chapter02_two_stage_coarsening_is_T_adic_order
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ))
    {f : LaurentSeries K} (hf : f ≠ 0) :
    (ofLex
      ((Chapter02TwoStageLaurentValuation v f).untop (by sorry))).1 = f.order := by
  sorry

def Chapter02ConstantLaurentSeries {K : Type*} [Zero K] (a : K) : LaurentSeries K :=
  HahnSeries.single 0 a

theorem chapter02_two_stage_constant_series_recovers_coefficient_value
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ)) {a : K} (ha : a ≠ 0) :
    (ofLex
      ((Chapter02TwoStageLaurentValuation v (Chapter02ConstantLaurentSeries a)).untop
        (by sorry))).2 = (v a).untop ((AddValuation.ne_top_iff v).2 ha) := by
  sorry

theorem chapter02_two_stage_is_a_higher_rank_value_group
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] :
    ¬ ∃ f : Chapter02TwoStageValueGroup Γ →+o ℝ, Function.Injective f := by
  sorry

theorem chapter02_two_stage_constant_subfield_has_original_valuation
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ)) {a : K} (ha : a ≠ 0) :
    (ofLex
      ((Chapter02TwoStageLaurentValuation v (Chapter02ConstantLaurentSeries a)).untop
        (by sorry))).2 = (v a).untop ((AddValuation.ne_top_iff v).2 ha) := by
  sorry

end
end ValuationsBook.Chapter02
