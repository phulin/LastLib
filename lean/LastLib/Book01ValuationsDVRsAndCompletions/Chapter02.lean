import Mathlib.Algebra.Order.Ring.Archimedean
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Real.Embedding
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.HahnSeries.Basic
import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Quotient
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.UniformSpace.CompareReals
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter02

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
  simp

theorem chapter02_add_value_top
    {Γ : Type*} [Add Γ] (γ : Γ) :
    (⊤ : WithTop Γ) + γ = ⊤ := by
  simp

/-- The ordered-group formulation of the rank-one/Archimedean condition. -/
theorem chapter02_finite_values_are_translation_ordered
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (α β γ : Γ) (h : α ≤ β) : α + γ ≤ β + γ := by
  exact add_le_add_left h γ

theorem chapter02_every_finite_value_is_below_infinity
    {Γ : Type*} [LinearOrder Γ] (γ : Γ) : (γ : WithTop Γ) < ⊤ := by
  exact WithTop.coe_lt_top γ

def Chapter02ArchimedeanValueGroup (Γ : Type*)
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] : Prop :=
  ∀ α β : Γ, 0 < α → 0 < β → ∃ n : ℕ, 1 ≤ n ∧ β ≤ n • α

theorem chapter02_archimedean_value_group_iff
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] :
    Chapter02ArchimedeanValueGroup Γ ↔ Archimedean Γ := by
  constructor
  · intro h
    exact ⟨fun x {y} hy => by
      by_cases hx : x ≤ 0
      · exact ⟨0, by simpa using hx⟩
      · obtain ⟨n, hn, hxy⟩ := h y x hy (lt_of_not_ge hx)
        exact ⟨n, hxy⟩⟩
  · intro h α β hα hβ
    obtain ⟨n, hn⟩ := h.arch β hα
    refine ⟨n, ?_, hn⟩
    by_contra hnot
    have hn0 : n = 0 := by omega
    subst n
    have hn' : β ≤ (0 : Γ) := by simpa using hn
    exact (not_le_of_gt hβ) hn'

theorem chapter02_archimedean_values_embed_in_reals
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (hΓ : Chapter02ArchimedeanValueGroup Γ) :
    ∃ f : Γ →+o ℝ, Function.Injective f := by
  letI : Archimedean Γ := (chapter02_archimedean_value_group_iff).1 hΓ
  exact Archimedean.exists_orderAddMonoidHom_real_injective Γ

/-- A convenient name for the lexicographically ordered copy of `ℤ × ℤ`. -/
abbrev Chapter02LexicographicIntegers := ℤ ×ₗ ℤ

theorem chapter02_lexicographic_order_formula (a b c d : ℤ) :
    toLex (a, b) < toLex (c, d) ↔
      a < c ∨ (a = c ∧ b < d) := by
  exact Prod.Lex.toLex_lt_toLex

theorem chapter02_lex_second_coordinate_refines_first (n : ℤ) :
    toLex ((0 : ℤ), 1) < toLex (1, n) := by
  exact (chapter02_lexicographic_order_formula 0 1 1 n).2 (Or.inl (by omega))

theorem chapter02_lexicographic_integers_nonarchimedean :
    ¬ Chapter02ArchimedeanValueGroup Chapter02LexicographicIntegers := by
  intro h
  obtain ⟨n, hn, hle⟩ := h (toLex ((0 : ℤ), 1)) (toLex (1, 0))
    (by change toLex ((0 : ℤ), 0) < toLex ((0 : ℤ), 1)
        rw [Prod.Lex.toLex_lt_toLex]; omega)
    (by change toLex ((0 : ℤ), 0) < toLex ((1 : ℤ), 0)
        rw [Prod.Lex.toLex_lt_toLex]; omega)
  have hsmul : n • toLex ((0 : ℤ), 1) = toLex ((0 : ℤ), (n : ℤ)) := by
    change toLex (n • ((0 : ℤ), (1 : ℤ))) =
      toLex ((0 : ℤ), (n : ℤ))
    simp
  have hle' : toLex ((1 : ℤ), 0) ≤ toLex ((0 : ℤ), (n : ℤ)) := by
    rw [← hsmul]
    exact hle
  have hlt : toLex ((0 : ℤ), (n : ℤ)) < toLex (1, 0) :=
    (chapter02_lexicographic_order_formula 0 n 1 0).2 (Or.inl (by omega))
  exact (not_le_of_gt hlt) hle'

theorem chapter02_lexicographic_integers_have_coarse_and_refining_coordinates :
    ∃ q : Chapter02LexicographicIntegers →+o ℤ,
      (∀ a b : ℤ, q (toLex (a, b)) = a) ∧
      (∀ n : ℤ, q (toLex (0, n)) = 0) := by
  let q : Chapter02LexicographicIntegers →+o ℤ :=
    { toFun := fun p => (ofLex p).1
      map_zero' := by simp
      map_add' := by intro p r; simp
      monotone' := Prod.Lex.monotone_fst_ofLex }
  refine ⟨q, ?_, ?_⟩
  · intro a b
    rfl
  · intro n
    rfl

/-- The subgroup `ℤ + √2 ℤ` of the real line. -/
def Chapter02SqrtTwoIntegerSubgroup : AddSubgroup ℝ :=
  AddSubgroup.closure ({(1 : ℝ), Real.sqrt 2} : Set ℝ)

theorem chapter02_sqrt_two_integer_subgroup_is_archimedean :
    Chapter02ArchimedeanValueGroup (↥Chapter02SqrtTwoIntegerSubgroup) := by
  intro α β hα hβ
  obtain ⟨n, hn⟩ := Archimedean.arch (β : ℝ) (show 0 < (α : ℝ) from hα)
  refine ⟨n, ?_, ?_⟩
  · by_contra hnot
    have hn0 : n = 0 := by omega
    subst n
    simpa using (not_le_of_gt (show 0 < (β : ℝ) from hβ) hn)
  · exact hn

theorem chapter02_rank_one_need_not_be_discrete :
    Chapter02ArchimedeanValueGroup ℚ ∧
      DenselyOrdered ℚ ∧
      ¬ ∃ d : ℚ, 0 < d ∧ ∀ x : ℚ, 0 < x → d ≤ x := by
  refine ⟨?_, inferInstance, ?_⟩
  · exact (chapter02_archimedean_value_group_iff).2 inferInstance
  · rintro ⟨d, hd, hleast⟩
    have hhalf : 0 < d / 2 := by linarith
    have := hleast (d / 2) hhalf
    linarith

theorem chapter02_lexicographic_group_has_no_real_order_embedding :
    ¬ ∃ f : Chapter02LexicographicIntegers →+o ℝ, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hmono : Monotone f := f.monotone'
  have hsmall : 0 ≤ f (toLex ((0 : ℤ), 1)) := by
    have hzero : (0 : Chapter02LexicographicIntegers) ≤
        toLex ((0 : ℤ), 1) := by
      change toLex ((0 : ℤ), 0) ≤ toLex ((0 : ℤ), 1)
      rw [Prod.Lex.toLex_le_toLex]
      omega
    simpa using hmono hzero
  by_cases hsmall0 : f (toLex ((0 : ℤ), 1)) = 0
  · have heq : f (toLex ((0 : ℤ), 1)) = f (toLex ((0 : ℤ), 0)) := by
      calc
        f (toLex ((0 : ℤ), 1)) = 0 := hsmall0
        _ = f (toLex ((0 : ℤ), 0)) := by
          change 0 = f 0
          exact (f.map_zero).symm
    have hbad : toLex ((0 : ℤ), (1 : ℤ)) =
        toLex ((0 : ℤ), (0 : ℤ)) := hf heq
    have hne : toLex ((0 : ℤ), (1 : ℤ)) ≠
        toLex ((0 : ℤ), (0 : ℤ)) := by
      intro h
      have := congrArg (fun p : Chapter02LexicographicIntegers =>
        (ofLex p).2) h
      norm_num at this
    exact hne hbad
  · have hsmallpos : 0 < f (toLex ((0 : ℤ), 1)) :=
      lt_of_le_of_ne hsmall (Ne.symm hsmall0)
    obtain ⟨n, hn⟩ := Archimedean.arch (f (toLex ((1 : ℤ), 0))) hsmallpos
    have hltlex : toLex ((0 : ℤ), (n : ℤ)) < toLex ((1 : ℤ), 0) :=
      (chapter02_lexicographic_order_formula 0 n 1 0).2 (Or.inl (by omega))
    have hlt : f (toLex ((0 : ℤ), (n : ℤ))) < f (toLex ((1 : ℤ), 0)) :=
      (hmono.strictMono_of_injective hf) hltlex
    have hsmul : n • toLex ((0 : ℤ), 1) = toLex ((0 : ℤ), (n : ℤ)) := by
      change toLex (n • ((0 : ℤ), (1 : ℤ))) =
        toLex ((0 : ℤ), (n : ℤ))
      simp
    have hmap : f (toLex ((0 : ℤ), (n : ℤ))) =
        n • f (toLex ((0 : ℤ), 1)) := by
      rw [← hsmul]
      exact f.map_nsmul _ _
    rw [hmap] at hlt
    exact (not_lt_of_ge hn) hlt

/-! ## 2.2. Additive valuations -/

/-- Chapter 2's additive valuation interface, using Mathlib's definition. -/
abbrev Chapter02AdditiveValuation (R Γ : Type*) [CommRing R]
    [LinearOrderedAddCommMonoidWithTop Γ] := AddValuation R Γ

theorem chapter02_additive_valuation_axioms
    {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) :
    v 0 = (⊤ : Γ) ∧
      v 1 = 0 ∧
      (∀ x y : R, v (x * y) = v x + v y) ∧
      (∀ x y : R, min (v x) (v y) ≤ v (x + y)) := by
  exact ⟨v.map_zero, v.map_one, v.map_mul, v.map_add⟩

theorem chapter02_additive_valuation_zero_is_infinity
    {R Γ : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) : v 0 = (⊤ : Γ) := by
  exact v.map_zero

theorem chapter02_additive_valuation_one_is_zero
    {R Γ : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) : v 1 = 0 := by
  exact v.map_one

def Chapter02Support {R Γ : Type*} [CommRing R]
    [LinearOrderedAddCommMonoidWithTop Γ] (v : AddValuation R Γ) : Ideal R :=
  AddValuation.supp v

theorem chapter02_support_characterization
    {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) (x : R) :
    x ∈ Chapter02Support v ↔ v x = (⊤ : Γ) := by
  exact AddValuation.mem_supp_iff v x

theorem chapter02_support_closed_under_addition
    {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) {x y : R}
    (hx : x ∈ Chapter02Support v) (hy : y ∈ Chapter02Support v) :
    x + y ∈ Chapter02Support v := by
  exact (Chapter02Support v).add_mem hx hy

theorem chapter02_support_absorbs_multiplication
    {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) {x y : R}
    (hx : x ∈ Chapter02Support v) :
    x * y ∈ Chapter02Support v := by
  apply (chapter02_support_characterization v (x * y)).2
  rw [v.map_mul, (chapter02_support_characterization v x).1 hx]
  simp

theorem chapter02_support_product_characterization
    {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    [Nontrivial (Multiplicative Γᵒᵈ)] [NoZeroDivisors (Multiplicative Γᵒᵈ)]
    (v : AddValuation R Γ) (x y : R) :
    x * y ∈ Chapter02Support v ↔
      x ∈ Chapter02Support v ∨ y ∈ Chapter02Support v := by
  rw [chapter02_support_characterization, chapter02_support_characterization,
    chapter02_support_characterization, v.map_mul]
  constructor
  · intro hxy
    by_cases hx : v x = ⊤
    · exact Or.inl hx
    by_cases hy : v y = ⊤
    · exact Or.inr hy
    exfalso
    apply hy
    apply (add_right_injective_of_ne_top (v x) hx)
    simpa using hxy
  · rintro (hx | hy)
    · simp [hx]
    · simp [hy]

theorem chapter02_support_is_prime
    {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    [Nontrivial (Multiplicative Γᵒᵈ)] [NoZeroDivisors (Multiplicative Γᵒᵈ)]
    (v : AddValuation R Γ) :
    (Chapter02Support v).IsPrime := by
  letI : Nontrivial Γ := ‹Nontrivial (Multiplicative Γᵒᵈ)›
  have hzeroTop : (0 : Γ) ≠ ⊤ := by
    intro hzero
    obtain ⟨a, b, hab⟩ := exists_pair_ne Γ
    apply hab
    calc
      a = 0 + a := (zero_add a).symm
      _ = ⊤ + a := by rw [hzero]
      _ = ⊤ := top_add _
      _ = ⊤ + b := (top_add _).symm
      _ = 0 + b := by rw [hzero]
      _ = b := zero_add b
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 : (1 : R) ∈ Chapter02Support v := by
      rw [htop]
      trivial
    have hv1 := (chapter02_support_characterization v 1).1 h1
    exact hzeroTop (by simpa using hv1)
  · intro x y hxy
    exact (chapter02_support_product_characterization v x y).1 hxy

theorem chapter02_field_support_is_zero
    {K Γ : Type*} [Field K] [LinearOrderedAddCommMonoidWithTop Γ]
    [Nontrivial (Multiplicative Γᵒᵈ)] [NoZeroDivisors (Multiplicative Γᵒᵈ)]
    (v : AddValuation K Γ) : Chapter02Support v = ⊥ := by
  letI : Nontrivial Γ := ‹Nontrivial (Multiplicative Γᵒᵈ)›
  ext x
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · exfalso
      exact (AddValuation.ne_top_iff v).2 hx0
        ((chapter02_support_characterization v x).1 hx)
  · intro hx0
    subst x
    exact (Chapter02Support v).zero_mem

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
    map_one' := by
      simp [Chapter02FiniteValueOfNonzero]
    map_mul' := by
      intro u z
      apply congrArg Multiplicative.ofAdd
      apply WithTop.coe_injective
      simpa [Chapter02FiniteValueOfNonzero, WithTop.coe_untop,
        Units.val_mul] using v.map_mul (u : K) (z : K)
  }

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
  refine ⟨Chapter02FieldUnitValueHom v, ?_⟩
  intro x hx
  rfl

theorem chapter02_unit_hom_converse
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (φ : Kˣ →* Multiplicative Γ)
    (hφ : Chapter02UnitHomSumInequality φ) :
    ∃! v : AddValuation K (WithTop Γ),
      ∀ x : K, v x = Chapter02ExtensionValue φ x := by
  let v : AddValuation K (WithTop Γ) :=
    AddValuation.of (Chapter02ExtensionValue φ)
      (by simp [Chapter02ExtensionValue])
      (by simp [Chapter02ExtensionValue])
      (by
        intro x y
        classical
        by_cases hx : x = 0
        · simp [Chapter02ExtensionValue, hx]
        by_cases hy : y = 0
        · simp [Chapter02ExtensionValue, hy]
        by_cases hxy : x + y = 0
        · simp [Chapter02ExtensionValue, hxy]
        simpa [Chapter02ExtensionValue, hx, hy, hxy] using hφ x y hx hy hxy)
      (by
        intro x y
        classical
        by_cases hx : x = 0
        · simp [Chapter02ExtensionValue, hx]
        by_cases hy : y = 0
        · simp [Chapter02ExtensionValue, hy]
        simpa [Chapter02ExtensionValue, hx, hy, Units.mk0_mul] using
          congrArg Multiplicative.toAdd
            (φ.map_mul (Units.mk0 x hx) (Units.mk0 y hy)))
  refine ⟨v, by intro x; rfl, ?_⟩
  intro w hw
  apply AddValuation.ext
  intro x
  simpa [v] using hw x

theorem chapter02_field_valuation_is_a_group_hom_on_nonzero_elements
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] [Nontrivial Γ]
    (v : AddValuation K (WithTop Γ)) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    Chapter02FiniteValueOfNonzero v (x * y) (mul_ne_zero hx hy) =
      Chapter02FiniteValueOfNonzero v x hx +
        Chapter02FiniteValueOfNonzero v y hy := by
  apply WithTop.coe_injective
  simpa [Chapter02FiniteValueOfNonzero, WithTop.coe_untop,
    WithTop.coe_add] using v.map_mul x y

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
  rw [Ideal.Quotient.isDomain_iff_prime]
  exact chapter02_support_is_prime v

theorem chapter02_valuation_factors_through_support
    {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) :
    ∀ x : R, v x = Chapter02SupportQuotientValuation v (Ideal.Quotient.mk _ x) := by
  intro x
  have hcomp :
      (Chapter02SupportQuotientValuation v).comap
          (Ideal.Quotient.mk (Chapter02Support v)) = v := by
    exact AddValuation.onQuot_comap_eq v (by simp [Chapter02Support])
  have hx := congrArg (fun z => z x) hcomp
  exact hx.symm

theorem chapter02_fraction_field_extension
    {A Γ : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (v : AddValuation A (WithTop Γ))
    (hsupp : AddValuation.supp v = ⊥) :
    ∃! w : AddValuation (FractionRing A) (WithTop Γ),
      (∀ a : A, w (algebraMap A (FractionRing A) a) = v a) ∧
      (∀ (a b : A) (hb : b ≠ 0),
        w (algebraMap A (FractionRing A) a /
            algebraMap A (FractionRing A) b) = v a - v b) := by
  have hS : nonZeroDivisors A ≤ (v.toValuation).supp.primeCompl := by
    intro s hs
    change s ∉ (v.toValuation).supp
    intro hmem
    have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
    apply hs0
    have hvs : v s = (⊤ : WithTop Γ) := by
      have hmem' : (v.toValuation) s = 0 :=
        (Valuation.mem_supp_iff (v.toValuation) s).1 hmem
      have hval := congrArg Multiplicative.toAdd hmem'
      have hval' := congrArg
        (fun z : (WithTop Γ)ᵒᵈ => OrderDual.ofDual z) hval
      simpa using hval'
    have hsuppmem : s ∈ AddValuation.supp v :=
      (AddValuation.mem_supp_iff v s).2 hvs
    simpa [hsupp] using hsuppmem
  let W : Valuation (FractionRing A) (Multiplicative (WithTop Γ)ᵒᵈ) :=
    (v.toValuation).extendToLocalization hS (FractionRing A)
  let w : AddValuation (FractionRing A) (WithTop Γ) :=
    AddValuation.ofValuation W
  have hmap (a : A) : w (algebraMap A (FractionRing A) a) = v a := by
    change W (algebraMap A (FractionRing A) a) = (v.toValuation) a
    exact Valuation.extendToLocalization_apply_map_apply
      (v.toValuation) hS (FractionRing A) a
  refine ⟨w, ⟨hmap, ?_⟩, ?_⟩
  · intro a b hb
    rw [AddValuation.map_div, hmap, hmap]
  · intro w' hw'
    apply AddValuation.ext
    intro z
    obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective A z
    calc
      w' z = v a - v b := by
        rw [← hz]
        exact hw'.2 a b (mem_nonZeroDivisors_iff_ne_zero.mp hb)
      _ = w z := by
        rw [← hz, AddValuation.map_div, hmap a, hmap b]

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
  let H : AddSubgroup Γ :=
    { carrier := Chapter02AttainedValueSet v
      zero_mem' := by
        refine ⟨1, one_ne_zero, ?_⟩
        simp
      add_mem' := by
        rintro x y ⟨a, ha, hax⟩ ⟨b, hb, hby⟩
        refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
        rw [v.map_mul, hax, hby]
        exact (WithTop.coe_add x y).symm
      neg_mem' := by
        rintro x ⟨a, ha, hax⟩
        refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
        simp [hax] }
  apply Set.Subset.antisymm
  · exact (AddSubgroup.closure_le H).2 (by
      intro x hx
      exact hx)
  · exact AddSubgroup.subset_closure

theorem chapter02_surjective_iff_value_group_is_ambient
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) :
    Chapter02SurjectiveValuation v ↔ Chapter02ValueGroup v = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro γ hγ
    have hγ' : γ ∈ Chapter02AttainedValueSet v := by
      rcases h γ with ⟨x, hx, hv⟩
      exact ⟨x, hx, hv⟩
    have hc : (γ ∈ (Chapter02ValueGroup v : Set Γ)) =
        (γ ∈ Chapter02AttainedValueSet v) :=
      congrArg (fun S : Set Γ => γ ∈ S) (chapter02_value_group_carrier v)
    change γ ∈ (Chapter02ValueGroup v : Set Γ)
    exact hc.symm ▸ hγ'
  · intro h γ
    have hγ : γ ∈ Chapter02ValueGroup v := by
      rw [h]
      trivial
    have hc : (γ ∈ (Chapter02ValueGroup v : Set Γ)) =
        (γ ∈ Chapter02AttainedValueSet v) :=
      congrArg (fun S : Set Γ => γ ∈ S) (chapter02_value_group_carrier v)
    change γ ∈ (Chapter02ValueGroup v : Set Γ) at hγ
    change γ ∈ Chapter02AttainedValueSet v
    exact hc ▸ hγ

/-! ## 2.3. The decisive equality -/

theorem chapter02_unequal_values_do_not_cancel
    {R Γ : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) {x y : R} (hxy : v x ≠ v y) :
    v (x + y) = min (v x) (v y) := by
  exact v.map_add_of_distinct_val hxy

theorem chapter02_strictly_smallest_term_controls_finite_sum
    {R Γ ι : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    [DecidableEq ι] (v : AddValuation R Γ) (s : Finset ι) (f : ι → R) (j : ι)
    (hj : j ∈ s)
    (hmin : ∀ i ∈ s, i ≠ j → v (f j) < v (f i)) :
    v (∑ i ∈ s, f i) = v (f j) := by
  classical
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hj]
  let t := s \ {j}
  by_cases ht : t.Nonempty
  · have hfjtop : v (f j) ≠ (⊤ : Γ) := by
      obtain ⟨i, hi⟩ := ht
      exact ne_of_lt <| (hmin i (Finset.mem_sdiff.mp hi).1 (by
        intro hij
        exact (Finset.mem_sdiff.mp hi).2 (by simpa [hij]))).trans_le le_top
    apply v.map_add_eq_of_lt_left
    apply v.map_lt_sum hfjtop
    intro i hi
    exact hmin i (Finset.mem_sdiff.mp hi).1 (by
      intro hij
      exact (Finset.mem_sdiff.mp hi).2 (by simpa [hij]))
  · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    simp [t, ht0]

/-- For a finite zero-sum of nonzero terms, the minimum valuation occurs at
least twice. The nonzero condition makes explicit the usual convention that
zero terms have first been discarded from the sum. -/
theorem chapter02_zero_finite_sum_has_repeated_minimum
    {R Γ ι : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    [DecidableEq ι] (v : AddValuation R Γ) (s : Finset ι) (f : ι → R)
    (hs : s.Nonempty) (hz : ∑ i ∈ s, f i = 0)
    (hnz : ∀ i ∈ s, f i ≠ 0) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧
      v (f i) = v (f j) ∧ ∀ k ∈ s, v (f i) ≤ v (f k) := by
  obtain ⟨i, hi, himin⟩ := Finset.exists_min_image s (fun k => v (f k)) hs
  by_cases hstrict : ∀ k ∈ s, k ≠ i → v (f i) < v (f k)
  · have hsum := chapter02_strictly_smallest_term_controls_finite_sum v s f i hi hstrict
    have hfi_top : v (f i) ≠ (⊤ : Γ) := by
      intro htop
      by_cases hsone : s = {i}
      · apply hnz i hi
        simpa [hsone] using hz
      · have hs_sub : s ⊆ {i} := by
          intro k hk
          by_contra hki
          have hki' : k ≠ i := by
            intro hki'
            exact hki (Finset.mem_singleton.mpr hki')
          exact (not_lt_of_ge (by simp [htop])) (hstrict k hk hki')
        have hs_eq : s = {i} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hi, fun k hk => Finset.mem_singleton.mp (hs_sub hk)⟩
        exact hsone hs_eq
    exfalso
    apply hfi_top
    simpa [hz] using hsum.symm
  · push_neg at hstrict
    obtain ⟨j, hj, hji, hjnot⟩ := hstrict
    refine ⟨i, hi, j, hj, hji.symm, le_antisymm (himin j hj) hjnot, ?_⟩
    exact himin

theorem chapter02_minimum_occurs_twice_in_zero_sum
    {R Γ ι : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    [DecidableEq ι] (v : AddValuation R Γ) (s : Finset ι) (f : ι → R)
    (hz : ∑ i ∈ s, f i = 0) (hunique : ∃ j ∈ s,
      ∀ i ∈ s, i ≠ j → v (f j) < v (f i)) :
    ¬ (∀ i ∈ s, f i ≠ 0) := by
  intro hnz
  rcases hunique with ⟨j, hj, hjmin⟩
  have hsum := chapter02_strictly_smallest_term_controls_finite_sum v s f j hj hjmin
  have hfjtop : v (f j) ≠ (⊤ : Γ) := by
    intro htop
    by_cases hsone : s = {j}
    · apply hnz j hj
      simpa [hsone] using hz
    · have hs_sub : s ⊆ {j} := by
        intro k hk
        by_contra hkj
        have hkj' : k ≠ j := by
          intro hkj'
          exact hkj (Finset.mem_singleton.mpr hkj')
        exact (not_lt_of_ge (by simp [htop])) (hjmin k hk hkj')
      have hs_eq : s = {j} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hj, fun k hk => Finset.mem_singleton.mp (hs_sub hk)⟩
      exact hsone hs_eq
  apply hfjtop
  simpa [hz] using hsum.symm

/-! ## 2.4. Equivalence and normalization -/

def Chapter02EquivalentValuations
    {K Γ Δ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    (v : AddValuation K (WithTop Γ)) (w : AddValuation K (WithTop Δ)) : Prop :=
  AddValuation.IsEquiv v w

theorem chapter02_equivalent_iff_same_comparisons
    {K Γ Δ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    (v : AddValuation K (WithTop Γ)) (w : AddValuation K (WithTop Δ)) :
    Chapter02EquivalentValuations v w ↔
      ∀ x y : K, v x ≤ v y ↔ w x ≤ w y := by
  change (∀ x y : K, v y ≤ v x ↔ w y ≤ w x) ↔
    ∀ x y : K, v x ≤ v y ↔ w x ≤ w y
  constructor <;> intro h x y
  · exact h y x
  · exact h y x

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
  rcases h with ⟨e, he⟩
  apply (chapter02_equivalent_iff_same_comparisons v w).2
  intro x y
  rw [he x, he y]
  by_cases hx : v x = ⊤ <;> by_cases hy : v y = ⊤
  · simp [Chapter02OrderRelabelValue, hx, hy]
  · simp [Chapter02OrderRelabelValue, hx, hy]
  · simp [Chapter02OrderRelabelValue, hx, hy]
  · simp only [Chapter02OrderRelabelValue, dif_neg hx, dif_neg hy]
    constructor
    · intro hxy
      apply WithTop.coe_le_coe.mpr
      apply (map_le_map_iff e).2
      exact WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hxy)
    · intro hxy
      have hfinite : (v x).untop hx ≤ (v y).untop hy :=
        (map_le_map_iff e).1 (WithTop.coe_le_coe.mp hxy)
      simpa only [WithTop.coe_untop] using (WithTop.coe_le_coe.mpr hfinite)

theorem chapter02_equivalence_and_surjectivity_give_order_relabeling
    {K Γ Δ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    {v : AddValuation K (WithTop Γ)} {w : AddValuation K (WithTop Δ)}
    (hv : Chapter02SurjectiveValuation v)
    (hw : Chapter02SurjectiveValuation w)
    (he : Chapter02EquivalentValuations v w) :
    Chapter02EquivalentByOrderedRelabeling v w := by
  classical
  have hcomp (a b : K) : v a ≤ v b ↔ w a ≤ w b :=
    (chapter02_equivalent_iff_same_comparisons v w).1 he a b
  let xv : Γ → K := fun γ => Classical.choose (hv γ)
  have hxv : ∀ γ : Γ, xv γ ≠ 0 ∧ v (xv γ) = (γ : WithTop Γ) := by
    intro γ
    exact Classical.choose_spec (hv γ)
  let yw : Δ → K := fun δ => Classical.choose (hw δ)
  have hyw : ∀ δ : Δ, yw δ ≠ 0 ∧ w (yw δ) = (δ : WithTop Δ) := by
    intro δ
    exact Classical.choose_spec (hw δ)
  have heq {a b : K} (h : v a = v b) : w a = w b := by
    apply le_antisymm
    · exact (hcomp a b).1 (by rw [h])
    · exact (hcomp b a).1 (by rw [h])
  have heqv {a b : K} (h : w a = w b) : v a = v b := by
    apply le_antisymm
    · exact (hcomp a b).2 (by rw [h])
    · exact (hcomp b a).2 (by rw [h])
  let e : Γ ≃+o Δ :=
    { toFun := fun γ =>
        (w (xv γ)).untop ((AddValuation.ne_top_iff w).2 (hxv γ).1)
      invFun := fun δ =>
        (v (yw δ)).untop ((AddValuation.ne_top_iff v).2 (hyw δ).1)
      left_inv := by
        intro γ
        apply WithTop.coe_injective
        have hval : v (yw ((w (xv γ)).untop
            ((AddValuation.ne_top_iff w).2 (hxv γ).1))) = v (xv γ) := by
          apply heqv
          calc
            w (yw ((w (xv γ)).untop _)) =
                ((w (xv γ)).untop _ : WithTop Δ) := (hyw _).2
            _ = w (xv γ) := WithTop.coe_untop _ _
        simpa only [WithTop.coe_untop, (hxv γ).2] using hval
      right_inv := by
        intro δ
        apply WithTop.coe_injective
        have hval : w (xv ((v (yw δ)).untop
            ((AddValuation.ne_top_iff v).2 (hyw δ).1))) = w (yw δ) := by
          apply heq
          calc
            v (xv ((v (yw δ)).untop _)) =
                ((v (yw δ)).untop _ : WithTop Γ) := (hxv _).2
            _ = v (yw δ) := WithTop.coe_untop _ _
        simpa only [WithTop.coe_untop, (hyw δ).2] using hval
      map_add' := by
        intro γ γ'
        apply WithTop.coe_injective
        have hval : w (xv (γ + γ')) =
            w (xv γ) + w (xv γ') := by
          rw [← w.map_mul]
          apply heq
          rw [v.map_mul, (hxv γ).2, (hxv γ').2, (hxv (γ + γ')).2]
          simp
        simpa only [WithTop.coe_untop, WithTop.coe_add] using hval
      map_le_map_iff' := by
        intro γ γ'
        constructor
        · intro hγ
          apply WithTop.coe_le_coe.mp
          have hvle : v (xv γ) ≤ v (xv γ') :=
            (hcomp (xv γ) (xv γ')).2 (by
              simpa only [WithTop.coe_untop] using
                (WithTop.coe_le_coe.mpr hγ))
          simpa only [(hxv γ).2, (hxv γ').2] using hvle
        · intro hγ
          apply WithTop.coe_le_coe.mp
          have hwle : w (xv γ) ≤ w (xv γ') :=
            (hcomp (xv γ) (xv γ')).1 (by
              simpa only [(hxv γ).2, (hxv γ').2] using
                (WithTop.coe_le_coe.mpr hγ))
          simpa only [WithTop.coe_untop] using hwle }
  refine ⟨e, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, Chapter02OrderRelabelValue]
  have hvx : v x ≠ (⊤ : WithTop Γ) := (AddValuation.ne_top_iff v).2 hx
  have hval : w x = w (xv ((v x).untop hvx)) := by
    apply heq
    calc
      v x = ((v x).untop hvx : WithTop Γ) := (WithTop.coe_untop _ _).symm
      _ = v (xv ((v x).untop hvx)) := ((hxv _).2).symm
  simpa [Chapter02OrderRelabelValue, hvx, e, WithTop.coe_untop] using hval

def Chapter02DiscreteValueGroup (Γ : Type*)
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] : Prop :=
  Nonempty (Γ ≃+o ℤ)

theorem chapter02_discrete_value_group_has_unique_smallest_positive
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (hΓ : Chapter02DiscreteValueGroup Γ) :
    ∃! π : Γ, 0 < π ∧ ∀ γ : Γ, 0 < γ → π ≤ γ := by
  rcases hΓ with ⟨e⟩
  let π : Γ := e.symm 1
  have hπ : 0 < π := by
    dsimp [π]
    rw [← e.symm.map_zero]
    exact (map_lt_map_iff e.symm).2 (by omega)
  have hleast : ∀ γ : Γ, 0 < γ → π ≤ γ := by
    intro γ hγ
    apply (map_le_map_iff e).1
    have heπ : e π = 1 := by simp [π]
    have hpos : 0 < e γ := by
      rw [← e.map_zero]
      exact (map_lt_map_iff e).2 hγ
    rw [heπ]
    omega
  refine ⟨π, ⟨hπ, hleast⟩, ?_⟩
  intro π' hπ'
  exact le_antisymm (hπ'.2 π hπ) (hleast π' hπ'.1)

noncomputable def Chapter02NormalizedValuation
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (e : Γ ≃+o ℤ) (v : AddValuation K (WithTop Γ)) :
    AddValuation K (WithTop ℤ) := by
  exact v.map (AddMonoidHom.withTopMap (e : Γ →+ ℤ)) (by simp)
    (OrderHomClass.monotone e).withTop_map

theorem chapter02_normalized_valuation_uses_unit_step
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (e : Γ ≃+o ℤ) (v : AddValuation K (WithTop Γ))
    {x : K} {π : Γ} (hx : x ≠ 0)
    (hπ : 0 < π) (hleast : ∀ γ : Γ, 0 < γ → π ≤ γ)
    (hv : v x = (π : WithTop Γ)) :
    Chapter02NormalizedValuation e v x = (1 : WithTop ℤ) := by
  have heπ : e π = 1 := by
    have hpos : 0 < e π := by
      rw [← e.map_zero]
      exact (map_lt_map_iff e).2 hπ
    have hle : (1 : ℤ) ≤ e π := by omega
    have hnot : e π ≤ 1 := by
      by_contra hnot
      have h1pos : 0 < e.symm 1 := by
        rw [← e.symm.map_zero]
        exact (map_lt_map_iff e.symm).2 (by omega)
      have hlt : e.symm 1 < π := by
        apply (map_lt_map_iff e).1
        have h1lt : (1 : ℤ) < e π := lt_of_not_ge hnot
        simpa using h1lt
      exact (not_lt_of_ge (hleast (e.symm 1) h1pos)) hlt
    exact le_antisymm hnot hle
  change (AddMonoidHom.withTopMap (e : Γ →+ ℤ)) (v x) =
    (1 : WithTop ℤ)
  rw [hv]
  change (e π : WithTop ℤ) = (1 : WithTop ℤ)
  rw [heπ]
  simp

noncomputable def Chapter02TwiceValuation
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : AddValuation K (WithTop ℤ) :=
  AddValuation.of (fun x => 2 • v x)
    (by rw [v.map_zero]; change 2 • (⊤ : WithTop ℤ) = ⊤; rfl)
    (by simp)
    (by
      intro x y
      simpa [smul_min_of_nonneg (by norm_num : (0 : ℕ) ≤ 2)] using
        nsmul_le_nsmul_right (v.map_add x y) 2)
    (by
      intro x y
      simp [v.map_mul, add_nsmul])

theorem chapter02_twice_valuation_formula
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) (x : K) :
    Chapter02TwiceValuation v x = 2 • v x := by
  rfl

def Chapter02ValuationRing
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) : Subring K :=
  { carrier := {x | 0 ≤ v x}
    zero_mem' := by simp
    one_mem' := by simp
    add_mem' := by
      intro x y hx hy
      exact le_trans (le_min hx hy) (v.map_add x y)
    mul_mem' := by
      intro x y hx hy
      simpa [v.map_mul] using add_nonneg hx hy
    neg_mem' := by
      intro x hx
      simpa using hx
  }

theorem chapter02_equivalent_scalings_have_same_valuation_ring
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) :
    Chapter02ValuationRing (Chapter02TwiceValuation v) =
      Chapter02ValuationRing v := by
  ext x
  change (0 ≤ 2 • v x) ↔ 0 ≤ v x
  cases h : v x with
  | top =>
      have htop : (2 : ℕ) • (⊤ : WithTop ℤ) = ⊤ := by rfl
      rw [htop]
  | coe z =>
      change (((0 : ℤ) : WithTop ℤ) ≤ ((2 * z : ℤ) : WithTop ℤ)) ↔
        (((0 : ℤ) : WithTop ℤ) ≤ ((z : ℤ) : WithTop ℤ))
      rw [WithTop.coe_le_coe, WithTop.coe_le_coe]
      constructor
      · intro hz
        nlinarith
      · intro hz
        nlinarith

theorem chapter02_ramification_labels_depend_on_normalization
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
    {x : K} (hx : v x = (1 : WithTop ℤ)) :
    Chapter02TwiceValuation v x = (2 : WithTop ℤ) ∧
      Chapter02TwiceValuation v x ≠ v x := by
  constructor
  · simp [Chapter02TwiceValuation, hx]
  · simp [Chapter02TwiceValuation, hx]

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
  exact v.map (AddMonoidHom.withTopMap (q : Γ →+ Λ)) (by simp)
    (OrderHomClass.monotone q).withTop_map

theorem chapter02_convex_subgroup_gives_ordered_quotient
    {Γ Λ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (H : AddSubgroup Γ) (hH : Chapter02ConvexAddSubgroup H)
    (q : Γ →+o Λ) (hq : Function.Surjective q)
    (hker : ∀ γ : Γ, q γ = 0 ↔ γ ∈ H)
    (horder : ∀ a b : Γ, q a ≤ q b ↔
      ∃ h : H, a ≤ b + (h : Γ)) :
    Chapter02ConvexQuotientInterface H q := by
  refine ⟨hq, hker, ?_⟩
  intro Ω _ _ _ f hfH
  have hwell : ∀ {a b : Γ}, q a = q b → f a = f b := by
    intro a b hab
    have hqsub : q (a - b) = 0 := by simpa [map_sub, hab]
    have hmem : a - b ∈ H := (hker (a - b)).1 hqsub
    have hf0 := hfH (a - b) hmem
    have : f a - f b = 0 := by simpa [map_sub] using hf0
    exact sub_eq_zero.mp this
  let g : Λ →+o Ω :=
    { toFun := fun z => f (Classical.choose (hq z))
      map_zero' := by
        have hz : q (Classical.choose (hq 0)) = q 0 := by simp [Classical.choose_spec (hq 0)]
        simpa using (hwell hz).trans f.map_zero
      map_add' := by
        intro z t
        have hz : q (Classical.choose (hq (z + t))) =
            q (Classical.choose (hq z) + Classical.choose (hq t)) := by
          simp [Classical.choose_spec (hq (z + t)),
            Classical.choose_spec (hq z), Classical.choose_spec (hq t)]
        have hzg := hwell hz
        simpa [map_add] using hzg
      monotone' := by
        intro z t hzt
        have hqt : q (Classical.choose (hq z)) ≤ q (Classical.choose (hq t)) := by
          simpa [Classical.choose_spec (hq z), Classical.choose_spec (hq t)] using hzt
        rcases (horder (Classical.choose (hq z)) (Classical.choose (hq t))).1 hqt with
          ⟨h, hab⟩
        calc
          f (Classical.choose (hq z)) ≤
              f (Classical.choose (hq t) + (h : Γ)) :=
                (OrderHomClass.monotone f) hab
          _ = f (Classical.choose (hq t)) := by
            simpa only [map_add, hfH (h : Γ) h.property, add_zero] }
  have hfactor : f = g.comp q := by
    ext a
    have hz : q (Classical.choose (hq (q a))) = q a :=
      Classical.choose_spec (hq (q a))
    change f a = f (Classical.choose (hq (q a)))
    exact (hwell hz).symm
  refine ⟨g, hfactor, ?_⟩
  intro g' hg'
  ext z
  rcases hq z with ⟨a, rfl⟩
  have h₁ := congrArg (fun F => F a) hg'
  have h₂ := congrArg (fun F => F a) hfactor
  exact h₁.symm.trans h₂

theorem chapter02_coarsening_is_composition_with_quotient
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (H : AddSubgroup Γ) (q : Γ →+o Λ)
    (hQ : Chapter02ConvexQuotientInterface H q)
    (v : AddValuation K (WithTop Γ)) :
    ∀ x : K, Chapter02CoarsenedValuation q v x =
      (if h : v x = ⊤ then ⊤ else (q ((v x).untop h) : WithTop Λ)) := by
  intro x
  by_cases hx : v x = ⊤
  · have hx0 : x = 0 := (AddValuation.top_iff v).1 hx
    simp [Chapter02CoarsenedValuation, hx, hx0]
  · simp only [Chapter02CoarsenedValuation, dif_neg hx, AddValuation.map_apply]
    change (AddMonoidHom.withTopMap (q : Γ →+ Λ)) (v x) =
      (q ((v x).untop hx) : WithTop Λ)
    have hvx : v x = ((v x).untop hx : WithTop Γ) :=
      (WithTop.coe_untop (v x) hx).symm
    calc
      (AddMonoidHom.withTopMap (q : Γ →+ Λ)) (v x) =
          (AddMonoidHom.withTopMap (q : Γ →+ Λ))
            ((v x).untop hx : WithTop Γ) := congrArg _ hvx
      _ = (q ((v x).untop hx) : WithTop Λ) := rfl

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
  intro a b c hab hbc ha hc
  change (ofLex b).1 = 0
  have hab' : (ofLex a).1 ≤ (ofLex b).1 :=
    Prod.Lex.monotone_fst a b hab
  have hbc' : (ofLex b).1 ≤ (ofLex c).1 :=
    Prod.Lex.monotone_fst b c hbc
  have ha' : (ofLex a).1 = 0 := ha
  have hc' : (ofLex c).1 = 0 := hc
  omega

theorem chapter02_lex_quotient_remembers_first_coordinate :
    Function.Surjective Chapter02LexFirstCoordinate ∧
      ∀ p : Chapter02LexicographicIntegers,
        Chapter02LexFirstCoordinate p = 0 ↔
          p ∈ Chapter02LexSecondCoordinateSubgroup := by
  constructor
  · intro z
    exact ⟨toLex (z, (0 : ℤ)), rfl⟩
  · intro p
    rfl

theorem chapter02_lex_quotient_is_an_ordered_convex_quotient :
    Chapter02ConvexQuotientInterface Chapter02LexSecondCoordinateSubgroup
      Chapter02LexFirstCoordinate := by
  apply chapter02_convex_subgroup_gives_ordered_quotient
    Chapter02LexSecondCoordinateSubgroup chapter02_lex_second_coordinate_is_convex
    Chapter02LexFirstCoordinate
    (chapter02_lex_quotient_remembers_first_coordinate).1
    (chapter02_lex_quotient_remembers_first_coordinate).2
  intro a b
  change (ofLex a).1 ≤ (ofLex b).1 ↔
    ∃ h : Chapter02LexSecondCoordinateSubgroup,
      a ≤ b + (h : Chapter02LexicographicIntegers)
  constructor
  · intro hab
    rcases hab.lt_or_eq with hablt | habeq
    · refine ⟨0, ?_⟩
      simpa using (Prod.Lex.toLex_le_toLex.mpr (Or.inl hablt))
    · let h : Chapter02LexSecondCoordinateSubgroup :=
        ⟨toLex ((0 : ℤ), (ofLex a).2 - (ofLex b).2), by
          change (ofLex (toLex ((0 : ℤ), (ofLex a).2 - (ofLex b).2))).1 = 0
          simp⟩
      refine ⟨h, ?_⟩
      dsimp [h]
      change toLex ((ofLex a).1, (ofLex a).2) ≤
        toLex ((ofLex b).1 + 0,
          (ofLex b).2 + ((ofLex a).2 - (ofLex b).2))
      rw [Prod.Lex.toLex_le_toLex]
      exact Or.inr ⟨by omega, by omega⟩
  · rintro ⟨h, hab⟩
    have hle := Prod.Lex.monotone_fst a (b + (h : Chapter02LexicographicIntegers)) hab
    have hh : (ofLex (h : Chapter02LexicographicIntegers)).1 = 0 := by
      exact h.property
    simpa [hh] using hle

theorem chapter02_discrete_rank_one_has_no_proper_coarsening
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (hΓ : Chapter02DiscreteValueGroup Γ) (H : AddSubgroup Γ)
    (hH : Chapter02ConvexAddSubgroup H) : H = ⊥ ∨ H = ⊤ := by
  rcases hΓ with ⟨e⟩
  by_cases hp : ∃ h : Γ, h ∈ H ∧ 0 < h
  · right
    rcases hp with ⟨h, hh, hpos⟩
    let p : Γ := e.symm 1
    have hppos : 0 < p := by
      dsimp [p]
      rw [← e.symm.map_zero]
      exact (map_lt_map_iff e.symm).2 (by omega)
    have hple : p ≤ h := by
      apply (map_le_map_iff e).1
      have hep : e p = 1 := by simp [p]
      have : 0 < e h := by
        rw [← e.map_zero]
        exact (map_lt_map_iff e).2 hpos
      rw [hep]
      omega
    have hpH : p ∈ H := hH (le_of_lt hppos) hple H.zero_mem hh
    apply le_antisymm le_top
    intro γ _
    have hγ : (e γ) • p = γ := by
      apply e.injective
      simp [p]
    rw [← hγ]
    exact H.zsmul_mem hpH (e γ)
  · left
    apply le_antisymm ?_ bot_le
    intro h hh
    have hnotpos : ¬ 0 < h := by
      intro hpos
      exact hp ⟨h, hh, hpos⟩
    have hnotneg : ¬ h < 0 := by
      intro hneg
      apply hp
      refine ⟨-h, H.neg_mem hh, ?_⟩
      exact neg_pos.mpr hneg
    have : h = 0 := le_antisymm (le_of_not_gt hnotpos) (le_of_not_gt hnotneg)
    simpa [this]

/-! ## 2.5. From additive values to multiplicative absolute values -/

def Chapter02RealSizeFromValuation
    {K : Type*} [Field K] (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (v : AddValuation K (WithTop ℝ)) (x : K) : ℝ :=
  if hx : v x = ⊤ then 0 else Real.rpow c ((v x).untop hx)

theorem chapter02_real_size_of_zero
    {K : Type*} [Field K] {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (v : AddValuation K (WithTop ℝ)) :
    Chapter02RealSizeFromValuation c hc hc1 v 0 = 0 := by
  simp [Chapter02RealSizeFromValuation]

theorem chapter02_real_size_of_one
    {K : Type*} [Field K] {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (v : AddValuation K (WithTop ℝ)) :
    Chapter02RealSizeFromValuation c hc hc1 v 1 = 1 := by
  simp [Chapter02RealSizeFromValuation]

theorem chapter02_real_size_is_multiplicative
    {K : Type*} [Field K] {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (v : AddValuation K (WithTop ℝ)) (x y : K) :
    Chapter02RealSizeFromValuation c hc hc1 v (x * y) =
      Chapter02RealSizeFromValuation c hc hc1 v x *
        Chapter02RealSizeFromValuation c hc hc1 v y := by
  classical
  by_cases hx : x = 0
  · simp [Chapter02RealSizeFromValuation, hx]
  by_cases hy : y = 0
  · simp [Chapter02RealSizeFromValuation, hy]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hxv : v x ≠ (⊤ : WithTop ℝ) := (AddValuation.ne_top_iff v).2 hx
  have hyv : v y ≠ (⊤ : WithTop ℝ) := (AddValuation.ne_top_iff v).2 hy
  have hxyv : v (x * y) ≠ (⊤ : WithTop ℝ) :=
    (AddValuation.ne_top_iff v).2 hxy
  have hun : (v (x * y)).untop hxyv =
      (v x).untop hxv + (v y).untop hyv := by
    apply WithTop.coe_injective
    simp [v.map_mul]
  simp only [Chapter02RealSizeFromValuation, dif_neg hxv, dif_neg hyv, dif_neg hxyv]
  rw [hun]
  exact Real.rpow_add hc _ _

theorem chapter02_real_size_is_ultrametric
    {K : Type*} [Field K] {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (v : AddValuation K (WithTop ℝ)) (x y : K) :
    Chapter02RealSizeFromValuation c hc hc1 v (x + y) ≤
      max (Chapter02RealSizeFromValuation c hc hc1 v x)
        (Chapter02RealSizeFromValuation c hc hc1 v y) := by
  classical
  by_cases hx : x = 0
  · simp [Chapter02RealSizeFromValuation, hx]
  by_cases hy : y = 0
  · simp [Chapter02RealSizeFromValuation, hy]
  by_cases hxy : x + y = 0
  · have hxyv0 : v (x + y) = (⊤ : WithTop ℝ) := by
      rw [hxy]
      exact v.map_zero
    simp only [Chapter02RealSizeFromValuation, dif_pos hxyv0]
    apply le_max_of_le_left
    split_ifs with hzero
    · simp
    · exact Real.rpow_nonneg hc.le _
  have hxv : v x ≠ (⊤ : WithTop ℝ) := (AddValuation.ne_top_iff v).2 hx
  have hyv : v y ≠ (⊤ : WithTop ℝ) := (AddValuation.ne_top_iff v).2 hy
  have hxyv : v (x + y) ≠ (⊤ : WithTop ℝ) :=
    (AddValuation.ne_top_iff v).2 hxy
  have hsum := v.map_add x y
  rcases le_total (v x) (v y) with hxyval | hyxval
  · have hsumx : v x ≤ v (x + y) := by
      simpa [min_eq_left hxyval] using hsum
    have hxexp : (v x).untop hxv ≤ (v (x + y)).untop hxyv := by
      exact WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hsumx)
    have hyexp : (v x).untop hxv ≤ (v y).untop hyv := by
      exact WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hxyval)
    have hpow_sum := Real.rpow_le_rpow_of_exponent_ge hc hc1.le hxexp
    have hpow_y := Real.rpow_le_rpow_of_exponent_ge hc hc1.le hyexp
    have hmax : max (Real.rpow c ((v x).untop hxv))
        (Real.rpow c ((v y).untop hyv)) =
        Real.rpow c ((v x).untop hxv) := max_eq_left hpow_y
    have hbound : Real.rpow c ((v (x + y)).untop hxyv) ≤
        max (Real.rpow c ((v x).untop hxv))
          (Real.rpow c ((v y).untop hyv)) := by
      rw [hmax]
      exact hpow_sum
    simpa only [Chapter02RealSizeFromValuation, dif_neg hxv, dif_neg hyv,
      dif_neg hxyv] using hbound
  · have hsumy : v y ≤ v (x + y) := by
      simpa [min_eq_right hyxval] using hsum
    have hyexp : (v y).untop hyv ≤ (v (x + y)).untop hxyv := by
      exact WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hsumy)
    have hxexp : (v y).untop hyv ≤ (v x).untop hxv := by
      exact WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hyxval)
    have hpow_sum := Real.rpow_le_rpow_of_exponent_ge hc hc1.le hyexp
    have hpow_x := Real.rpow_le_rpow_of_exponent_ge hc hc1.le hxexp
    have hmax : max (Real.rpow c ((v x).untop hxv))
        (Real.rpow c ((v y).untop hyv)) =
        Real.rpow c ((v y).untop hyv) := max_eq_right hpow_x
    have hbound : Real.rpow c ((v (x + y)).untop hxyv) ≤
        max (Real.rpow c ((v x).untop hxv))
          (Real.rpow c ((v y).untop hyv)) := by
      rw [hmax]
      exact hpow_sum
    simpa only [Chapter02RealSizeFromValuation, dif_neg hxv, dif_neg hyv,
      dif_neg hxyv] using hbound

def Chapter02PadicAdditiveValuation (p : ℕ) [Fact p.Prime] :
    AddValuation ℚ (WithTop ℤ) :=
  AddValuation.of
    (fun x : ℚ => if x = 0 then ⊤ else (padicValRat p x : WithTop ℤ))
    (by simp)
    (by simp)
    (by
      intro x y
      by_cases hxy : x + y = 0
      · simp [hxy]
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      simp only [if_neg hx, if_neg hy, if_neg hxy]
      exact_mod_cast (padicValRat.min_le_padicValRat_add (p := p) hxy))
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      simp [hx, hy, padicValRat.mul])

def Chapter02PadicAbsoluteValue (p : ℕ) [Fact p.Prime] (x : ℚ) : ℝ :=
  if x = 0 then 0 else Real.rpow (p : ℝ) (-(padicValRat p x : ℝ))
theorem chapter02_padic_value_of_p
    (p : ℕ) [Fact p.Prime] :
    Chapter02PadicAdditiveValuation p p = (1 : WithTop ℤ) := by
  have hp : Nat.Prime p := Fact.out
  simp [Chapter02PadicAdditiveValuation, hp.ne_zero, padicValRat.self hp.one_lt]

theorem chapter02_padic_absolute_value_of_p
    (p : ℕ) [Fact p.Prime] :
    Chapter02PadicAbsoluteValue p p = (p : ℝ)⁻¹ := by
  have hp : Nat.Prime p := Fact.out
  simp [Chapter02PadicAbsoluteValue, hp.ne_zero, padicValRat.self hp.one_lt,
    Real.rpow_neg_one]


theorem chapter02_padic_absolute_value_of_p_pow_times_prime_to_p
    (p n : ℕ) [Fact p.Prime] (a b : ℤ) (hb : b ≠ 0)
    (ha : ¬ (p : ℤ) ∣ a) (hbp : ¬ (p : ℤ) ∣ b) :
    Chapter02PadicAbsoluteValue p
        (((p : ℚ) ^ n) * (a : ℚ) / (b : ℚ)) =
      Real.rpow (p : ℝ) (-(n : ℝ)) := by
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    simp at ha
  have hpn0 : (p : ℚ) ^ n ≠ 0 := by
    have hp : Nat.Prime p := Fact.out
    exact pow_ne_zero n (by exact_mod_cast hp.ne_zero)
  have hpa0 : (a : ℚ) ≠ 0 := by exact_mod_cast ha0
  have hpb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hq0 : ((p : ℚ) ^ n) * (a : ℚ) / (b : ℚ) ≠ 0 :=
    div_ne_zero (mul_ne_zero hpn0 hpa0) hpb0
  have hva : padicValRat p (a : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd ha]
    norm_num
  have hvb : padicValRat p (b : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hbp]
    norm_num
  simp only [Chapter02PadicAbsoluteValue, if_neg hq0]
  rw [padicValRat.div (mul_ne_zero hpn0 hpa0) hpb0,
    padicValRat.mul hpn0 hpa0, padicValRat.pow,
    padicValRat.self (show 1 < p from (Fact.out : Nat.Prime p).one_lt), hva, hvb]
  norm_num

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
  have hlogc : Real.log c < 0 := Real.log_neg hc hc1
  have hmul : ∀ x y : K,
      Chapter02LogarithmicValueFromAbsoluteValue c hc hc1 (f : K → ℝ) (x * y) =
        Chapter02LogarithmicValueFromAbsoluteValue c hc hc1 (f : K → ℝ) x +
          Chapter02LogarithmicValueFromAbsoluteValue c hc hc1 (f : K → ℝ) y := by
    intro x y
    classical
    by_cases hx : x = 0
    · simp [Chapter02LogarithmicValueFromAbsoluteValue, hx]
    by_cases hy : y = 0
    · simp [Chapter02LogarithmicValueFromAbsoluteValue, hy]
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    simp only [Chapter02LogarithmicValueFromAbsoluteValue, dif_neg hx, dif_neg hy,
      dif_neg hxy]
    rw [f.map_mul, Real.log_mul (f.ne_zero hx) (f.ne_zero hy), add_div]
    exact (WithTop.coe_add _ _).symm
  have hadd : ∀ x y : K,
      min (Chapter02LogarithmicValueFromAbsoluteValue c hc hc1 (f : K → ℝ) x)
          (Chapter02LogarithmicValueFromAbsoluteValue c hc hc1 (f : K → ℝ) y) ≤
        Chapter02LogarithmicValueFromAbsoluteValue c hc hc1 (f : K → ℝ) (x + y) := by
    intro x y
    classical
    by_cases hxy : x + y = 0
    · have htop : Chapter02LogarithmicValueFromAbsoluteValue c hc hc1
          (f : K → ℝ) (x + y) = ⊤ := by
        simp [Chapter02LogarithmicValueFromAbsoluteValue, hxy]
      rw [htop]
      exact le_top
    by_cases hx : x = 0
    · subst x
      simp [Chapter02LogarithmicValueFromAbsoluteValue, hxy]
    by_cases hy : y = 0
    · subst y
      simp [Chapter02LogarithmicValueFromAbsoluteValue, hxy]
    simp only [Chapter02LogarithmicValueFromAbsoluteValue, dif_neg hx, dif_neg hy,
      dif_neg hxy]
    rcases le_total (f x) (f y) with hxyf | hyxf
    · have hlogxy : Real.log (f x) ≤ Real.log (f y) :=
        Real.strictMonoOn_log.monotoneOn (f.pos hx) (f.pos hy) hxyf
      have hmin : min (Real.log (f x) / Real.log c)
            (Real.log (f y) / Real.log c) =
          Real.log (f y) / Real.log c := by
        rw [min_eq_right]
        exact (div_le_div_right_of_neg hlogc).2 hlogxy
      have hsum : f (x + y) ≤ f y := by
        simpa [max_eq_right hxyf] using hf x y
      have hlogsum : Real.log (f (x + y)) ≤ Real.log (f y) :=
        Real.strictMonoOn_log.monotoneOn (f.pos hxy) (f.pos hy) hsum
      have hdiv : Real.log (f y) / Real.log c ≤
          Real.log (f (x + y)) / Real.log c :=
        (div_le_div_right_of_neg hlogc).2 hlogsum
      exact (min_le_iff.mpr (Or.inr (WithTop.coe_le_coe.mpr hdiv)))
    · have hlogyx : Real.log (f y) ≤ Real.log (f x) :=
        Real.strictMonoOn_log.monotoneOn (f.pos hy) (f.pos hx) hyxf
      have hmin : min (Real.log (f x) / Real.log c)
            (Real.log (f y) / Real.log c) =
          Real.log (f x) / Real.log c := by
        rw [min_eq_left]
        exact (div_le_div_right_of_neg hlogc).2 hlogyx
      have hsum : f (x + y) ≤ f x := by
        simpa [max_eq_left hyxf] using hf x y
      have hlogsum : Real.log (f (x + y)) ≤ Real.log (f x) :=
        Real.strictMonoOn_log.monotoneOn (f.pos hxy) (f.pos hx) hsum
      have hdiv : Real.log (f x) / Real.log c ≤
          Real.log (f (x + y)) / Real.log c :=
        (div_le_div_right_of_neg hlogc).2 hlogsum
      exact (min_le_iff.mpr (Or.inl (WithTop.coe_le_coe.mpr hdiv)))
  let v : AddValuation K (WithTop ℝ) :=
    AddValuation.of
      (fun x => Chapter02LogarithmicValueFromAbsoluteValue c hc hc1
        (f : K → ℝ) x)
      (by simp [Chapter02LogarithmicValueFromAbsoluteValue])
      (by simp [Chapter02LogarithmicValueFromAbsoluteValue])
      hadd hmul
  refine ⟨v, ?_, ?_⟩
  · intro x
    rfl
  · intro w hw
    apply AddValuation.ext
    intro x
    rw [hw x]
    rfl

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
  have hlogc : Real.log c < 0 := Real.log_neg hc hc1
  have hlogd : Real.log d < 0 := Real.log_neg hd hd1
  refine ⟨Real.log c / Real.log d, div_pos_of_neg_of_neg hlogc hlogd, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [Chapter02LogarithmicValueFromAbsoluteValue, hx]
  simp only [Chapter02LogarithmicValueFromAbsoluteValue, dif_neg hx]
  have hsrc : (Real.log (f x) / Real.log c : WithTop ℝ) ≠ ⊤ :=
    WithTop.coe_ne_top
  simp only [dif_neg hsrc, WithTop.coe_untop]
  rw [← WithTop.coe_mul]
  apply WithTop.coe_injective
  field_simp [ne_of_lt hlogc, ne_of_lt hlogd]

theorem chapter02_positive_rescaling_preserves_comparisons
    {K : Type*} [Field K] (v w : K → WithTop ℝ)
    (h : Chapter02PositiveValueRescaling v w) (x y : K) :
    v x ≤ v y ↔ w x ≤ w y := by
  rcases h with ⟨r, hr, hw⟩
  by_cases hx : v x = ⊤
  · by_cases hy : v y = ⊤
    · simp [hw, hx, hy]
    · simp only [hw, dif_pos hx, dif_neg hy]
      have hne : (↑r * v y : WithTop ℝ) ≠ ⊤ := by
        cases hval : v y with
        | top => exact (hy hval).elim
        | coe z =>
            rw [← WithTop.coe_mul]
            exact WithTop.coe_ne_top
      simp [hx, hy, hw, hne]
  · by_cases hy : v y = ⊤
    · simp [hw, hx, hy]
    · simp only [hw, dif_neg hx, dif_neg hy]
      constructor
      · intro hxy
        have hxy' :
            (v x).untop hx ≤ (v y).untop hy :=
          WithTop.coe_le_coe.mp (by
            simpa only [WithTop.coe_untop] using hxy)
        exact WithTop.coe_le_coe.mpr
          ((mul_le_mul_iff_of_pos_left hr).2 hxy')
      · intro hxy
        have hxy' : (v x).untop hx ≤ (v y).untop hy :=
          (mul_le_mul_iff_of_pos_left hr).1
            (WithTop.coe_le_coe.mp hxy)
        exact by
          simpa only [WithTop.coe_untop] using
            (WithTop.coe_le_coe.mpr hxy')

/-! ## 2.6. Trivial valuations and a failure of the ordinary absolute value -/

def Chapter02TrivialAdditiveValuation {K : Type*} [Field K] :
    AddValuation K (WithTop ℤ) := by
  classical
  exact AddValuation.of (fun x : K => if x = 0 then ⊤ else 0)
    (by simp) (by simp)
    (by
      intro x y
      by_cases hx : x = 0
      · by_cases hy : y = 0 <;> simp [hx, hy]
      by_cases hy : y = 0
      · simp [hy]
      by_cases hxy : x + y = 0 <;> simp [hx, hy, hxy])
    (by
      intro x y
      by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy])

theorem chapter02_trivial_valuation_ring_is_the_whole_field
    {K : Type*} [Field K] :
    Chapter02ValuationRing (Chapter02TrivialAdditiveValuation :
      AddValuation K (WithTop ℤ)) = (⊤ : Subring K) := by
  ext x
  by_cases hx : x = 0 <;>
    simp [Chapter02ValuationRing, Chapter02TrivialAdditiveValuation, hx]

def Chapter02TrivialAbsoluteValue {K : Type*} [Field K] (x : K) : ℝ := by
  classical
  exact if x = 0 then 0 else 1

theorem chapter02_trivial_absolute_value_is_one_off_zero
    {K : Type*} [Field K] {x : K} (hx : x ≠ 0) :
    Chapter02TrivialAbsoluteValue x = 1 := by
  simp [Chapter02TrivialAbsoluteValue, hx]

def Chapter02TrivialDistance {K : Type*} [Field K] (x y : K) : ℝ := by
  classical
  exact if x = y then 0 else 1

theorem chapter02_trivial_distance_characterization
    {K : Type*} [Field K] (x y : K) :
    Chapter02TrivialDistance x y = 0 ↔ x = y := by
  simp [Chapter02TrivialDistance]

theorem chapter02_trivial_distance_of_distinct_points
    {K : Type*} [Field K] {x y : K} (hxy : x ≠ y) :
    Chapter02TrivialDistance x y = 1 := by
  simp [Chapter02TrivialDistance, hxy]

def Chapter02OrdinaryRationalAbsoluteValue (x : ℚ) : ℝ :=
  |(x : ℝ)|

theorem chapter02_ordinary_absolute_value_fails_ultrametricity :
    ¬ Chapter02IsUltrametricAbsoluteValue Chapter02OrdinaryRationalAbsoluteValue := by
  intro h
  have hh := h 1 1
  norm_num [Chapter02OrdinaryRationalAbsoluteValue] at hh

theorem chapter02_ordinary_absolute_value_one_plus_one :
    Chapter02OrdinaryRationalAbsoluteValue (1 + 1) = 2 ∧
      Chapter02OrdinaryRationalAbsoluteValue 1 = 1 := by
  norm_num [Chapter02OrdinaryRationalAbsoluteValue]

theorem chapter02_rational_completion_is_real_model :
    Nonempty (UniformSpace.Completion ℚ ≃ₜ ℝ) := by
  have hU := Rat.uniformSpace_eq
  have hB :
      CompareReals.Bourbaki.uniformSpace =
        @UniformSpace.Completion.uniformSpace ℚ
          (@AbsoluteValue.abs ℚ _).uniformSpace := by
    unfold CompareReals.Bourbaki.uniformSpace CompareReals.uniformSpace
    rfl
  have eAbs :
    @Homeomorph
        (@UniformSpace.Completion ℚ (@AbsoluteValue.abs ℚ _).uniformSpace) ℝ
        (@UniformSpace.Completion.uniformSpace ℚ
          (@AbsoluteValue.abs ℚ _).uniformSpace).toTopologicalSpace
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    have e := CompareReals.compareEquiv.toHomeomorph
    have htop := congrArg
      (fun u : UniformSpace CompareReals.Bourbakiℝ => u.toTopologicalSpace) hB
    rw [htop] at e
    change @Homeomorph
      (@UniformSpace.Completion ℚ (@AbsoluteValue.abs ℚ _).uniformSpace) ℝ
      (@UniformSpace.Completion.uniformSpace ℚ
        (@AbsoluteValue.abs ℚ _).uniformSpace).toTopologicalSpace
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace at e
    exact e
  exact ⟨hU ▸ eAbs⟩

def Chapter02UltrametricDistance {K : Type*} [Ring K]
    (f : K → ℝ) (x y : K) : ℝ := f (x - y)

theorem chapter02_ultrametric_longest_side
    {K : Type*} [Ring K] (f : K → ℝ)
    (hf : Chapter02IsUltrametricAbsoluteValue f) (x y z : K) :
    Chapter02UltrametricDistance f x z ≤
      max (Chapter02UltrametricDistance f x y)
        (Chapter02UltrametricDistance f y z) := by
  simpa [Chapter02UltrametricDistance, sub_eq_add_neg, add_assoc, add_comm,
    add_left_comm] using hf (x - y) (y - z)

theorem chapter02_ultrametric_series_criterion
    {K : Type*} [NormedAddCommGroup K] [CompleteSpace K]
    (htri : ∀ x y : K, ‖x + y‖ ≤ max ‖x‖ ‖y‖) (u : ℕ → K)
    (hu : Filter.Tendsto (fun n => ‖u n‖) Filter.atTop (nhds 0)) :
    Summable u := by
  rw [summable_iff_vanishing_norm]
  intro ε hε
  have hev : ∀ᶠ n in Filter.atTop, ‖u n‖ < ε :=
    hu.eventually (Iio_mem_nhds hε)
  have hev' : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖u n‖ < ε := by
    simpa only [Filter.eventually_atTop] using hev
  rcases hev' with ⟨N, hN⟩
  refine ⟨Finset.range N, ?_⟩
  intro t hdis
  induction t using Finset.induction_on with
  | empty => simp [hε]
  | @insert a t ha ih =>
      rw [Finset.sum_insert ha]
      apply lt_of_le_of_lt (htri (u a) (∑ i ∈ t, u i))
      apply max_lt
      · apply hN
        by_contra hna
        have haN : a ∈ Finset.range N :=
          Finset.mem_range.mpr (Nat.lt_of_not_ge hna)
        exact Finset.disjoint_left.mp hdis (Finset.mem_insert_self a t) haN
      · apply ih
        exact Finset.disjoint_left.2 (by
          intro i hi hiN
          exact Finset.disjoint_left.mp hdis
            (Finset.mem_insert_of_mem hi) hiN)

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
  classical
  let W : Polynomial K → ℕ → WithTop Λ :=
    fun p i => Chapter02WeightedCoefficientValue v e α (p.coeff i) i
  have hG (p : Polynomial K) (i : ℕ) :
      Chapter02GaussValuationFunction v e α p ≤ W p i := by
    by_cases hp : p.support.Nonempty
    · by_cases hi : i ∈ p.support
      · simp only [W, Chapter02GaussValuationFunction, dif_pos hp]
        exact Finset.inf'_le _ hi
      · have hzero : p.coeff i = 0 := Polynomial.notMem_support_iff.mp hi
        have hp' : p.support.Nonempty := hp
        obtain ⟨b, hb⟩ := hp'
        simp only [W, Chapter02GaussValuationFunction, dif_pos hp]
        exact (Finset.inf'_le _ hb).trans (by
          simp [Chapter02WeightedCoefficientValue, hzero])
    · have hp0 : p = 0 := by
        by_contra hp0
        exact hp (Polynomial.support_nonempty.mpr hp0)
      subst p
      simp [W, Chapter02GaussValuationFunction, Chapter02WeightedCoefficientValue]
  have hW (i : ℕ) : min (W f i) (W g i) ≤ W (f + g) i := by
    by_cases hfi : f.coeff i = 0
    · simp [W, Chapter02WeightedCoefficientValue, hfi]
    by_cases hgi : g.coeff i = 0
    · simp [W, Chapter02WeightedCoefficientValue, hgi]
    by_cases hsum : f.coeff i + g.coeff i = 0
    · simp [W, Chapter02WeightedCoefficientValue, hsum]
    have hfv : v (f.coeff i) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 hfi
    have hgv : v (g.coeff i) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 hgi
    have hsv : v (f.coeff i + g.coeff i) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 hsum
    rcases le_total (v (f.coeff i)) (v (g.coeff i)) with hfg | hgf
    · have hmin : W f i ≤ W g i := by
        simp only [W, Chapter02WeightedCoefficientValue, dif_neg hfv, dif_neg hgv]
        have hfg' :
            ((v (f.coeff i)).untop hfv : WithTop Γ) ≤
              (v (g.coeff i)).untop hgv := by
          simpa only [WithTop.coe_untop] using hfg
        exact WithTop.coe_le_coe.mpr
          (add_le_add_left ((OrderHomClass.monotone e)
            (WithTop.coe_le_coe.mp hfg')) (i • α))
      have hsumv : v (f.coeff i) ≤ v (f.coeff i + g.coeff i) := by
        have h := v.map_add (f.coeff i) (g.coeff i)
        simpa [min_eq_left hfg] using h
      have hsumv' : (v (f.coeff i)).untop hfv ≤
          (v (f.coeff i + g.coeff i)).untop hsv :=
        WithTop.coe_le_coe.mp (by
          simpa only [WithTop.coe_untop] using hsumv)
      have hweighted := add_le_add_left ((OrderHomClass.monotone e) hsumv') (i • α)
      rw [min_eq_left hmin]
      simp only [W, Polynomial.coeff_add, Chapter02WeightedCoefficientValue,
        dif_neg hfv, dif_neg hsv]
      exact WithTop.coe_le_coe.mpr hweighted
    · have hmin : W g i ≤ W f i := by
        simp only [W, Chapter02WeightedCoefficientValue, dif_neg hgv, dif_neg hfv]
        have hgf' :
            ((v (g.coeff i)).untop hgv : WithTop Γ) ≤
              (v (f.coeff i)).untop hfv := by
          simpa only [WithTop.coe_untop] using hgf
        exact WithTop.coe_le_coe.mpr
          (add_le_add_left ((OrderHomClass.monotone e)
            (WithTop.coe_le_coe.mp hgf')) (i • α))
      have hsumv : v (g.coeff i) ≤ v (f.coeff i + g.coeff i) := by
        have h := v.map_add (f.coeff i) (g.coeff i)
        simpa [min_eq_right hgf] using h
      have hsumv' : (v (g.coeff i)).untop hgv ≤
          (v (f.coeff i + g.coeff i)).untop hsv :=
        WithTop.coe_le_coe.mp (by
          simpa only [WithTop.coe_untop] using hsumv)
      have hweighted := add_le_add_left ((OrderHomClass.monotone e) hsumv') (i • α)
      rw [min_eq_right hmin]
      simp only [W, Polynomial.coeff_add, Chapter02WeightedCoefficientValue,
        dif_neg hgv, dif_neg hsv]
      exact WithTop.coe_le_coe.mpr hweighted
  by_cases hf : f.support.Nonempty
  · by_cases hg : g.support.Nonempty
    · by_cases hsum : (f + g).support.Nonempty
      · simp only [Chapter02GaussValuationFunction, dif_pos hf, dif_pos hg, dif_pos hsum]
        rw [Finset.le_inf'_iff]
        intro i hi
        simpa only [W, Chapter02GaussValuationFunction, dif_pos hf, dif_pos hg] using
          ((min_le_min (hG f i) (hG g i)).trans (hW i))
      · have hzero : f + g = 0 := by
            by_contra hzero
            exact hsum (Polynomial.support_nonempty.mpr hzero)
        simp [Chapter02GaussValuationFunction, hzero]
    · have hg0 : g = 0 := by
        by_contra hg0
        exact hg (Polynomial.support_nonempty.mpr hg0)
      subst g
      simp [Chapter02GaussValuationFunction]
  · have hf0 : f = 0 := by
      by_contra hf0
      exact hf (Polynomial.support_nonempty.mpr hf0)
    subst f
    simp [Chapter02GaussValuationFunction]

theorem chapter02_gauss_valuation_is_multiplicative
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ)
    (f g : Polynomial K) :
    Chapter02GaussValuationFunction v e α (f * g) =
      Chapter02GaussValuationFunction v e α f +
        Chapter02GaussValuationFunction v e α g := by
  classical
  let W : Polynomial K → ℕ → WithTop Λ :=
    fun p i => Chapter02WeightedCoefficientValue v e α (p.coeff i) i
  have hG (p : Polynomial K) (i : ℕ) :
      Chapter02GaussValuationFunction v e α p ≤ W p i := by
    by_cases hp : p.support.Nonempty
    · by_cases hi : i ∈ p.support
      · simp only [W, Chapter02GaussValuationFunction, dif_pos hp]
        exact Finset.inf'_le _ hi
      · have hzero : p.coeff i = 0 := Polynomial.notMem_support_iff.mp hi
        have hp' : p.support.Nonempty := hp
        obtain ⟨b, hb⟩ := hp'
        simp only [W, Chapter02GaussValuationFunction, dif_pos hp]
        exact (Finset.inf'_le _ hb).trans (by
          simp [Chapter02WeightedCoefficientValue, hzero])
    · have hp0 : p = 0 := by
        by_contra hp0
        exact hp (Polynomial.support_nonempty.mpr hp0)
      subst p
      simp [W, Chapter02GaussValuationFunction, Chapter02WeightedCoefficientValue]
  have hterm (k l : ℕ) :
      Chapter02GaussValuationFunction v e α f +
          Chapter02GaussValuationFunction v e α g ≤
        Chapter02WeightedCoefficientValue v e α
          (f.coeff k * g.coeff l) (k + l) := by
    by_cases hfk : f.coeff k = 0
    · simp [Chapter02WeightedCoefficientValue, hfk]
    by_cases hgl : g.coeff l = 0
    · simp [Chapter02WeightedCoefficientValue, hgl]
    have hprod : f.coeff k * g.coeff l ≠ 0 := mul_ne_zero hfk hgl
    have hfk_top : v (f.coeff k) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 hfk
    have hgl_top : v (g.coeff l) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 hgl
    have hprod_top : v (f.coeff k * g.coeff l) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 hprod
    have hsum := add_le_add (hG f k) (hG g l)
    have heq :
        W f k + W g l =
          Chapter02WeightedCoefficientValue v e α
            (f.coeff k * g.coeff l) (k + l) := by
      have hvsum :
          (v (f.coeff k * g.coeff l)).untop hprod_top =
            (v (f.coeff k)).untop hfk_top + (v (g.coeff l)).untop hgl_top := by
        apply WithTop.coe_injective
        simp only [WithTop.coe_untop, v.map_mul, WithTop.coe_add]
      apply WithTop.coe_injective
      simp only [W, Chapter02WeightedCoefficientValue, dif_neg hfk_top,
        dif_neg hgl_top, dif_neg hprod_top, WithTop.coe_add]
      rw [hvsum]
      simp [add_nsmul, add_assoc, add_left_comm, add_comm]
    exact heq ▸ hsum
  have hprod_weight (n : ℕ) (hn : (f * g).coeff n ≠ 0) :
      Chapter02GaussValuationFunction v e α f +
          Chapter02GaussValuationFunction v e α g ≤ W (f * g) n := by
    let s : Finset (ℕ × ℕ) :=
      Finset.HasAntidiagonal.antidiagonal (A := ℕ) n
    have hs : s.Nonempty := by
      refine ⟨(n, 0), ?_⟩
      simp [s]
    have hex : ∃ p ∈ s, f.coeff p.1 * g.coeff p.2 ≠ 0 := by
      by_contra h
      push_neg at h
      apply hn
      rw [Polynomial.coeff_mul]
      apply Finset.sum_eq_zero
      intro r hr
      exact h r (by simpa [s] using hr)
    obtain ⟨p, hp, hp0⟩ := hex
    obtain ⟨q, hq, hqmin⟩ :=
      Finset.exists_min_image s
        (fun r => v (f.coeff r.1 * g.coeff r.2)) hs
    have hqtop : v (f.coeff q.1 * g.coeff q.2) ≠ (⊤ : WithTop Γ) :=
      ne_of_lt ((hqmin p hp).trans_lt
        (lt_top_iff_ne_top.mpr ((AddValuation.ne_top_iff v).2 hp0)))
    have hval :
        v (f.coeff q.1 * g.coeff q.2) ≤ v ((f * g).coeff n) := by
      rw [Polynomial.coeff_mul]
      exact v.map_le_sum (by
        intro r hr
        exact hqmin r (by simpa [s] using hr))
    have hval' :
        (v (f.coeff q.1 * g.coeff q.2)).untop hqtop ≤
          (v ((f * g).coeff n)).untop
            ((AddValuation.ne_top_iff v).2 hn) :=
      WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hval)
    have heval := (OrderHomClass.monotone e) hval'
    have hweighted :
        (e ((v (f.coeff q.1 * g.coeff q.2)).untop hqtop) +
            n • α : Λ) ≤
          e ((v ((f * g).coeff n)).untop
            ((AddValuation.ne_top_iff v).2 hn)) + n • α := by
      exact add_le_add_left heval (n • α)
    have hqsum : q.1 + q.2 = n := by simpa [s] using hq
    have hqterm := hterm q.1 q.2
    rw [hqsum] at hqterm
    have hqprod : f.coeff q.1 * g.coeff q.2 ≠ 0 :=
      (AddValuation.ne_top_iff v).1 hqtop
    have hqf : f.coeff q.1 ≠ 0 := by
      intro hqf
      exact hqprod (by simp [hqf])
    have hqg : g.coeff q.2 ≠ 0 := by
      intro hqg
      exact hqprod (by simp [hqg])
    have hqterm' :
        Chapter02GaussValuationFunction v e α f +
            Chapter02GaussValuationFunction v e α g ≤
          (e ((v (f.coeff q.1 * g.coeff q.2)).untop hqtop) +
            n • α : Λ) := by
      simpa [Chapter02WeightedCoefficientValue, hqf, hqg, hqtop] using hqterm
    have hWn : W (f * g) n =
        (e ((v ((f * g).coeff n)).untop
          ((AddValuation.ne_top_iff v).2 hn)) + n • α : Λ) := by
      simp only [W, Chapter02WeightedCoefficientValue,
        dif_neg ((AddValuation.ne_top_iff v).2 hn)]
    exact hqterm'.trans (by
      rw [hWn]
      exact WithTop.coe_le_coe.mpr hweighted)
  by_cases hf : f = 0
  · simp [hf, Chapter02GaussValuationFunction]
  by_cases hg : g = 0
  · simp [hg, Chapter02GaussValuationFunction]
  have hfS : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  have hgS : g.support.Nonempty := Polynomial.support_nonempty.mpr hg
  let Sf : Finset ℕ :=
    f.support.filter
      (fun i => W f i = Chapter02GaussValuationFunction v e α f)
  let Sg : Finset ℕ :=
    g.support.filter
      (fun i => W g i = Chapter02GaussValuationFunction v e α g)
  have hSf : Sf.Nonempty := by
    obtain ⟨i, hi, hi_eq⟩ :=
      Finset.exists_mem_eq_inf' (s := f.support) hfS
        (fun j => Chapter02WeightedCoefficientValue v e α (f.coeff j) j)
    refine ⟨i, ?_⟩
    exact Finset.mem_filter.mpr ⟨hi, by
      simpa only [W, Chapter02GaussValuationFunction, dif_pos hfS] using hi_eq.symm⟩
  have hSg : Sg.Nonempty := by
    obtain ⟨i, hi, hi_eq⟩ :=
      Finset.exists_mem_eq_inf' (s := g.support) hgS
        (fun j => Chapter02WeightedCoefficientValue v e α (g.coeff j) j)
    refine ⟨i, ?_⟩
    exact Finset.mem_filter.mpr ⟨hi, by
      simpa only [W, Chapter02GaussValuationFunction, dif_pos hgS] using hi_eq.symm⟩
  let i : ℕ := Sf.max' hSf
  let j : ℕ := Sg.max' hSg
  have hiS : i ∈ Sf := by
    exact Finset.max'_mem Sf hSf
  have hjS : j ∈ Sg := by
    exact Finset.max'_mem Sg hSg
  have hiF : i ∈ f.support := (Finset.mem_filter.mp hiS).1
  have hjG : j ∈ g.support := (Finset.mem_filter.mp hjS).1
  have hi_eq :
      W f i = Chapter02GaussValuationFunction v e α f :=
    (Finset.mem_filter.mp hiS).2
  have hj_eq :
      W g j = Chapter02GaussValuationFunction v e α g :=
    (Finset.mem_filter.mp hjS).2
  have hmaxF {k : ℕ} (hk : k ∈ Sf) : k ≤ i :=
    Finset.le_max' Sf k hk
  have hmaxG {l : ℕ} (hl : l ∈ Sg) : l ≤ j :=
    Finset.le_max' Sg l hl
  have hstrictF {k : ℕ} (hk : k ∈ f.support) (hik : i < k) :
      W f i < W f k := by
    have hle : W f i ≤ W f k := by
      rw [hi_eq]
      exact hG f k
    apply lt_of_le_of_ne hle
    intro heq
    have hkS : k ∈ Sf := Finset.mem_filter.mpr ⟨hk, heq.symm.trans hi_eq⟩
    exact (not_le_of_gt hik) (hmaxF hkS)
  have hstrictG {l : ℕ} (hl : l ∈ g.support) (hjl : j < l) :
      W g j < W g l := by
    have hle : W g j ≤ W g l := by
      rw [hj_eq]
      exact hG g l
    apply lt_of_le_of_ne hle
    intro heq
    have hlS : l ∈ Sg := Finset.mem_filter.mpr ⟨hl, heq.symm.trans hj_eq⟩
    exact (not_le_of_gt hjl) (hmaxG hlS)
  have hpair_lt {k l : ℕ} (hk : k ∈ f.support) (hl : l ∈ g.support)
      (hkl : k + l = i + j) (hne : (k, l) ≠ (i, j)) :
      v (f.coeff i * g.coeff j) < v (f.coeff k * g.coeff l) := by
    have hif : f.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hiF
    have hjg : g.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hjG
    have hklf : f.coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
    have hklg : g.coeff l ≠ 0 := Polynomial.mem_support_iff.mp hl
    have hsel : v (f.coeff i * g.coeff j) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 (mul_ne_zero hif hjg)
    by_contra hnot
    have hval : v (f.coeff k * g.coeff l) ≤
        v (f.coeff i * g.coeff j) := le_of_not_gt hnot
    have hval' :
        (v (f.coeff k * g.coeff l)).untop
            ((AddValuation.ne_top_iff v).2 (mul_ne_zero hklf hklg)) ≤
          (v (f.coeff i * g.coeff j)).untop hsel :=
      WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hval)
    have hsumW :
        W f k + W g l ≤ W f i + W g j := by
      have htotal :
          e ((v (f.coeff k * g.coeff l)).untop
              ((AddValuation.ne_top_iff v).2 (mul_ne_zero hklf hklg))) +
              (k + l) • α ≤
            e ((v (f.coeff i * g.coeff j)).untop hsel) +
              (i + j) • α := by
        have := add_le_add_left ((OrderHomClass.monotone e) hval') ((k + l) • α)
        simpa only [hkl] using this
      have hvkl :
          (v (f.coeff k * g.coeff l)).untop
              ((AddValuation.ne_top_iff v).2 (mul_ne_zero hklf hklg)) =
            (v (f.coeff k)).untop
                ((AddValuation.ne_top_iff v).2 hklf) +
              (v (g.coeff l)).untop
                ((AddValuation.ne_top_iff v).2 hklg) := by
        apply WithTop.coe_injective
        simp only [WithTop.coe_untop, v.map_mul, WithTop.coe_add]
      have hvij :
          (v (f.coeff i * g.coeff j)).untop hsel =
            (v (f.coeff i)).untop
                ((AddValuation.ne_top_iff v).2 hif) +
              (v (g.coeff j)).untop
                ((AddValuation.ne_top_iff v).2 hjg) := by
        apply WithTop.coe_injective
        simp only [WithTop.coe_untop, v.map_mul, WithTop.coe_add]
      have htotal' :
          (e ((v (f.coeff k * g.coeff l)).untop
              ((AddValuation.ne_top_iff v).2 (mul_ne_zero hklf hklg))) +
            (k + l) • α : WithTop Λ) ≤
          (e ((v (f.coeff i * g.coeff j)).untop hsel) +
            (i + j) • α : WithTop Λ) :=
        WithTop.coe_le_coe.mpr htotal
      have hWfkval : W f k =
          (e ((v (f.coeff k)).untop
            ((AddValuation.ne_top_iff v).2 hklf)) + k • α : Λ) := by
        simp only [W, Chapter02WeightedCoefficientValue,
          dif_neg ((AddValuation.ne_top_iff v).2 hklf)]
      have hWglval : W g l =
          (e ((v (g.coeff l)).untop
            ((AddValuation.ne_top_iff v).2 hklg)) + l • α : Λ) := by
        simp only [W, Chapter02WeightedCoefficientValue,
          dif_neg ((AddValuation.ne_top_iff v).2 hklg)]
      have hWfival : W f i =
          (e ((v (f.coeff i)).untop
            ((AddValuation.ne_top_iff v).2 hif)) + i • α : Λ) := by
        simp only [W, Chapter02WeightedCoefficientValue,
          dif_neg ((AddValuation.ne_top_iff v).2 hif)]
      have hWgjval : W g j =
          (e ((v (g.coeff j)).untop
            ((AddValuation.ne_top_iff v).2 hjg)) + j • α : Λ) := by
        simp only [W, Chapter02WeightedCoefficientValue,
          dif_neg ((AddValuation.ne_top_iff v).2 hjg)]
      calc
        W f k + W g l =
            ((e ((v (f.coeff k)).untop
                ((AddValuation.ne_top_iff v).2 hklf)) + k • α : Λ) :
              WithTop Λ) +
              ((e ((v (g.coeff l)).untop
                ((AddValuation.ne_top_iff v).2 hklg)) + l • α : Λ) :
                WithTop Λ) := by rw [hWfkval, hWglval]
        _ = (e ((v (f.coeff k * g.coeff l)).untop
              ((AddValuation.ne_top_iff v).2 (mul_ne_zero hklf hklg))) +
            (k + l) • α : Λ) := by
          rw [← WithTop.coe_add]
          apply WithTop.coe_injective
          rw [hvkl, map_add]
          simp only [add_nsmul]
          abel
        _ ≤ (e ((v (f.coeff i * g.coeff j)).untop hsel) +
            (i + j) • α : Λ) := htotal'
        _ = W f i + W g j := by
          rw [hWfival, hWgjval]
          rw [← WithTop.coe_add]
          apply WithTop.coe_injective
          rw [hvij, map_add]
          simp only [add_nsmul]
          abel
    have hsumW' : W f i + W g j ≤ W f k + W g l := by
      exact add_le_add
        (by rw [hi_eq]; exact hG f k)
        (by rw [hj_eq]; exact hG g l)
    have hsumEq : W f k + W g l = W f i + W g j :=
      le_antisymm hsumW hsumW'
    have hWgl : W g j ≠ (⊤ : WithTop Λ) := by
      simp only [W, Chapter02WeightedCoefficientValue,
        dif_neg ((AddValuation.ne_top_iff v).2 (Polynomial.mem_support_iff.mp hjG))]
      exact WithTop.coe_ne_top
    have hWfi : W f i ≠ (⊤ : WithTop Λ) := by
      simp only [W, Chapter02WeightedCoefficientValue,
        dif_neg ((AddValuation.ne_top_iff v).2 (Polynomial.mem_support_iff.mp hiF))]
      exact WithTop.coe_ne_top
    have hfkEq : W f k = W f i := by
      have hgjle : W g j ≤ W g l := by
        rw [hj_eq]
        exact hG g l
      apply le_antisymm
      · apply (add_le_add_iff_left_of_ne_top hWgl).mp
        calc
          W f k + W g j ≤ W f k + W g l := by
            simpa [add_comm] using (add_le_add_left hgjle (W f k))
          _ = W f i + W g j := hsumEq
      · exact le_of_not_gt (by
          intro h
          exact (not_le_of_gt h)
            (by rw [hi_eq]; exact hG f k))
    have hglEq : W g l = W g j := by
      have hfkle : W f i ≤ W f k := by
        rw [hi_eq]
        exact hG f k
      apply le_antisymm
      · apply (add_le_add_iff_right_of_ne_top hWfi).mp
        calc
          W f i + W g l ≤ W f k + W g l := by
            simpa [add_comm] using (add_le_add_right hfkle (W g l))
          _ = W f i + W g j := hsumEq
      · exact le_of_not_gt (by
          intro h
          exact (not_le_of_gt h)
            (by rw [hj_eq]; exact hG g l))
    have hkS : k ∈ Sf := Finset.mem_filter.mpr ⟨hk, hfkEq.trans hi_eq⟩
    have hlS : l ∈ Sg := Finset.mem_filter.mpr ⟨hl, hglEq.trans hj_eq⟩
    have hk_le : k ≤ i := hmaxF hkS
    have hl_le : l ≤ j := hmaxG hlS
    have : k = i ∧ l = j := by omega
    exact hne (by exact Prod.ext this.1 this.2)
  have hsum_coeff :
      v ((f * g).coeff (i + j)) = v (f.coeff i * g.coeff j) := by
    rw [Polynomial.coeff_mul]
    exact chapter02_strictly_smallest_term_controls_finite_sum v
      (Finset.HasAntidiagonal.antidiagonal (A := ℕ) (i + j))
      (fun p : ℕ × ℕ => f.coeff p.1 * g.coeff p.2) (i, j) (by simp)
      (by
        intro p hp hne
        have hsel_ne : v (f.coeff i * g.coeff j) ≠ (⊤ : WithTop Γ) :=
          (AddValuation.ne_top_iff v).2
            (mul_ne_zero (Polynomial.mem_support_iff.mp hiF)
              (Polynomial.mem_support_iff.mp hjG))
        by_cases hpf : p.1 ∈ f.support
        · by_cases hpg : p.2 ∈ g.support
          · exact hpair_lt hpf hpg (by simpa using hp) hne
          · have hpzero : g.coeff p.2 = 0 :=
              Polynomial.notMem_support_iff.mp hpg
            simpa [hpzero] using (lt_top_iff_ne_top.mpr hsel_ne)
        · have hpzero : f.coeff p.1 = 0 :=
            Polynomial.notMem_support_iff.mp hpf
          simpa [hpzero] using (lt_top_iff_ne_top.mpr hsel_ne))
  have hsel_coeff : (f * g).coeff (i + j) ≠ 0 := by
    have hterm_ne : v (f.coeff i * g.coeff j) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2
        (mul_ne_zero (Polynomial.mem_support_iff.mp hiF)
          (Polynomial.mem_support_iff.mp hjG))
    intro hzero
    apply hterm_ne
    calc
      v (f.coeff i * g.coeff j) = v ((f * g).coeff (i + j)) := hsum_coeff.symm
      _ = ⊤ := by simp [hzero]
  have hprodS : (f * g).support.Nonempty :=
    Polynomial.support_nonempty.mpr (by
      intro hzero
      exact hsel_coeff (by simpa [hzero]))
  have hlower : Chapter02GaussValuationFunction v e α f +
      Chapter02GaussValuationFunction v e α g ≤
        Chapter02GaussValuationFunction v e α (f * g) := by
    simp only [Chapter02GaussValuationFunction, dif_pos hfS, dif_pos hgS, dif_pos hprodS]
    rw [Finset.le_inf'_iff]
    intro n hn
    simpa only [W, Chapter02GaussValuationFunction,
      dif_pos hfS, dif_pos hgS, dif_pos hprodS] using
      hprod_weight n (Polynomial.mem_support_iff.mp hn)
  have hselected :
      W (f * g) (i + j) =
        Chapter02GaussValuationFunction v e α f +
          Chapter02GaussValuationFunction v e α g := by
    have heq :
        W f i + W g j = W (f * g) (i + j) := by
      have hif : f.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hiF
      have hjg : g.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hjG
      have hpij : f.coeff i * g.coeff j ≠ 0 := mul_ne_zero hif hjg
      have hvi : v (f.coeff i) ≠ (⊤ : WithTop Γ) :=
        (AddValuation.ne_top_iff v).2 hif
      have hvj : v (g.coeff j) ≠ (⊤ : WithTop Γ) :=
        (AddValuation.ne_top_iff v).2 hjg
      have hvp : v (f.coeff i * g.coeff j) ≠ (⊤ : WithTop Γ) :=
        (AddValuation.ne_top_iff v).2 hpij
      have hvij :
          (v (f.coeff i * g.coeff j)).untop hvp =
            (v (f.coeff i)).untop hvi + (v (g.coeff j)).untop hvj := by
        apply WithTop.coe_injective
        simp only [WithTop.coe_untop, v.map_mul, WithTop.coe_add]
      have hWfi : W f i =
          (e ((v (f.coeff i)).untop hvi) + i • α : Λ) := by
        simp only [W, Chapter02WeightedCoefficientValue, dif_neg hvi]
      have hWgj : W g j =
          (e ((v (g.coeff j)).untop hvj) + j • α : Λ) := by
        simp only [W, Chapter02WeightedCoefficientValue, dif_neg hvj]
      have hWprod : W (f * g) (i + j) =
          (e ((v ((f * g).coeff (i + j))).untop
            ((AddValuation.ne_top_iff v).2 hsel_coeff)) +
            (i + j) • α : Λ) := by
        simp only [W, Chapter02WeightedCoefficientValue,
          dif_neg ((AddValuation.ne_top_iff v).2 hsel_coeff)]
      have huv :
          (v ((f * g).coeff (i + j))).untop
              ((AddValuation.ne_top_iff v).2 hsel_coeff) =
            (v (f.coeff i * g.coeff j)).untop hvp := by
        apply WithTop.coe_injective
        simpa only [WithTop.coe_untop] using hsum_coeff
      calc
        W f i + W g j =
            ((e ((v (f.coeff i)).untop hvi) + i • α : Λ) : WithTop Λ) +
              ((e ((v (g.coeff j)).untop hvj) + j • α : Λ) : WithTop Λ) := by
          rw [hWfi, hWgj]
        _ = (e ((v (f.coeff i * g.coeff j)).untop hvp) +
            (i + j) • α : Λ) := by
          rw [← WithTop.coe_add]
          apply WithTop.coe_injective
          rw [hvij, map_add]
          simp only [add_nsmul]
          abel
        _ = W (f * g) (i + j) := by
          rw [hWprod]
          apply WithTop.coe_injective
          rw [huv]
    calc
      W (f * g) (i + j) = W f i + W g j := heq.symm
      _ = Chapter02GaussValuationFunction v e α f +
          Chapter02GaussValuationFunction v e α g := by
        rw [hi_eq, hj_eq]
  have hupper : Chapter02GaussValuationFunction v e α (f * g) ≤
      Chapter02GaussValuationFunction v e α f +
        Chapter02GaussValuationFunction v e α g := by
    simp only [Chapter02GaussValuationFunction, dif_pos hprodS]
    exact (Finset.inf'_le _ (by
      exact Polynomial.mem_support_iff.mpr hsel_coeff)).trans_eq hselected
  exact le_antisymm hupper hlower

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
  classical
  let G : Polynomial K → WithTop Λ :=
    Chapter02GaussValuationFunction v e α
  have hcancel (a b c : WithTop Λ) (ha : a ≠ ⊤) :
      a + b - (a + c) = b - c := by
    obtain rfl | hb := eq_or_ne b ⊤
    · simp
    obtain rfl | hc := eq_or_ne c ⊤
    · simp
    cases a with
    | top => exact (ha rfl).elim
    | coe a =>
      cases b with
      | top => exact (hb rfl).elim
      | coe b =>
        cases c with
        | top => exact (hc rfl).elim
        | coe c =>
          change ((a + b - (a + c) : Λ) : WithTop Λ) =
            ((b - c : Λ) : WithTop Λ)
          exact congrArg (fun z : Λ => (z : WithTop Λ))
            (show a + b - (a + c) = b - c by abel)
  have hG_ne_top {p : Polynomial K} (hp : p ≠ 0) : G p ≠ ⊤ := by
    have hs : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
    obtain ⟨i, hi⟩ := hs
    have hpi : p.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
    have hWi :
        Chapter02WeightedCoefficientValue v e α (p.coeff i) i ≠
          (⊤ : WithTop Λ) := by
      simp only [Chapter02WeightedCoefficientValue,
        dif_neg ((AddValuation.ne_top_iff v).2 hpi)]
      exact WithTop.coe_ne_top
    have hle : G p ≤
        Chapter02WeightedCoefficientValue v e α (p.coeff i) i := by
      simp only [G, Chapter02GaussValuationFunction, dif_pos
        (Polynomial.support_nonempty.mpr hp)]
      exact Finset.inf'_le _ hi
    exact ne_of_lt (hle.trans_lt (lt_top_iff_ne_top.mpr hWi))
  by_cases hf0 : f = 0
  · subst f
    simp [Chapter02GaussValuationOnRationalFunctions,
      Chapter02GaussValuationFunction, hg]
  let x : RatFunc K :=
    algebraMap (Polynomial K) (RatFunc K) f /
      algebraMap (Polynomial K) (RatFunc K) g
  have hx : x ≠ 0 := by
    dsimp [x]
    exact div_ne_zero (RatFunc.algebraMap_ne_zero hf0)
      (RatFunc.algebraMap_ne_zero hg)
  let d : Polynomial K := gcd f g
  let f' : Polynomial K := f / d
  let g' : Polynomial K := g / d
  let c : Polynomial K := Polynomial.C (g'.leadingCoeff⁻¹)
  have hd0 : d ≠ 0 := by
    intro hd
    apply hg
    have hzero := (gcd_eq_zero_iff f g).mp (by simpa [d] using hd)
    exact hzero.2
  have hfd : d * f' = f := by
    dsimp [f', d]
    exact EuclideanDomain.mul_div_cancel' hd0
      (gcd_dvd_left f g)
  have hgd : d * g' = g := by
    dsimp [g', d]
    exact EuclideanDomain.mul_div_cancel' hd0
      (gcd_dvd_right f g)
  have hf'0 : f' ≠ 0 := by
    intro hf'
    apply hf0
    calc
      f = d * f' := hfd.symm
      _ = 0 := by simp [hf']
  have hg'0 : g' ≠ 0 := by
    intro hg'
    apply hg
    calc
      g = d * g' := hgd.symm
      _ = 0 := by simp [hg']
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact C_ne_zero.mpr (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hg'0))
  have hGc : G c ≠ ⊤ := hG_ne_top hc0
  have hGd : G d ≠ ⊤ := hG_ne_top hd0
  have hmul (p q : Polynomial K) :
      G (p * q) = G p + G q := by
    change Chapter02GaussValuationFunction v e α (p * q) =
      Chapter02GaussValuationFunction v e α p +
        Chapter02GaussValuationFunction v e α q
    exact chapter02_gauss_valuation_is_multiplicative v e α p q
  have hcf : G (c * f') = G c + G f' := by
    exact hmul c f'
  have hcg : G (c * g') = G c + G g' := by
    exact hmul c g'
  have hdf : G f = G d + G f' := by
    simpa only [hfd] using hmul d f'
  have hdg : G g = G d + G g' := by
    simpa only [hgd] using hmul d g'
  change (if h : x = 0 then ⊤ else G x.num - G x.denom) = G f - G g
  rw [dif_neg hx]
  dsimp [x]
  rw [RatFunc.num_div, RatFunc.denom_div _ hg]
  have hmain : G (c * f') - G (c * g') = G f - G g := by
    calc
      G (c * f') - G (c * g') =
          (G c + G f') - (G c + G g') := by rw [hcf, hcg]
      _ = G f' - G g' := hcancel (G c) (G f') (G g') hGc
      _ = (G d + G f') - (G d + G g') :=
        (hcancel (G d) (G f') (G g') hGd).symm
      _ = G f - G g := by rw [hdf, hdg]
  have hnum :
      Polynomial.C (g / gcd f g).leadingCoeff⁻¹ *
          (f / gcd f g) = c * f' := by
    rfl
  have hden :
      Polynomial.C (g / gcd f g).leadingCoeff⁻¹ *
          (g / gcd f g) = c * g' := by
    rfl
  rw [hnum, hden]
  exact hmain

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
  simp [Chapter02GaussValuationFunction, Chapter02WeightedCoefficientValue]

theorem chapter02_gauss_variable_has_prescribed_value
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) (α : Λ) :
    Chapter02GaussValuationFunction v e α Polynomial.X = (α : WithTop Λ) := by
  simp [Chapter02GaussValuationFunction, Chapter02WeightedCoefficientValue]

theorem chapter02_gauss_positive_parameter_makes_the_variable_small
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ) {α : Λ} (hα : 0 < α) :
    0 < Chapter02GaussValuationFunction v e α Polynomial.X := by
  rw [chapter02_gauss_variable_has_prescribed_value]
  exact WithTop.coe_pos.mpr hα

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
  classical
  have hsupport : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  obtain ⟨i, hi, hi_eq⟩ :=
    Finset.exists_mem_eq_inf' (s := f.support) hsupport
      (fun j => Chapter02WeightedCoefficientValue v e α (f.coeff j) j)
  refine ⟨i, ?_⟩
  exact ⟨hi, by
    simpa [Chapter02GaussValuationFunction, hf] using hi_eq.symm⟩

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
  Ideal.Quotient.mk _ ⟨x, hx⟩

theorem chapter02_withTop_sub_nonneg_of_le
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    {a b : WithTop Γ} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (h : b ≤ a) :
    0 ≤ a - b := by
  have h' : b.untop hb ≤ a.untop ha :=
    WithTop.coe_le_coe.mp (by
      simpa only [WithTop.coe_untop] using h)
  have hco : ((0 : Γ) : WithTop Γ) ≤
      ((a.untop ha - b.untop hb : Γ) : WithTop Γ) :=
    WithTop.coe_le_coe.mpr (sub_nonneg.mpr h')
  rw [← WithTop.coe_untop a ha, ← WithTop.coe_untop b hb]
  change ((0 : Γ) : WithTop Γ) ≤
    ((a.untop ha - b.untop hb : Γ) : WithTop Γ)
  exact hco

theorem chapter02_gauss_residue_remembers_scaled_polynomial
    {K Γ Λ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (v : AddValuation K (WithTop Γ)) (e : Γ →+o Λ)
    {f : Polynomial K} (hf : f ≠ 0) :
    ∃ i : ℕ, ∃ hi : i ∈ f.support,
      ∃ hmin : ∀ j : ℕ, j ∈ f.support →
        v (f.coeff i) ≤ v (f.coeff j),
      Chapter02WeightedCoefficientValue v e 0 (f.coeff i) i =
        Chapter02GaussValuationFunction v e 0 f ∧
      ∃ g : Polynomial (Chapter02ResidueField v),
        g.coeff i = 1 ∧
        g.support ⊆ f.support ∧
        ∀ j : ℕ, (hj : j ∈ f.support) →
          g.coeff j = Chapter02ResidueOfIntegral v
            ((f.coeff j) / (f.coeff i)) (by
              by_cases hzero : f.coeff j = 0
              · simp [hzero]
              have hij : v (f.coeff i) ≤ v (f.coeff j) :=
                hmin j hj
              rw [v.map_div]
              exact chapter02_withTop_sub_nonneg_of_le
                ((AddValuation.ne_top_iff v).2 (Polynomial.mem_support_iff.mp hj))
                ((AddValuation.ne_top_iff v).2
                  (Polynomial.mem_support_iff.mp hi)) hij) := by
  classical
  have hsupport : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  obtain ⟨i, hi, hmin⟩ :=
    Finset.exists_min_image f.support (fun j => v (f.coeff j)) hsupport
  have hfi : f.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hweight (j : ℕ) (hj : j ∈ f.support) :
      Chapter02WeightedCoefficientValue v e 0 (f.coeff i) i ≤
        Chapter02WeightedCoefficientValue v e 0 (f.coeff j) j := by
    have hfj : f.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    have hvi : v (f.coeff i) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 hfi
    have hvj : v (f.coeff j) ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 hfj
    simp only [Chapter02WeightedCoefficientValue, dif_neg hvi, dif_neg hvj,
      nsmul_zero, add_zero]
    have hmin' :
        (v (f.coeff i)).untop
            ((AddValuation.ne_top_iff v).2 hfi) ≤
          (v (f.coeff j)).untop
            ((AddValuation.ne_top_iff v).2 hfj) :=
      WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hmin j hj)
    exact WithTop.coe_le_coe.mpr
      ((OrderHomClass.monotone e) hmin')
  have hGauss :
      Chapter02WeightedCoefficientValue v e 0 (f.coeff i) i =
        Chapter02GaussValuationFunction v e 0 f := by
    apply le_antisymm
    · simp only [Chapter02GaussValuationFunction, dif_pos hsupport]
      rw [Finset.le_inf'_iff]
      intro j hj
      exact hweight j hj
    · simp only [Chapter02GaussValuationFunction, dif_pos hsupport]
      exact Finset.inf'_le _ hi
  have hint (j : ℕ) (hj : j ∈ f.support) :
      0 ≤ v ((f.coeff j) / (f.coeff i)) := by
    have hfj : f.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    rw [v.map_div]
    exact chapter02_withTop_sub_nonneg_of_le
      ((AddValuation.ne_top_iff v).2 hfj)
      ((AddValuation.ne_top_iff v).2 hfi) (hmin j hj)
  let r : ℕ → Chapter02ResidueField v := fun j =>
    if hj : j ∈ f.support then
      Chapter02ResidueOfIntegral v ((f.coeff j) / (f.coeff i)) (hint j hj)
    else 0
  have hr : ∀ j : ℕ, r j ≠ 0 → j ∈ f.support := by
    intro j hj
    by_cases hmem : j ∈ f.support
    · exact hmem
    · have hrzero : r j = 0 := by
        dsimp [r]
        rw [dif_neg hmem]
      exact (hj hrzero).elim
  let F : ℕ →₀ Chapter02ResidueField v :=
    Finsupp.onFinset f.support r hr
  let g : Polynomial (Chapter02ResidueField v) := Polynomial.ofFinsupp ⟨F⟩
  have hgcoeff (j : ℕ) : g.coeff j = r j := by
    simp [g, F]
  have hgsup : g.support ⊆ f.support := by
    intro j hj
    rw [Polynomial.support_ofFinsupp] at hj
    exact (Finsupp.support_onFinset_subset (s := f.support) (f := r)
      (hf := hr)) hj
  have hri : r i = 1 := by
    simp only [r, dif_pos hi]
    have hunit : Chapter02ResidueOfIntegral v (1 : K) (by simp) =
        (1 : Chapter02ResidueField v) := by
      change Ideal.Quotient.mk _ ⟨(1 : K), _⟩ = (1 : Chapter02ResidueField v)
      have hone : (⟨(1 : K), (by simp : 0 ≤ v (1 : K))⟩ :
          Chapter02ValuationSubring v) = 1 := by
        ext
        simp
      rw [hone]
      exact map_one _
    simpa only [div_self hfi] using hunit
  refine ⟨i, hi, hmin, hGauss, g, ?_, hgsup, ?_⟩
  · rw [hgcoeff, hri]
  · intro j hj
    rw [hgcoeff]
    have hfj : f.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    simp [r, hj, hfj]

theorem chapter02_gauss_residue_construction_requires_a_unit_coefficient
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ]
    (v : AddValuation K (WithTop Γ)) {a : K} (ha : a ≠ 0) :
    ∃ s : K, s ≠ 0 ∧ v (s * a) = 0 ∧ v s + v a = 0 := by
  refine ⟨a⁻¹, inv_ne_zero ha, ?_, ?_⟩
  · simp [v.map_mul, ha]
  · rw [v.map_inv]
    exact LinearOrderedAddCommGroupWithTop.neg_add_cancel_of_ne_top
      ((AddValuation.ne_top_iff v).2 ha)

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
  simp [Chapter02TwoStageLaurentValuation]

theorem chapter02_two_stage_value_of_one
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ)) :
    Chapter02TwoStageLaurentValuation v 1 =
      (0 : WithTop (Chapter02TwoStageValueGroup Γ)) := by
  simp [Chapter02TwoStageLaurentValuation]

theorem chapter02_two_stage_value_is_multiplicative
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ))
    (f g : LaurentSeries K) :
    Chapter02TwoStageLaurentValuation v (f * g) =
      Chapter02TwoStageLaurentValuation v f +
        Chapter02TwoStageLaurentValuation v g := by
  by_cases hf : f = 0
  · subst f
    simp [Chapter02TwoStageLaurentValuation]
  by_cases hg : g = 0
  · subst g
    simp [Chapter02TwoStageLaurentValuation]
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have hflead : f.leadingCoeff ≠ 0 :=
    HahnSeries.leadingCoeff_ne_zero.mpr hf
  have hglead : g.leadingCoeff ≠ 0 :=
    HahnSeries.leadingCoeff_ne_zero.mpr hg
  have hvf : v f.leadingCoeff ≠ (⊤ : WithTop Γ) :=
    (AddValuation.ne_top_iff v).2 hflead
  have hvg : v g.leadingCoeff ≠ (⊤ : WithTop Γ) :=
    (AddValuation.ne_top_iff v).2 hglead
  have hvfg : v f.leadingCoeff + v g.leadingCoeff ≠ (⊤ : WithTop Γ) := by
    rw [← v.map_mul]
    exact (AddValuation.ne_top_iff v).2 (mul_ne_zero hflead hglead)
  have hlead : (f * g).leadingCoeff = f.leadingCoeff * g.leadingCoeff :=
    HahnSeries.leadingCoeff_mul_of_ne_zero
      (mul_ne_zero hflead hglead)
  simp only [Chapter02TwoStageLaurentValuation, dif_neg hf, dif_neg hg,
    dif_neg hfg, HahnSeries.order_mul hf hg, hlead, v.map_mul]
  rw [← WithTop.coe_add]
  have hlex :
      (toLex (order f + order g,
        (v f.leadingCoeff + v g.leadingCoeff).untop hvfg) :
        Chapter02TwoStageValueGroup Γ) =
        toLex (order f, (v f.leadingCoeff).untop hvf) +
          toLex (order g, (v g.leadingCoeff).untop hvg) := by
    change toLex (order f + order g,
        (v f.leadingCoeff + v g.leadingCoeff).untop hvfg) =
      toLex ((order f, (v f.leadingCoeff).untop hvf) +
        (order g, (v g.leadingCoeff).untop hvg))
    apply toLex_inj.mp
    apply Prod.ext
    · rfl
    · apply WithTop.coe_injective
      change
        (↑((v f.leadingCoeff + v g.leadingCoeff).untop hvfg) : WithTop Γ) =
          ↑((v f.leadingCoeff).untop hvf + (v g.leadingCoeff).untop hvg)
      simp only [WithTop.coe_untop, WithTop.coe_add]
  exact congrArg (fun x : Chapter02TwoStageValueGroup Γ =>
    (x : WithTop (Chapter02TwoStageValueGroup Γ))) hlex

theorem chapter02_two_stage_value_satisfies_sum_inequality
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ))
    (f g : LaurentSeries K) :
    min (Chapter02TwoStageLaurentValuation v f)
        (Chapter02TwoStageLaurentValuation v g) ≤
      Chapter02TwoStageLaurentValuation v (f + g) := by
  by_cases hf : f = 0
  · subst f
    rw [zero_add]
    simp [Chapter02TwoStageLaurentValuation]
  by_cases hg : g = 0
  · subst g
    rw [add_zero]
    simp [Chapter02TwoStageLaurentValuation]
  by_cases hfg : f + g = 0
  · simp [hfg, Chapter02TwoStageLaurentValuation]
  have hfo : f.orderTop = (f.order : WithTop ℤ) :=
    (HahnSeries.order_eq_orderTop_of_ne_zero hf).symm
  have hgo : g.orderTop = (g.order : WithTop ℤ) :=
    (HahnSeries.order_eq_orderTop_of_ne_zero hg).symm
  have hsumorder : min f.orderTop g.orderTop ≤ (f + g).orderTop :=
    HahnSeries.min_orderTop_le_orderTop_add
  have hvalue_le_of_order_lt {p q : LaurentSeries K} (hp : p ≠ 0)
      (hq : q ≠ 0) (hpq : p.order < q.order) :
      Chapter02TwoStageLaurentValuation v p ≤
        Chapter02TwoStageLaurentValuation v q := by
    simp only [Chapter02TwoStageLaurentValuation, dif_neg hp, dif_neg hq]
    exact WithTop.coe_le_coe.mpr
      (Prod.Lex.toLex_le_toLex.mpr (Or.inl hpq))
  have hvalue_le_of_order_eq {p q : LaurentSeries K} (hp : p ≠ 0)
      (hq : q ≠ 0) (hpq : p.order = q.order)
      (hpqv : v p.leadingCoeff ≤ v q.leadingCoeff) :
      Chapter02TwoStageLaurentValuation v p ≤
        Chapter02TwoStageLaurentValuation v q := by
    have hpv : v p.leadingCoeff ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 (HahnSeries.leadingCoeff_ne_zero.mpr hp)
    have hqv : v q.leadingCoeff ≠ (⊤ : WithTop Γ) :=
      (AddValuation.ne_top_iff v).2 (HahnSeries.leadingCoeff_ne_zero.mpr hq)
    have hpqv' : (v p.leadingCoeff).untop hpv ≤
        (v q.leadingCoeff).untop hqv :=
      WithTop.coe_le_coe.mp (by
        simpa only [WithTop.coe_untop] using hpqv)
    simp only [Chapter02TwoStageLaurentValuation, dif_neg hp, dif_neg hq]
    exact WithTop.coe_le_coe.mpr
      (Prod.Lex.toLex_le_toLex.mpr
        (Or.inr ⟨hpq, hpqv'⟩))
  by_cases hlt : f.order < g.order
  · have ho : (f + g).order = f.order := by
      have horderlt : f.orderTop < g.orderTop := by
        rw [hfo, hgo]
        exact WithTop.coe_lt_coe.mpr hlt
      have htop := HahnSeries.orderTop_add_eq_left horderlt
      apply WithTop.coe_injective
      rw [HahnSeries.order_eq_orderTop_of_ne_zero hfg,
        HahnSeries.order_eq_orderTop_of_ne_zero hf,
        htop]
    have hc := HahnSeries.leadingCoeff_add_eq_left
      (show f.orderTop < g.orderTop by
        rw [hfo, hgo]
        exact WithTop.coe_lt_coe.mpr hlt)
    have hfgval := hvalue_le_of_order_lt hf hg hlt
    have hfsumval :
        Chapter02TwoStageLaurentValuation v f ≤
          Chapter02TwoStageLaurentValuation v (f + g) :=
      hvalue_le_of_order_eq hf hfg ho.symm (by rw [hc])
    rw [min_eq_left hfgval]
    exact hfsumval
  · by_cases hgt : g.order < f.order
    · have ho : (f + g).order = g.order := by
        have horderlt : g.orderTop < f.orderTop := by
          rw [hfo, hgo]
          exact WithTop.coe_lt_coe.mpr hgt
        have htop := HahnSeries.orderTop_add_eq_right horderlt
        apply WithTop.coe_injective
        rw [HahnSeries.order_eq_orderTop_of_ne_zero hfg,
          HahnSeries.order_eq_orderTop_of_ne_zero hg,
          htop]
      have hc := HahnSeries.leadingCoeff_add_eq_right
        (show g.orderTop < f.orderTop by
          rw [hfo, hgo]
          exact WithTop.coe_lt_coe.mpr hgt)
      have hgval := hvalue_le_of_order_lt hg hf hgt
      have hgsumval :
          Chapter02TwoStageLaurentValuation v g ≤
            Chapter02TwoStageLaurentValuation v (f + g) :=
        hvalue_le_of_order_eq hg hfg ho.symm (by rw [hc])
      rw [min_eq_right hgval]
      exact hgsumval
    · have heq : f.order = g.order := le_antisymm (le_of_not_gt hgt)
        (le_of_not_gt hlt)
      have hfirst : f.order ≤ (f + g).order := by
        have h := hsumorder
        rw [hfo, hgo, ← heq, min_self] at h
        rw [← HahnSeries.order_eq_orderTop_of_ne_zero hfg] at h
        exact WithTop.coe_le_coe.mp h
      by_cases hsumord : (f + g).order = f.order
      · have hcoeff : (f + g).leadingCoeff = f.leadingCoeff + g.leadingCoeff := by
          rw [HahnSeries.leadingCoeff_eq, hsumord, HahnSeries.leadingCoeff_eq,
            HahnSeries.leadingCoeff_eq, heq, HahnSeries.coeff_add]
        rcases le_total (v f.leadingCoeff) (v g.leadingCoeff) with hvfg | hvgf
        · have hvadd : v f.leadingCoeff ≤
              v (f.leadingCoeff + g.leadingCoeff) := by
            simpa [min_eq_left hvfg] using v.map_add f.leadingCoeff g.leadingCoeff
          have hvsum : v f.leadingCoeff ≤ v (f + g).leadingCoeff := by
            simpa [hcoeff] using hvadd
          have hfsumval :
              Chapter02TwoStageLaurentValuation v f ≤
                Chapter02TwoStageLaurentValuation v (f + g) :=
            hvalue_le_of_order_eq hf hfg hsumord.symm hvsum
          exact (min_le_left _ _).trans hfsumval
        · have hvadd : v g.leadingCoeff ≤
              v (f.leadingCoeff + g.leadingCoeff) := by
            simpa [min_eq_right hvgf] using v.map_add f.leadingCoeff g.leadingCoeff
          have hvsum : v g.leadingCoeff ≤ v (f + g).leadingCoeff := by
            simpa [hcoeff] using hvadd
          have hgsumval :
              Chapter02TwoStageLaurentValuation v g ≤
                Chapter02TwoStageLaurentValuation v (f + g) :=
            hvalue_le_of_order_eq hg hfg (hsumord.trans heq).symm hvsum
          exact (min_le_right _ _).trans hgsumval
      · have hstrict : f.order < (f + g).order :=
          lt_of_le_of_ne hfirst (Ne.symm hsumord)
        have hfsumval := hvalue_le_of_order_lt hf hfg hstrict
        exact (min_le_left _ _).trans hfsumval

noncomputable def Chapter02TwoStageAdditiveValuation
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ)) :
    AddValuation (LaurentSeries K) (WithTop (Chapter02TwoStageValueGroup Γ)) :=
  AddValuation.of (Chapter02TwoStageLaurentValuation v)
    (chapter02_two_stage_value_of_zero v)
    (chapter02_two_stage_value_of_one v)
    (chapter02_two_stage_value_satisfies_sum_inequality v)
    (chapter02_two_stage_value_is_multiplicative v)

theorem chapter02_positive_T_order_outweighs_every_coefficient_value
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    {n : ℤ} (hn : 0 < n) (γ : Γ) :
    toLex (0, γ) < toLex (n, 0) := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hn)

theorem chapter02_two_stage_order_is_lexicographic
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ))
    {f : LaurentSeries K} (hf : f ≠ 0) :
    ∃ n : ℤ, ∃ a : K, ∃ ha : a ≠ 0, n = f.order ∧ a = f.leadingCoeff ∧
      Chapter02TwoStageLaurentValuation v f =
        ((toLex (n, (v a).untop (by
          exact (AddValuation.ne_top_iff v).2 ha)) :
          Chapter02TwoStageValueGroup Γ) :
          WithTop (Chapter02TwoStageValueGroup Γ)) := by
  refine ⟨f.order, f.leadingCoeff, HahnSeries.leadingCoeff_ne_zero.mpr hf, rfl, rfl, ?_⟩
  simp [Chapter02TwoStageLaurentValuation, hf]

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
      ((Chapter02TwoStageLaurentValuation v f).untop
        (by simp [Chapter02TwoStageLaurentValuation, hf]))).1 = f.order := by
  simp [Chapter02TwoStageLaurentValuation, hf]

def Chapter02ConstantLaurentSeries {K : Type*} [Zero K] (a : K) : LaurentSeries K :=
  HahnSeries.single 0 a

theorem chapter02_two_stage_constant_series_recovers_coefficient_value
    {K Γ : Type*} [Field K]
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] (v : AddValuation K (WithTop Γ)) {a : K} (ha : a ≠ 0) :
    (ofLex
      ((Chapter02TwoStageLaurentValuation v (Chapter02ConstantLaurentSeries a)).untop
        (by simp [Chapter02TwoStageLaurentValuation, Chapter02ConstantLaurentSeries, ha]))).2 =
      (v a).untop ((AddValuation.ne_top_iff v).2 ha) := by
  simp [Chapter02ConstantLaurentSeries, Chapter02TwoStageLaurentValuation, ha]

theorem chapter02_two_stage_is_a_higher_rank_value_group
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] :
    ¬ ∃ f : Chapter02TwoStageValueGroup Γ →+o ℝ, Function.Injective f := by
  rintro ⟨f, hf⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : Γ, 0 < γ := by
    by_cases h : ∃ γ : Γ, 0 < γ
    · exact h
    · push_neg at h
      have hneg : ∀ γ : Γ, γ ≤ 0 := fun γ => h γ
      obtain ⟨a, b, hab⟩ := exists_pair_ne Γ
      let γ : Γ := a - b
      have hγ0 : γ ≠ 0 := sub_ne_zero.mpr hab
      by_cases hpos : 0 < γ
      · exact ⟨γ, hpos⟩
      · have hneg' : 0 < -γ := by
          exact neg_pos.mpr (lt_of_le_of_ne (hneg γ) hγ0)
        exact ⟨-γ, hneg'⟩
  have hmono : Monotone f := OrderHomClass.monotone f
  have hnonneg : 0 ≤ f (toLex ((0 : ℤ), γ)) := by
    have hle : f (toLex ((0 : ℤ), 0)) ≤ f (toLex ((0 : ℤ), γ)) :=
      hmono (show toLex ((0 : ℤ), 0) ≤ toLex ((0 : ℤ), γ) by
      exact Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, hγ.le⟩))
    have hzero : f (toLex ((0 : ℤ), (0 : Γ))) = 0 := by
      change f 0 = 0
      exact f.toAddMonoidHom.map_zero
    rw [← hzero]
    exact hle
  have hpos : 0 < f (toLex ((0 : ℤ), γ)) := by
    have hne : f (toLex ((0 : ℤ), γ)) ≠ 0 := by
      intro hz
      have hz0 : f (toLex ((0 : ℤ), 0)) =
          f (toLex ((0 : ℤ), γ)) := by
        rw [show f (toLex ((0 : ℤ), (0 : Γ))) = 0 by
          change f 0 = 0
          exact f.toAddMonoidHom.map_zero, hz]
      have hdom : toLex ((0 : ℤ), 0) = toLex ((0 : ℤ), γ) := hf hz0
      have hdom' : ((0 : ℤ), (0 : Γ)) = ((0 : ℤ), γ) :=
        toLex_inj.mp hdom
      exact hγ.ne (congrArg Prod.snd hdom')
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  obtain ⟨n, hn⟩ := Archimedean.arch (f (toLex ((1 : ℤ), 0))) hpos
  have hltlex : toLex ((0 : ℤ), n • γ) < toLex ((1 : ℤ), 0) :=
    Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by omega))
  have hlt : f (toLex ((0 : ℤ), n • γ)) < f (toLex ((1 : ℤ), 0)) :=
    (hmono.strictMono_of_injective hf) hltlex
  have hmap : f (toLex ((0 : ℤ), n • γ)) =
      n • f (toLex ((0 : ℤ), γ)) := by
    change f (n • toLex ((0 : ℤ), γ)) =
      n • f (toLex ((0 : ℤ), γ))
    exact map_nsmul f n (toLex ((0 : ℤ), γ))
  rw [hmap] at hlt
  exact (not_lt_of_ge hn) hlt

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter02
