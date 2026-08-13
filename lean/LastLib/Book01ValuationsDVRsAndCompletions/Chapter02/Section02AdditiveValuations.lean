import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Valuation.Quotient

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
open scoped BigOperators
open Polynomial

/-! # Book 1, Chapter 2, Section 2.2: Additive Valuations
-/

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
    [Nontrivial (Multiplicative Γᵒᵈ)]
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
    [Nontrivial (Multiplicative Γᵒᵈ)]
    (v : AddValuation R Γ) :
    (Chapter02Support v).IsPrime := by
  let _ : Nontrivial Γ := ‹Nontrivial (Multiplicative Γᵒᵈ)›
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
    [Nontrivial (Multiplicative Γᵒᵈ)]
    (v : AddValuation K Γ) : Chapter02Support v = ⊥ := by
  let _ : Nontrivial Γ := ‹Nontrivial (Multiplicative Γᵒᵈ)›
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
      simp [Chapter02FiniteValueOfNonzero, WithTop.coe_untop,
        Units.val_mul, v.map_mul]
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

theorem chapter02_field_unit_value_hom_satisfies_sum_inequality
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] [Nontrivial Γ]
    (v : AddValuation K (WithTop Γ)) :
    Chapter02UnitHomSumInequality (Chapter02FieldUnitValueHom v) := by
  intro x y hx hy hxy
  have hxv : v x ≠ (⊤ : WithTop Γ) := (AddValuation.ne_top_iff v).2 hx
  have hyv : v y ≠ (⊤ : WithTop Γ) := (AddValuation.ne_top_iff v).2 hy
  have hxyv : v (x + y) ≠ (⊤ : WithTop Γ) :=
    (AddValuation.ne_top_iff v).2 hxy
  change min ((v x).untop hxv) ((v y).untop hyv) ≤
    (v (x + y)).untop hxyv
  apply WithTop.coe_le_coe.mp
  simpa only [WithTop.coe_untop, WithTop.coe_min] using v.map_add x y

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
        simp [Chapter02ExtensionValue, hx, hy, Units.mk0_mul])
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
  simp [Chapter02FiniteValueOfNonzero, WithTop.coe_untop,
    WithTop.coe_add, v.map_mul]

def Chapter02SupportQuotientValuation
    {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) :
    AddValuation (R ⧸ Chapter02Support v) Γ := by
  exact AddValuation.onQuot v (by
    simp [Chapter02Support])

theorem chapter02_support_quotient_is_a_domain
    {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
    [Nontrivial (Multiplicative Γᵒᵈ)]
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
      (∀ (a b : A) (_hb : b ≠ 0),
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

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter02
