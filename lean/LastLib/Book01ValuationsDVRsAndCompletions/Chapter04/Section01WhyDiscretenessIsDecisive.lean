import Mathlib.Algebra.Order.Ring.Archimedean
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter04

open scoped BigOperators Multiplicative PowerSeries WithZero
open Ideal IsLocalRing LinearOrderedCommGroup

noncomputable section

/-!
# Chapter 4: Discrete valuation rings

This file is a statement-generation pass for Sections 4.1--4.3 of Book 1.  The
zero-extended multiplicative target `ℤᵐ⁰` is used for Mathlib valuations; its
nonzero part is the additive integer-valued valuation `Kˣ → ℤ` from the prose.
-/

/-! # Book 1, Chapter 4, Section 4.1: Why Discreteness Is Decisive
-/

/-! ## 4.1. Discrete valuation data and uniformizers -/

/-- A Mathlib valuation is discrete in the chapter's sense when it is surjective
onto the zero-extended multiplicative copy of `ℤ`. -/
def IsSurjectiveIntegerValuation (K : Type*) [Field K]
    (v : Valuation K ℤᵐ⁰) : Prop :=
  Function.Surjective v

/-- A valuation witness saying that `A` is the valuation ring of a surjective
integer-valued valuation on its fraction field. -/
structure Chapter04DVRValuationWitness (A K : Type*)
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] where
  valuation : Valuation K ℤᵐ⁰
  surjective : IsSurjectiveIntegerValuation K valuation
  valuationSubring_eq_image :
    valuation.valuationSubring.toSubring =
      Subring.map (algebraMap A K) (⊤ : Subring A)

/-- “`A` is the valuation ring of a discrete valuation `Kˣ → ℤ`”, expressed
using the zero-extended Mathlib valuation interface. -/
def IsValuationRingOfDiscreteValuation (A K : Type*)
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] : Prop :=
  Nonempty (Chapter04DVRValuationWitness A K)

/-- A chapter-local spelling of “uniformizer”: an element generating the maximal
ideal of a local domain. -/
def Chapter04Uniformizer (A : Type*) [CommRing A] [IsDomain A] [IsLocalRing A]
    (π : A) : Prop :=
  π ≠ 0 ∧ IsLocalRing.maximalIdeal A = Ideal.span ({π} : Set A)

/-- Mathlib's normalized additive valuation on a DVR, exposed with a chapter-local name. -/
def chapter04AdditiveValue (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (x : A) : ℕ∞ :=
  IsDiscreteValuationRing.addVal A x

/-- The ideal `(π^r)` used throughout the arithmetic part of the chapter. -/
def chapter04IdealPower (A : Type*) [CommRing A] (π : A) (r : ℕ) : Ideal A :=
  Ideal.span ({π ^ r} : Set A)

/-- The abstract order-theoretic condition that a magnitude order has a first
positive magnitude. -/
def HasLeastPositiveMagnitude (Γ : Type*) [Preorder Γ] [Zero Γ] : Prop :=
  ∃ γ : Γ, 0 < γ ∧ ∀ δ : Γ, 0 < δ → γ ≤ δ

/-- The failure of a first positive magnitude, recording the nondiscrete
rank-one phenomenon mentioned in Section 4.1. -/
def HasNoLeastPositiveMagnitude (Γ : Type*) [Preorder Γ] [Zero Γ] : Prop :=
  ¬ HasLeastPositiveMagnitude Γ

/-- A surjective integer valuation has the discrete generator required by
Mathlib's rank-one discrete valuation interface. -/
theorem surjective_integer_valuation_is_rank_one_discrete
    (K : Type*) [Field K] (v : Valuation K ℤᵐ⁰)
    (hv : IsSurjectiveIntegerValuation K v) :
    Valuation.IsRankOneDiscrete v := by
  let f : K →*₀ ℤᵐ⁰ := MonoidWithZeroHom.ofClass v
  have hvg : MonoidWithZeroHom.valueGroup f = ⊤ := by
    apply top_unique
    intro g hg
    obtain ⟨x, hx⟩ := hv (g : ℤᵐ⁰)
    apply MonoidWithZeroHom.mem_valueGroup f
    exact ⟨x, by simpa [f] using hx⟩
  let : IsCyclic (MonoidWithZeroHom.valueGroup f) := by
    rw [hvg]
    exact (Subgroup.topEquiv.isCyclic :
      IsCyclic (⊤ : Subgroup ((ℤᵐ⁰)ˣ)) ↔ IsCyclic ((ℤᵐ⁰)ˣ)).mpr inferInstance
  let : Nontrivial (MonoidWithZeroHom.valueGroup f) := by
    rw [hvg]
    infer_instance
  exact Valuation.IsRankOneDiscrete.mk' v

/-- The first positive step in a discrete value group is represented by a
generator below `1` in the multiplicative Mathlib convention. -/
theorem rank_one_discrete_valuation_has_generator
    (K : Type*) [Field K] (v : Valuation K ℤᵐ⁰)
    [Valuation.IsRankOneDiscrete v] :
    ∃ γ : (ℤᵐ⁰)ˣ,
      Subgroup.zpowers γ = MonoidWithZeroHom.valueGroup (.ofClass v) ∧ γ < 1 := by
  exact Valuation.IsRankOneDiscrete.exists_generator_lt_one v

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter04
