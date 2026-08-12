import LastLib.Book04AdelesAndIdeles.Chapter02.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter02

noncomputable section

open NumberField
open scoped BigOperators TensorProduct WithZero

universe u

/-! Shared interfaces for Chapter 2.  The two summands deliberately retain the
canonical Mathlib place types; only the book-facing normalized value combines
the finite and infinite conventions. -/

/-- The finite places of a number field, indexed canonically by height-one primes. -/
abbrev Chapter02FinitePlace (K : Type*) [Field K] [NumberField K] :=
  NumberField.FinitePlace K

/-- The infinite places of a number field. -/
abbrev Chapter02InfinitePlace (K : Type*) [Field K] [NumberField K] :=
  NumberField.InfinitePlace K

/-- A finite-or-infinite place used by the chapter-level API. -/
abbrev Chapter02Place (K : Type*) [Field K] [NumberField K] :=
  Chapter02FinitePlace K ⊕ Chapter02InfinitePlace K

/-- The underlying, unsquared absolute value represented by a place. -/
def Chapter02PlaceAbsoluteValue {K : Type*} [Field K] [NumberField K]
    (v : Chapter02Place K) : AbsoluteValue K ℝ :=
  match v with
  | Sum.inl w => w.1
  | Sum.inr w => w.1

/-- The normalized local size used in the product formula. -/
def Chapter02PlaceValue {K : Type*} [Field K] [NumberField K]
    (v : Chapter02Place K) (x : K) : ℝ :=
  match v with
  | Sum.inl w => w x
  | Sum.inr w => w x ^ w.mult

@[simp]
theorem chapter02_placeValue_finite {K : Type*} [Field K] [NumberField K]
    (w : Chapter02FinitePlace K) (x : K) :
    Chapter02PlaceValue (Sum.inl w : Chapter02Place K) x = w x := rfl

@[simp]
theorem chapter02_placeValue_infinite {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (x : K) :
    Chapter02PlaceValue (Sum.inr w : Chapter02Place K) x = w x ^ w.mult := rfl

/-- The completion attached to a finite place. -/
abbrev Chapter02FiniteCompletion {K : Type*} [Field K] [NumberField K]
    (w : Chapter02FinitePlace K) : Type _ :=
  w.maximalIdeal.adicCompletion K

/-- The completion attached to an infinite place. -/
abbrev Chapter02InfiniteCompletion {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) : Type _ := w.Completion

/-- The Chapter 2 global product, split into its archimedean and finite parts. -/
def Chapter02GlobalProduct {K : Type*} [Field K] [NumberField K] (x : K) : ℝ :=
  (∏ w : Chapter02InfinitePlace K, w x ^ w.mult) *
    ∏ᶠ w : Chapter02FinitePlace K, w x

/-- Rational primes are used as a finite-place index without losing primality. -/
abbrev Chapter02RationalPrime := {p : ℕ // Nat.Prime p}

/-- The global degree appearing in the restriction formulas. -/
def Chapter02GlobalDegree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank ℚ K

end

end LastLib.Book04AdelesAndIdeles.Chapter02
