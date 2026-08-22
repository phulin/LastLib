import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section08TraceAndBoundedness
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section08NormsOfIdealsAndDeterminants
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section05MonogenicityAndResidueGenerators
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section02LinearizingTheNorm
import Mathlib.Algebra.Module.Presentation.Differentials
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Length

namespace LastLib.Book03RamificationTheory.Chapter07

noncomputable section

open scoped BigOperators Polynomial nonZeroDivisors

/-! Common interfaces for Book 3, Chapter 7.  The chapter keeps valuation
    rings and residue fields explicit so that its statements can be used with
    either the canonical `ValuationSubring` or a chosen integral model. -/

/-- The valuation ring attached to an additive valuation. -/
abbrev chapter07ValuationRing {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Type _ :=
  v.toValuation.valuationSubring

/-- The residue field attached to a valuation ring. -/
abbrev chapter07ResidueField {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Type _ :=
  IsLocalRing.ResidueField (chapter07ValuationRing v)

/- A residue-field model must identify the residue map induced by `A → B`
   with the specified field extension `k → l`; separate ring equivalences do
   not provide that compatibility. -/
def chapter07CompatibleResidueModel
    (A B k l : Type*) [CommRing A] [CommRing B] [Field k] [Field l]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [Algebra k l] : Prop :=
  ∃ eA : (A ⧸ IsLocalRing.maximalIdeal A) ≃+* k,
    ∃ eB : (B ⧸ IsLocalRing.maximalIdeal B) ≃+* l,
      ∀ a : A,
        eB (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) (algebraMap A B a)) =
          algebraMap k l
            (eA (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a))

/-- A normalized value-one element, the valuation-level uniformizer interface
    used in the derivative estimates. -/
def chapter07IsUniformizer {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : K) : Prop :=
  π ≠ 0 ∧ v π = (1 : WithTop ℤ)

theorem chapter07_is_uniformizer_ne_zero {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : K)
    (hπ : chapter07IsUniformizer v π) : π ≠ 0 := by
  exact hπ.1

theorem chapter07_is_uniformizer_value {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : K)
    (hπ : chapter07IsUniformizer v π) : v π = (1 : WithTop ℤ) := by
  exact hπ.2

/-- The floor quotient occurring in the trace-ideal formula.  For positive
    `e`, integer division is the floor of `(n + d) / e`, including negative
    exponents. -/
def chapter07FloorDiv (n d : ℤ) (e : ℕ) : ℤ :=
  (n + d) / (e : ℤ)

theorem chapter07FloorDiv_eq_floor (n d : ℤ) (e : ℕ) (he : 0 < e) :
    chapter07FloorDiv n d e = ⌊(n + d : ℚ) / e⌋ := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter07
