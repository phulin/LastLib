import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section05HigherRamificationBoundary
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Dependencies
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne

namespace LastLib.Book03RamificationTheory.Chapter02

noncomputable section

open scoped BigOperators Pointwise

/-!
Shared valuation-ring interfaces for Chapter 2.

The preceding book-facing API defines congruence groups at the powers of the
maximal ideal.  This chapter uses the lower-numbering shift
`G_i = RamificationGroup (i + 1)`, while `G₋₁` is the whole decomposition group.
The displacement is kept in the normalized additive value group `WithTop ℤ` so
that the minimum formulation and the congruence formulation can be compared.
-/

universe u v

/-- The chosen decomposition group attached to a normalized extension valuation. -/
abbrev chapter02DecompositionGroup
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) : Type _ :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
    K v.toValuation.valuationSubring

/--
The displacement of a decomposition-group automorphism.  The identity is given
the value `+∞`; otherwise the value is the infimum of all integral
displacements.  In the finite discrete situation this infimum is a minimum.
-/
noncomputable def chapter02Displacement
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ))
    (σ : chapter02DecompositionGroup K v) : WithTop ℤ :=
  by
    classical
    exact if σ = 1 then ⊤ else
      sInf (Set.range (fun x : v.toValuation.valuationSubring =>
        v ((σ : Gal(L / K)) (x : L) - (x : L))))

@[simp]
theorem chapter02Displacement_one
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) :
    chapter02Displacement K v (1 : chapter02DecompositionGroup K v) = ⊤ := by
  simp [chapter02Displacement]

/-- The lower group at an integer index, with all negative indices using `G₋₁`. -/
def chapter02LowerGroup
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) (i : ℤ) :
    Subgroup (chapter02DecompositionGroup K v) :=
  if i < 0 then ⊤ else
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
      K v.toValuation.valuationSubring (i.toNat + 1)

/-- The nonnegative lower group in the canonical congruence indexing. -/
abbrev chapter02LowerGroupNat
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) (n : ℕ) :
    Subgroup (chapter02DecompositionGroup K v) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
    K v.toValuation.valuationSubring (n + 1)

/-- The all-integral-elements congruence formulation of a lower group. -/
def chapter02HigherCongruence
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (v : AddValuation L (WithTop ℤ)) (i : ℤ)
    (σ : chapter02DecompositionGroup K v) : Prop :=
  if i < 0 then σ ∈ (⊤ : Subgroup (chapter02DecompositionGroup K v)) else
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
      v.toValuation.valuationSubring (i.toNat + 1) σ

end

end LastLib.Book03RamificationTheory.Chapter02
