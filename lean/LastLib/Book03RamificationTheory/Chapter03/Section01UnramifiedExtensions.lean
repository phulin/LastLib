import LastLib.Book03RamificationTheory.Chapter03.Dependencies
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section02FrobeniusInAnUnramifiedExtension
import Mathlib.FieldTheory.Galois.Basic

namespace LastLib.Book03RamificationTheory.Chapter03

noncomputable section

open scoped BigOperators Pointwise

/-! ## 3.1. Unramified extensions -/

/-
The local data used for the unramified calculation.  `decomposition_top`
records the single-branch/local-field situation in which the source writes
the decomposition group as the full Galois group; faithful reduction is the
intrinsic unramified condition needed for `G_0 = 1`. -/
structure Chapter03UnramifiedGaloisData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] where
  valuationRing : ValuationSubring L
  decomposition_top :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        K valuationRing = ⊤
  reduction_faithful :
    Function.Injective
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ResidueAction
        K valuationRing)

theorem chapter03_unramified_inertia_is_trivial
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : Chapter03UnramifiedGaloisData K L) :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup
        K D.valuationRing = ⊥ := by
  sorry

theorem chapter03_unramified_reduction_has_no_positive_ramification
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : Chapter03UnramifiedGaloisData K L) :
    chapter03GaloisLowerGroup K D.valuationRing (-1) = ⊤ ∧
      chapter03GaloisLowerGroup K D.valuationRing 0 = ⊥ ∧
      (∀ i : ℤ, 0 < i → chapter03GaloisLowerGroup K D.valuationRing i = ⊥) := by
  sorry

theorem chapter03_unramified_lower_groups
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : Chapter03UnramifiedGaloisData K L) :
    chapter03GaloisLowerGroup K D.valuationRing (-1) = ⊤ ∧
      chapter03GaloisLowerGroup K D.valuationRing 0 = ⊥ := by
  sorry

/- SOURCE_ISSUE (3.1): The sentence that Frobenius lies at level `-1` but
   not at level `0` is false for the trivial unramified extension (`f = 1`),
   where Frobenius is the identity.  The theorem below makes the minimal
   correction by assuming the residue extension has degree greater than one. -/

/- Arithmetic Frobenius is recorded at the residue-visible, `-1` level. -/
theorem chapter03_unramified_arithmetic_frobenius_at_minus_one
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : Chapter03UnramifiedGaloisData K L)
    (R : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Chapter06UnramifiedGaloisReduction
      K L k l)
    (hdegree : 1 < Module.finrank k l) :
    (∀ σ : Gal(L / K),
        ∃ n : ℤ,
          (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06UnramifiedArithmeticFrobenius
            R) ^ n = σ) ∧
      chapter03GaloisLowerGroup K D.valuationRing (-1) = ⊤ ∧
      chapter03GaloisLowerGroup K D.valuationRing 0 ≠ ⊤ := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter03
