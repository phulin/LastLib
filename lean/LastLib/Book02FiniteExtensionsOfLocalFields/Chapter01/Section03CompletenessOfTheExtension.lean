import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section02ExistenceUniquenessAndCompleteness
import Mathlib.NumberTheory.Padics.Complex

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01

noncomputable section

/-! # Book 2, Chapter 1, Section 1.3

Finite-dimensional coordinate comparison is recorded through the norm and
Cauchy interfaces already developed in Book 1.  This avoids choosing a new
normed-field instance merely to state the comparison.
-/

/-! ### Coordinate norms and finite-dimensional completeness -/

/-- The coordinate max norm used for a finite basis. -/
abbrev chapter01CoordinateNorm
    {K L ι : Type*} [NormedField K] [AddCommGroup L] [Module K L]
    [Fintype ι] [Nonempty ι] (b : Module.Basis ι K L) : L → ℝ :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10CoordinateNorm b

/-- Coordinate Cauchy sequences converge in the complete base-field setting. -/
theorem chapter01_coordinate_norm_cauchy_sequences_converge
    {K L ι : Type*} [NormedField K] [CompleteSpace K]
    [Field L] [Algebra K L] [Fintype ι] [Nonempty ι]
    (b : Module.Basis ι K L) (s : ℕ → L)
    (hs : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10CauchyInNorm
      (chapter01CoordinateNorm b) s) :
    ∃ x : L,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TendsToInNorm
        (chapter01CoordinateNorm b) s x := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_coordinate_norm_complete
    b s hs

/-- Two-sided bounds express equivalence of an extension norm and coordinates. -/
theorem chapter01_extended_norm_equivalent_to_coordinate_norm
    {K L ι : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [Field L] [Algebra K L] [Fintype ι] [Nonempty ι]
    [FiniteDimensional K L]
    (b : Module.Basis ι K L) (N : AlgebraNorm K L)
    (hN : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10NonarchimedeanNorm
      (N : L → ℝ)) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10EquivalentRealNorms
      (N : L → ℝ) (chapter01CoordinateNorm b) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_nonarchimedean_norm_equivalent_to_coordinate_norm
    b N hN

/-- Equivalent positive real norms have exactly the same Cauchy sequences. -/
def chapter01SameCauchySequences {L : Type*} [AddGroup L]
    (N M : L → ℝ) : Prop :=
  ∀ s : ℕ → L,
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10CauchyInNorm N s ↔
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10CauchyInNorm M s

/-- The coordinate comparison transfers Cauchy completeness to the extension norm. -/
theorem chapter01_equivalent_norms_have_same_cauchy_sequences
    {L : Type*} [AddGroup L] (N M : L → ℝ)
    (heq : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10EquivalentRealNorms N M) :
    chapter01SameCauchySequences N M := by
  sorry

/-- Every finite extension of a complete nontrivially normed field is complete. -/
theorem chapter01_theorem_1_2
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedField L] [NormedAlgebra K L] [FiniteDimensional K L] :
    CompleteSpace L := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_finite_extension_is_complete
    (K := K) (L := L)

/-! ### The infinite algebraic warning -/

/-- The algebraic closure of a `p`-adic field is not complete. -/
theorem chapter01_padic_algebraic_closure_is_not_complete
    [Fact (Nat.Prime 5)] :
    ¬ CompleteSpace (PadicAlgCl 5) := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01
