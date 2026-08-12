import LastLib.Book05LocalClassFieldTheory.Chapter04.Core

namespace LastLib.Book05LocalClassFieldTheory.Chapter04

noncomputable section

/-! ## 4.1. Why central simple algebras enter reciprocity -/

theorem chapter04_csa_has_canonical_central_simple_instances
    {K : Type*} [Field K] (A : chapter04CentralSimpleAlgebra K) :
    Algebra.IsCentral K A ∧
      IsSimpleRing A ∧
      FiniteDimensional K A := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Every central simple algebra has a matrix-over-division representative. -/
theorem chapter04_wedderburn_decomposition_exists
    {K : Type*} [Field K] (A : chapter04CentralSimpleAlgebra K) :
    Nonempty (Chapter04WedderburnDecomposition A) := by
  sorry

theorem chapter04_wedderburn_division_representative_unique
    {K : Type*} [Field K] (A : chapter04CentralSimpleAlgebra K)
    (W₁ W₂ : Chapter04WedderburnDecomposition A) :
    Nonempty (W₁.division.carrier ≃ₐ[K] W₂.division.carrier) := by
  sorry

theorem chapter04_wedderburn_decomposition_matrix_dimension
    {K : Type*} [Field K] (A : chapter04CentralSimpleAlgebra K)
    (W : Chapter04WedderburnDecomposition A) :
    Module.finrank K A =
      W.matrixSize ^ 2 * Module.finrank K W.division.carrier := by
  sorry

theorem chapter04_brauer_class_eq_iff
    {K : Type*} [Field K]
    (A B : chapter04CentralSimpleAlgebra K) :
    chapter04BrauerClass A = chapter04BrauerClass B ↔
      chapter04BrauerEquivalent A B := by
  sorry

theorem chapter04_brauer_group_law_exists
    (K : Type*) [Field K] :
    Nonempty (Chapter04BrauerGroupLaw K) := by
  sorry

theorem chapter04_brauer_tensor_is_abelian
    {K : Type*} [Field K] (B : Chapter04BrauerGroupLaw K) :
    (∀ a b c, B.tensor (B.tensor a b) c = B.tensor a (B.tensor b c)) ∧
      (∀ a b, B.tensor a b = B.tensor b a) ∧
      (∀ a, B.tensor B.one a = a) ∧
      (∀ a, B.tensor a B.one = a) := by
  exact ⟨B.tensor_assoc, B.tensor_comm, B.one_tensor, B.tensor_one⟩

theorem chapter04_opposite_represents_brauer_inverse
    {K : Type*} [Field K] (B : Chapter04BrauerGroupLaw K)
    (a : chapter04BrauerGroup K) :
    B.tensor a (B.opposite a) = B.one ∧
      B.tensor (B.opposite a) a = B.one := by
  exact ⟨B.tensor_opposite a, B.opposite_tensor a⟩

/- The invariant target is named before its construction.  Section 4.3
  supplies the local invariant data and its restriction formula. -/
def chapter04InvariantTarget : Type := chapter04RationalResidue

theorem chapter04_central_simple_algebra_is_class_representative
    {K : Type*} [Field K] (A : chapter04CentralSimpleAlgebra K) :
    chapter04BrauerClass A = @Quotient.mk' _ (Brauer.CSA_Setoid K) A := rfl

end

end LastLib.Book05LocalClassFieldTheory.Chapter04
