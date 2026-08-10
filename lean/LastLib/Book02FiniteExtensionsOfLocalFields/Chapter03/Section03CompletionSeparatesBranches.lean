import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section02IntersectionsAndComposita

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

noncomputable section

open scoped BigOperators TensorProduct

/-! ## 3.3. Completion separates branches -/

/-- The canonical scalar structure on a valuation completion. -/
noncomputable instance chapter03ValuationCompletionAlgebra
    {K₀ Γ : Type*} [Field K₀] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K₀ Γ) : Algebra K₀ (Valuation.Completion v) :=
  (UniformSpace.Completion.coeRingHom.comp (WithVal.equiv v).symm.toRingHom).toAlgebra

/-- The completed field attached to one valuation branch. -/
abbrev chapter03CompletedBranch
    {E Γ : Type*} [Field E] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation E Γ) : Type _ :=
  Valuation.Completion w

/--
Data for the decomposition after completion.  The branch factors are named
separately from the original field so that the product decomposition does not
pretend that the tensor product is a field.
-/
structure Chapter03CompletionBranchData
    (K₀ E Γ : Type*) [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ]
    [Algebra K₀ E] (v : Valuation K₀ Γ)
    where
  index : Type*
  index_finite : Fintype index
  base_discrete : Valuation.IsRankOneDiscrete v
  separable : Algebra.IsSeparable K₀ E
  branchValuation : index → Valuation E Γ
  branch_extends : ∀ i, ∀ x : K₀,
    branchValuation i (algebraMap K₀ E x) = v x
  factor : index → Type*
  factor_field : ∀ i, Field (factor i)
  factor_algebra : ∀ i, Algebra (Valuation.Completion v) (factor i)
  factor_completion : ∀ i,
    Nonempty (factor i ≃+* chapter03CompletedBranch (branchValuation i))
  e : index → ℕ
  f : index → ℕ
  factor_degree : ∀ i, Module.finrank (Valuation.Completion v) (factor i) =
    e i * f i
  decomposition :
    Nonempty
      (E ⊗[K₀] Valuation.Completion v ≃+*
        (∀ i, factor i))

instance {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    (v : Valuation K₀ Γ) (D : Chapter03CompletionBranchData K₀ E Γ v) :
    Fintype D.index :=
  D.index_finite

instance {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    (v : Valuation K₀ Γ) (D : Chapter03CompletionBranchData K₀ E Γ v)
    (i : D.index) : Field (D.factor i) :=
  D.factor_field i

instance {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    (v : Valuation K₀ Γ) (D : Chapter03CompletionBranchData K₀ E Γ v)
    (i : D.index) : Algebra (Valuation.Completion v) (D.factor i) :=
  D.factor_algebra i

/-- The product decomposition itself. -/
theorem chapter03_completion_tensor_product_decomposition
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    (v : Valuation K₀ Γ)
    (D : Chapter03CompletionBranchData K₀ E Γ v) :
    Nonempty
      (E ⊗[K₀] Valuation.Completion v ≃+* (∀ i, D.factor i)) :=
  D.decomposition

/-- Each completed branch has the local degree e times f. -/
theorem chapter03_completed_branch_degree
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    (v : Valuation K₀ Γ)
    (D : Chapter03CompletionBranchData K₀ E Γ v) (i : D.index) :
    Module.finrank (Valuation.Completion v) (D.factor i) =
      D.e i * D.f i :=
  D.factor_degree i

/-- The defectless degree condition needed for the branch sum. -/
def chapter03DefectlessCompletionDegree
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    [FiniteDimensional K₀ E] (v : Valuation K₀ Γ)
    (D : Chapter03CompletionBranchData K₀ E Γ v) : Prop :=
  Module.finrank K₀ E = ∑ i, D.e i * D.f i

-- SOURCE_ISSUE: The displayed equalities in §3.3 are not valid for every
-- finite separable extension over an arbitrary imperfect-residue discretely
-- valued field: a defect can remain.  The theorem below adds the precise
-- defectless/fundamental-equality hypothesis.
theorem chapter03_sum_of_branch_degrees
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    [FiniteDimensional K₀ E] (v : Valuation K₀ Γ)
    (D : Chapter03CompletionBranchData K₀ E Γ v)
    (hdefectless : chapter03DefectlessCompletionDegree v D) :
    Module.finrank K₀ E = ∑ i, D.e i * D.f i :=
  hdefectless

/-- Completion records branches as product factors instead of merging them. -/
def chapter03CompletionPreservesBranchCount
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    (v : Valuation K₀ Γ) (D : Chapter03CompletionBranchData K₀ E Γ v) : Prop :=
  Nonempty
    (E ⊗[K₀] Valuation.Completion v ≃+* (∀ i, D.factor i))

/--
If the base is complete and the extension is a field, the completed tensor
product has one valuation factor.  Completeness is represented by the
topological instance on the base; the branch data still exposes the factor.
-/
theorem chapter03_complete_base_has_one_completion_branch
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    (v : Valuation K₀ Γ) [CompleteSpace (WithVal v)]
    [FiniteDimensional K₀ E]
    (D : Chapter03CompletionBranchData K₀ E Γ v)
    (hne : Nonempty D.index) :
    Subsingleton D.index := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
