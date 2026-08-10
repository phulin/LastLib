import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section02IntersectionsAndComposita

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

noncomputable section

open scoped BigOperators TensorProduct
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

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

/-- A valuation branch is a valuation extension, with the fixed value group
used for the normalized local presentation. -/
abbrev chapter03ValuationBranch
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    (v : Valuation K₀ Γ) : Type _ :=
  ValuationExtension v E

/-! The index type below is only an enumeration of branches.  It does not
contain the tensor-product decomposition or any degree equation. -/
structure Chapter03CompletionBranchData
    (K₀ E Γ : Type*) [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ]
    [Algebra K₀ E] (v : Valuation K₀ Γ)
    where
  index : Type*
  index_finite : Fintype index
  branch : index → chapter03ValuationBranch (K₀ := K₀) (E := E) (Γ := Γ) v
  branch_exhaustive :
    ∀ w : chapter03ValuationBranch (K₀ := K₀) (E := E) (Γ := Γ) v,
      ∃ i, (branch i).1.IsEquiv w.1
  branch_pairwise_inequivalent :
    Pairwise (fun i j => ¬(branch i).1.IsEquiv (branch j).1)

instance {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    (v : Valuation K₀ Γ) (D : Chapter03CompletionBranchData K₀ E Γ v) :
    Fintype D.index :=
  D.index_finite

/-- The branch decomposition is indexed by valuation classes: the data
enumerates representatives up to `IsEquiv`, not all valuation-extension
structures literally. -/
theorem chapter03_completion_tensor_product_decomposition
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    (v : Valuation K₀ Γ) [Valuation.IsRankOneDiscrete v]
    [FiniteDimensional K₀ E] [Algebra.IsSeparable K₀ E]
    (D : Chapter03CompletionBranchData K₀ E Γ v) :
    Nonempty
      (E ⊗[K₀] Valuation.Completion v ≃+*
        (∀ i, chapter03CompletedBranch (D.branch i).1)) := by
  sorry

/- The factor degree is stated using the actual ramification and inertia
indices of the completed local rings, rather than free profile fields. -/
theorem chapter03_completed_branch_degree
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    (v : Valuation K₀ Γ) (w : Valuation E Γ)
    [Valuation.IsRankOneDiscrete v] [Valuation.IsRankOneDiscrete w]
    [Algebra (Valuation.Completion v) (Valuation.Completion w)]
    [IsScalarTower K₀ E (Valuation.Completion w)]
    [IsScalarTower K₀ (Valuation.Completion v)
      (Valuation.Completion w)]
    [FiniteDimensional (Valuation.Completion v) (Valuation.Completion w)]
    [PerfectField
      (IsLocalRing.ResidueField (Valuation.Completion v))]
    (e f : ℕ)
    (hbranch : v.IsEquiv (w.comap (algebraMap K₀ E)))
    (he : (IsLocalRing.maximalIdeal (Valuation.Completion w)).ramificationIdx
      (Valuation.Completion v) = e)
    (hf : (IsLocalRing.maximalIdeal (Valuation.Completion w)).inertiaDeg
      (Valuation.Completion v) = f) :
    Module.finrank (Valuation.Completion v) (Valuation.Completion w) = e * f := by
  sorry

/- The finite-normalization form of the branch sum.  This is the ring-level
statement behind the field formula and is the canonical earlier interface. -/
theorem chapter03_sum_of_branch_degrees
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [Module.Finite A B] [Module.Flat A B]
    (p : Ideal A) [p.IsPrime] [Fintype (p.primesOver B)] :
    Module.finrank A B =
      ∑ q : p.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A := by
  simpa using (Ideal.sum_ramification_inertia_eq_finrank p B).symm

/-/ A complete base has only one branch once the branch index enumerates
inequivalent valuation extensions. -/
theorem chapter03_complete_base_has_one_completion_branch
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    (v : Valuation K₀ Γ) [Valuation.IsRankOneDiscrete v]
    [Algebra.IsAlgebraic K₀ E]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal v.valuationSubring) v.valuationSubring)
    (D : Chapter03CompletionBranchData K₀ E Γ v)
    (hne : Nonempty D.index) :
    Subsingleton D.index := by
  let huniq :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01_theorem_1_1
      v hcomplete
  refine ⟨?_⟩
  intro i j
  by_contra hij
  apply D.branch_pairwise_inequivalent hij
  let Wi : HeterogeneousValuationExtension v E :=
    { valueGroup := Γ
      valuation := (D.branch i).1
      isExtension := (D.branch i).2 }
  let Wj : HeterogeneousValuationExtension v E :=
    { valueGroup := Γ
      valuation := (D.branch j).1
      isExtension := (D.branch j).2 }
  simpa [Wi, Wj] using huniq.2 Wi Wj

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
