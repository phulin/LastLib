import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section01WhyTowerFormulasMatter
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section02ExistenceUniquenessAndCompleteness
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section05SeveralExtensionsAndTheFundamentalEquality
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section04FactorizationOfTheMaximalIdeal
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section02TheCompletedProductTheorem

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

universe uK₀ uE uΓ

noncomputable section

open scoped BigOperators TensorProduct
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

/-! ## 3.3. Completion separates branches -/

/-- The completed field attached to one valuation extension. -/
abbrev chapter03CompletedBranch
    {E Γ : Type*} [Field E] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation E Γ) : Type _ :=
  Valuation.Completion w

/-- A valuation branch may use a genuinely larger value group upstairs. -/
abbrev chapter03ValuationBranch
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    [FiniteDimensional K₀ E]
    (v : Valuation K₀ Γ) : Type _ :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValuationBranch
    (K := K₀) (L := E) v

/- The indexed product view below is a bridge to Chapter 10's established
   complete branch-family interface. -/
structure Chapter03CompletionBranchData
    (K₀ : Type uK₀) (E : Type uE) (Γ : Type uΓ) [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ]
    [Algebra K₀ E] [FiniteDimensional K₀ E] (v : Valuation K₀ Γ)
    where
  family : Finset
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValuationBranch
      (K := K₀) (L := E) v)
  family_complete :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10CompleteBranchFamily.{
      uK₀, uE, uΓ, max (max uK₀ uE) uΓ} v family

namespace Chapter03CompletionBranchData

abbrev index
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    [FiniteDimensional K₀ E]
    {v : Valuation K₀ Γ}
    (D : Chapter03CompletionBranchData K₀ E Γ v) : Type _ :=
  {b // b ∈ D.family}

def branch
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    [FiniteDimensional K₀ E]
    {v : Valuation K₀ Γ}
    (D : Chapter03CompletionBranchData K₀ E Γ v) (i : D.index) :
    chapter03ValuationBranch (K₀ := K₀) (E := E) (Γ := Γ) v :=
  i.1

instance
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    [FiniteDimensional K₀ E]
    {v : Valuation K₀ Γ}
    (D : Chapter03CompletionBranchData K₀ E Γ v) : Fintype D.index :=
  Fintype.ofFinset D.family (fun _ => Iff.rfl)

end Chapter03CompletionBranchData

/-- The completed tensor product is the product of the completed branches. -/
theorem chapter03_completion_tensor_product_decomposition
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    (v : Valuation K₀ Γ) [Algebra K₀ (Valuation.Completion v)]
    [Valuation.IsRankOneDiscrete v]
    [FiniteDimensional K₀ E] [Algebra.IsSeparable K₀ E]
    (D : Chapter03CompletionBranchData K₀ E Γ v)
    (hne : Nonempty D.index)
    [Algebra (Valuation.Completion v)
      (E ⊗[K₀] Valuation.Completion v)]
    [∀ i, Algebra (Valuation.Completion v)
      (chapter03CompletedBranch (D.branch i).extension.valuation)] :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasCompletedAlgebraProduct
      K₀ E (Valuation.Completion v)
      (fun i => chapter03CompletedBranch (D.branch i).extension.valuation) := by
  sorry

/-- The degree of one completed branch is its ramification factor times its
residue degree. -/
theorem chapter03_completed_branch_degree
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    [FiniteDimensional K₀ E]
    (v : Valuation K₀ Γ)
    (b : chapter03ValuationBranch (K₀ := K₀) (E := E) (Γ := Γ) v)
    (vComp : Valuation (Valuation.Completion v) b.extension.valueGroup)
    (wComp : Valuation (Valuation.Completion b.extension.valuation)
      b.extension.valueGroup)
    [Algebra (Valuation.Completion v)
      (Valuation.Completion b.extension.valuation)]
    [vComp.HasExtension wComp]
    [Valuation.IsRankOneDiscrete vComp]
    [Valuation.IsRankOneDiscrete wComp]
    [FiniteDimensional (Valuation.Completion v)
      (Valuation.Completion b.extension.valuation)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vComp.valuationSubring) vComp.valuationSubring)
    (e f : ℕ)
    (he : chapterRamificationIndex vComp.valuationSubring wComp.valuationSubring
      (IsLocalRing.maximalIdeal wComp.valuationSubring) = e)
    (hf : chapterResidueDegree vComp.valuationSubring wComp.valuationSubring
      (IsLocalRing.maximalIdeal wComp.valuationSubring) = f) :
    Module.finrank (Valuation.Completion v)
        (Valuation.Completion b.extension.valuation) = e * f := by
  simpa only [he, hf] using
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.complete_extension_defectless_without_separability
      vComp wComp hcomplete)

/-- The sum over all prime branches recovers the finite degree. -/
theorem chapter03_sum_of_branch_degrees
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L]
    [Module.Finite A B] [Module.Free A B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [IsDedekindDomain B]
    (p : Ideal A) [p.IsPrime] [p.IsMaximal] :
    Module.finrank K L =
      ∑ q : p.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A := by
  calc
    Module.finrank K L = Module.finrank A B := IsFractionRing.finrank_eq A K B L
    _ = ∑ q : p.primesOver B, q.1.ramificationIdx A * q.1.inertiaDeg A :=
      (Ideal.sum_ramification_inertia_eq_finrank p B).symm

/-- A complete base has one valuation branch up to equivalence. -/
theorem chapter03_complete_base_has_one_completion_branch
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    [FiniteDimensional K₀ E]
    (v : Valuation K₀ Γ) [Valuation.IsRankOneDiscrete v]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal v.valuationSubring) v.valuationSubring)
    (D : Chapter03CompletionBranchData K₀ E Γ v) :
    Nonempty D.index ∧ Subsingleton D.index := by
  sorry

/-- In the complete case the tensor-product decomposition has one field
factor. -/
theorem chapter03_complete_base_tensor_product_is_one_completion
    {K₀ E Γ : Type*} [Field K₀] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K₀ E]
    (v : Valuation K₀ Γ)
    [Algebra K₀ (Valuation.Completion v)]
    [Valuation.IsRankOneDiscrete v]
    [FiniteDimensional K₀ E] [Algebra.IsSeparable K₀ E]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal v.valuationSubring) v.valuationSubring)
    (D : Chapter03CompletionBranchData K₀ E Γ v)
    [∀ i, Algebra (Valuation.Completion v)
      (chapter03CompletedBranch (D.branch i).extension.valuation)] :
    letI : Algebra (Valuation.Completion v)
      (E ⊗[K₀] Valuation.Completion v) :=
      Algebra.TensorProduct.rightAlgebra
    ∃ i : D.index,
      Nonempty
        (E ⊗[K₀] Valuation.Completion v ≃ₐ[Valuation.Completion v]
          chapter03CompletedBranch (D.branch i).extension.valuation) := by
  obtain ⟨hne, hsub⟩ :=
    chapter03_complete_base_has_one_completion_branch v hcomplete D
  let : Algebra (Valuation.Completion v)
      (E ⊗[K₀] Valuation.Completion v) :=
    Algebra.TensorProduct.rightAlgebra
  let i₀ : D.index := Classical.choice hne
  let _ : Unique D.index :=
    { default := i₀
      uniq := fun i => hsub.elim i i₀ }
  obtain ⟨e⟩ :=
    chapter03_completion_tensor_product_decomposition v D hne
  let eFactor : ∀ i : D.index,
      chapter03CompletedBranch (D.branch i).extension.valuation ≃ₐ[
        Valuation.Completion v]
        chapter03CompletedBranch (D.branch default).extension.valuation := by
    intro i
    have hi : i = default := Subsingleton.elim i default
    subst i
    exact AlgEquiv.refl
  let ePi := AlgEquiv.piCongrRight eFactor
  let eUnique := AlgEquiv.funUnique (Valuation.Completion v) D.index
    (chapter03CompletedBranch (D.branch default).extension.valuation)
  refine ⟨default, ⟨e.trans (ePi.trans eUnique)⟩⟩

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
