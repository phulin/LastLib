import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section03CompletionSeparatesBranches

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

universe uK uL uKp

noncomputable section

open scoped TensorProduct

/-! ## 3.4. Scalar extension of a local field -/

/-- The scalar-extension algebra whose field factors are studied in §3.4. -/
abbrev chapter03ScalarExtension
    (K L K' : Type*) [CommRing K] [CommRing L] [CommRing K']
    [Algebra K L] [Algebra K K'] : Type _ :=
  L ⊗[K] K'

/-- The scalar extension is an algebra over its right tensor factor. -/
noncomputable instance chapter03ScalarExtensionRightAlgebra
    (K L K' : Type*) [CommRing K] [CommRing L] [CommRing K']
    [Algebra K L] [Algebra K K'] :
    Algebra K' (chapter03ScalarExtension K L K') :=
  Algebra.TensorProduct.rightAlgebra

/-- The finite reduced algebra property of a scalar extension. -/
def chapter03FiniteReducedScalarExtension
    (K L K' : Type*) [CommRing K] [CommRing L] [CommRing K']
    [Algebra K L] [Algebra K K'] : Prop :=
  Algebra.Etale K' (chapter03ScalarExtension K L K')

/--
For a finite separable field extension, scalar extension is finite étale and
hence is a finite reduced product of field factors.
-/
theorem chapter03_separable_scalar_extension_is_finite_reduced
    (K L K' : Type*) [Field K] [Field L] [Field K']
    [Algebra K L] [Algebra K K'] [FiniteDimensional K L]
    [FiniteDimensional K K']
    [Algebra.IsSeparable K L] :
    chapter03FiniteReducedScalarExtension K L K' := by
  change Algebra.Etale K' (L ⊗[K] K')
  letI : Algebra.Etale K L :=
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
      finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  infer_instance

/-- The product-of-fields characterization supplied by Mathlib's étale API. -/
theorem chapter03_separable_scalar_extension_has_field_factors
    (K : Type uK) (L : Type uL) (K' : Type uKp) [Field K] [Field L] [Field K']
    [Algebra K L] [Algebra K K'] [FiniteDimensional K L]
    [FiniteDimensional K K']
    [Algebra.IsSeparable K L]
    (h : chapter03FiniteReducedScalarExtension K L K') :
    ∃ (I : Type (max uL uKp)) (_ : Finite I)
      (F : I → Type (max uL uKp)) (_ : ∀ i, Field (F i))
      (_ : ∀ i, Algebra K' (F i)),
      Nonempty (chapter03ScalarExtension K L K' ≃ₐ[K'] (∀ i, F i)) := by
  change Algebra.Etale K' (chapter03ScalarExtension K L K') at h
  rw [Algebra.Etale.iff_exists_algEquiv_prod] at h
  obtain ⟨I, hI, F, hF, hAlg, e, hfinite⟩ := h
  exact ⟨I, hI, F, hF, hAlg, ⟨e⟩⟩

/--
Over a complete rank-one valued base, each finite field factor has a unique
extension of the local valuation.  The completeness/rank-one hypotheses are
made explicit because a bare field factor does not carry a canonical
valuation.
-/
/- The source chapter works in the complete local-field setting.  Completeness
and rank-one discreteness are explicit here because a bare field factor does
not carry a canonical valuation outside that setting. -/
theorem chapter03_complete_factor_has_unique_local_valuation
    {K' F Γ : Type u} [Field K'] [Field F]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K' F]
    (v : Valuation K' Γ) [Valuation.IsRankOneDiscrete v]
    [Algebra.IsAlgebraic K' F]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal v.valuationSubring) v.valuationSubring) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueValuationExtension v F := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01_theorem_1_1
    v hcomplete

/-- Inseparable scalar extension may have nilpotents rather than field factors. -/
def chapter03ScalarExtensionHasNilpotents
    (K L K' : Type*) [CommRing K] [CommRing L] [CommRing K']
    [Algebra K L] [Algebra K K'] : Prop :=
  ¬ IsReduced (chapter03ScalarExtension K L K')

theorem chapter03_inseparable_self_scalar_extension_has_nilpotents
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hinseparable : ¬ Algebra.IsSeparable K L) :
    chapter03ScalarExtensionHasNilpotents K L L := by
  sorry

/-- A scalar extension is a field only when its product/nilpotent behavior permits it. -/
def chapter03ScalarExtensionIsAField
    (K L K' : Type*) [CommRing K] [CommRing L] [CommRing K']
    [Algebra K L] [Algebra K K'] : Prop :=
  IsField (chapter03ScalarExtension K L K')

/-- The finite étale residue-field base change appearing in the unramified case. -/
def chapter03ResidueScalarExtensionIsFiniteEtale
    (k l k' : Type*) [Field k] [Field l] [Field k']
    [Algebra k l] [Algebra k k'] : Prop :=
  Algebra.Etale k' (l ⊗[k] k')

theorem chapter03_separable_residue_extension_is_stable_under_base_change
    (k l k' : Type*) [Field k] [Field l] [Field k']
    [Algebra k l] [Algebra k k'] [FiniteDimensional k l]
    [FiniteDimensional k k']
    [Algebra.IsSeparable k l] :
    chapter03ResidueScalarExtensionIsFiniteEtale k l k' := by
  change Algebra.Etale k' (l ⊗[k] k')
  letI : Algebra.Etale k l :=
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable k l
      finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  infer_instance

/--
The e/f bookkeeping for a base-change theorem.  The first argument is the
field upstairs and the second is the chosen base inside the common overfield.
-/
def chapter03BaseChangeCompositum
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L K' : IntermediateField K Ω) : IntermediateField K Ω :=
  L ⊔ K'

noncomputable instance chapter03BaseChangeCompositumLeftAlgebra
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L K' : IntermediateField K Ω) :
    Algebra (↥L) (↥(chapter03BaseChangeCompositum L K')) :=
  (IntermediateField.inclusion le_sup_left).toAlgebra

noncomputable instance chapter03BaseChangeCompositumRightAlgebra
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L K' : IntermediateField K Ω) :
    Algebra (↥K') (↥(chapter03BaseChangeCompositum L K')) :=
  (IntermediateField.inclusion le_sup_right).toAlgebra

/-- Unramified base change preserves the expected total/unramified split. -/
theorem chapter03_totally_ramified_extension_after_unramified_base_change
    {K Ω Γ : Type*} [Field K] [Field Ω]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K Ω]
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K']
    [IsGalois K K']
    (vK : Valuation K Γ)
    (vL : Valuation (↥L) Γ)
    (vK' : Valuation (↥K') Γ)
    (vC : Valuation (↥(chapter03BaseChangeCompositum L K')) Γ)
    [vK.HasExtension vL] [vK.HasExtension vK']
    [vK.HasExtension vC] [vL.HasExtension vC]
    [vK'.HasExtension vC]
    [IsScalarTower K (↥L) (↥(chapter03BaseChangeCompositum L K'))]
    [IsScalarTower K (↥K') (↥(chapter03BaseChangeCompositum L K'))]
    [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    [Valuation.IsRankOneDiscrete vK']
    [Valuation.IsRankOneDiscrete vC]
    [PerfectField (IsLocalRing.ResidueField vK.valuationSubring)]
    [FiniteDimensional (↥L) (↥(chapter03BaseChangeCompositum L K'))]
    [FiniteDimensional (↥K') (↥(chapter03BaseChangeCompositum L K'))]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hL_total : chapter03ResidueDegree vK vL = 1)
    (hK'_unramified : chapter03RamificationIndex vK vK' = 1) :
    (L ⊓ K' = ⊥) ∧
      L.LinearDisjoint K' ∧
      chapter03ResidueDegree vK' vC = 1 ∧
      chapter03RamificationIndex vL vC = 1 := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
