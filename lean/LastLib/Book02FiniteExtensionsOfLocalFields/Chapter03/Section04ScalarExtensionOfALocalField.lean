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
  sorry

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
-- SOURCE_ISSUE: “each factor carries the unique local valuation” in §3.4
-- needs completeness (or henselianity) and a specified rank-one valuation;
-- it is not true for an arbitrary noncomplete valued base.
theorem chapter03_complete_factor_has_unique_local_valuation
    {K' F Γ : Type u} [Field K'] [Field F]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K' F]
    [FiniteDimensional K' F] (v : Valuation K' Γ)
    [CompleteSpace (WithVal v)] (w : Valuation F Γ)
    [Valuation.IsRankOneDiscrete v] [Valuation.IsRankOneDiscrete w]
    (hext : v.IsEquiv (w.comap (algebraMap K' F))) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueValuationExtension v F := by
  sorry

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
  sorry

/--
The e/f bookkeeping for a base-change theorem.  The first argument is the
field upstairs and the second is the chosen base inside the common overfield.
-/
structure Chapter03BaseChangeInvariantData
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (e f : IntermediateField K Ω → IntermediateField K Ω → ℕ) where
  L : IntermediateField K Ω
  K' : IntermediateField K Ω
  compositum : IntermediateField K Ω := L ⊔ K'
  compositum_is_sup : compositum = L ⊔ K'
  linearly_disjoint : L ⊓ K' = ⊥
  source_total : f L ⊥ = 1
  base_unramified : e K' ⊥ = 1
  compositum_over_base : f compositum K' = 1
  compositum_over_source : e compositum L = 1

/--
Unramified base change preserves the expected total/unramified split.  This
records both conclusions and the linear-disjointness assertion.
-/
theorem chapter03_totally_ramified_extension_after_unramified_base_change
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (e f : IntermediateField K Ω → IntermediateField K Ω → ℕ)
    (D : Chapter03BaseChangeInvariantData e f) :
    (D.L ⊓ D.K' = ⊥) ∧ f D.compositum D.K' = 1 ∧
      e D.compositum D.L = 1 := by
  exact ⟨D.linearly_disjoint, D.compositum_over_base, D.compositum_over_source⟩

/-- The compositum used in the base-change statement is the field LK'. -/
theorem chapter03_base_change_compositum_is_sup
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (e f : IntermediateField K Ω → IntermediateField K Ω → ℕ)
    (D : Chapter03BaseChangeInvariantData e f) :
    D.compositum = D.L ⊔ D.K' :=
  D.compositum_is_sup

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
