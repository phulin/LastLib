import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section05HigherRamificationBoundary

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05

noncomputable section

open scoped BigOperators

/-! ## 5.6. Counting branches before completion -/

/-- Orbit--stabilizer for the Galois action on the finite set of branches above `v`. -/
theorem galois_group_order_eq_branch_count_mul_decomposition_order
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) (w : Valuation E Γ)
    (hw : w ∈ chapter05ValuationsAbove v)
    (hbranches : (chapter05ValuationsAbove (E := E) v).Finite)
    (htrans :
      ∀ ⦃w₁ w₂ : Valuation E Γ⦄,
        w₁ ∈ chapter05ValuationsAbove v → w₂ ∈ chapter05ValuationsAbove v →
          ∃ σ : Gal(E / F), chapter05ValuationAction σ w₁ = w₂) :
    Nat.card (Gal(E / F)) =
      chapter05BranchCount (E := E) v *
        Nat.card (chapter05DecompositionGroup F w.valuationSubring) := by
  sorry

/-- The selected completed branch has the order of its decomposition group as degree. -/
theorem selected_completion_galois_order_eq_degree
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) (w : Valuation E Γ)
    (hw : w ∈ chapter05ValuationsAbove v)
    [Algebra (v.Completion) (w.Completion)]
    [FiniteDimensional (v.Completion) (w.Completion)]
    [IsGalois (v.Completion) (w.Completion)] :
    Nat.card (chapter05DecompositionGroup F w.valuationSubring) =
      Module.finrank (v.Completion) (w.Completion) := by
  sorry

/-- The completed local degree is `e f` once the local group order is so identified. -/
theorem selected_completion_degree_is_ef
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) (w : Valuation E Γ)
    (hw : w ∈ chapter05ValuationsAbove v)
    [Algebra (v.Completion) (w.Completion)]
    [FiniteDimensional (v.Completion) (w.Completion)]
    [IsGalois (v.Completion) (w.Completion)]
    (e f : ℕ)
    (hD : Nat.card (chapter05DecompositionGroup F w.valuationSubring) = e * f) :
    Module.finrank (v.Completion) (w.Completion) = e * f := by
  calc
    Module.finrank (v.Completion) (w.Completion) =
        Nat.card (chapter05DecompositionGroup F w.valuationSubring) :=
      (selected_completion_galois_order_eq_degree v w hw).symm
    _ = e * f := hD

/-- A finite residue exact sequence accounts for the local factors `e` and `f`. -/
theorem selected_decomposition_order_is_ef
    {D Q : Type*} [Group D] [Group Q] [Finite D] [Finite Q]
    (ρ : D →* Q) (hρ : Function.Surjective ρ)
    (e f : ℕ) (he : Nat.card (MonoidHom.ker ρ) = e)
    (hf : Nat.card Q = f) :
    Nat.card D = e * f := by
  calc
    Nat.card D = Nat.card (MonoidHom.ker ρ) * Nat.card Q :=
      residue_exact_sequence_cardinality ρ hρ
    _ = e * f := by rw [he, hf]

/-- The global degree is the product of branch count, ramification, and residue degree. -/
theorem finite_galois_degree_eq_branch_count_mul_ef
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) (w : Valuation E Γ)
    (hw : w ∈ chapter05ValuationsAbove v)
    (hbranches : (chapter05ValuationsAbove (E := E) v).Finite)
    (htrans :
      ∀ ⦃w₁ w₂ : Valuation E Γ⦄,
        w₁ ∈ chapter05ValuationsAbove v → w₂ ∈ chapter05ValuationsAbove v →
          ∃ σ : Gal(E / F), chapter05ValuationAction σ w₁ = w₂)
    (e f : ℕ)
    (hD : Nat.card (chapter05DecompositionGroup F w.valuationSubring) = e * f) :
    Module.finrank F E = chapter05BranchCount (E := E) v * e * f := by
  sorry

/-- Conjugate branch ideals have the same ramification and residue labels. -/
theorem galois_conjugate_branch_profiles_have_equal_ef
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P Q : Ideal B) (τ : B ≃ₐ[A] B)
    (hPQ : Ideal.map τ.toRingHom P = Q)
    (pP : Chapter05LocalEFProfile A B P)
    (pQ : Chapter05LocalEFProfile A B Q) :
    pP.e = pQ.e ∧ pP.f = pQ.f := by
  sorry

/-- If the base is complete and there is one branch, the local index is one. -/
theorem complete_branch_decomposition_index_eq_one
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ]
    (A : ValuationSubring E)
    (hD : chapter05DecompositionGroup F A = ⊤) :
    (chapter05DecompositionGroup F A).index = 1 := by
  rw [hD]
  simp

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05
