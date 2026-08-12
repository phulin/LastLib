import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section05HigherRamificationBoundary

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05

noncomputable section

open scoped BigOperators Pointwise

/-! ## 5.6. Counting branches before completion -/

/- SOURCE_ISSUE: The displayed formula `[E : F] = g e f` in §5.6 needs a
   defectless hypothesis.  The chapter allows imperfect residue fields, where
   a finite completed extension can have a nontrivial defect and degree
   `e * f * d`.  The API below keeps the local equality as an explicit
   hypothesis instead of deriving it from completeness and discreteness alone. -/

/-- Orbit--stabilizer for the Galois action on the finite set of branches above `v`. -/
theorem galois_group_order_eq_branch_count_mul_decomposition_order
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) (A : ValuationSubring E)
    (hA : A ∈ chapter05ValuationsAbove v)
    (hbranches : (chapter05ValuationsAbove (E := E) v).Finite)
    (htrans :
      ∀ ⦃A₁ A₂ : ValuationSubring E⦄,
        A₁ ∈ chapter05ValuationsAbove v → A₂ ∈ chapter05ValuationsAbove v →
          ∃ σ : Gal(E / F), σ • A₁ = A₂) :
    Nat.card (Gal(E / F)) =
      chapter05BranchCount (E := E) v *
        Nat.card (chapter05DecompositionGroup F A) := by
  sorry

/-- The selected completed branch has the order of its decomposition group as degree. -/
theorem selected_completion_galois_order_eq_degree
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) (w : Valuation E Γ)
    (hw : w.valuationSubring ∈ chapter05ValuationsAbove v)
    [Algebra (v.Completion) (w.Completion)]
    [FiniteDimensional (v.Completion) (w.Completion)]
    [MulSemiringAction (chapter05DecompositionGroup F w.valuationSubring)
      (w.Completion)]
    [Finite (chapter05DecompositionGroup F w.valuationSubring)]
    (hD : IsGaloisGroup (chapter05DecompositionGroup F w.valuationSubring)
      (v.Completion) (w.Completion)) :
    Nat.card (chapter05DecompositionGroup F w.valuationSubring) =
      Module.finrank (v.Completion) (w.Completion) := by
  sorry

/- The completed-degree form of the global factorization is kept explicit:
   it is the bridge between the orbit count and the selected local factor. -/
theorem finite_galois_degree_eq_branch_count_mul_selected_completion_degree
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) (w : Valuation E Γ)
    (hw : w.valuationSubring ∈ chapter05ValuationsAbove v)
    (hbranches : (chapter05ValuationsAbove (E := E) v).Finite)
    (htrans :
      ∀ ⦃A₁ A₂ : ValuationSubring E⦄,
        A₁ ∈ chapter05ValuationsAbove v → A₂ ∈ chapter05ValuationsAbove v →
          ∃ σ : Gal(E / F), σ • A₁ = A₂)
    [Algebra (v.Completion) (w.Completion)]
    [FiniteDimensional (v.Completion) (w.Completion)]
    [MulSemiringAction (chapter05DecompositionGroup F w.valuationSubring)
      (w.Completion)]
    [Finite (chapter05DecompositionGroup F w.valuationSubring)]
    (hD : IsGaloisGroup (chapter05DecompositionGroup F w.valuationSubring)
      (v.Completion) (w.Completion)) :
    Module.finrank F E = chapter05BranchCount (E := E) v *
      Module.finrank (v.Completion) (w.Completion) := by
  sorry

/-- The completed local degree is `e f` once the local group order is so identified. -/
theorem selected_completion_degree_is_ef
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) (w : Valuation E Γ)
    (hw : w.valuationSubring ∈ chapter05ValuationsAbove v)
    [Algebra (v.Completion) (w.Completion)]
    [FiniteDimensional (v.Completion) (w.Completion)]
    [MulSemiringAction (chapter05DecompositionGroup F w.valuationSubring)
      (w.Completion)]
    [Finite (chapter05DecompositionGroup F w.valuationSubring)]
    (hDgroup : IsGaloisGroup (chapter05DecompositionGroup F w.valuationSubring)
      (v.Completion) (w.Completion))
    (e f : ℕ)
    (hD : Nat.card (chapter05DecompositionGroup F w.valuationSubring) = e * f) :
    Module.finrank (v.Completion) (w.Completion) = e * f := by
  sorry

/-- A finite residue exact sequence accounts for the local factors `e` and `f`. -/
theorem selected_decomposition_order_is_ef
    {D Q : Type*} [Group D] [Group Q] [Finite D] [Finite Q]
    (ρ : D →* Q) (hρ : Function.Surjective ρ)
    (e f : ℕ) (he : Nat.card (MonoidHom.ker ρ) = e)
    (hf : Nat.card Q = f) :
    Nat.card D = e * f := by
  sorry

/-- The global degree is the product of branch count, ramification, and residue degree. -/
theorem finite_galois_degree_eq_branch_count_mul_ef
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) (w : Valuation E Γ)
    (hw : w.valuationSubring ∈ chapter05ValuationsAbove v)
    (hbranches : (chapter05ValuationsAbove (E := E) v).Finite)
    (htrans :
      ∀ ⦃A₁ A₂ : ValuationSubring E⦄,
        A₁ ∈ chapter05ValuationsAbove v → A₂ ∈ chapter05ValuationsAbove v →
          ∃ σ : Gal(E / F), σ • A₁ = A₂)
    (e f : ℕ)
    (hD : Nat.card (chapter05DecompositionGroup F w.valuationSubring) = e * f) :
    Module.finrank F E = chapter05BranchCount (E := E) v * e * f := by
  sorry

/-- Conjugate branch ideals have the same ramification and residue labels. -/
theorem galois_conjugate_branch_profiles_have_equal_ef
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P Q : Ideal B) [P.IsPrime] [P.IsMaximal] [Q.IsPrime] [Q.IsMaximal]
    (τ : B ≃ₐ[A] B)
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
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05
