import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section02DecompositionGroups
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section03ResidueActionAndInertia
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section04FixedFieldsOfInertia

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05

noncomputable section

open scoped BigOperators Pointwise

/-! ## 5.6. Counting branches before completion -/

/- The branch count is separated from the selected local factor.  The
   numerical identification of the decomposition-group order with `e * f`
   is kept explicit below, while orbit--stabilizer supplies the branch factor. -/

/-- Orbit--stabilizer for the Galois action on the finite set of branches above `v`. -/
theorem galois_group_order_eq_branch_count_mul_decomposition_order
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) (A : ValuationSubring E)
    (hA : A ∈ chapter05ValuationsAbove v)
    (hbranches : (chapter05ValuationsAbove (E := E) v).Finite) :
    Nat.card (Gal(E / F)) =
      chapter05BranchCount (E := E) v *
        Nat.card (chapter05DecompositionGroup F A) := by
  calc
    Nat.card (Gal(E / F)) =
        (chapter05DecompositionGroup F A).index *
          Nat.card (chapter05DecompositionGroup F A) :=
      (Subgroup.index_mul_card (chapter05DecompositionGroup F A)).symm
    _ = chapter05BranchCount (E := E) v *
          Nat.card (chapter05DecompositionGroup F A) := by
      rw [branch_count_eq_decomposition_index v A hA hbranches]

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
  have _hw := hw
  exact IsGaloisGroup.card_eq_finrank _ _ _

/- The completed-degree form of the global factorization is kept explicit:
   it is the bridge between the orbit count and the selected local factor. -/
theorem finite_galois_degree_eq_branch_count_mul_selected_completion_degree
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) (w : Valuation E Γ)
    (hw : w.valuationSubring ∈ chapter05ValuationsAbove v)
    (hbranches : (chapter05ValuationsAbove (E := E) v).Finite)
    [Algebra (v.Completion) (w.Completion)]
    [FiniteDimensional (v.Completion) (w.Completion)]
    [MulSemiringAction (chapter05DecompositionGroup F w.valuationSubring)
      (w.Completion)]
    [Finite (chapter05DecompositionGroup F w.valuationSubring)]
    (hD : IsGaloisGroup (chapter05DecompositionGroup F w.valuationSubring)
      (v.Completion) (w.Completion)) :
    Module.finrank F E = chapter05BranchCount (E := E) v *
      Module.finrank (v.Completion) (w.Completion) := by
  calc
    Module.finrank F E = Nat.card (Gal(E / F)) :=
      (IsGalois.card_aut_eq_finrank F E).symm
    _ = chapter05BranchCount (E := E) v *
          Nat.card (chapter05DecompositionGroup F w.valuationSubring) :=
      galois_group_order_eq_branch_count_mul_decomposition_order v
        w.valuationSubring hw hbranches
    _ = chapter05BranchCount (E := E) v *
          Module.finrank (v.Completion) (w.Completion) := by
      rw [selected_completion_galois_order_eq_degree v w hw hD]

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
  calc
    Module.finrank (v.Completion) (w.Completion) =
        Nat.card (chapter05DecompositionGroup F w.valuationSubring) :=
      (selected_completion_galois_order_eq_degree v w hw hDgroup).symm
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

/-- The global degree is the product of branch count, ramification, and residue degree
once the selected branch supplies its finite residue exact sequence. -/
theorem finite_galois_degree_eq_branch_count_mul_ef
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) (w : Valuation E Γ)
    (hw : w.valuationSubring ∈ chapter05ValuationsAbove v)
    (hbranches : (chapter05ValuationsAbove (E := E) v).Finite)
    {Q : Type*} [Group Q] [Finite Q]
    (ρ : chapter05DecompositionGroup F w.valuationSubring →* Q)
    (hρ : Function.Surjective ρ)
    (e f : ℕ)
    (he : Nat.card (MonoidHom.ker ρ) = e)
    (hf : Nat.card Q = f) :
    Module.finrank F E = chapter05BranchCount (E := E) v * e * f := by
  have hD : Nat.card (chapter05DecompositionGroup F w.valuationSubring) = e * f :=
    selected_decomposition_order_is_ef ρ hρ e f he hf
  calc
    Module.finrank F E = Nat.card (Gal(E / F)) :=
      (IsGalois.card_aut_eq_finrank F E).symm
    _ = chapter05BranchCount (E := E) v *
          Nat.card (chapter05DecompositionGroup F w.valuationSubring) :=
      galois_group_order_eq_branch_count_mul_decomposition_order v
        w.valuationSubring hw hbranches
    _ = chapter05BranchCount (E := E) v * (e * f) := by rw [hD]
    _ = chapter05BranchCount (E := E) v * e * f := by rw [Nat.mul_assoc]

/-- Conjugate branch ideals have the same ramification and residue labels. -/
theorem galois_conjugate_branch_profiles_have_equal_ef
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P Q : Ideal B) [P.IsPrime] [P.IsMaximal] [Q.IsPrime] [Q.IsMaximal]
    (τ : B ≃ₐ[A] B)
    (hPQ : Ideal.map τ.toRingHom P = Q)
    (pP : Chapter05LocalEFProfile A B P)
    (pQ : Chapter05LocalEFProfile A B Q) :
    pP.e = pQ.e ∧ pP.f = pQ.f := by
  have hsmul : τ • P = Ideal.map τ.toRingHom P := by
    rw [Ideal.pointwise_smul_def]
    rfl
  constructor
  · calc
      pP.e = P.ramificationIdx A := pP.e_eq
      _ = (Ideal.map τ.toRingHom P).ramificationIdx A := by
        rw [← hsmul]
        exact (Ideal.ramificationIdx_smul A P τ).symm
      _ = Q.ramificationIdx A := by rw [hPQ]
      _ = pQ.e := pQ.e_eq.symm
  · calc
      pP.f = P.inertiaDeg A := pP.f_eq
      _ = (Ideal.map τ.toRingHom P).inertiaDeg A := by
        rw [← hsmul]
        exact (Ideal.inertiaDeg_smul A P τ).symm
      _ = Q.inertiaDeg A := by rw [hPQ]
      _ = pQ.f := pQ.f_eq.symm

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
