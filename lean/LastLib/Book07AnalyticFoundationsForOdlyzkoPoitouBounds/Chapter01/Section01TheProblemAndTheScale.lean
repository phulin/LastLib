import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01

noncomputable section

open NumberField

/-! ## 1.1. The problem and the scale -/

/- The degree is kept as a book-facing name for the canonical finite
   dimensional degree over `ℚ`. -/
def chapter01Degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank ℚ K

@[simp]
theorem chapter01Degree_def (K : Type*) [Field K] [NumberField K] :
    chapter01Degree K = Module.finrank ℚ K :=
  rfl

theorem chapter01Degree_pos (K : Type*) [Field K] [NumberField K] :
    0 < chapter01Degree K := by
  exact Module.finrank_pos

theorem chapter01Degree_eq_card_complex_embeddings
    (K : Type*) [Field K] [NumberField K] :
    chapter01Degree K = Fintype.card (K →+* ℂ) := by
  exact (NumberField.Embeddings.card K ℂ).symm

/- The source writes the absolute discriminant as a positive real number.
   Mathlib stores the signed integer discriminant, so the absolute value is
   taken after casting to `ℝ`. -/
noncomputable def chapter01AbsoluteDiscriminant
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  |(NumberField.discr K : ℝ)|

/- The root discriminant removes the repetition caused by a tower degree. -/
noncomputable def chapter01RootDiscriminant
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  chapter01AbsoluteDiscriminant K ^ (chapter01Degree K : ℝ)⁻¹

theorem chapter01RootDiscriminant_def
    (K : Type*) [Field K] [NumberField K] :
    chapter01RootDiscriminant K =
      chapter01AbsoluteDiscriminant K ^ (chapter01Degree K : ℝ)⁻¹ :=
  rfl

theorem chapter01RootDiscriminant_eq_canonical
    (K : Type*) [Field K] [NumberField K] :
    chapter01RootDiscriminant K = NumberField.rootDiscr K := by
  rw [chapter01RootDiscriminant_def, NumberField.rootDiscr_def]
  simp [chapter01AbsoluteDiscriminant, chapter01Degree, Int.cast_abs]

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01
