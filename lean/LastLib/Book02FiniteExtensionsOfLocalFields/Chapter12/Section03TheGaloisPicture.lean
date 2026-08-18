import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section02TheSeparabilityMap

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12

noncomputable section

/-! ## 12.3. Krasner's lemma -/

/--
The field-theoretic conclusion of Krasner's lemma in the form supplied by
Mathlib's `IsKrasner.krasner`.  The splitting hypothesis says that all
conjugates needed by the comparison live in the chosen normed overfield.
-/
theorem chapter12_krasner_membership
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    [IsKrasner K L] {α β : L}
    (hα : IsSeparable K α)
    (hsplits : ((minpoly K α).map (algebraMap K L)).Splits)
    (hβ : IsIntegral K β)
    (hclose : chapter12KrasnerProximity (K := K) α β) :
    α ∈ IntermediateField.adjoin K ({β} : Set L) := by
  apply IsKrasner.krasner hα hsplits hβ
  intro α' hconj hne
  simpa only [norm_sub_rev] using hclose α' hconj hne

/-- The membership statement upgraded to the inclusion `K(α) ⊆ K(β)`. -/
theorem chapter12_krasner_lemma
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    [IsKrasner K L] {α β : L}
    (hα : IsSeparable K α)
    (hsplits : ((minpoly K α).map (algebraMap K L)).Splits)
    (hβ : IsIntegral K β)
    (hclose : chapter12KrasnerProximity (K := K) α β) :
    IntermediateField.adjoin K ({α} : Set L) ≤
      IntermediateField.adjoin K ({β} : Set L) := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  exact chapter12_krasner_membership hα hsplits hβ hclose

/-- Completeness of the base supplies the `IsKrasner` instance used above;
the algebraic extension need not itself be complete. -/
theorem chapter12_krasner_lemma_over_complete_base
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [NormedField L] [NormedAlgebra K L]
    [Algebra.IsAlgebraic K L] {α β : L}
    (hα : IsSeparable K α)
    (hsplits : ((minpoly K α).map (algebraMap K L)).Splits)
    (hβ : IsIntegral K β)
    (hclose : chapter12KrasnerProximity (K := K) α β) :
    IntermediateField.adjoin K ({α} : Set L) ≤
      IntermediateField.adjoin K ({β} : Set L) := by
  exact chapter12_krasner_lemma hα hsplits hβ hclose

/-- The radius form is equivalent to the conjugate-by-conjugate form once the
finite conjugate set has been identified. -/
theorem chapter12_krasner_lemma_of_radius
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    [IsKrasner K L] {α β : L}
    (hα : IsSeparable K α)
    (hsplits : ((minpoly K α).map (algebraMap K L)).Splits)
    (hβ : IsIntegral K β)
    (hradius : ENNReal.ofReal ‖β - α‖ < chapter12KrasnerRadius (K := K) α) :
    IntermediateField.adjoin K ({α} : Set L) ≤
      IntermediateField.adjoin K ({β} : Set L) := by
  apply chapter12_krasner_lemma hα hsplits hβ
  exact (chapter12_krasner_proximity_iff_radius α β hα.isIntegral
    (chapter12_krasner_distance_set_finite α hα.isIntegral hsplits)).2 hradius

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12
