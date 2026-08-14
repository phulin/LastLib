import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Dependencies

/-!
# Book 12, Chapter 14, §14.1: solving the balancing equations
-/

noncomputable section

open scoped BigOperators

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14

/-! ## Compatibility and existence -/

theorem chapter14_fiber_matrix_image_eq_orthogonal
    {r : ℕ} (F : Chapter14FiberMatrix r) :
    Set.range (chapter14MatrixVec (chapter14FiberRationalMatrix F)) =
      {d : Chapter14RationalVector r |
        chapter14RationalCompatibility F d} := by
  sorry

theorem chapter14_balancing_equation_has_solution_iff
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (d : Chapter14RationalVector r) :
    (∃ v : Chapter14RationalVerticalDivisor F,
      chapter14Balanced F d v) ↔
      chapter14RationalCompatibility F d := by
  sorry

theorem chapter14_horizontal_divisor_satisfies_equation_14_1
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (D : Chapter14HorizontalDivisor F) :
    ∑ i, F.multiplicity i * D.componentIntersections i = 0 := by
  exact D.compatibility

theorem chapter14_equation_14_1
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (D : Chapter14HorizontalDivisor F) :
    ∑ i, F.multiplicity i * D.componentIntersections i = 0 := by
  exact chapter14_horizontal_divisor_satisfies_equation_14_1 D

/-! ## The correction and its class -/

structure Chapter14VerticalCorrection {r : ℕ}
    {F : Chapter14FiberMatrix r}
    (D : Chapter14HorizontalDivisor F) where
  coefficients : Chapter14RationalVerticalDivisor F
  balanced : chapter14Balanced F
    (fun i => (D.componentIntersections i : ℚ)) coefficients

theorem chapter14_vertical_correction_exists
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (hconnected : F.connected)
    (D : Chapter14HorizontalDivisor F) :
    Nonempty (Chapter14VerticalCorrection D) := by
  sorry

theorem chapter14_theorem_14_1_vertical_correction
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (hconnected : F.connected)
    (D : Chapter14HorizontalDivisor F) :
    ∃ v : Chapter14RationalVerticalDivisor F,
      chapter14Balanced F
        (fun i => (D.componentIntersections i : ℚ)) v ∧
      ∀ w : Chapter14RationalVerticalDivisor F,
        chapter14Balanced F
          (fun i => (D.componentIntersections i : ℚ)) w →
          chapter14RationallyEquivalentModuloFiber F v w := by
  sorry

noncomputable def chapter14VerticalCorrection
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (hconnected : F.connected)
    (D : Chapter14HorizontalDivisor F) :
    Chapter14VerticalCorrection D :=
  Classical.choice (chapter14_vertical_correction_exists F hconnected D)

theorem chapter14VerticalCorrection_balanced
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (hconnected : F.connected)
    (D : Chapter14HorizontalDivisor F) :
    chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ))
      (chapter14VerticalCorrection F hconnected D).coefficients := by
  exact (chapter14VerticalCorrection F hconnected D).balanced

theorem chapter14_equation_14_2
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (D : Chapter14HorizontalDivisor F)
    (v : Chapter14RationalVerticalDivisor F) :
    chapter14Balanced F
        (fun i => (D.componentIntersections i : ℚ)) v ↔
      ∀ i, chapter14CorrectedComponentVector F D v i = 0 := by
  sorry

theorem chapter14_vertical_corrections_differ_by_fiber
    {r : ℕ} {F : Chapter14FiberMatrix r}
    {D : Chapter14HorizontalDivisor F}
    (C₁ C₂ : Chapter14VerticalCorrection D) :
    chapter14RationallyEquivalentModuloFiber F
      C₁.coefficients C₂.coefficients := by
  sorry

theorem chapter14_vertical_correction_unique_mod_fiber
    {r : ℕ} {F : Chapter14FiberMatrix r}
    {D : Chapter14HorizontalDivisor F}
    {v w : Chapter14RationalVerticalDivisor F}
    (hv : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) v)
    (hw : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) w) :
    chapter14RationallyEquivalentModuloFiber F v w := by
  sorry

/-! ## Normalizations -/

def chapter14WeightedNormalization {r : ℕ}
    {F : Chapter14FiberMatrix r}
    (v : Chapter14RationalVerticalDivisor F) : Prop :=
  chapter14DotProduct (chapter14FiberMultiplicityRat F) v = 0

def chapter14ChosenComponentNormalization {r : ℕ}
    {F : Chapter14FiberMatrix r} (i₀ : Fin r)
    (v : Chapter14RationalVerticalDivisor F) : Prop :=
  v i₀ = 0

theorem chapter14_weighted_normalization_exists_unique
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (D : Chapter14HorizontalDivisor F) :
    ∃! v : Chapter14RationalVerticalDivisor F,
      chapter14Balanced F
        (fun i => (D.componentIntersections i : ℚ)) v ∧
        chapter14WeightedNormalization v := by
  sorry

theorem chapter14_chosen_component_normalization_exists_unique
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (D : Chapter14HorizontalDivisor F) (i₀ : Fin r) :
    ∃! v : Chapter14RationalVerticalDivisor F,
      chapter14Balanced F
        (fun i => (D.componentIntersections i : ℚ)) v ∧
        chapter14ChosenComponentNormalization i₀ v := by
  sorry

noncomputable def chapter14WeightedNormalizedCorrection
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (D : Chapter14HorizontalDivisor F) :
    Chapter14RationalVerticalDivisor F :=
  Classical.choose (chapter14_weighted_normalization_exists_unique F D)

theorem chapter14WeightedNormalizedCorrection_spec
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (D : Chapter14HorizontalDivisor F) :
    chapter14Balanced F
        (fun i => (D.componentIntersections i : ℚ))
        (chapter14WeightedNormalizedCorrection F D) ∧
      chapter14WeightedNormalization
        (chapter14WeightedNormalizedCorrection F D) := by
  sorry

noncomputable def chapter14ChosenComponentNormalizedCorrection
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (D : Chapter14HorizontalDivisor F) (i₀ : Fin r) :
    Chapter14RationalVerticalDivisor F :=
  Classical.choose (chapter14_chosen_component_normalization_exists_unique F D i₀)

theorem chapter14ChosenComponentNormalizedCorrection_spec
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (D : Chapter14HorizontalDivisor F) (i₀ : Fin r) :
    chapter14Balanced F
        (fun i => (D.componentIntersections i : ℚ))
        (chapter14ChosenComponentNormalizedCorrection F D i₀) ∧
      chapter14ChosenComponentNormalization i₀
        (chapter14ChosenComponentNormalizedCorrection F D i₀) := by
  sorry

theorem chapter14_normalization_changes_only_representative
    {r : ℕ} {F : Chapter14FiberMatrix r}
    {D : Chapter14HorizontalDivisor F}
    {v w : Chapter14RationalVerticalDivisor F}
    (hv : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) v)
    (hw : chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) w) :
    chapter14RationallyEquivalentModuloFiber F v w := by
  exact chapter14_vertical_correction_unique_mod_fiber hv hw

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14
