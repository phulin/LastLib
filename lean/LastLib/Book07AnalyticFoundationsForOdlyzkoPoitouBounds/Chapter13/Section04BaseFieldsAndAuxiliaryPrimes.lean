import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13

noncomputable section

universe u v

open scoped BigOperators NumberField

/-! ### 13.4 Base fields and auxiliary primes -/

/-! Formula (13.2): the root discriminant in a finite number-field
extension, expressed through the relative different. -/
theorem chapter13_relative_rootDiscriminant_formula
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [IsScalarTower ℚ F L] [Module.Finite F L]
    [Module.Finite (𝓞 F) (𝓞 L)] :
    chapter13RootDiscriminant L =
      chapter13RootDiscriminant F *
        Real.rpow (chapter13RelativeDiscriminantNorm F L : ℝ)
          ((chapter13Degree L : ℝ)⁻¹) := by
  exact chapter13_rootDiscriminant_tower_formula F L

/-! Formula (13.3), with a finite injective support of normalized local
different costs. -/
theorem chapter13_local_cost_ceiling_formula
    (F : Type*) [Field F] [NumberField F]
    (P : Chapter13LocalDifferentCostProfile F) :
    chapter13AbsoluteCeilingFromLocalCosts F P =
      chapter13RootDiscriminant F *
        ∏ i : P.index,
          Real.rpow (chapter13FinitePlaceNorm (P.place i))
            (P.cost i / (chapter13Degree F : ℝ)) := by
  rfl

structure Chapter13BaseFieldCeilingCertificate
    (F : Type u) [Field F] [NumberField F] where
  profile : Chapter13LocalDifferentCostProfile.{u, v} F
  U : ℝ
  U_pos : 0 < U
  U_eq : U = chapter13AbsoluteCeilingFromLocalCosts F profile

noncomputable def chapter13BaseFieldCeilingCertificate
    (F : Type u) [Field F] [NumberField F]
    (P : Chapter13LocalDifferentCostProfile.{u, v} F) :
    Chapter13BaseFieldCeilingCertificate.{u, v} F where
  profile := P
  U := chapter13AbsoluteCeilingFromLocalCosts F P
  U_pos := chapter13_absolute_ceiling_from_local_costs_pos F P
  U_eq := rfl

@[simp]
theorem chapter13_base_field_ceiling_certificate_value
    (F : Type*) [Field F] [NumberField F]
    (P : Chapter13LocalDifferentCostProfile F) :
    (chapter13BaseFieldCeilingCertificate F P).U =
      chapter13AbsoluteCeilingFromLocalCosts F P :=
  rfl

/- The local-cost certificate is an arithmetic input.  The analytic theorem
   below consumes its value and does not manufacture the costs or prove the
   product identity. -/
theorem chapter13_absolute_degree_cap_from_base_field_ceiling
    (F : Type*) [Field F] [NumberField F]
    (P : Chapter13LocalDifferentCostProfile F)
    (α₀ : ℝ) (N : ℕ) (f : ℝ → ℝ)
    (hα₀ : 0 ≤ α₀) (hα₀' : α₀ ≤ 1) (hN : 0 < N)
    (hC : chapter13C f ≤ Real.pi / 2)
    (hmargin : chapter13LogLowerBound f N α₀ >
      Real.log (chapter13AbsoluteCeilingFromLocalCosts F P))
    (L : Type u) [Field L] [NumberField L]
    (hanalytic : chapter13FieldwiseAnalyticBound f L)
    (hceil : chapter13RootDiscriminant L ≤
      chapter13AbsoluteCeilingFromLocalCosts F P)
    (hα : α₀ ≤ chapter13RealProportion L) :
    chapter13Degree L < N := by
  sorry

theorem chapter13_relative_degree_cap_from_absolute_degree_cap
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [Algebra ℚ F] [Algebra ℚ L] [IsScalarTower ℚ F L]
    {N : ℕ} (hdegree : chapter13Degree L < N) :
    (Module.finrank F L : ℝ) < N / (chapter13Degree F : ℝ) := by
  exact chapter13_relative_degree_lt_of_absolute_degree_lt F L hdegree

theorem chapter13_base_field_ceiling_gives_relative_cap
    (F : Type*) [Field F] [NumberField F]
    (P : Chapter13LocalDifferentCostProfile F)
    (α₀ : ℝ) (N : ℕ) (f : ℝ → ℝ)
    (hα₀ : 0 ≤ α₀) (hα₀' : α₀ ≤ 1) (hN : 0 < N)
    (hC : chapter13C f ≤ Real.pi / 2)
    (hmargin : chapter13LogLowerBound f N α₀ >
      Real.log (chapter13AbsoluteCeilingFromLocalCosts F P))
    (L : Type u) [Field L] [NumberField L]
    (hanalytic : chapter13FieldwiseAnalyticBound f L)
    [Algebra F L] [Algebra ℚ F] [Algebra ℚ L] [IsScalarTower ℚ F L]
    (hceil : chapter13RootDiscriminant L ≤
      chapter13AbsoluteCeilingFromLocalCosts F P)
    (hα : α₀ ≤ chapter13RealProportion L) :
    (Module.finrank F L : ℝ) < N / (chapter13Degree F : ℝ) := by
  have hdegree : chapter13Degree L < N := by
    exact chapter13_absolute_degree_cap_from_base_field_ceiling
      F P α₀ N f hα₀ hα₀' hN hC hmargin L hanalytic hceil hα
  exact chapter13_relative_degree_cap_from_absolute_degree_cap F L hdegree

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13
