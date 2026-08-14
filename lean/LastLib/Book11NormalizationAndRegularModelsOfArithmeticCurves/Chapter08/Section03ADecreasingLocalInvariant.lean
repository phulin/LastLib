import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08.Section02PreparingTheSingularLocus

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ## 8.3. A decreasing local invariant -/

def chapter08HilbertSamuelValue
    (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) : ℚ :=
  ((chapter08RingQuotientLength A
      (chapter08MaximalIdeal A ^ (n + 1) : Ideal A)).toNat : ℚ)

def Chapter08LinearErrorBound (error : ℕ → ℚ) : Prop :=
  ∃ C N : ℕ, ∀ n : ℕ, N ≤ n →
    |error n| ≤ (C : ℚ) * (n : ℚ) + C

def chapter08HilbertSamuelQuadraticAsymptotic
    (A : Type u) [CommRing A] [IsLocalRing A] (e : ℕ) : Prop :=
  ∃ error : ℕ → ℚ,
    Chapter08LinearErrorBound error ∧
      ∀ n : ℕ,
        chapter08HilbertSamuelValue A n =
          (e : ℚ) / 2 * (n : ℚ) ^ 2 + error n

structure Chapter08HilbertSamuelData
    (A : Type u) [CommRing A] [IsLocalRing A] where
  multiplicity : ℕ
  positive : 0 < multiplicity
  asymptotic : chapter08HilbertSamuelQuadraticAsymptotic A multiplicity

theorem chapter08_hilbertSamuel_data_exists
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) :
    Nonempty (Chapter08HilbertSamuelData A) := by
  sorry

noncomputable def chapter08HilbertSamuelData
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) : Chapter08HilbertSamuelData A :=
  Classical.choice (chapter08_hilbertSamuel_data_exists A hdim)

noncomputable def chapter08Multiplicity
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) : ℕ :=
  (chapter08HilbertSamuelData A hdim).multiplicity

theorem chapter08_multiplicity_pos
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) :
    0 < chapter08Multiplicity A hdim := by
  exact (chapter08HilbertSamuelData A hdim).positive

theorem chapter08_hilbertSamuel_asymptotic
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) :
    chapter08HilbertSamuelQuadraticAsymptotic A (chapter08Multiplicity A hdim) := by
  exact (chapter08HilbertSamuelData A hdim).asymptotic

theorem chapter08_regular_local_multiplicity_one
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2)
    (hregular : IsRegularLocalRing A) :
    chapter08Multiplicity A hdim = 1 := by
  sorry

theorem chapter08_unmixed_multiplicity_one_iff_regular
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2)
    (hunmixed : Chapter08UnmixedLocalRing A) :
    chapter08Multiplicity A hdim = 1 ↔ IsRegularLocalRing A := by
  sorry

/-! The associated graded ring and its affine tangent cone are the objects used to refine
Hilbert--Samuel multiplicity. -/

def chapter08TangentCone
    (A : Type u) [CommRing A] [IsLocalRing A] : Scheme.{u} :=
  Spec (.of (chapter08AssociatedGraded A))

theorem chapter08_tangentCone_is_affine
    (A : Type u) [CommRing A] [IsLocalRing A] :
    chapter08TangentCone A = Spec (.of (chapter08AssociatedGraded A)) :=
  rfl

structure Chapter08SurfaceLocalInvariantInput
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] : Prop where
  domain : IsDomain A
  normal : IsIntegrallyClosed A
  excellent : Chapter03Excellent A
  dimension_two : ringKrullDim A = 2

theorem chapter08SurfaceLocalInvariantInput_of_excellentNormal
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (hA : Chapter08ExcellentNormalTwoDimensionalLocalDomain A) :
    Chapter08SurfaceLocalInvariantInput A := by
  sorry

structure Chapter08ConductorProfile
    (A : Type u) [CommRing A] [IsLocalRing A] where
  parameter : A
  parameter_is_general : Prop
  sectionRing : Type u
  sectionRing_identification :
    sectionRing = (A ⧸ Ideal.span ({parameter} : Set A))
  normalization : Type u
  finite_normalization : Prop
  conductor_colength : ℕ
  conductor_colength_specification : Prop
  independent_of_general_choice : Prop

structure Chapter08LocalInvariantData
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] where
  multiplicity : ℕ
  directrixField : Type u
  [directrixField_isField : Field directrixField]
  [directrixField_algebra : Algebra (IsLocalRing.ResidueField A) directrixField]
  directrix : Chapter08DirectrixProfile A directrixField
  conductor : Chapter08ConductorProfile A
  multiplicity_specification : Prop

theorem chapter08_localInvariantData_exists
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : Chapter08SurfaceLocalInvariantInput A) :
    Nonempty (Chapter08LocalInvariantData A) := by
  sorry

noncomputable def chapter08LocalInvariantData
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : Chapter08SurfaceLocalInvariantInput A) :
    Chapter08LocalInvariantData A :=
  Classical.choice (chapter08_localInvariantData_exists A hA)

def chapter08InvariantOfData
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (D : Chapter08LocalInvariantData A) : ℕ × ℕ × ℕ :=
  letI := D.directrixField_isField
  letI := D.directrixField_algebra
  (D.multiplicity,
    (2 - Module.finrank D.directrixField D.directrix.directrix,
      D.conductor.conductor_colength))

noncomputable def chapter08Invariant
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : Chapter08SurfaceLocalInvariantInput A) : ℕ × ℕ × ℕ :=
  chapter08InvariantOfData A (chapter08LocalInvariantData A hA)

theorem chapter08_invariant_first_component_is_multiplicity
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : Chapter08SurfaceLocalInvariantInput A) :
    (chapter08Invariant A hA).1 =
      (chapter08LocalInvariantData A hA).multiplicity := by
  rfl

theorem chapter08_localInvariantData_multiplicity_is_hilbertSamuel
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : Chapter08SurfaceLocalInvariantInput A) :
    (chapter08LocalInvariantData A hA).multiplicity =
      chapter08Multiplicity A hA.dimension_two := by
  sorry

def chapter08LexLess (a b : ℕ × ℕ × ℕ) : Prop :=
  a.1 < b.1 ∨
    (a.1 = b.1 ∧
      (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)))

theorem chapter08_lexLess_irreflexive (a : ℕ × ℕ × ℕ) :
    ¬ chapter08LexLess a a := by
  sorry

theorem chapter08_lexLess_transitive
    {a b c : ℕ × ℕ × ℕ}
    (hab : chapter08LexLess a b) (hbc : chapter08LexLess b c) :
    chapter08LexLess a c := by
  sorry

/-! The conductor computation is retained as an independent interface because it is also useful
for the one-dimensional normalization statements in the examples. -/

def chapter08ConductorLengthFormula
    {ι : Type u} [Fintype ι]
    (totalLength baseLength : ℕ∞)
    (branchLength : ι → ℕ∞) : Prop :=
  totalLength = (∑ j, branchLength j) - baseLength

structure Chapter08ConductorLengthData where
  branchIndex : Type u
  [branchIndex_finite : Fintype branchIndex]
  totalLength : ℕ∞
  baseLength : ℕ∞
  branchLength : branchIndex → ℕ∞
  baseLength_le_branchSum : baseLength ≤ ∑ j, branchLength j
  branch_quotient_lengths : Prop
  base_quotient_length : Prop
  formula : chapter08ConductorLengthFormula totalLength baseLength branchLength

theorem chapter08_conductor_length_formula
    (D : Chapter08ConductorLengthData) :
    letI := D.branchIndex_finite
    D.totalLength = (∑ j, D.branchLength j) - D.baseLength := by
  exact D.formula

theorem chapter08_conductor_length_data_exists
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : Chapter08SurfaceLocalInvariantInput A) :
    Nonempty (Chapter08ConductorLengthData) := by
  sorry

structure Chapter08ResidueExtensionCenterDescent
    (A : Type u) [CommRing A] [IsLocalRing A] (I : Ideal A) where
  extensionDegree : ℕ
  extensionDegree_positive : 0 < extensionDegree
  finite_unramified_extension : Prop
  originalCenter : Ideal A
  originalCenter_eq : originalCenter = I
  extendedCenter : Ideal A
  descent_compatibility : Prop

theorem chapter08_finite_unramified_extension_descends_center
    (A : Type u) [CommRing A] [IsLocalRing A]
    (I : Ideal A) :
    Nonempty (Chapter08ResidueExtensionCenterDescent A I) := by
  sorry

/-! Interfaces for the normalized blowup pointwise decrease. -/

structure Chapter08SurfaceDecreaseIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] where
  ideal : Ideal A
  m_primary : Chapter08MPrimaryIdeal ideal
  maximal_order_generators : Chapter08MaximalOrderGenerated ideal
  compatible_with_regular_punctured_spectrum : Prop

structure Chapter08NonregularNormalizedBlowupPoint
    (A : Type u) [CommRing A] [IsLocalRing A]
    (I : Ideal A) (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] where
  lies_on_normalized_blowup : Prop
  local_input : Chapter08SurfaceLocalInvariantInput B
  nonregular : ¬ IsRegularLocalRing B

def Chapter08RegularPuncturedSpectrumCondition
    (A : Type u) [CommRing A] [IsLocalRing A]
    (V : Set (chapter08LocalSurfaceSpec A)) : Prop :=
  ∀ x : chapter08LocalSurfaceSpec A, x ∈ V →
    IsRegularLocalRing ((chapter08LocalSurfaceSpec A).presheaf.stalk x)

theorem chapter08_surface_decrease
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : Chapter08SurfaceLocalInvariantInput A)
    (hnotregular : ¬ IsRegularLocalRing A) :
    ∃ D : Chapter08SurfaceDecreaseIdeal A,
      ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
        (P : Chapter08NonregularNormalizedBlowupPoint A D.ideal B),
        chapter08LexLess (chapter08Invariant B P.local_input)
          (chapter08Invariant A hA) := by
  sorry

theorem chapter08_surface_decrease_with_prescribed_regular_punctured_spectrum
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : Chapter08SurfaceLocalInvariantInput A)
    (hnotregular : ¬ IsRegularLocalRing A)
    (V : Set (chapter08LocalSurfaceSpec A))
    (hV : Chapter08RegularPuncturedSpectrumCondition A V) :
    ∃ D : Chapter08SurfaceDecreaseIdeal A,
      D.compatible_with_regular_punctured_spectrum ∧
        ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
          (P : Chapter08NonregularNormalizedBlowupPoint A D.ideal B),
          chapter08LexLess (chapter08Invariant B P.local_input)
            (chapter08Invariant A hA) := by
  sorry

def Chapter08MultiplicityPlateau
    (A B : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (hA : Chapter08SurfaceLocalInvariantInput A)
    (hB : Chapter08SurfaceLocalInvariantInput B) : Prop :=
  chapter08Multiplicity A hA.dimension_two = chapter08Multiplicity B hB.dimension_two

structure Chapter08MultiplicityPlateauExample : Type (u + 1) where
  A : Type u
  [commRingA : CommRing A]
  [localA : IsLocalRing A]
  [noetherianA : IsNoetherianRing A]
  hA : Chapter08SurfaceLocalInvariantInput A
  center : Ideal A
  B : Type u
  [commRingB : CommRing B]
  [localB : IsLocalRing B]
  [noetherianB : IsNoetherianRing B]
  point : Chapter08NonregularNormalizedBlowupPoint A center B
  multiplicity_equal :
    chapter08Multiplicity A hA.dimension_two =
      chapter08Multiplicity B point.local_input.dimension_two

theorem chapter08_multiplicity_can_remain_constant_under_normalized_blowup :
    Nonempty Chapter08MultiplicityPlateauExample := by
  sorry

theorem chapter08_multiplicity_is_only_the_first_invariant_component
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : Chapter08SurfaceLocalInvariantInput A) :
    (chapter08Invariant A hA).1 = chapter08Multiplicity A hA.dimension_two := by
  rw [chapter08_invariant_first_component_is_multiplicity]
  exact chapter08_localInvariantData_multiplicity_is_hilbertSamuel A hA

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08
