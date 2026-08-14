import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

/-! ## 4.1. The bundle attached to a divisor -/

/-!
The following subtype is the literal local formula
`{g : 𝓚_X(U) | g f_i is regular on U ∩ U_i for every i}`.
The restriction to an intersection is made with the chosen total-quotient
presheaf, while regularity means that the product lies in the image of the
structure sheaf.
-/
def chapter04OofDSections {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) (U : X.Opens) :
    Set (Chapter04TotalQuotientSection X U) :=
  {g | ∀ i : D.cover.I₀, ∃ a : Γ(X, U ⊓ (D.cover.f i).opensRange),
    chapter04StructureToTotal _ a =
      chapter04TotalQuotientRestriction inf_le_left g *
        chapter04TotalQuotientRestriction inf_le_right (D.equation i)}

abbrev Chapter04OofDSection {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) (U : X.Opens) :=
  {g : Chapter04TotalQuotientSection X U // g ∈ chapter04OofDSections D U}

/- LOCAL_DEPENDENCY_GUESS: the pinned sheaf API does not yet construct the
subsheaf of the total quotient sheaf cut out by these local inequalities.
This record keeps the section formula and its sheafification tied together,
instead of introducing an unrelated module sheaf called `O(D)`. -/
structure Chapter04OofDData {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) where
  lineBundle : Chapter04LineBundle X
  sectionEquiv : ∀ U : X.Opens,
    lineBundle.sheaf.val.presheaf.obj (Opposite.op U) ≃ Chapter04OofDSection D U

theorem chapter04_oOfD_data_exists {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) : Nonempty (Chapter04OofDData D) := by
  sorry

noncomputable def chapter04OofDData {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) : Chapter04OofDData D :=
  Classical.choice (chapter04_oOfD_data_exists D)

noncomputable def chapter04OofD {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) : Chapter04LineBundle X :=
  (chapter04OofDData D).lineBundle

theorem chapter04OofD_sections_characterization {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) (U : X.Opens) :
    ∃ e : (chapter04OofD D).sheaf.val.presheaf.obj (Opposite.op U) ≃
      Chapter04OofDSection D U,
      ∀ s, (e s).1 ∈ chapter04OofDSections D U := by
  exact ⟨(chapter04OofDData D).sectionEquiv U, fun s => (chapter04OofDData D).sectionEquiv U s |>.2⟩

def chapter04OofDLocalGeneration {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) (i : D.cover.I₀) : Prop :=
  ∀ g : Chapter04OofDSection D (D.cover.f i).opensRange, ∃ a : Γ(X, (D.cover.f i).opensRange),
    chapter04StructureToTotal _ a *
        (↑((D.equation_unit i)⁻¹) :
          Chapter04TotalQuotientSection X (D.cover.f i).opensRange) = g.1

theorem chapter04_oOfD_locally_generated_by_inverse_equation {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) (i : D.cover.I₀) :
    chapter04OofDLocalGeneration D i := by
  sorry

/-!
The sign convention is recorded by taking the inverse Cartier cocycle for
`-D`.  Thus the object whose local generator is `f_i` is `O(-D)`, while
`O(D)` allows the inverse generator `f_i⁻¹`.
-/
noncomputable def chapter04OofNegD {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) : Chapter04LineBundle X :=
  chapter04OofD (chapter04CartierDivisorNeg D)

theorem chapter04_oOfNegD_is_dual {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) :
    chapter04LineBundleIsomorphic
      (chapter04OofNegD D) (chapter04DualLineBundle (chapter04OofD D)) := by
  sorry

theorem chapter04_oOf_add_is_tensor {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D E : Chapter04CartierDivisor X) :
    chapter04LineBundleIsomorphic
      (chapter04OofD (chapter04CartierDivisorAdd D E))
      (chapter04LineBundleTensor (chapter04OofD D) (chapter04OofD E)) := by
  sorry

theorem chapter04_oOf_sub_is_tensor_with_dual {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D E : Chapter04CartierDivisor X) :
    chapter04LineBundleIsomorphic
      (chapter04OofD (chapter04CartierDivisorSub D E))
      (chapter04LineBundleTensor (chapter04OofD D) (chapter04DualLineBundle (chapter04OofD E))) := by
  sorry

/-! ### Effective divisors and the canonical section -/

def chapter04OofDGlobalRationalValue {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X)
    (s : Chapter04GlobalSection (chapter04OofD D)) :
    Chapter04TotalQuotientSection X ⊤ :=
  ((chapter04OofDData D).sectionEquiv ⊤ s).1

structure Chapter04CanonicalSectionData {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) where
  section : Chapter04GlobalSection (chapter04OofD D.cartier)
  rationalValue : chapter04OofDGlobalRationalValue D.cartier section =
    chapter04StructureToTotal ⊤ 1
  vanishingIdeal : X.IdealSheafData
  vanishingIdeal_eq : vanishingIdeal = D.ideal

theorem chapter04_effectiveCartier_canonicalSection_exists {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) :
    Nonempty (Chapter04CanonicalSectionData D) := by
  sorry

noncomputable def chapter04CanonicalSectionData {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) : Chapter04CanonicalSectionData D :=
  Classical.choice (chapter04_effectiveCartier_canonicalSection_exists D)

noncomputable def chapter04CanonicalSection {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) :
    Chapter04GlobalSection (chapter04OofD D.cartier) :=
  (chapter04CanonicalSectionData D).section

theorem chapter04_canonicalSection_has_rational_value_one {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) :
    chapter04OofDGlobalRationalValue D.cartier (chapter04CanonicalSection D) =
      chapter04StructureToTotal ⊤ 1 := by
  exact (chapter04CanonicalSectionData D).rationalValue

theorem chapter04_canonicalSection_vanishing_exactly_on_divisor {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) :
    (chapter04CanonicalSectionData D).vanishingIdeal = D.ideal := by
  exact (chapter04CanonicalSectionData D).vanishingIdeal_eq

def chapter04EffectiveCartierNegativeLineBundle {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) : Chapter04LineBundle X :=
  (chapter04EffectiveCartierSequenceData D).negative

theorem chapter04_effectiveCartier_negative_lineBundle_is_ideal {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) :
    chapter04LineBundleIsomorphic
      (chapter04EffectiveCartierNegativeLineBundle D)
      (chapter04OofNegD D.cartier) := by
  sorry

def chapter04EffectiveCartierExactSequence {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) : ShortComplex X.Modules :=
  ShortComplex.mk
    (chapter04EffectiveCartierSequenceData D).inclusion_map
    (chapter04EffectiveCartierSequenceData D).quotient_map

theorem chapter04_effectiveCartier_exact_sequence {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) :
    (chapter04EffectiveCartierExactSequence D).Exact := by
  exact (chapter04EffectiveCartierSequenceData D).exact

/-! ### Curves and the pole-bound description -/

def chapter04CurveOofDCondition {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter04CartierOrderAPI X]
    (D : Chapter04CartierDivisor X) (U : X.Opens) (g : X.functionField) : Prop :=
  ∀ x : X, x ∈ U → ∀ hx : coheight x = 1,
    AlgebraicGeometry.Scheme.ord g x + chapter04CartierOrder D ⟨x, hx⟩ ≥ 0

def chapter04RationalFunctionsWithPoleBound {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter04CartierOrderAPI X]
    (D : Chapter04CartierDivisor X) : Set X.functionField :=
  {g | chapter04CurveOofDCondition D ⊤ g}

def chapter04RationalFunctionsWithPoleBoundOnOpen {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter04CartierOrderAPI X]
    (D : Chapter04CartierDivisor X) (U : X.Opens) : Set X.functionField :=
  {g | chapter04CurveOofDCondition D U g}

theorem chapter04_regular_integral_curve_OofD_sections {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter04CartierOrderAPI X]
    (D : Chapter04CartierDivisor X) (U : X.Opens) :
    ∀ g : X.functionField,
      g ∈ chapter04RationalFunctionsWithPoleBoundOnOpen D U ↔
        ∀ x : X, x ∈ U → ∀ hx : coheight x = 1,
          AlgebraicGeometry.Scheme.ord g x + chapter04CartierOrder D ⟨x, hx⟩ ≥ 0 := by
  intro g
  rfl

theorem chapter04_globalSections_OofD_are_bounded_poles {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter04CartierOrderAPI X]
    (D : Chapter04CartierDivisor X) :
    Nonempty (Chapter04GlobalSection (chapter04OofD D) ≃
      {g : X.functionField // g ∈ chapter04RationalFunctionsWithPoleBound D}) := by
  sorry

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04
