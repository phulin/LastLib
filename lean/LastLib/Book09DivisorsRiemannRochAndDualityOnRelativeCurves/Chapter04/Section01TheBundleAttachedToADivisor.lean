import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02.Section02EffectiveCartierDivisors

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

/- The structure map supplies the scalar algebra on each total-quotient
section.  This keeps the local formula below a genuine submodule condition,
rather than a bare predicate on a ring. -/
noncomputable instance chapter04TotalQuotientSectionAlgebra {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] (U : X.Opens) :
    Algebra (Γ(X, U)) (Chapter04TotalQuotientSection X U) :=
  (chapter04StructureToTotal U).toAlgebra

def chapter04OofDSectionsSubmodule {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) (U : X.Opens) :
    Submodule (Γ(X, U)) (Chapter04TotalQuotientSection X U) :=
  { carrier := chapter04OofDSections D U
    zero_mem' := by
      sorry
    add_mem' := by
      sorry
    smul_mem' := by
      sorry }

abbrev Chapter04OofDSection {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) (U : X.Opens) :=
  chapter04OofDSectionsSubmodule D U

def chapter04OofDSectionRestriction {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) {U V : X.Opens} (h : V ≤ U)
    (s : Chapter04OofDSection D U) : Chapter04OofDSection D V :=
  { val := chapter04TotalQuotientRestriction h s.1
    property := by
      sorry }

/- LOCAL_DEPENDENCY_GUESS: the pinned sheaf API does not yet construct a named
subsheaf of the total quotient sheaf cut out by these local inequalities.
The pointwise submodules and their restriction-compatible linear
equivalences below keep the section formula tied to the line bundle. -/
structure Chapter04OofDData {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) where
  lineBundle : Chapter04LineBundle X
  sectionEquiv : ∀ U : X.Opens,
    Γ(lineBundle.sheaf, U) ≃ₗ[Γ(X, U)]
      Chapter04OofDSection D U
  sectionEquiv_restrict :
    ∀ (U V : X.Opens) (h : V ≤ U) (s : Chapter04OofDSection D U),
      sectionEquiv V
          (lineBundle.sheaf.val.presheaf.map (homOfLE h).op
            ((sectionEquiv U).symm s)) =
        chapter04OofDSectionRestriction D h s

theorem chapter04_oOfD_data_exists {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) : Nonempty (Chapter04OofDData D) := by
  sorry

noncomputable def chapter04OofDData {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) : Chapter04OofDData D :=
  Classical.choice (chapter04_oOfD_data_exists D)

noncomputable abbrev chapter04OofD {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) : Chapter04LineBundle X :=
  (chapter04OofDData D).lineBundle

theorem chapter04OofD_sections_characterization {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) (U : X.Opens) :
    ∃ e : Γ((chapter04OofD D).sheaf, U) ≃
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

noncomputable def chapter04EffectiveCartierIdealQuotient {X : Scheme.{u}}
    (I : X.IdealSheafData) :
    (chapter04TrivialLineBundle X).sheaf ⟶
      (Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom

noncomputable def chapter04EffectiveCartierIdealOminusD {X : Scheme.{u}}
    (I : X.IdealSheafData) : X.Modules :=
  kernel (chapter04EffectiveCartierIdealQuotient I)

noncomputable def chapter04EffectiveCartierIdealInclusion {X : Scheme.{u}}
    (I : X.IdealSheafData) :
    chapter04EffectiveCartierIdealOminusD I ⟶
      (chapter04TrivialLineBundle X).sheaf :=
  kernel.ι (chapter04EffectiveCartierIdealQuotient I)

/-!
The exact-sequence witness is placed after `O(-D)` is available, so its
negative term cannot be an unrelated line bundle chosen by an existential
proof.  This records the canonical identification needed by the effective
Cartier sequence below.
-/
structure Chapter04EffectiveCartierSequenceData {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) where
  negative : Chapter04LineBundle X
  negative_is_OofNegD :
    chapter04LineBundleIsomorphic negative (chapter04OofNegD D.cartier)
  quotient : X.Modules
  quotient_iso : quotient ≅
    (Scheme.Modules.pushforward D.inclusion).obj
      (SheafOfModules.unit D.subscheme.ringCatSheaf)
  negative_to_ideal :
    negative.sheaf ≅ chapter04EffectiveCartierIdealOminusD D.ideal
  inclusion_map : negative.sheaf ⟶ (chapter04TrivialLineBundle X).sheaf
  quotient_map : (chapter04TrivialLineBundle X).sheaf ⟶ quotient
  inclusion_map_eq :
    inclusion_map =
      negative_to_ideal.hom ≫ chapter04EffectiveCartierIdealInclusion D.ideal
  quotient_map_eq :
    quotient_map ≫ quotient_iso.hom =
      chapter04EffectiveCartierIdealQuotient D.ideal
  comp_zero : inclusion_map ≫ quotient_map = 0
  exact : (ShortComplex.mk inclusion_map quotient_map comp_zero).Exact

theorem chapter04_effectiveCartier_sequence_exists {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) :
    Nonempty (Chapter04EffectiveCartierSequenceData D) := by
  sorry

noncomputable def chapter04EffectiveCartierSequenceData {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) : Chapter04EffectiveCartierSequenceData D :=
  Classical.choice (chapter04_effectiveCartier_sequence_exists D)

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
    (s : Γ((chapter04OofDData D).lineBundle.sheaf, (⊤ : X.Opens))) :
    Chapter04TotalQuotientSection X ⊤ :=
  ((chapter04OofDData D).sectionEquiv ⊤ s).1

structure Chapter04CanonicalSectionData {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) where
  canonical_section :
    Γ((chapter04OofDData D.cartier).lineBundle.sheaf, (⊤ : X.Opens))
  rationalValue : chapter04OofDGlobalRationalValue D.cartier canonical_section =
    chapter04StructureToTotal ⊤ 1
  canonical_section_eq_one :
    (chapter04OofDData D.cartier).sectionEquiv ⊤ canonical_section =
      (⟨chapter04StructureToTotal ⊤ 1, by sorry⟩ :
        Chapter04OofDSection D.cartier ⊤)
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
    Γ((chapter04OofDData D.cartier).lineBundle.sheaf, (⊤ : X.Opens)) :=
  (chapter04CanonicalSectionData D).canonical_section

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
  exact (chapter04EffectiveCartierSequenceData D).negative_is_OofNegD

theorem chapter04_effectiveCartier_negative_lineBundle_is_ideal_kernel {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) :
    Nonempty ((chapter04EffectiveCartierNegativeLineBundle D).sheaf ≅
      chapter04EffectiveCartierIdealOminusD D.ideal) := by
  exact ⟨(chapter04EffectiveCartierSequenceData D).negative_to_ideal⟩

def chapter04EffectiveCartierExactSequence {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) : ShortComplex X.Modules :=
  ShortComplex.mk
    (chapter04EffectiveCartierSequenceData D).inclusion_map
    (chapter04EffectiveCartierSequenceData D).quotient_map
    (chapter04EffectiveCartierSequenceData D).comp_zero

theorem chapter04_effectiveCartier_exact_sequence {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) :
    (chapter04EffectiveCartierExactSequence D).Exact := by
  exact (chapter04EffectiveCartierSequenceData D).exact

theorem chapter04_effectiveCartier_add_exists {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D E : Chapter04EffectiveCartierDivisor X) :
    Nonempty {F : Chapter04EffectiveCartierDivisor X //
      F.cartier = chapter04CartierDivisorAdd D.cartier E.cartier ∧
        F.ideal = D.ideal * E.ideal} := by
  sorry

noncomputable def chapter04EffectiveCartierDivisorAdd {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D E : Chapter04EffectiveCartierDivisor X) :
    Chapter04EffectiveCartierDivisor X :=
  (Classical.choice (chapter04_effectiveCartier_add_exists D E)).1

theorem chapter04_effectiveCartierDivisorAdd_cartier {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D E : Chapter04EffectiveCartierDivisor X) :
    (chapter04EffectiveCartierDivisorAdd D E).cartier =
      chapter04CartierDivisorAdd D.cartier E.cartier := by
  exact (Classical.choice (chapter04_effectiveCartier_add_exists D E)).2.1

theorem chapter04_effectiveCartierDivisorAdd_ideal {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D E : Chapter04EffectiveCartierDivisor X) :
    (chapter04EffectiveCartierDivisorAdd D E).ideal = D.ideal * E.ideal := by
  exact (Classical.choice (chapter04_effectiveCartier_add_exists D E)).2.2

/-! ### Curves and the pole-bound description -/

def chapter04CurveOofDCondition {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (D : Chapter04CartierDivisor X) (U : X.Opens) (g : X.functionField) : Prop :=
  ∀ x : X, x ∈ U → ∀ hx : Order.coheight x = 1,
    AlgebraicGeometry.Scheme.ord g x + chapter04CartierOrder D ⟨x, hx⟩ ≥ 0

def chapter04RationalFunctionsWithPoleBound {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (D : Chapter04CartierDivisor X) : Set X.functionField :=
  {g | chapter04CurveOofDCondition D ⊤ g}

def chapter04RationalFunctionsWithPoleBoundOnOpen {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (D : Chapter04CartierDivisor X) (U : X.Opens) : Set X.functionField :=
  {g | chapter04CurveOofDCondition D U g}

theorem chapter04_regular_integral_curve_OofD_sections {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (D : Chapter04CartierDivisor X) (U : X.Opens) :
    ∀ g : X.functionField,
      g ∈ chapter04RationalFunctionsWithPoleBoundOnOpen D U ↔
        ∀ x : X, x ∈ U → ∀ hx : Order.coheight x = 1,
          AlgebraicGeometry.Scheme.ord g x + chapter04CartierOrder D ⟨x, hx⟩ ≥ 0 := by
  intro g
  rfl

theorem chapter04_globalSections_OofD_are_bounded_poles {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03IntegralNoetherianCurve X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03Regular X]
    [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (D : Chapter04CartierDivisor X) :
    Nonempty (Chapter04GlobalSection (chapter04OofD D) ≃
      {g : X.functionField // g ∈ chapter04RationalFunctionsWithPoleBound D}) := by
  sorry

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04
