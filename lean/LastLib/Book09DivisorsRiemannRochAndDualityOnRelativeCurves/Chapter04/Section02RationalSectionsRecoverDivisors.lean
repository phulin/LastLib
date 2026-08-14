import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Section01TheBundleAttachedToADivisor

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

/-! ## 4.2. Rational sections recover divisors -/

/-!
For an integral scheme, the generic stalk of a line bundle is a one-dimensional
function-field vector space.  The module structure is a canonical sheaf-level
bridge that is not currently named by Mathlib.
-/
theorem chapter04_genericFiberModule_exists {X : Scheme.{u}}
    [IsIntegral X] (L : Chapter04LineBundle X) :
    Nonempty (Module X.functionField
      (L.sheaf.presheaf.stalk (genericPoint X))) := by
  sorry

@[instance_reducible]
noncomputable def chapter04GenericFiberModule {X : Scheme.{u}}
    [IsIntegral X] (L : Chapter04LineBundle X) : Module X.functionField
      (L.sheaf.presheaf.stalk (genericPoint X)) :=
  Classical.choice (chapter04_genericFiberModule_exists L)

def chapter04IsGenericFiberGenerator {X : Scheme.{u}}
    [IsIntegral X] (L : Chapter04LineBundle X)
    (v : L.sheaf.presheaf.stalk (genericPoint X)) : Prop :=
  letI := chapter04GenericFiberModule L
  v ≠ 0 ∧ ∀ w, ∃ a : X.functionField, a • v = w

structure Chapter04RationalSection {X : Scheme.{u}}
    [IsIntegral X] (L : Chapter04LineBundle X) where
  value : L.sheaf.presheaf.stalk (genericPoint X)
  isGenerator : chapter04IsGenericFiberGenerator L value

def chapter04RationalSectionNonzero {X : Scheme.{u}}
    [IsIntegral X] {L : Chapter04LineBundle X}
    (s : Chapter04RationalSection L) : Prop :=
  s.value ≠ 0

theorem chapter04_rationalSection_nonzero {X : Scheme.{u}}
    [IsIntegral X] {L : Chapter04LineBundle X}
    (s : Chapter04RationalSection L) : chapter04RationalSectionNonzero s := by
  exact s.isGenerator.1

/- LOCAL_DEPENDENCY_GUESS: the transition from local generators of a module
sheaf to their generic-fiber coordinates is not exposed as one Mathlib map.
This record records the actual local generators, coefficients, and overlap
identities used by the divisor construction. -/
structure Chapter04RationalSectionCoordinateData {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [Chapter04RationalFunctionLocalValueAPI X]
    (L : Chapter04LineBundle X) (s : Chapter04RationalSection L) where
  cover : X.OpenCover
  localGenerator : ∀ i : cover.I₀,
    Γ(L.sheaf, (cover.f i).opensRange)
  localGenerator_isGenerator :
    ∀ i : cover.I₀, ∀ y : Γ(L.sheaf, (cover.f i).opensRange),
      ∃ a : Γ(X, (cover.f i).opensRange),
        a • localGenerator i = y
  localGenerator_isFaithful :
    ∀ i : cover.I₀, ∀ a : Γ(X, (cover.f i).opensRange),
      a • localGenerator i = 0 → a = 0
  coefficient : ∀ i : cover.I₀,
    Chapter04TotalQuotientSection X (cover.f i).opensRange
  coefficient_isUnit : ∀ i, IsUnit (coefficient i)
  local_equation :
    ∀ i : cover.I₀, ∀ hη : genericPoint X ∈ (cover.f i).opensRange,
      letI := chapter04GenericFiberModule L
      Chapter04RationalFunctionLocalValueAPI.toFunctionField
          ⟨(cover.f i).opensRange, ⟨genericPoint X, hη⟩⟩ (coefficient i) •
        L.sheaf.presheaf.germ _ _ hη (localGenerator i) = s.value
  overlap_compatibility :
    ∀ i j : cover.I₀, ∀ hη : genericPoint X ∈
      (cover.f i).opensRange ⊓ (cover.f j).opensRange,
      letI := chapter04GenericFiberModule L
      Chapter04RationalFunctionLocalValueAPI.toFunctionField
          ⟨(cover.f i).opensRange ⊓ (cover.f j).opensRange,
            ⟨genericPoint X, hη⟩⟩
          (chapter04TotalQuotientRestriction inf_le_left (coefficient i)) •
      L.sheaf.presheaf.germ _ _ hη
          (L.sheaf.presheaf.map (homOfLE inf_le_left).op (localGenerator i)) =
      Chapter04RationalFunctionLocalValueAPI.toFunctionField
          ⟨(cover.f i).opensRange ⊓ (cover.f j).opensRange,
            ⟨genericPoint X, hη⟩⟩
          (chapter04TotalQuotientRestriction inf_le_right (coefficient j)) •
        L.sheaf.presheaf.germ _ _ hη
          (L.sheaf.presheaf.map (homOfLE inf_le_right).op (localGenerator j))

theorem chapter04_rationalSection_coordinates_exist {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [Chapter04RationalFunctionLocalValueAPI X]
    (L : Chapter04LineBundle X) (s : Chapter04RationalSection L) :
    Nonempty (Chapter04RationalSectionCoordinateData L s) := by
  sorry

/-! The divisor attached to the coefficients is characterized by its local
equations, not merely by an abstract existence statement. -/
structure Chapter04DivisorOfRationalSectionData {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [Chapter04RationalFunctionLocalValueAPI X]
    (L : Chapter04LineBundle X) (s : Chapter04RationalSection L) where
  divisor : Chapter04CartierDivisor X
  coordinates : Chapter04RationalSectionCoordinateData L s
  coordinate_index : ∀ _i : divisor.cover.I₀, coordinates.cover.I₀
  coordinate_refines :
    ∀ i : divisor.cover.I₀,
      (divisor.cover.f i).opensRange ≤
        (coordinates.cover.f (coordinate_index i)).opensRange
  divisor_cover_nonempty :
    ∀ i : divisor.cover.I₀,
      Set.Nonempty ((divisor.cover.f i).opensRange : Set X)
  coordinate_cover_nonempty :
    ∀ i : coordinates.cover.I₀,
      Set.Nonempty ((coordinates.cover.f i).opensRange : Set X)
  coordinate_equation :
    ∀ i : divisor.cover.I₀,
      Chapter04RationalFunctionLocalValueAPI.toFunctionField
          ⟨(divisor.cover.f i).opensRange, divisor_cover_nonempty i⟩
          (divisor.equation i) =
        Chapter04RationalFunctionLocalValueAPI.toFunctionField
          ⟨(coordinates.cover.f (coordinate_index i)).opensRange,
            coordinate_cover_nonempty (coordinate_index i)⟩
          (coordinates.coefficient (coordinate_index i))
  bundle_iso : Nonempty ((chapter04OofD divisor).sheaf ≅ L.sheaf)
  canonical_section :
    Γ((chapter04OofDData divisor).lineBundle.sheaf, (⊤ : X.Opens))
  canonical_section_maps_to_s :
    ∃ e : (chapter04OofD divisor).sheaf ≅ L.sheaf,
      letI := chapter04GenericFiberModule L
      (TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map e.hom.mapPresheaf
          ((chapter04OofDData divisor).lineBundle.sheaf.presheaf.germ
            ⊤ (genericPoint X) (by trivial) canonical_section) = s.value

theorem chapter04_divisorOfRationalSection_exists {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [Chapter04RationalFunctionLocalValueAPI X]
    (L : Chapter04LineBundle X) (s : Chapter04RationalSection L) :
    Nonempty (Chapter04DivisorOfRationalSectionData L s) := by
  sorry

noncomputable def chapter04DivisorOfRationalSectionData {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [Chapter04RationalFunctionLocalValueAPI X]
    (L : Chapter04LineBundle X) (s : Chapter04RationalSection L) :
    Chapter04DivisorOfRationalSectionData L s :=
  Classical.choice (chapter04_divisorOfRationalSection_exists L s)

noncomputable def chapter04DivisorOfRationalSection {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [Chapter04RationalFunctionLocalValueAPI X]
    (L : Chapter04LineBundle X) (s : Chapter04RationalSection L) :
    Chapter04CartierDivisor X :=
  (chapter04DivisorOfRationalSectionData L s).divisor

theorem chapter04_divisorOfRationalSection_bundle_iso {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [Chapter04RationalFunctionLocalValueAPI X]
    (L : Chapter04LineBundle X) (s : Chapter04RationalSection L) :
    chapter04LineBundleIsomorphic
      (chapter04OofD (chapter04DivisorOfRationalSection L s)) L := by
  exact ⟨Classical.choice (chapter04DivisorOfRationalSectionData L s).bundle_iso⟩

theorem chapter04_divisorOfRationalSection_canonical_maps_to_section {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [Chapter04RationalFunctionLocalValueAPI X]
    (L : Chapter04LineBundle X) (s : Chapter04RationalSection L) :
    ∃ e : (chapter04OofD (chapter04DivisorOfRationalSection L s)).sheaf ≅ L.sheaf,
      letI := chapter04GenericFiberModule L
      (TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map e.hom.mapPresheaf
          ((chapter04OofDData (chapter04DivisorOfRationalSection L s)).lineBundle.sheaf.presheaf.germ
            ⊤ (genericPoint X) (by trivial)
              (chapter04DivisorOfRationalSectionData L s).canonical_section) = s.value := by
  exact (chapter04DivisorOfRationalSectionData L s).canonical_section_maps_to_s

/-! ### Reduced schemes with several generic points -/

def chapter04IsBasisAtGenericPoint {X : Scheme.{u}}
    [IsReduced X] (L : Chapter04LineBundle X)
    (C : irreducibleComponents X)
    (v : ↑(L.sheaf.presheaf.stalk C.property.1.genericPoint)) : Prop :=
  letI : Module (X.presheaf.stalk C.property.1.genericPoint)
      (L.sheaf.presheaf.stalk C.property.1.genericPoint) := by
    change Module (X.presheaf.stalk C.property.1.genericPoint)
      (↑(TopCat.Presheaf.stalk L.sheaf.val.presheaf C.property.1.genericPoint))
    exact
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) L.sheaf.val C.property.1.genericPoint
  v ≠ 0 ∧ ∀ w, ∃ a : X.presheaf.stalk C.property.1.genericPoint,
    a • v = w

structure Chapter04ComponentwiseRationalSection {X : Scheme.{u}}
    [IsReduced X] (L : Chapter04LineBundle X) where
  commonOpen : X.Opens
  commonOpen_dense : Dense (commonOpen : Set X)
  commonOpen_contains_genericPoint :
    ∀ C : irreducibleComponents X,
      C.property.1.genericPoint ∈ commonOpen
  commonSection :
    ↑(L.sheaf.val.presheaf.obj (Opposite.op commonOpen))
  isBasisAtGenericPoint : ∀ C : irreducibleComponents X,
    chapter04IsBasisAtGenericPoint L C
      (L.sheaf.presheaf.germ commonOpen C.property.1.genericPoint
        (commonOpen_contains_genericPoint C) commonSection)

def Chapter04ComponentwiseRationalSection.value {X : Scheme.{u}}
    [IsReduced X] {L : Chapter04LineBundle X}
    (s : Chapter04ComponentwiseRationalSection L)
    (C : irreducibleComponents X) :
    ↑(L.sheaf.presheaf.stalk C.property.1.genericPoint) :=
  L.sheaf.presheaf.germ s.commonOpen C.property.1.genericPoint
    (s.commonOpen_contains_genericPoint C) s.commonSection

def chapter04IsBasisAtEveryGenericPoint {X : Scheme.{u}}
    [IsReduced X] (L : Chapter04LineBundle X)
    (s : Chapter04ComponentwiseRationalSection L) : Prop :=
  ∀ C : irreducibleComponents X, chapter04IsBasisAtGenericPoint L C (s.value C)

/-!
The noetherian existence statement is deliberately separated from the
integral definition: finitely many generic points permit clearing a common
denominator, whereas an arbitrary infinitely-component scheme need not admit
a single rational section that is a basis at every component.
-/
theorem chapter04_noetherian_lineBundle_has_componentwise_rationalSection
    {X : Scheme.{u}} [IsReduced X] [IsNoetherian X]
    (L : Chapter04LineBundle X) :
    Nonempty (Chapter04ComponentwiseRationalSection L) := by
  sorry

def chapter04HasFinitelyManyGenericPoints (X : Scheme.{u}) : Prop :=
  (irreducibleComponents X).Finite

theorem chapter04_noetherian_has_finitely_many_generic_points
    (X : Scheme.{u}) [IsNoetherian X] :
    chapter04HasFinitelyManyGenericPoints X := by
  exact NoetherianSpace.finite_irreducibleComponents

/-! ### Regular sections and their vanishing -/

noncomputable def chapter04GlobalSectionAsSection {X : Scheme.{u}}
    (L : Chapter04LineBundle X) (s : Chapter04GlobalSection L) :
    L.sheaf.val.sections :=
  PresheafOfModules.sectionsMk
    (fun U =>
      L.sheaf.val.map
        (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op s)
    (by sorry)

noncomputable def chapter04SectionToHom {X : Scheme.{u}}
    (L : Chapter04LineBundle X) (s : Chapter04GlobalSection L) :
    (chapter04TrivialLineBundle X).sheaf ⟶ L.sheaf :=
  (SheafOfModules.unitHomEquiv L.sheaf).symm
    (chapter04GlobalSectionAsSection L s)

noncomputable def chapter04RestrictScalarsId {X : Scheme.{u}}
    (F : X.Modules) :
  PresheafOfModules.restrictScalarsObj F.val (𝟙 X.ringCatSheaf.obj) ⟶ F.val where
  app U :=
    ModuleCat.restrictScalarsId'App
      (NatTrans.app (𝟙 (X.ringCatSheaf.obj)) U).hom (by rfl) (F.val.obj U)
      |>.hom
  naturality := by sorry

noncomputable def chapter04SectionTensorLeft {X : Scheme.{u}}
    (L M : Chapter04LineBundle X) (s : Chapter04GlobalSection L) :
    M.sheaf ⟶ chapter04Tensor L.sheaf M.sheaf :=
  let α : X.ringCatSheaf.obj ⟶ X.ringCatSheaf.obj := 𝟙 _
  let F := chapter04Tensor L.sheaf M.sheaf
  let M' : SheafOfModules X.ringCatSheaf := M.sheaf
  let F' : SheafOfModules X.ringCatSheaf := F
  let P := PresheafOfModules.Monoidal.tensorObj L.sheaf.val M.sheaf.val
  let g : M'.val ⟶ F'.val :=
    (((PresheafOfModules.monoidalCategoryStruct (R := X.sheaf.obj)).leftUnitor
          (show PresheafOfModules (X.sheaf.obj ⋙ forget₂ _ _) from M'.val)).inv ≫
        PresheafOfModules.Monoidal.tensorHom
          (chapter04SectionToHom L s).val (𝟙 M'.val) ≫
        (PresheafOfModules.sheafificationAdjunction
          (R := X.ringCatSheaf) α).unit.app P) ≫
      chapter04RestrictScalarsId F'
  ((SheafOfModules.fullyFaithfulForget X.ringCatSheaf).homEquiv
    (X := M') (Y := F')).symm g

noncomputable def chapter04SectionMultiplication {X : Scheme.{u}}
    (L : Chapter04LineBundle X) (s : Chapter04GlobalSection L) :
    (chapter04DualLineBundle L).sheaf ⟶ (chapter04TrivialLineBundle X).sheaf :=
  chapter04SectionTensorLeft L (chapter04DualLineBundle L) s ≫
    (Classical.choice (chapter04_dualLineBundle_exists L)).evaluation.hom

def chapter04MorphismIsInjective {X : Scheme.{u}}
    {M N : X.Modules} (φ : M ⟶ N) : Prop :=
  ∀ (P : X.Modules) (g h : P ⟶ M), g ≫ φ = h ≫ φ → g = h

def chapter04SectionIsRegular {X : Scheme.{u}}
    (L : Chapter04LineBundle X) (s : Chapter04GlobalSection L) : Prop :=
  chapter04MorphismIsInjective (chapter04SectionMultiplication L s)

def chapter04SectionIsRegularAtPoint {X : Scheme.{u}}
    (L : Chapter04LineBundle X) (s : Chapter04GlobalSection L) (x : X) : Prop :=
  Function.Injective
    ((TopCat.Presheaf.stalkFunctor Ab x).map
      (chapter04SectionMultiplication L s).mapPresheaf)

def chapter04IsAssociatedPoint {X : Scheme.{u}} (x : X) : Prop :=
  ∃ U : X.affineOpens, ∃ hx : x ∈ U.1,
    IsAssociatedPrime
      (U.2.primeIdealOf ⟨x, hx⟩).asIdeal
      Γ(X, U)

class Chapter04AssociatedPointAPI (X : Scheme.{u}) where
  isAssociated : X → Prop
  isAssociated_iff : ∀ x, isAssociated x ↔ chapter04IsAssociatedPoint x

instance (X : Scheme.{u}) : Chapter04AssociatedPointAPI X where
  isAssociated := chapter04IsAssociatedPoint
  isAssociated_iff := fun _ => Iff.rfl

def chapter04SectionIsRegularAtAssociatedPoints {X : Scheme.{u}}
    [Chapter04AssociatedPointAPI X]
    (L : Chapter04LineBundle X) (s : Chapter04GlobalSection L) : Prop :=
  ∀ x : X, Chapter04AssociatedPointAPI.isAssociated x →
    chapter04SectionIsRegularAtPoint L s x

theorem chapter04_section_injective_iff_regular_at_associated_points
    {X : Scheme.{u}} [IsNoetherian X] [Chapter04AssociatedPointAPI X]
    (L : Chapter04LineBundle X) (s : Chapter04GlobalSection L) :
    chapter04SectionIsRegular L s ↔
      chapter04SectionIsRegularAtAssociatedPoints L s := by
  sorry

theorem chapter04_integral_nonzero_section_is_regular
    {X : Scheme.{u}} [IsIntegral X]
    (L : Chapter04LineBundle X) {s : Chapter04GlobalSection L}
    (hs : s ≠ 0) : chapter04SectionIsRegular L s := by
  sorry

theorem chapter04_effectiveCartier_canonicalSection_is_regular {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) :
    chapter04SectionIsRegular (chapter04OofD D.cartier)
      (chapter04CanonicalSection D) := by
  sorry

def chapter04SectionVanishesIdenticallyOnComponent {X : Scheme.{u}}
    (L : Chapter04LineBundle X) (s : Chapter04GlobalSection L)
    (C : irreducibleComponents X) : Prop :=
  ∀ x : C.1,
    L.sheaf.presheaf.germ ⊤ x.1 (by trivial) s = 0

theorem chapter04_section_vanishing_on_a_component_is_not_regular
    {X : Scheme.{u}} [IsReduced X] [IsNoetherian X]
    [Chapter04AssociatedPointAPI X]
    (L : Chapter04LineBundle X) (s : Chapter04GlobalSection L)
    (C : irreducibleComponents X)
    (hzero : chapter04SectionVanishesIdenticallyOnComponent L s C) :
    ¬ chapter04SectionIsRegular L s := by
  sorry

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04
