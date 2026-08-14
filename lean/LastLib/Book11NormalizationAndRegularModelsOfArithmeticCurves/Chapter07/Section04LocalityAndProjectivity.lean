import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Section01TheUniversalRemedyForAnIdeal

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open scoped AlgebraicGeometry

universe u v

/-! ## 7.4. Locality and projectivity -/

/-! ### Locality on the target -/

structure Chapter07BlowupLocalityWitness
  {X : Scheme.{u}} (I : Chapter07CoherentIdeal X)
    (B : Chapter07Blowup I) (U : X.Opens) where
  restricted : Chapter07Blowup (I.comap U.ι)
  iso : restricted.carrier ≅ (B.projection ⁻¹ᵁ U).toScheme
  over : iso.hom ≫ (B.projection ∣_ U) = restricted.projection

theorem chapter07_blowup_is_local_on_target
    {X : Scheme.{u}} (I : Chapter07CoherentIdeal X)
    (B : Chapter07Blowup I) (U : X.Opens) :
    Nonempty (Chapter07BlowupLocalityWitness I B U) := by
  sorry

theorem chapter07_blowup_is_projective
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    (B : Chapter07Blowup I) :
    Chapter07IsProjectiveMorphism B.projection :=
  B.projective

/-! ### Base change and strict transforms -/

def chapter07BlowupBaseChange
    {X Y : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    (B : Chapter07Blowup I) (f : Y ⟶ X) : Scheme :=
  pullback B.projection f

def chapter07BlowupBaseChangeMap
    {X Y : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    (B : Chapter07Blowup I) (f : Y ⟶ X) :
    chapter07BlowupBaseChange B f ⟶ Y :=
  pullback.snd B.projection f

structure Chapter07BlowupBaseChangeWitness
    {X Y : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    (B : Chapter07Blowup I) (f : Y ⟶ X) where
  pulledBack : Chapter07Blowup (I.comap f)
  iso : pulledBack.carrier ≅ chapter07BlowupBaseChange B f
  over : iso.hom ≫ chapter07BlowupBaseChangeMap B f = pulledBack.projection

theorem chapter07_blowup_commutes_with_flat_base_change
    {X Y : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    (B : Chapter07Blowup I) (f : Y ⟶ X) (_hf : Flat f) :
    Nonempty (Chapter07BlowupBaseChangeWitness B f) := by
  sorry

/- Strict transform data explicitly records that whole exceptional components have been removed;
this is the part lost by simply taking a scheme-theoretic pullback. -/
structure Chapter07StrictTransformData
    {Z Y X : Scheme.{u}} (z : Z ⟶ X) (f : Y ⟶ X) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ Y
  inclusion_closed : IsClosedImmersion inclusion
  toSubscheme : carrier ⟶ Z
  compatibility : inclusion ≫ f = toSubscheme ≫ z
  flatBaseChange : Flat z
  removedExceptionalComponents :
    ∀ E : Chapter07ExceptionalDivisor f,
      ¬ E.divisor.support ⊆ Set.range inclusion

theorem chapter07_strict_transform_removes_exceptional_components
    {Z Y X : Scheme.{u}} {z : Z ⟶ X} {f : Y ⟶ X}
    (T : Chapter07StrictTransformData z f) :
    ∀ E : Chapter07ExceptionalDivisor f,
      ¬ E.divisor.support ⊆ Set.range T.inclusion :=
  T.removedExceptionalComponents

/-! ### Arithmetic surfaces and the generic curve -/

def Chapter07VerticalCenter
    {X S : Scheme.{u}} (f : X ⟶ S) (I : Chapter07CoherentIdeal X)
    (G : Chapter07GenericOpen S) : Prop :=
  Chapter07CenterDisjointFromGenericOpen f I G

structure Chapter07GenericFiberAgreement
    {Y X S : Scheme.{u}} (g : Y ⟶ X) (f : X ⟶ S) (η : S) where
  iso : (g ≫ f).fiber η ≅ f.fiber η
  iso_eq : iso.hom = chapter07GenericFiberMap g f η

theorem chapter07_blowup_isIso_on_generic_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) (I : Chapter07CoherentIdeal X)
    (η : S) (hη : Chapter07CenterDisjointFromGenericFiber f I η)
    (B : Chapter07Blowup I) :
    Nonempty (Chapter07GenericFiberAgreement B.projection f η) := by
  sorry

theorem chapter07_arithmetic_surface_center_is_vertical
    (M : Chapter07ArithmeticSurface) (I : Chapter07CoherentIdeal M.model)
    (hI : Chapter07CenterDisjointFromGenericOpen M.structureMap I M.generic) :
    Chapter07VerticalCenter M.structureMap I M.generic :=
  hI

theorem chapter07_arithmetic_surface_blowup_preserves_generic_curve
    (M : Chapter07ArithmeticSurface) (I : Chapter07CoherentIdeal M.model)
    (η : M.base) (hη : Chapter07CenterDisjointFromGenericFiber M.structureMap I η)
    (B : Chapter07Blowup I) :
    Nonempty (Chapter07GenericFiberAgreement B.projection M.structureMap η) := by
  exact chapter07_blowup_isIso_on_generic_fiber M.structureMap I η hη B

/-! ### Finite composites -/

/- A finite chain remembers whether a step is a blowup or a finite normalization, and its
composition constructor gives the reusable closure interface for projectivity. -/
inductive Chapter07ProjectiveModification :
    {Y X : Scheme.{u}} → (Y ⟶ X) → Prop
  | blowup {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
      (B : Chapter07Blowup I)
      (hbirational : Chapter07Birational B.projection) :
      Chapter07ProjectiveModification B.projection
  | finiteNormalization {Y X : Scheme.{u}} (f : Y ⟶ X)
      (hfinite : IsFinite f) (hintegral : IsIntegralHom f) :
      Chapter07Birational f →
      Chapter07ProjectiveModification f
  | comp {Z Y X : Scheme.{u}} {g : Z ⟶ Y} {f : Y ⟶ X}
      (hg : Chapter07ProjectiveModification g)
      (hf : Chapter07ProjectiveModification f) :
      Chapter07ProjectiveModification (g ≫ f)

theorem chapter07_finite_normalization_is_projective
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    (hfinite : IsFinite f) (hintegral : IsIntegralHom f) :
    Chapter07IsProjectiveMorphism f := by
  sorry

theorem chapter07_projectiveModification_is_projective
    {Y X : Scheme.{u}} {f : Y ⟶ X}
    (h : Chapter07ProjectiveModification f) :
    Chapter07IsProjectiveMorphism f := by
  sorry

abbrev Chapter07FiniteBlowupNormalizationChain
    {Y X : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  Chapter07ProjectiveModification f

theorem chapter07_finitely_many_blowups_and_normalizations_are_projective
    {Y X : Scheme.{u}} {f : Y ⟶ X}
    (h : Chapter07FiniteBlowupNormalizationChain f) :
    Chapter07IsProjectiveMorphism f :=
  chapter07_projectiveModification_is_projective h

theorem chapter07_resolving_projective_model_stays_projective
    (M : Chapter07ArithmeticSurface) {Y : Scheme.{u}}
    (g : Y ⟶ M.model) (hmodel : Chapter07IsProjectiveMorphism M.structureMap)
    (h : Chapter07FiniteBlowupNormalizationChain g) :
    Chapter07IsProjectiveMorphism (g ≫ M.structureMap) := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
