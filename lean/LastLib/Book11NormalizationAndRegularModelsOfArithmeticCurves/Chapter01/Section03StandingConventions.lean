import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u v

/-! ### 1.3 Standing conventions -/

/- A curve over a field keeps the structure map and the three defining properties together. -/
structure Chapter01CurveOverField (k : Type u) [Field k] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ Spec (CommRingCat.of k)
  separated : IsSeparated structureMap
  finiteType : Chapter01FiniteType structureMap
  pureDimensionOne : Chapter01PureDimensionOne carrier

namespace Chapter01CurveOverField

variable {k : Type u} [Field k]

instance (C : Chapter01CurveOverField k) : IsSeparated C.structureMap := C.separated

instance (C : Chapter01CurveOverField k) : LocallyOfFiniteType C.structureMap :=
  C.finiteType.1

instance (C : Chapter01CurveOverField k) : QuasiCompact C.structureMap :=
  C.finiteType.2

theorem finite_type (C : Chapter01CurveOverField k) :
    Chapter01FiniteType C.structureMap :=
  C.finiteType

theorem pure_dimension_one (C : Chapter01CurveOverField k) :
    Chapter01PureDimensionOne C.carrier :=
  C.pureDimensionOne

end Chapter01CurveOverField

/- Geometric connectedness is required here because later function-field notation chooses one
generic curve rather than a product over several connected components. -/
structure Chapter01SmoothProperCurveOverField (k : Type u) [Field k]
    extends Chapter01CurveOverField k where
  proper : IsProper structureMap
  smooth : Smooth structureMap
  geometricallyConnected : GeometricallyConnected structureMap

namespace Chapter01SmoothProperCurveOverField

variable {k : Type u} [Field k]

instance (C : Chapter01SmoothProperCurveOverField k) : IsSeparated C.structureMap :=
  C.toChapter01CurveOverField.separated

instance (C : Chapter01SmoothProperCurveOverField k) : LocallyOfFiniteType C.structureMap :=
  C.toChapter01CurveOverField.finiteType.1

instance (C : Chapter01SmoothProperCurveOverField k) : QuasiCompact C.structureMap :=
  C.toChapter01CurveOverField.finiteType.2

instance (C : Chapter01SmoothProperCurveOverField k) : IsProper C.structureMap := C.proper

instance (C : Chapter01SmoothProperCurveOverField k) : Smooth C.structureMap := C.smooth

instance (C : Chapter01SmoothProperCurveOverField k) :
    GeometricallyConnected C.structureMap := C.geometricallyConnected

theorem geometrically_connected (C : Chapter01SmoothProperCurveOverField k) :
    GeometricallyConnected C.structureMap :=
  C.geometricallyConnected

end Chapter01SmoothProperCurveOverField

abbrev Chapter01ModelGenericFiber {S C : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter01IntegralBase S K} {c : C ⟶ Spec (CommRingCat.of K)}
    (M : Chapter01Model B c) : Scheme.{u} :=
  chapter01GenericFiber M.structureMap B.genericPointMap

theorem chapter01_model_flat
    {S C : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter01IntegralBase S K} {c : C ⟶ Spec (CommRingCat.of K)}
    (M : Chapter01Model B c) : Flat M.structureMap :=
  M.flat

def chapter01_model_generic_fiber_identification
    {S C : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter01IntegralBase S K} {c : C ⟶ Spec (CommRingCat.of K)}
    (M : Chapter01Model B c) :
    Chapter01ModelGenericFiber M ≅ C :=
  M.genericFiberIso

theorem chapter01_model_generic_fiber_identification_over
    {S C : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter01IntegralBase S K} {c : C ⟶ Spec (CommRingCat.of K)}
    (M : Chapter01Model B c) :
    M.genericFiberIso.hom ≫ c = pullback.snd M.structureMap B.genericPointMap :=
  M.genericFiberIso_over

/- LOCAL_DEPENDENCY_GUESS: a candidate with the same generic fiber but no flatness hypothesis models the vertical
embedded-component warning in the source.  The nonflatness field records the required defect; its
concrete associated-prime API is deferred to the local-algebra chapters. -/
structure Chapter01NonflatGenericFiberCandidate {S C : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter01IntegralBase S K) (c : C ⟶ Spec (CommRingCat.of K)) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S
  finiteType : Chapter01FiniteType structureMap
  genericFiberIso : chapter01GenericFiber structureMap B.genericPointMap ≅ C
  genericFiberIso_over :
    genericFiberIso.hom ≫ c = pullback.snd structureMap B.genericPointMap
  notFlat : ¬ Flat structureMap

def Chapter01FlatnessIsPartOfModelDefinition : Prop :=
  ∀ {S C : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter01IntegralBase S K) (c : C ⟶ Spec (CommRingCat.of K))
    (M : Chapter01Model B c), Flat M.structureMap

theorem chapter01_flatness_is_part_of_model_definition :
    Chapter01FlatnessIsPartOfModelDefinition := by
  intro S C K _ B c M
  exact M.flat

end
end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
