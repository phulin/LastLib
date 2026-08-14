import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter09.Section02KeepingAPrescribedGoodOpen

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter09

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
open scoped AlgebraicGeometry

universe u v

/-! ## 9.3. Dominating finitely many models -/

theorem chapter09_regular_domination_of_finite_models
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (F : Chapter09FiniteProjectiveModelFamily B C) :
    Nonempty (Chapter09RegularDomination F) := by
  sorry

theorem chapter09_theorem_9_2
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (F : Chapter09FiniteProjectiveModelFamily B C) :
    Nonempty (Chapter09RegularDomination F) :=
  chapter09_regular_domination_of_finite_models F

theorem chapter09_regularDomination_dominates
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    {F : Chapter09FiniteProjectiveModelFamily B C}
    (D : Chapter09RegularDomination F) (i : F.index) :
    (D.map i).map ≫ (F.model i).structureMap = D.model.structureMap :=
  (D.map i).over

theorem chapter09_regularDomination_map_is_proper
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    {F : Chapter09FiniteProjectiveModelFamily B C}
    (D : Chapter09RegularDomination F) (i : F.index) :
    IsProper (D.map i).map :=
  D.proper i

theorem chapter09_regularDomination_map_is_projective
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    {F : Chapter09FiniteProjectiveModelFamily B C}
    (D : Chapter09RegularDomination F) (i : F.index) :
    Chapter01ProjectiveMorphism (D.map i).map :=
  D.projective i

theorem chapter09_regularDomination_genericFiber_is_identity
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    {F : Chapter09FiniteProjectiveModelFamily B C}
    (D : Chapter09RegularDomination F) (i : F.index) :
    (D.map i).genericFiberMap ≫ (F.model i).genericFiberIso.hom =
      D.model.genericFiberIso.hom :=
  (D.map i).genericFiber_is_identity

theorem chapter09_regularDomination_genericFiber_map_source
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    {F : Chapter09FiniteProjectiveModelFamily B C}
    (D : Chapter09RegularDomination F) (i : F.index) :
    (D.map i).genericFiberMap ≫
        pullback.fst (F.model i).structureMap B.genericPointMap =
      pullback.fst D.model.structureMap B.genericPointMap ≫ (D.map i).map :=
  (D.map i).genericFiberMap_source

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter09
