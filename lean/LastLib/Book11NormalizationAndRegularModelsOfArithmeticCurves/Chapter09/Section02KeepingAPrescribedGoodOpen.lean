import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter09.Section01ExistenceOverExcellentDedekindBases

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter09

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08
open scoped AlgebraicGeometry

universe u v

/-! ## 9.2. Keeping a prescribed good open -/

structure Chapter09ClosureRestrictionIdentification
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K)
    (C : Chapter09SmoothProjectiveCurve K)
    (U : S.Opens)
    (D : Chapter01ProjectiveClosureData B.toChapter01DedekindBase C.structureMap)
    (M : Chapter09RegularProjectiveOpenModel B C U) where
  iso : (D.closureMap ⁻¹ᵁ U).toScheme ≅ M.carrier
  «over» : iso.hom ≫ M.structureMap = D.closureMap ∣_ U

theorem chapter09_closureRestrictionIdentification_over
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    {U : S.Opens}
    {D : Chapter01ProjectiveClosureData B.toChapter01DedekindBase C.structureMap}
    {M : Chapter09RegularProjectiveOpenModel B C U}
    (I : Chapter09ClosureRestrictionIdentification B C U D M) :
    I.iso.hom ≫ M.structureMap = D.closureMap ∣_ U :=
  I.over

theorem chapter09_compatible_projective_closure_exists
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K)
    (C : Chapter09SmoothProjectiveCurve K)
    (U : S.Opens)
    (M : Chapter09RegularProjectiveOpenModel B C U) :
    ∃ D : Chapter01ProjectiveClosureData B.toChapter01DedekindBase C.structureMap,
      Nonempty (Chapter09ClosureRestrictionIdentification B C U D M) := by
  sorry

theorem chapter09_regular_model_theorem_relative
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K)
    (C : Chapter09SmoothProjectiveCurve K)
    (U : S.Opens)
    (M : Chapter09RegularProjectiveOpenModel B C U) :
    ∃ X : Chapter09RegularProjectiveModel B C,
      Nonempty (Chapter09ModelRestrictionIdentification X U M) := by
  sorry

def Chapter09IsomorphismOverOpen
    {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) : Prop :=
  IsIso (f ∣_ U)

theorem chapter09_normalization_isIso_over_normal_open
    {Y X : Scheme.{u}} (ν : Y ⟶ X)
    (hν : Chapter03NormalizationMap ν)
    (hbirational : Chapter07Birational ν)
    (U : X.Opens)
    (hU : Chapter01NormalScheme U.toScheme) :
    Chapter09IsomorphismOverOpen ν U := by
  sorry

theorem chapter09_resolution_isIso_over_good_open
    {X : Scheme.{u}} {U : X.Opens}
    (R : Chapter08ResolutionData X U) :
    Chapter09IsomorphismOverOpen R.map U :=
  R.isIso_over_U

theorem chapter09_nonempty_affine_open_has_finite_complement
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K)
    (U : S.Opens) (hU : IsAffineOpen U) (hU_nonempty : U ≠ ⊥) :
    Set.Finite ((U : Set S)ᶜ) := by
  sorry

def Chapter09ExceptionalLocusVerticalOver
    {Y X S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (U : S.Opens) : Prop :=
  chapter07ExceptionalLocus g ⊆ f ⁻¹' ((U : Set S)ᶜ)

theorem chapter09_exceptional_locus_is_vertical_over_preserved_open
    {Y X S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X)
    (U : S.Opens)
    (hiso : IsIso (g ∣_ (f ⁻¹ᵁ U))) :
    Chapter09ExceptionalLocusVerticalOver f g U := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter09
