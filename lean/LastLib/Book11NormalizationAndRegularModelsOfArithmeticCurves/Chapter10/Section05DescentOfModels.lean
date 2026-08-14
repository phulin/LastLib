import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter10.Section04RamificationAndVerticalMultiplicities

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
open LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10
open LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ## 10.5 Descent of models -/

abbrev Chapter10FpqcDescentCover {S T : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Scheme.IsFpqcMorphism p

abbrev Chapter10FiniteFaithfullyFlatCover {S T : Scheme.{u}} (p : T ⟶ S) : Prop :=
  IsFinite p ∧ Scheme.IsFaithfullyFlat p

theorem chapter10_finiteFaithfullyFlat_to_fpqc
    {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FiniteFaithfullyFlatCover p) : Chapter10FpqcDescentCover p := by
  let _ : IsFinite p := hp.1
  exact ⟨hp.2.1, hp.2.2, by infer_instance⟩

abbrev Chapter10SchemeDescentDatum {S T : Scheme.{u}} (p : T ⟶ S) : Type _ :=
  SchemeDescent.Data
    (ι := PUnit.{u + 1}) (S := S) (X := fun _ : PUnit.{u + 1} => T)
    (fun _ : PUnit.{u + 1} => p)

structure Chapter10QuasiProjectiveSchemeDescentData
    {S T : Scheme.{u}} (p : T ⟶ S) where
  datum : Chapter10SchemeDescentDatum p
  quasiProjective : IsQuasiProjectiveMorphism (datum.obj PUnit.unit).hom

theorem chapter10_quasi_projective_scheme_descent_is_effective
    {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FpqcDescentCover p)
    (D : Chapter10QuasiProjectiveSchemeDescentData p) :
    Nonempty (SchemeDescent.Effective (fun _ : PUnit.{u + 1} => p) D.datum) := by
  exact (SchemeDescent.singleton_effective_of_fpqc p hp) D.datum

theorem chapter10_finite_faithfully_flat_scheme_descent_is_effective
    {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FiniteFaithfullyFlatCover p)
    (D : Chapter10SchemeDescentDatum p) :
    Nonempty (SchemeDescent.Effective (fun _ : PUnit.{u + 1} => p) D) := by
  exact (SchemeDescent.singleton_effective_of_fpqc p
    (chapter10_finiteFaithfullyFlat_to_fpqc p hp)) D

noncomputable def chapter10_descent_datum_morphisms_are_unique
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter10FpqcDescentCover p) :
    (SchemeDescent.overPseudofunctor.toDescentData
      (fun _ : PUnit.{u + 1} => p)).FullyFaithful := by
  exact SchemeDescent.singleton_morphisms_descend_uniquely p hp

structure Chapter10PolarizedProjectiveDescentData
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) where
  downstairsLineBundle : LineBundle X
  upstairsLineBundle : LineBundle (baseChange f p)
  compatible : IsBaseChangeOf f p downstairsLineBundle upstairsLineBundle
  quasiCompact : QuasiCompact f
  quasiSeparated : QuasiSeparated f
  proper : IsProper f
  locallyFinitePresentation : LocallyOfFinitePresentation f
  baseQuasiCompact : QuasiCompact (𝟙 S)
  faithfullyFlat : IsFaithfullyFlat p
  coverQuasiCompact : QuasiCompact p
  upstairsAmple : IsAmple (baseChangeToBase f p) upstairsLineBundle

theorem chapter10_projectivity_descends_from_compatible_polarization
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (D : Chapter10PolarizedProjectiveDescentData f p) :
    IsAmple f D.downstairsLineBundle ∧ IsProjectiveMorphism f := by
  exact projectivity_descent_from_upstairs_polarized_data f p
    D.downstairsLineBundle D.upstairsLineBundle D.compatible
    D.quasiCompact D.quasiSeparated D.proper D.locallyFinitePresentation
    D.baseQuasiCompact D.faithfullyFlat D.coverQuasiCompact D.upstairsAmple

theorem chapter10_flatness_descends_from_finite_faithfully_flat_cover
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcDescentCover p)
    (hf : Flat (chapter10BaseChangeToBase f p)) :
    Flat f := by
  let hcover :
      LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Chapter10FpqcCover p :=
    { surjective := hp.2.1, flat := hp.1, quasiCompact := hp.2.2 }
  exact LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10_flat_descends
    f p hcover hf

theorem chapter10_finite_presentation_descends_from_finite_faithfully_flat_cover
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcDescentCover p)
    (hf : chapter10FinitePresentation (chapter10BaseChangeToBase f p)) :
    chapter10FinitePresentation f := by
  sorry

theorem chapter10_properness_descends_from_finite_faithfully_flat_cover
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcDescentCover p)
    (hf : chapter10FiniteType (chapter10BaseChangeToBase f p))
    (hsep : IsSeparated (chapter10BaseChangeToBase f p))
    (hclosed : UniversallyClosed (chapter10BaseChangeToBase f p)) :
    IsProper f := by
  let hcover :
      LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Chapter10FpqcCover p :=
    { surjective := hp.2.1, flat := hp.1, quasiCompact := hp.2.2 }
  exact (chapter10_properByDefinition_iff_isProper f).mp
    (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10_proper_descends
      f p hcover hf hsep hclosed)

theorem chapter10_smoothness_descends_from_finite_faithfully_flat_cover
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcDescentCover p)
    (hf : Smooth (chapter10BaseChangeToBase f p)) :
    Smooth f := by
  let hcover :
      LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Chapter10FpqcCover p :=
    { surjective := hp.2.1, flat := hp.1, quasiCompact := hp.2.2 }
  exact LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10_smooth_descends
    f p hcover hf

abbrev Chapter10GeometricallyRegularCover {S T : Scheme.{u}} (p : T ⟶ S) : Prop :=
  LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10GeometricallyRegularFibers p

def Chapter10GeometricallyNormalCover {S T : Scheme.{u}} (p : T ⟶ S) : Prop :=
  ∀ s : S, Chapter10GeometricallyNormal (p.fiberToSpecResidueField s)

theorem chapter10_regularity_descends_with_geometrically_regular_fibers
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcDescentCover p)
    (hgeom : Chapter10GeometricallyRegularCover p)
    (hup : Chapter10RegularScheme (chapter10BaseChange f p)) :
    Chapter10RegularScheme X := by
  sorry

theorem chapter10_regularity_descends_under_etale_covers
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcDescentCover p) (hetale : Etale p)
    (hup : Chapter10RegularScheme (chapter10BaseChange f p)) :
    Chapter10RegularScheme X := by
  sorry

theorem chapter10_normality_descends_with_geometrically_normal_fibers
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcDescentCover p)
    (hgeom : Chapter10GeometricallyNormalCover p)
    (hup : Chapter10NormalScheme (chapter10BaseChange f p)) :
    Chapter10NormalScheme X := by
  sorry

structure Chapter10RamifiedRegularDescentFailure where
  S : Scheme.{u}
  T : Scheme.{u}
  cover : T ⟶ S
  fpqc : Scheme.IsFpqcMorphism cover
  ramified : ¬ Etale cover
  datum : Chapter10SchemeDescentDatum cover
  effective : SchemeDescent.Effective (fun _ : PUnit.{u + 1} => cover) datum
  descendedSingular : ¬ Chapter10RegularScheme effective.descended.left
  upstairsRegular : Chapter10RegularScheme (datum.obj PUnit.unit).left

theorem chapter10_regular_model_upstairs_may_descend_to_a_singular_quotient :
    Nonempty Chapter10RamifiedRegularDescentFailure := by
  sorry

structure Chapter10TwoPartDescentCheck
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) where
  objectDatum : Chapter10SchemeDescentDatum p
  objectEffective : Nonempty
    (SchemeDescent.Effective (fun _ : PUnit.{u + 1} => p) objectDatum)
  polarization : ∃ (L : LineBundle X) (M : LineBundle (baseChange f p)),
    IsBaseChangeOf f p L M ∧
      IsAmple (baseChangeToBase f p) M
  property : ObjectProperty Scheme.{u}
  propertyVerified : property (Classical.choice objectEffective).descended.left

theorem chapter10_descent_is_object_polarization_and_property_check
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (D : Chapter10TwoPartDescentCheck f p) :
    Nonempty
        (SchemeDescent.Effective (fun _ : PUnit.{u + 1} => p) D.objectDatum) ∧
      (∃ (L : LineBundle X) (M : LineBundle (baseChange f p)),
        IsBaseChangeOf f p L M ∧
          IsAmple (baseChangeToBase f p) M) ∧
      D.property (Classical.choice D.objectEffective).descended.left := by
  exact ⟨D.objectEffective, D.polarization, D.propertyVerified⟩

end
end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter10
