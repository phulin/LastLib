import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter12.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry

universe u v

/-! ## 12.1. The exact reusable model theorem -/

structure Chapter12ArithmeticCurveModelPackage
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter12ExcellentDedekindBase S K)
    (C : Chapter01SmoothProperCurveOverField K)
    (U : S.Opens)
    (M : Chapter12SmoothProjectiveOpenModel B C U) where
  normalModel : Chapter12NormalFlatProjectiveModel B C
  normalExtension : Chapter12ModelExtension M (chapter12NormalModelToFlat normalModel)
  regularModel : Chapter12RegularFlatProjectiveModel B C
  regularExtension : Chapter12ModelExtension M (chapter12RegularModelToFlat regularModel)
  regularModification :
    Chapter12RegularModification M normalModel regularModel normalExtension regularExtension
  finiteCollectionDomination :
    ∀ F : Chapter12FiniteProjectiveModelSystem B C,
      Nonempty (Chapter12CommonRegularDomination F)
  finiteExtensionResolution :
    ∀ {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L],
      Chapter12FiniteSeparableExtension K L →
        ∃ (B' : Chapter12NormalizedDedekindBase B),
          Nonempty (Chapter12ResolvedBaseChange (chapter12NormalModelToFlat normalModel) B')
  semistable_centers_avoid_open :
    ∀ {V : S.Opens} (N : Chapter12SemistableOpenModel B C V),
      Nonempty (Chapter12SemistableResolutionOutsideOpen N)
  minimal_positive_genus :
    Chapter12PositiveGenus C →
      Nonempty (Chapter12MinimalContraction regularModel)

theorem chapter12_arithmeticCurve_model_package
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter12ExcellentDedekindBase S K)
    (C : Chapter01SmoothProperCurveOverField K)
    (U : S.Opens) (hU : U ≠ ⊥)
    (M : Chapter12SmoothProjectiveOpenModel B C U) :
    Nonempty (Chapter12ArithmeticCurveModelPackage B C U M) := by
  sorry

noncomputable def chapter12ArithmeticCurveModelPackage
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter12ExcellentDedekindBase S K)
    (C : Chapter01SmoothProperCurveOverField K)
    (U : S.Opens) (hU : U ≠ ⊥)
    (M : Chapter12SmoothProjectiveOpenModel B C U) :
    Chapter12ArithmeticCurveModelPackage B C U M :=
  Classical.choice (chapter12_arithmeticCurve_model_package B C U hU M)

theorem chapter12_package_has_normal_flat_projective_model
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    {U : S.Opens} {M : Chapter12SmoothProjectiveOpenModel B C U}
    (P : Chapter12ArithmeticCurveModelPackage B C U M) :
    Chapter12NormalFlatProjectiveModel B C :=
  P.normalModel

theorem chapter12_package_has_regular_flat_projective_model
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    {U : S.Opens} {M : Chapter12SmoothProjectiveOpenModel B C U}
    (P : Chapter12ArithmeticCurveModelPackage B C U M) :
    Chapter12RegularFlatProjectiveModel B C :=
  P.regularModel

theorem chapter12_package_regular_map_is_projective_birational
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    {U : S.Opens} {M : Chapter12SmoothProjectiveOpenModel B C U}
    (P : Chapter12ArithmeticCurveModelPackage B C U M) :
    Chapter07IsProjectiveMorphism P.regularModification.map ∧
      Chapter07Birational P.regularModification.map :=
  ⟨P.regularModification.projective, P.regularModification.birational⟩

theorem chapter12_package_is_identical_over_prescribed_open
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    {U : S.Opens} {M : Chapter12SmoothProjectiveOpenModel B C U}
    (P : Chapter12ArithmeticCurveModelPackage B C U M) :
    P.regularModification.map ∣_ U =
      P.regularExtension.openIso.inv ≫ P.normalExtension.openIso.hom :=
  P.regularModification.identical_over_U

theorem chapter12_package_finite_extension_normalization_then_resolution
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    {U : S.Opens} {M : Chapter12SmoothProjectiveOpenModel B C U}
    (P : Chapter12ArithmeticCurveModelPackage B C U M)
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
    (E : Chapter12FiniteSeparableExtension K L) :
    ∃ (B' : Chapter12NormalizedDedekindBase B),
      Nonempty (Chapter12ResolvedBaseChange
        (chapter12NormalModelToFlat P.normalModel) B') :=
  P.finiteExtensionResolution E

theorem chapter12_package_dominates_finite_projective_model_system
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    {U : S.Opens} {M : Chapter12SmoothProjectiveOpenModel B C U}
    (P : Chapter12ArithmeticCurveModelPackage B C U M)
    (F : Chapter12FiniteProjectiveModelSystem B C) :
    Nonempty (Chapter12CommonRegularDomination F) :=
  P.finiteCollectionDomination F

/- The source's adjective ledger is kept explicit: none of these fields is inferred merely from
   properness.  In particular the projective witness and the generic connectedness hypothesis are
   independent inputs. -/
structure Chapter12ArithmeticCurveHypothesisLedger
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter12ExcellentDedekindBase S K)
    (C : Chapter01SmoothProperCurveOverField K)
    {U : S.Opens}
    (M : Chapter12SmoothProjectiveOpenModel B C U) where
  excellence : Chapter01ExcellentScheme S
  dedekind : Chapter01DedekindScheme S
  generic_smooth : Smooth C.structureMap
  generic_proper : IsProper C.structureMap
  generic_geometrically_connected : GeometricallyConnected C.structureMap
  normalization_finite : Prop
  surface_resolution_terminates : Prop
  flatness_from_integrality_over_dedekind : Prop
  projectivity_from_closure_embedding : Prop
  properness_preserved : Prop

theorem chapter12_arithmeticCurve_hypothesis_ledger
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter12ExcellentDedekindBase S K)
    (C : Chapter01SmoothProperCurveOverField K)
    {U : S.Opens} (M : Chapter12SmoothProjectiveOpenModel B C U) :
    Nonempty (Chapter12ArithmeticCurveHypothesisLedger B C M) := by
  sorry

/- The following two non-implications are the precise forms of the warnings attached to the
   theorem: normality is not regularity, and regularity is not smoothness of every fiber. -/
theorem chapter12_normalization_alone_does_not_give_regularity :
    ∃ (X : Scheme.{u}),
      Chapter07NormalIntegralScheme X ∧ ¬ Chapter04RegularScheme X := by
  sorry

theorem chapter12_regular_model_need_not_have_smooth_bad_fibers :
    ∃ (X S : Scheme.{u}) (f : X ⟶ S),
      Chapter04RegularScheme X ∧ ∃ s : S, ¬ Smooth (f.fiberToSpecResidueField s) := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter12
