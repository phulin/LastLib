import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open scoped AlgebraicGeometry

universe u v

/-! ### 1.2 The hierarchy of hypotheses -/

theorem chapter01_smooth_iff_lfp_flat_geometricallyRegularFibers
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Chapter01SmoothMorphism f ↔
      LocallyOfFinitePresentation f ∧ Flat f ∧
        Chapter01GeometricallyRegularFibers f := by
  sorry

theorem chapter01_smooth_iff_smoothMorphismData
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Chapter01SmoothMorphism f ↔ Nonempty (Chapter01SmoothMorphismData f) := by
  sorry

theorem chapter01_smooth_over_regular_base_is_regular
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter01RegularScheme S) (hf : Chapter01SmoothMorphism f) :
    Chapter01RegularScheme X := by
  sorry

theorem chapter01_regular_scheme_is_normal
    (X : Scheme.{u}) (hX : Chapter01RegularScheme X) :
    Chapter01NormalScheme X := by
  sorry

theorem chapter01_regular_local_ring_iff_cotangentSpace
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Chapter01RegularLocalRing R ↔
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) =
        ringKrullDim R := by
  sorry

theorem chapter01_excellent_is_nagata
    (R : Type u) [CommRing R] (hR : Chapter01ExcellentRing R) :
    Chapter01Nagata R := by
  sorry

theorem chapter01_proper_iff_separated_finiteType_universallyClosed
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Chapter01ProperMorphism f ↔
      IsSeparated f ∧ Chapter01FiniteType f ∧ UniversallyClosed f := by
  sorry

theorem chapter01_projective_iff_projective_witness
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Chapter01ProjectiveMorphism f ↔ Nonempty (Chapter04ProjectiveWitness f) := by
  rfl

theorem chapter01_nagata_gives_finite_normalization
    (A L : Type u) [CommRing A] [IsDomain A] [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L]
    (hA : Chapter01Nagata A) :
    Chapter01NormalizationFinite A L := by
  sorry

theorem chapter01_projective_is_proper
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : Chapter01ProjectiveMorphism f) :
    Chapter01ProperMorphism f := by
  sorry

/- These structures make the source's warning about non-reversible implications explicit without
turning a counterexample into an opaque proposition. -/
structure Chapter01RegularBaseNonSmoothExample where
  source : Scheme.{u}
  target : Scheme.{u}
  map : source ⟶ target
  sourceRegular : Chapter01RegularScheme source
  targetRegular : Chapter01RegularScheme target
  notSmooth : ¬ Chapter01SmoothMorphism map

structure Chapter01NormalNonRegularRingExample where
  carrier : Type u
  commRing : CommRing carrier
  normal : @Chapter01NormalRing carrier commRing
  notRegular : ¬ @Chapter01RegularRing carrier commRing

structure Chapter01NagataNonExcellentRingExample where
  carrier : Type u
  commRing : CommRing carrier
  nagata : @Chapter01Nagata carrier commRing
  notExcellent : ¬ @Chapter01ExcellentRing carrier commRing

structure Chapter01ProperNonProjectiveExample where
  source : Scheme.{u}
  target : Scheme.{u}
  map : source ⟶ target
  proper : Chapter01ProperMorphism map
  notProjective : ¬ Chapter01ProjectiveMorphism map

theorem chapter01_smooth_over_regular_base_has_no_converse :
    Nonempty Chapter01RegularBaseNonSmoothExample := by
  sorry

theorem chapter01_regular_has_no_normality_converse :
    Nonempty Chapter01NormalNonRegularRingExample := by
  sorry

theorem chapter01_nagata_has_no_excellence_converse :
    Nonempty Chapter01NagataNonExcellentRingExample := by
  sorry

theorem chapter01_proper_has_no_projectivity_converse :
    Nonempty Chapter01ProperNonProjectiveExample := by
  sorry

end
end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
