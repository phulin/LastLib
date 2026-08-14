import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08.Section01TheResolutionTheoremInTheRequiredSetting

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry

universe u v

/-! ## 8.2. Preparing the singular locus -/

def Chapter08CodimensionAtLeastTwo {X : Scheme.{u}} (Z : Set X) : Prop :=
  ∀ x : X, x ∈ Z → 2 ≤ Order.coheight x

structure Chapter08SurfacePreparationData (X : Scheme.{u}) where
  normalization : Chapter08FiniteNormalization X
  regularOpen : normalization.carrier.Opens
  regularOpen_eq :
    (regularOpen : Set normalization.carrier) = chapter08RegularLocus normalization.carrier
  complement_closed : IsClosed ((regularOpen : Set normalization.carrier)ᶜ)
  complement_codimension_two :
    Chapter08CodimensionAtLeastTwo ((regularOpen : Set normalization.carrier)ᶜ)
  complement_finite_on_quasiCompact_open :
    ∀ V : normalization.carrier.Opens,
      IsQuasiCompact (V : Set normalization.carrier) →
        (((regularOpen : Set normalization.carrier)ᶜ) ∩
          (V : Set normalization.carrier)).Finite

def chapter08PreparedSingularLocus
    {X : Scheme.{u}} (P : Chapter08SurfacePreparationData X) : Set P.normalization.carrier :=
  (P.regularOpen : Set P.normalization.carrier)ᶜ

theorem chapter08_excellent_surface_has_finite_normalization
    (X : Scheme.{u}) (hX : Chapter08ExcellentSurfaceInput X) :
    Nonempty (Chapter08FiniteNormalization X) := by
  sorry

theorem chapter08_surface_preparation
    (X : Scheme.{u}) (hX : Chapter08ExcellentSurfaceInput X) :
    Nonempty (Chapter08SurfacePreparationData X) := by
  sorry

theorem chapter08_prepared_singular_locus_is_closed
    {X : Scheme.{u}} (P : Chapter08SurfacePreparationData X) :
    IsClosed (chapter08PreparedSingularLocus P) := by
  exact P.complement_closed

theorem chapter08_prepared_singular_locus_has_codimension_two
    {X : Scheme.{u}} (P : Chapter08SurfacePreparationData X) :
    Chapter08CodimensionAtLeastTwo (chapter08PreparedSingularLocus P) := by
  exact P.complement_codimension_two

theorem chapter08_prepared_singular_locus_is_finite_on_quasiCompact_open
    {X : Scheme.{u}} (P : Chapter08SurfacePreparationData X)
    (V : P.normalization.carrier.Opens)
    (hV : IsQuasiCompact (V : Set P.normalization.carrier)) :
    (chapter08PreparedSingularLocus P ∩ (V : Set P.normalization.carrier)).Finite := by
  exact P.complement_finite_on_quasiCompact_open V hV

/-! The local target singled out by the preparation argument. -/

structure Chapter08ExcellentNormalTwoDimensionalLocalDomain
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A] : Prop where
  excellent : Chapter03Excellent A
  normal : IsIntegrallyClosed A
  dimension_two : ringKrullDim A = 2

abbrev chapter08LocalSurfaceSpec
    (A : Type u) [CommRing A] : Scheme.{u} :=
  Spec (.of A)

def chapter08LocalSurfaceProblem
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A] : Prop :=
  Chapter08ExcellentNormalTwoDimensionalLocalDomain A

def chapter08MaximalPoint
    (A : Type u) [CommRing A] [IsLocalRing A]
    (hmax : (chapter08MaximalIdeal A).IsPrime) : chapter08LocalSurfaceSpec A :=
  ⟨chapter08MaximalIdeal A, hmax⟩

noncomputable def chapter08PuncturedSpectrum
    (A : Type u) [CommRing A] [IsLocalRing A]
    (hmax : (chapter08MaximalIdeal A).IsPrime) :
    (chapter08LocalSurfaceSpec A).Opens := by
  refine ⟨{x | x ≠ chapter08MaximalPoint A hmax}, ?_⟩
  sorry

def Chapter08ModificationSupportedAtClosedPoint
    {A Y : Type u} [CommRing A] [IsLocalRing A]
    (hmax : (chapter08MaximalIdeal A).IsPrime)
    (f : Y ⟶ chapter08LocalSurfaceSpec A) : Prop :=
  IsIso (f ∣_ chapter08PuncturedSpectrum A hmax)

theorem chapter08_supported_modification_glues_to_identity_off_closed_point
    {A Y : Type u} [CommRing A] [IsLocalRing A]
    (hmax : (chapter08MaximalIdeal A).IsPrime)
    (f : Y ⟶ chapter08LocalSurfaceSpec A)
    (h : Chapter08ModificationSupportedAtClosedPoint hmax f) :
    IsIso (f ∣_ chapter08PuncturedSpectrum A hmax) :=
  h

/-! Completion is exposed as a diagnostic interface, not as an extra hypothesis of the global
resolution theorem. -/

abbrev chapter08AdicCompletion
    (A : Type u) [CommRing A] [IsLocalRing A] :=
  AdicCompletion (chapter08MaximalIdeal A) A

noncomputable def chapter08CompletionMap
    (A : Type u) [CommRing A] [IsLocalRing A] :
    A →+* chapter08AdicCompletion A :=
  algebraMap A (chapter08AdicCompletion A)

def chapter08CompletionSchemeMap
    (A : Type u) [CommRing A] [IsLocalRing A] :
    Spec (.of (chapter08AdicCompletion A)) ⟶ Spec (.of A) :=
  Scheme.Spec.map (CommRingCat.ofHom (chapter08CompletionMap A))

def Chapter08CompletionMapIsRegular
    (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  Flat (chapter08CompletionSchemeMap A) ∧
    Chapter04GeometricallyRegularFibers (chapter08CompletionSchemeMap A)

structure Chapter08CompletionFacts
    (A : Type u) [CommRing A] [IsLocalRing A] where
  map_is_regular : Chapter08CompletionMapIsRegular A
  faithfully_flat : Module.FaithfullyFlat A (chapter08AdicCompletion A)
  regularity_iff :
    IsRegularLocalRing A ↔ IsRegularLocalRing (chapter08AdicCompletion A)

theorem chapter08_excellent_completion_facts
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (hA : Chapter03Excellent A) :
    Nonempty (Chapter08CompletionFacts A) := by
  sorry

theorem chapter08_completion_detects_regular_locality
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (hA : Chapter03Excellent A) :
    ∃ F : Chapter08CompletionFacts A,
      (IsRegularLocalRing A ↔ IsRegularLocalRing (chapter08AdicCompletion A)) := by
  rcases chapter08_excellent_completion_facts A hA with ⟨F⟩
  exact ⟨F, F.regularity_iff⟩

/- LOCAL_DEPENDENCY_GUESS: the pinned completion API does not expose the finite-neighborhood
   approximation comparison used in the chapter, so the comparison is retained as a named field
   rather than replacing it by an unconditional equality of ideals. -/
structure Chapter08CompletionIdealApproximation
    (A : Type u) [CommRing A] [IsLocalRing A] where
  completedIdeal : Ideal (chapter08AdicCompletion A)
  finiteNeighborhood : Prop
  approximatingIdeal : Ideal A
  approximation_compatibility : Prop

def chapter08CompletionQuotientRegularity
    (A : Type u) [CommRing A] [IsLocalRing A]
    (J : Ideal (chapter08AdicCompletion A)) : Prop :=
  Chapter04RegularScheme
    (Spec (.of (chapter08AdicCompletion A ⧸ J)))

def chapter08ApproximatingQuotientRegularity
    (A : Type u) [CommRing A] [IsLocalRing A]
    (J : Ideal A) : Prop :=
  Chapter04RegularScheme (Spec (.of (A ⧸ J)))

theorem chapter08_completion_approximation_descends_regularity
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (hA : Chapter03Excellent A)
    (D : Chapter08CompletionIdealApproximation A)
    (hD : D.finiteNeighborhood)
    (hregular : chapter08CompletionQuotientRegularity A D.completedIdeal) :
    chapter08ApproximatingQuotientRegularity A D.approximatingIdeal := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08
