import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u v

/-! ### 1.1 From a curve over a field to a surface -/

/- A projective closure records both the ambient projective embedding and the generic-fiber
identification.  The latter is part of the data rather than an inferred equality of schemes. -/
structure Chapter01ProjectiveClosureData {S C : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter01DedekindBase S K) (c : C ⟶ Spec (CommRingCat.of K)) where
  ambient : Scheme.{u}
  ambientMap : ambient ⟶ S
  ambientProjective : Chapter01ProjectiveMorphism ambientMap
  closure : Scheme.{u}
  closureMap : closure ⟶ S
  closureProjective : Chapter01ProjectiveMorphism closureMap
  embedding : closure ⟶ ambient
  embedding_closedImmersion : IsClosedImmersion embedding
  embedding_over : embedding ≫ ambientMap = closureMap
  genericFiberIso : chapter01GenericFiber closureMap B.genericPointMap ≅ C
  genericFiberIso_over :
    genericFiberIso.hom ≫ pullback.snd closureMap B.genericPointMap = c

/- LOCAL_DEPENDENCY_GUESS: the normalization stage is deliberately separated from the resolution stage.  The
`inFunctionField` field is a local interface for the function-field construction, which is not
yet exposed by the pinned scheme API in the exact form used by the source. -/
structure Chapter01NormalizationData (Y : Scheme.{u}) where
  baseIntegral : IsIntegral Y
  normalized : Scheme.{u}
  map : normalized ⟶ Y
  finite : IsFinite map
  normal : Chapter01NormalScheme normalized
  inFunctionField : Prop
  properBirational : Chapter01ProperBirational map

structure Chapter01ResolutionData (Y : Scheme.{u}) where
  regularModel : Scheme.{u}
  map : regularModel ⟶ Y
  regular : Chapter01RegularScheme regularModel
  properBirational : Chapter01ProperBirational map

/- The displayed route `C/K -> C̄/S <- C̄ⁿᵒʳ <- X` is represented by its three stages. -/
structure Chapter01IntegralModelRoute {S C : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter01DedekindBase S K) (c : C ⟶ Spec (CommRingCat.of K)) where
  closure : Chapter01ProjectiveClosureData B c
  normalization : Chapter01NormalizationData closure.closure
  resolution : Chapter01ResolutionData normalization.normalized

def Chapter01ResolutionExists (Y : Scheme.{u}) : Prop :=
  Nonempty (Chapter01ResolutionData Y)

/- LOCAL_DEPENDENCY_GUESS: the source's two-dimensional resolution hypothesis is kept as an explicit theorem interface;
the proof and its excellence hypotheses belong to the later resolution development. -/
theorem chapter01_resolution_exists_of_excellent_surface
    (Y : Scheme.{u}) (hY : Chapter01ExcellentScheme Y)
    (hDim : Chapter01PureDimensionTwo Y) :
    Chapter01ResolutionExists Y := by
  sorry

/- The affine equation in the source is made concrete as an actual polynomial quotient.  The
indices `0` and `1` are the two coordinates `x` and `y`. -/
def chapter01NodalSurfaceRelation (R : Type u) [CommRing R] (π : R) :
    Ideal (MvPolynomial (Fin 2) R) :=
  Ideal.span ({MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C π} :
    Set (MvPolynomial (Fin 2) R))

abbrev chapter01NodalSurfaceRing (R : Type u) [CommRing R] (π : R) :=
  (MvPolynomial (Fin 2) R) ⧸ chapter01NodalSurfaceRelation R π

abbrev chapter01NodalSpecialFiberRing (R : Type u) [CommRing R] (π : R) :=
  chapter01NodalSurfaceRing (R ⧸ Ideal.span ({π} : Set R)) 0

abbrev chapter01NodalSurfaceScheme (R : Type u) [CommRing R] (π : R) :=
  Spec (CommRingCat.of (chapter01NodalSurfaceRing R π))

abbrev chapter01NodalSpecialFiberScheme (R : Type u) [CommRing R] (π : R) :=
  Spec (CommRingCat.of (chapter01NodalSpecialFiberRing R π))

def Chapter01XYEqualsPiExample (R : Type u) [CommRing R] (π : R) : Prop :=
  Chapter01RegularScheme (chapter01NodalSurfaceScheme R π) ∧
    ¬ Chapter01RegularScheme (chapter01NodalSpecialFiberScheme R π)

theorem chapter01_xy_equals_pi_regular_total_singular_special
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : π ≠ 0)
    (hπ_uniformizer : Ideal.span ({π} : Set R) = maximalIdeal R) :
    Chapter01XYEqualsPiExample R π := by
  sorry

/- A smooth fiber is a statement about one base point; this predicate records the precise
non-implication warned about in the source. -/
def Chapter01SmoothFiberDoesNotControlTotalRegularity
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) : Prop :=
  Smooth (f.fiberToSpecResidueField s) ∧ ¬ Chapter01RegularScheme X

theorem chapter01_smooth_fiber_does_not_imply_total_regularity :
    ∃ (X S : Scheme.{u}) (f : X ⟶ S) (s : S),
      Chapter01SmoothFiberDoesNotControlTotalRegularity f s := by
  sorry

end
end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
