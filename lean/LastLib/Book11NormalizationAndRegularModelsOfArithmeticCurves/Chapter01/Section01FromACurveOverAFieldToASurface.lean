import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Dependencies
import Mathlib.RingTheory.DualNumber

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry DualNumber

universe u v

/-! ### 1.1 From a curve over a field to a surface -/

/- A projective closure records both the ambient projective embedding and the generic-fiber
identification.  The latter is part of the data rather than an inferred equality of schemes. -/
structure Chapter01ProjectiveClosureData {S C : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter01DedekindBase S K) (c : C ⟶ Spec (CommRingCat.of K)) where
  genericFiniteType : Chapter01FiniteType c
  genericProjective : Chapter01ProjectiveMorphism c
  genericSeparated : IsSeparated c
  genericSmooth : Chapter01SmoothMorphism c
  genericPureDimensionOne : Chapter01PureDimensionOne C
  genericGeometricallyConnected : GeometricallyConnected c
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
    genericFiberIso.hom ≫ c = pullback.snd closureMap B.genericPointMap

/- LOCAL_DEPENDENCY_GUESS: the normalization stage is deliberately separated from the resolution stage.
The finite normal proper-birational interface records the normalization without depending on a
separate function-field object. -/
structure Chapter01NormalizationData (Y : Scheme.{u}) where
  baseIntegral : IsIntegral Y
  normalized : Scheme.{u}
  map : normalized ⟶ Y
  finite : IsFinite map
  normal : Chapter01NormalScheme normalized
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
    (hDim : Chapter01PureDimensionTwo Y) (hIntegral : IsIntegral Y) :
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
    (hπ_uniformizer : Ideal.span ({π} : Set R) = IsLocalRing.maximalIdeal R) :
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
  let A₀ := ℚ[ε]
  let A := ULift.{u} A₀
  let e₀ : A ≃+* A₀ := ULift.ringEquiv
  have hA_local : IsLocalRing A := e₀.symm.isLocalRing
  let X : Scheme.{u} := Spec (CommRingCat.of A)
  let s : X := IsLocalRing.closedPoint (CommRingCat.of A)
  let f : X ⟶ X := 𝟙 X
  refine ⟨X, X, f, s, ?_⟩
  constructor
  · have hf_smooth : Smooth f := by
      simpa [f] using
        (HasRingHomProperty.containsIdentities (P := @Smooth)
          RingHom.Smooth.holdsForLocalizationAway.containsIdentities).id_mem X
    change Smooth (pullback.snd f (X.fromSpecResidueField s))
    have hf_instance : Smooth f := hf_smooth
    infer_instance
  · intro hX
    have hstalk : IsRegularLocalRing (X.presheaf.stalk s) := hX s
    have hstalk' : IsRegularLocalRing (X.presheaf.stalk s) := hstalk
    let e := (stalkClosedPointIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
    have hregA : IsRegularLocalRing A :=
      IsRegularLocalRing.of_ringEquiv e
    have hstalk_instance : IsRegularLocalRing (X.presheaf.stalk s) := hstalk'
    have hregA_instance : IsRegularLocalRing A := hregA
    have hreg₀ : IsRegularLocalRing A₀ :=
      IsRegularLocalRing.of_ringEquiv e₀
    have hdimLE : Ring.KrullDimLE 0 A₀ := by
      refine Ring.KrullDimLE.mk₀ ?_
      intro I hI
      have heps : (DualNumber.eps : A₀) ∈ I :=
        (nilpotent_iff_mem_prime.mp (DualNumber.isNilpotent_eps (R := ℚ))) I hI
      have hle : IsLocalRing.maximalIdeal A₀ ≤ I := by
        rw [DualNumber.maximalIdeal_eq_span_singleton_eps]
        exact Ideal.span_le.2 (by simpa using heps)
      rw [← (IsLocalRing.maximalIdeal.isMaximal A₀).eq_of_le hI.ne_top hle]
      exact IsLocalRing.maximalIdeal.isMaximal A₀
    have hdim : ringKrullDim A₀ = 0 :=
      (ringKrullDimZero_iff_ringKrullDim_eq_zero (R := A₀)).mp hdimLE
    have hspan := hreg₀.spanFinrank_maximalIdeal
    have heps_ne : (DualNumber.eps : A₀) ≠ 0 := by
      intro h
      have := congrArg TrivSqZeroExt.snd h
      simp at this
    rw [DualNumber.maximalIdeal_eq_span_singleton_eps,
      Submodule.spanFinrank_singleton heps_ne, hdim] at hspan
    norm_num at hspan

end
end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
