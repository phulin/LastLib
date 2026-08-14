import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Dependencies
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory

/-!
## 2.1 Projective bundles

The book uses the quotient convention
`P_S(E) = Proj_S(Sym E)`: points are rank-one quotients of `E`, and the universal line is
`𝒪(1)`.  Mathlib's affine `Proj` is used below whenever a graded algebra is available; the
relative scheme and universal quotient are the bundled interfaces from `Dependencies.lean`.
-/

/-- A projective space package on an arbitrary coordinate index type. -/
structure Chapter02ProjectiveSpaceData (S : Scheme.{u}) (I : Type u) where
  bundle : Chapter02ProjectiveBundleData S (chapter02FreeQuasiCoherentModule S I)
  coordinateSections : I → bundle.twistingLineBundle.carrier.sections
  /-- The free sheaf on the target identifies with the pullback of the free sheaf on `S`. -/
  coordinateComparison :
    SheafOfModules.free (R := bundle.scheme.ringCatSheaf) I ≅
      (Scheme.Modules.pullback bundle.projection).obj
        (chapter02FreeQuasiCoherentModule S I).carrier
  coordinateSections_spec :
    coordinateComparison.hom ≫ bundle.universalQuotient =
      (bundle.twistingLineBundle.carrier.freeHomEquiv).symm coordinateSections

/- LOCAL_DEPENDENCY_GUESS: the free relative Proj has its canonical coordinate sections. -/
theorem chapter02_projective_space_data_exists
    (S : Scheme.{u}) (I : Type u) :
    Nonempty (Chapter02ProjectiveSpaceData S I) := by
  obtain ⟨B⟩ :=
    chapter02_relative_projective_bundle_exists S
      (chapter02FreeQuasiCoherentModule S I)
  let C := chapter02FreePullbackComparisonData B.projection I
  refine ⟨{
    bundle := B
    coordinateSections :=
      B.twistingLineBundle.carrier.freeHomEquiv
        (C.comparison.hom ≫ B.universalQuotient)
    coordinateComparison := C.comparison
    coordinateSections_spec := ?_ }⟩
  rw [Equiv.symm_apply_apply]

noncomputable def chapter02ProjectiveSpaceData (S : Scheme.{u}) (I : Type u) :
    Chapter02ProjectiveSpaceData S I :=
  Classical.choice (chapter02_projective_space_data_exists S I)

abbrev chapter02ProjectiveSpaceOnIndex (S : Scheme.{u}) (I : Type u) : Scheme.{u} :=
  (chapter02ProjectiveSpaceData S I).bundle.scheme

abbrev chapter02ProjectiveSpaceOnIndexProjection
    (S : Scheme.{u}) (I : Type u) :
    chapter02ProjectiveSpaceOnIndex S I ⟶ S :=
  (chapter02ProjectiveSpaceData S I).bundle.projection

abbrev chapter02ProjectiveSpaceOnIndexTwistingLine
    (S : Scheme.{u}) (I : Type u) :
    Chapter02LineBundle (chapter02ProjectiveSpaceOnIndex S I) :=
  (chapter02ProjectiveSpaceData S I).bundle.twistingLineBundle

abbrev chapter02ProjectiveSpaceOnIndexCoordinates
    (S : Scheme.{u}) (I : Type u) :
    I → (chapter02ProjectiveSpaceOnIndexTwistingLine S I).carrier.sections :=
  (chapter02ProjectiveSpaceData S I).coordinateSections

/-- The universe-lifted finite index used by the free sheaf on `S`. -/
abbrev Chapter02ProjectiveSpaceIndex (r : ℕ) : Type u :=
  ULift.{u} (Fin (r + 1))

/-- The usual notation `P^r_S`, implemented with the lifted index type. -/
abbrev chapter02ProjectiveSpace (S : Scheme.{u}) (r : ℕ) : Scheme.{u} :=
  chapter02ProjectiveSpaceOnIndex S (Chapter02ProjectiveSpaceIndex r)

abbrev chapter02ProjectiveSpaceProjection (S : Scheme.{u}) (r : ℕ) :
    chapter02ProjectiveSpace S r ⟶ S :=
  chapter02ProjectiveSpaceOnIndexProjection S (Chapter02ProjectiveSpaceIndex r)

abbrev chapter02ProjectiveSpaceTwistingLine (S : Scheme.{u}) (r : ℕ) :
    Chapter02LineBundle (chapter02ProjectiveSpace S r) :=
  chapter02ProjectiveSpaceOnIndexTwistingLine S (Chapter02ProjectiveSpaceIndex r)

abbrev chapter02ProjectiveSpaceCoordinates (S : Scheme.{u}) (r : ℕ) :
    Fin (r + 1) → (chapter02ProjectiveSpaceTwistingLine S r).carrier.sections :=
  fun i =>
    chapter02ProjectiveSpaceOnIndexCoordinates S (Chapter02ProjectiveSpaceIndex r)
      (ULift.up i)

/-- The polynomial ring model used for ordinary projective space over an affine base. -/
abbrev chapter02PolynomialRing (R : Type u) [CommSemiring R] (r : ℕ) :=
  MvPolynomial (Fin (r + 1)) R

/-!
The pinned Mathlib API contains the standard homogeneous grading of a multivariate polynomial
ring.  Use it directly rather than choosing an arbitrary `GradedAlgebra`: the affine `Proj`
model below is meant to be the ordinary projective space, so its grading must be the total-degree
grading.
-/
theorem chapter02_polynomial_grading_exists
    (R : Type u) [CommRing R] (r : ℕ) :
    Nonempty (Chapter02GradedAlgebra R (chapter02PolynomialRing R r)) := by
  exact ⟨{
    component := fun d =>
      MvPolynomial.homogeneousSubmodule (σ := Fin (r + 1)) (R := R) d
    graded := MvPolynomial.gradedAlgebra
  }⟩

noncomputable def chapter02PolynomialGradedAlgebra
    (R : Type u) [CommRing R] (r : ℕ) :
    Chapter02GradedAlgebra R (chapter02PolynomialRing R r) :=
  {
    component := fun d =>
      MvPolynomial.homogeneousSubmodule (σ := Fin (r + 1)) (R := R) d
    graded := MvPolynomial.gradedAlgebra
  }

def chapter02ProjectiveSpaceOverRing
    (R : Type u) [CommRing R] (r : ℕ) : Scheme.{u} :=
  chapter02ProjOfGradedAlgebra (R := R) (A := chapter02PolynomialRing R r)
    (chapter02PolynomialGradedAlgebra R r)

noncomputable def chapter02ProjectiveSpaceOverRingProjection
    (R : Type u) [CommRing R] (r : ℕ) :
    chapter02ProjectiveSpaceOverRing R r ⟶
      AlgebraicGeometry.Spec (CommRingCat.of R) :=
  chapter02GradedAlgebraToSpec R (chapter02PolynomialGradedAlgebra R r)

/- LOCAL_DEPENDENCY_GUESS: the affine polynomial Proj and the relative free projective bundle agree. -/
theorem chapter02_projective_space_over_ring_is_relative_projective_space
    (R : Type u) [CommRing R] (r : ℕ) :
    ∃ e : chapter02ProjectiveSpaceOverRing R r ≅
        chapter02ProjectiveSpace (AlgebraicGeometry.Spec (CommRingCat.of R)) r,
      e.hom ≫ chapter02ProjectiveSpaceProjection
          (AlgebraicGeometry.Spec (CommRingCat.of R)) r =
        chapter02ProjectiveSpaceOverRingProjection R r := by
  sorry

structure Chapter02ProjectiveSpaceOverRingComparison (R : Type u) [CommRing R]
    (r : ℕ) where
  comparison : chapter02ProjectiveSpaceOverRing R r ≅
    chapter02ProjectiveSpace (AlgebraicGeometry.Spec (CommRingCat.of R)) r
  comparison_over :
    comparison.hom ≫ chapter02ProjectiveSpaceProjection
        (AlgebraicGeometry.Spec (CommRingCat.of R)) r =
      chapter02ProjectiveSpaceOverRingProjection R r

theorem chapter02_projective_space_over_ring_comparison_exists
    (R : Type u) [CommRing R] (r : ℕ) :
    Nonempty (Chapter02ProjectiveSpaceOverRingComparison R r) := by
  obtain ⟨e, he⟩ := chapter02_projective_space_over_ring_is_relative_projective_space R r
  exact ⟨{ comparison := e, comparison_over := he }⟩

noncomputable def chapter02ProjectiveSpaceOverRingComparison
    (R : Type u) [CommRing R] (r : ℕ) :
    Chapter02ProjectiveSpaceOverRingComparison R r :=
  Classical.choice (chapter02_projective_space_over_ring_comparison_exists R r)

theorem chapter02_projective_bundle_universal_quotient_is_epi
    {S : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02ProjectiveBundleData S E) :
    Epi P.universalQuotient :=
  P.universalQuotient_is_epi

/-- The standard affine cover by the `r+1` coordinate charts. -/
structure Chapter02StandardAffineCover
    (S : Scheme.{u}) (I : Type u)
    (P : Chapter02ProjectiveSpaceData S I) where
  chart : I → P.bundle.scheme.Opens
  affine : ∀ i, IsAffineOpen (chart i)
  chart_is_coordinate : ∀ i, (chart i : Set P.bundle.scheme) =
    {x | chapter02SectionGeneratesAt (P.coordinateSections i) x}
  cover : ∀ x : P.bundle.scheme, ∃ i, x ∈ chart i

/- LOCAL_DEPENDENCY_GUESS: the positive-degree basic opens of relative Proj give this finite cover. -/
theorem chapter02_standard_affine_cover_exists
    (S : Scheme.{u}) (I : Type u) (P : Chapter02ProjectiveSpaceData S I) :
    Nonempty (Chapter02StandardAffineCover S I P) := by
  sorry

abbrev Chapter02ProjectiveSpaceBasicOpenCover
    (S : Scheme.{u}) (I : Type u) (P : Chapter02ProjectiveSpaceData S I) :=
  Chapter02StandardAffineCover S I P

theorem chapter02_projective_space_basic_open_cover_exists
    (S : Scheme.{u}) (I : Type u) (P : Chapter02ProjectiveSpaceData S I) :
    Nonempty (Chapter02ProjectiveSpaceBasicOpenCover S I P) := by
  exact chapter02_standard_affine_cover_exists S I P

noncomputable def chapter02StandardAffineCover
    (S : Scheme.{u}) (I : Type u) (P : Chapter02ProjectiveSpaceData S I) :
    Chapter02StandardAffineCover S I P :=
  Classical.choice (chapter02_standard_affine_cover_exists S I P)

/-! Re-export the canonical polynomial basic-open cover from Chapter 1.  The separate declaration
keeps the affine `Proj` presentation and the free relative projective-space presentation visibly
connected without replacing the arbitrary-index cover above. -/
abbrev Chapter02PolynomialStandardAffineCover (R : Type u) [CommRing R] (r : ℕ) :=
  Chapter01.Chapter01PolynomialStandardAffineCover R r

theorem chapter02_polynomial_standard_affine_cover_exists
    (R : Type u) [CommRing R] (r : ℕ) :
    Nonempty (Chapter02PolynomialStandardAffineCover R r) := by
  sorry

abbrev Chapter02RelativeProjectiveSpaceBasicOpenCover
    (S : Scheme.{u}) (r : ℕ)
    (P : Chapter01.Chapter01RelativeProjectiveSpace S r) :=
  Chapter01.Chapter01RelativeProjectiveSpaceBasicOpenCover S r P

theorem chapter02_relative_projective_space_basic_open_cover_exists
    (S : Scheme.{u}) (r : ℕ)
    (P : Chapter01.Chapter01RelativeProjectiveSpace S r) :
    Nonempty (Chapter02RelativeProjectiveSpaceBasicOpenCover S r P) := by
  sorry

/-- Coordinate tuples used on standard charts. -/
abbrev Chapter02CoordinateTuple (K : Type u) (I : Type u) := I → K

/-- On a chart where the `i`th coordinate is nonzero, the other coordinates are ratios. -/
def chapter02CoordinateRatio {K : Type u} [CommGroupWithZero K]
    {I : Type u} (x : Chapter02CoordinateTuple K I) (i j : I) : K :=
  x j / x i

theorem chapter02CoordinateRatio_mul_denominator
    {K : Type u} [CommGroupWithZero K] {I : Type u}
    (x : Chapter02CoordinateTuple K I) (i j : I) (hi : x i ≠ 0) :
    chapter02CoordinateRatio x i j * x i = x j := by
  exact div_mul_cancel₀ (x j) hi

/-!
The transition statement is kept as a reusable chart-level interface: after choosing a nonzero
coordinate, all transition functions are the displayed ratios.  The actual relative chart rings
are obtained from the basic-open/localization API for `Proj`.
-/
structure Chapter02StandardAffineChartTransition
    {K : Type u} [CommGroupWithZero K] {I : Type u}
    (x : Chapter02CoordinateTuple K I) (i j : I) where
  ratio : K
  ratio_eq : ratio = chapter02CoordinateRatio x i j

theorem chapter02_standard_chart_transition_is_coordinate_ratio
    {K : Type u} [CommGroupWithZero K] {I : Type u}
    (x : Chapter02CoordinateTuple K I) (i j : I)
    (t : Chapter02StandardAffineChartTransition x i j) :
    t.ratio = chapter02CoordinateRatio x i j :=
  t.ratio_eq

/-!
When `E` is locally free of rank `r+1`, the fibers of `P_S(E)` are ordinary projective spaces
over the residue fields.  The fiber is the canonical scheme-theoretic fiber from Mathlib.
-/
theorem chapter02_projective_bundle_fiber_is_projective_space
    {S : Scheme.{u}} (E : Chapter02QuasiCoherentModule S)
    (r : ℕ) (hE : Chapter02LocallyFreeRank E.carrier (r + 1))
    (P : Chapter02ProjectiveBundleData S E) :
    ∀ s : S,
      ∃ e : P.projection.fiber s ≅
          chapter02ProjectiveSpaceOverRing (S.residueField s) r,
        IsIso e.hom ∧
          e.hom ≫ chapter02ProjectiveSpaceOverRingProjection (S.residueField s) r =
            P.projection.fiberToSpecResidueField s := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
