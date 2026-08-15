import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Dependencies
import Mathlib.AlgebraicGeometry.AffineSpace
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

/-! The relative Segre construction is exposed independently of a chosen presentation of the
tensor-product module.  Its line-bundle field records the tensor product of the two tautological
quotients, while the closed-immersion field is the geometric content used by products.
-/
structure Chapter02RelativeSegreData
    {S : Scheme.{u}} {E F : Chapter02QuasiCoherentModule S}
    (P : Chapter02RelativeProjectiveBundle S E)
    (Q : Chapter02RelativeProjectiveBundle S F)
    (R : Chapter02FiniteTensorProductModule S E.carrier F.carrier)
    (B : Chapter02RelativeProjectiveBundle S
      (chapter02FiniteTensorProductQuasiCoherentModule R)) where
  embedding : Limits.pullback P.projection Q.projection ⟶ B.carrier
  isClosedImmersion : IsClosedImmersion embedding
  overBase : embedding ≫ B.projection =
    Limits.pullback.fst P.projection Q.projection ≫ P.projection
  pullbackTwistingLineIso :
    (Scheme.Modules.pullback embedding).obj B.twistingLineBundle.carrier ≅
      Chapter01.chapter01SheafTensor
        ((Scheme.Modules.pullback (Limits.pullback.fst P.projection Q.projection)).obj
          P.twistingLineBundle.carrier)
        ((Scheme.Modules.pullback (Limits.pullback.snd P.projection Q.projection)).obj
          Q.twistingLineBundle.carrier)
  /-- The source of the pulled-back tensor quotient is identified with the tensor of the two
  pulled-back universal quotient sources. -/
  universalQuotientSourceIso :
    (Scheme.Modules.pullback embedding).obj
        ((Scheme.Modules.pullback B.projection).obj
          (chapter02FiniteTensorProductQuasiCoherentModule R).carrier) ≅
      chapter02Tensor
        ((Scheme.Modules.pullback (Limits.pullback.fst P.projection Q.projection)).obj
          ((Scheme.Modules.pullback P.projection).obj E.carrier))
        ((Scheme.Modules.pullback (Limits.pullback.snd P.projection Q.projection)).obj
          ((Scheme.Modules.pullback Q.projection).obj F.carrier))
  /-- The Segre map carries the pulled-back universal quotient to the tensor of the two quotient
  maps, after the displayed source and twisting-line identifications. -/
  universalQuotient_compatibility :
    universalQuotientSourceIso.hom ≫
        chapter02TensorMap
          ((Scheme.Modules.pullback (Limits.pullback.fst P.projection Q.projection)).map
            P.universalQuotient)
          ((Scheme.Modules.pullback (Limits.pullback.snd P.projection Q.projection)).map
            Q.universalQuotient) =
      (Scheme.Modules.pullback embedding).map B.universalQuotient ≫
        pullbackTwistingLineIso.hom

theorem chapter02_relative_segre_embedding
    {S : Scheme.{u}} {E F : Chapter02QuasiCoherentModule S}
    (P : Chapter02RelativeProjectiveBundle S E)
    (Q : Chapter02RelativeProjectiveBundle S F) :
    ∃ (R : Chapter02FiniteTensorProductModule S E.carrier F.carrier)
      (B : Chapter02RelativeProjectiveBundle S
        (chapter02FiniteTensorProductQuasiCoherentModule R)),
      Nonempty (Chapter02RelativeSegreData P Q R B) := by
  sorry

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

/-! A finite relative projective-bundle package on the free module represents the same functor as
the free relative projective-space package.  The comparison is stated over the base so it can be
composed with restrictions and base changes in later chapters.
-/
theorem chapter02_projective_space_compare_relative_bundle
    (S : Scheme.{u}) (r : ℕ)
    (P : Chapter02RelativeProjectiveBundle S
      (chapter02FreeQuasiCoherentModule S (Chapter02ProjectiveSpaceIndex r))) :
    ∃ e : chapter02ProjectiveSpace S r ≅ P.carrier,
      e.hom ≫ P.projection = chapter02ProjectiveSpaceProjection S r := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: adding zero coordinates gives a closed immersion of standard relative
projective spaces over the same base. -/
theorem chapter02_projective_space_rank_padding
    (S : Scheme.{u}) (r n : ℕ) (hrn : r ≤ n) :
    ∃ i : chapter02ProjectiveSpace S r ⟶ chapter02ProjectiveSpace S n,
      IsClosedImmersion i ∧
        i ≫ chapter02ProjectiveSpaceProjection S n =
          chapter02ProjectiveSpaceProjection S r := by
  sorry

/-! The standard affine chart is exposed using the same affine-space model as Mathlib.  The
coordinate chart is the nonvanishing locus of the first homogeneous coordinate; no choice of a
global trivialization of the base is involved.
-/
abbrev chapter02AffineSpace (S : Scheme.{u}) (r : ℕ) : Scheme.{u} :=
  AlgebraicGeometry.AffineSpace (ULift.{u} (Fin r)) S

def chapter02AffineSpaceProjection (S : Scheme.{u}) (r : ℕ) :
    chapter02AffineSpace S r ⟶ S :=
  CategoryTheory.CanonicallyOverClass.Simps.over
    (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin r)) S) S

structure Chapter02ProjectiveSpaceStandardOpenData (S : Scheme.{u}) (r : ℕ) where
  inclusion : chapter02AffineSpace S r ⟶ chapter02ProjectiveSpace S r
  isOpenImmersion : IsOpenImmersion inclusion
  overBase : inclusion ≫ chapter02ProjectiveSpaceProjection S r =
    chapter02AffineSpaceProjection S r
  coordinateOpen : (chapter02ProjectiveSpace S r).Opens
  coordinateOpen_eq : (coordinateOpen : Set (chapter02ProjectiveSpace S r)) =
    {x | chapter02SectionGeneratesAt (chapter02ProjectiveSpaceCoordinates S r 0) x}
  inclusion_range : inclusion.opensRange = coordinateOpen

theorem chapter02_projective_space_standard_open_exists (S : Scheme.{u}) (r : ℕ) :
    Nonempty (Chapter02ProjectiveSpaceStandardOpenData S r) := by
  sorry

theorem chapter02_relative_bundle_standard_open_exists
    (S : Scheme.{u}) (r : ℕ)
    (P : Chapter02RelativeProjectiveBundle S
      (chapter02FreeQuasiCoherentModule S (Chapter02ProjectiveSpaceIndex r))) :
    ∃ i : chapter02AffineSpace S r ⟶ P.carrier,
      IsOpenImmersion i ∧ i ≫ P.projection = chapter02AffineSpaceProjection S r := by
  sorry

/-! Local finite trivializations are recorded pointwise.  This is the form that remains valid for
finite locally free modules of variable rank and is exactly what is needed to transport local closed
immersions into standard projective spaces.
-/
theorem chapter02_finite_locally_free_local_trivialization
    {S : Scheme.{u}} (E : S.Modules)
    (hE : Chapter01.Chapter01FiniteLocallyFree E) (s : S) :
    ∃ U : S.Opens, s ∈ U ∧ ∃ r : ℕ,
      Nonempty ((Scheme.Modules.pullback U.ι).obj E ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf)
          (ULift.{u} (Fin (r + 1)))) := by
  sorry

theorem chapter02_projective_presentation_local_standardization
    {X S : Scheme.{u}} (f : X ⟶ S)
    (P : Chapter02ProjectivePresentation f) (U : S.Opens) (r : ℕ)
    (e : (Scheme.Modules.pullback U.ι).obj P.module.carrier ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf)
        (ULift.{u} (Fin (r + 1)))) :
    ∃ j : (f ⁻¹ᵁ U).toScheme ⟶ chapter02ProjectiveSpace U.toScheme r,
      IsClosedImmersion j ∧
        j ≫ chapter02ProjectiveSpaceProjection U.toScheme r = f ∣_ U := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: compactness and finite local trivializations give one rank after padding
on a finite subcover.  The conclusion retains a cover because a nontrivial bundle need not be
globally trivial. -/
theorem chapter02_projective_presentation_compact_base_uniform_rank
    {X S : Scheme.{u}} [CompactSpace S] (f : X ⟶ S)
    (P : Chapter02ProjectivePresentation f) :
    ∃ (r : ℕ) (𝒰 : S.OpenCover.{u}),
      ∀ i : 𝒰.I₀,
        ∃ j : (f ⁻¹ᵁ (𝒰.f i).opensRange).toScheme ⟶
            chapter02ProjectiveSpace (𝒰.f i).opensRange.toScheme r,
          IsClosedImmersion j ∧
            j ≫ chapter02ProjectiveSpaceProjection
                (𝒰.f i).opensRange.toScheme r =
              f ∣_ (𝒰.f i).opensRange := by
  sorry

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

/-! The polynomial basic open is kept tied to the chosen total-degree grading.  This prevents a
coordinate chart from silently referring to a different Proj presentation. -/
def chapter02PolynomialDPlus
    (R : Type u) [CommRing R] (r : ℕ) (i : Fin (r + 1)) :
    (chapter02ProjectiveSpaceOverRing R r).Opens := by
  let G := chapter02PolynomialGradedAlgebra R r
  letI : GradedAlgebra G.component := G.graded
  exact AlgebraicGeometry.Proj.basicOpen G.component (MvPolynomial.X i)

abbrev Chapter02PolynomialChartCoordinateRing
    (R : Type u) [CommRing R] (r : ℕ) (i : Fin (r + 1)) :=
  MvPolynomial {j : Fin (r + 1) // j ≠ i} R

/-! A polynomial `D_+(X_i)` chart records all of the geometric data needed to identify it with
affine space: the actual basic open, its affine coordinate ring, and the open immersion from the
affine-space model. -/
structure Chapter02PolynomialCoordinateChartData
    (R : Type u) [CommRing R] (r : ℕ) (i : Fin (r + 1)) where
  chart : (chapter02ProjectiveSpaceOverRing R r).Opens
  chart_is_DPlus : chart = chapter02PolynomialDPlus R r i
  affine : IsAffineOpen chart
  coordinateRing : chart.toScheme ≅
    AlgebraicGeometry.Spec
      (CommRingCat.of (Chapter02PolynomialChartCoordinateRing R r i))
  inclusion : chapter02AffineSpace
      (AlgebraicGeometry.Spec (CommRingCat.of R)) r ⟶
      chapter02ProjectiveSpaceOverRing R r
  isOpenImmersion : IsOpenImmersion inclusion
  overBase : inclusion ≫ chapter02ProjectiveSpaceOverRingProjection R r =
    chapter02AffineSpaceProjection
      (AlgebraicGeometry.Spec (CommRingCat.of R)) r
  inclusion_range : inclusion.opensRange = chart

/- LOCAL_DEPENDENCY_GUESS: the polynomial D_+(X_i) chart is affine space with the ratio
coordinates, including the base-map equation. -/
theorem chapter02_polynomial_coordinate_chart_exists
    (R : Type u) [CommRing R] (r : ℕ) (i : Fin (r + 1)) :
    Nonempty (Chapter02PolynomialCoordinateChartData R r i) := by
  sorry

noncomputable def chapter02PolynomialCoordinateChartData
    (R : Type u) [CommRing R] (r : ℕ) (i : Fin (r + 1)) :
    Chapter02PolynomialCoordinateChartData R r i :=
  Classical.choice (chapter02_polynomial_coordinate_chart_exists R r i)

/-! The chosen polynomial comparison can be required to carry the genuine first-coordinate chart
to the corresponding relative-projective-space chart. -/
structure Chapter02ProjectiveSpaceOverRingChartComparison
    (R : Type u) [CommRing R] (r : ℕ) where
  comparison : chapter02ProjectiveSpaceOverRing R r ≅
    chapter02ProjectiveSpace (AlgebraicGeometry.Spec (CommRingCat.of R)) r
  comparison_over :
    comparison.hom ≫ chapter02ProjectiveSpaceProjection
        (AlgebraicGeometry.Spec (CommRingCat.of R)) r =
      chapter02ProjectiveSpaceOverRingProjection R r
  polynomialChart : Chapter02PolynomialCoordinateChartData R r 0
  relativeChart : Chapter02ProjectiveSpaceStandardOpenData
    (AlgebraicGeometry.Spec (CommRingCat.of R)) r
  chart_compatibility : polynomialChart.inclusion ≫ comparison.hom =
    relativeChart.inclusion

/- LOCAL_DEPENDENCY_GUESS: the polynomial Proj comparison and its first D_+(X₀) chart can be chosen
compatibly with the relative affine-space chart. -/
theorem chapter02_projective_space_over_ring_chart_comparison_exists
    (R : Type u) [CommRing R] (r : ℕ) :
    Nonempty (Chapter02ProjectiveSpaceOverRingChartComparison R r) := by
  sorry

noncomputable def chapter02ProjectiveSpaceOverRingChartComparison
    (R : Type u) [CommRing R] (r : ℕ) :
    Chapter02ProjectiveSpaceOverRingChartComparison R r :=
  Classical.choice (chapter02_projective_space_over_ring_chart_comparison_exists R r)

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
  /-- The standard chart is affine over the base; its total scheme need not be affine when `S`
  is not affine. -/
  affine : ∀ i, IsAffineHom ((chart i).ι ≫ P.bundle.projection)
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

/-! The Chapter 1 re-export used an absolute-affineness predicate.  Relative standard charts are
affine over `S`; their total schemes need not be affine when `S` is non-affine. -/
structure Chapter02RelativeProjectiveSpaceBasicOpenCover
    (S : Scheme.{u}) (r : ℕ)
    (P : Chapter01.Chapter01RelativeProjectiveSpace S r) where
  chart : Chapter01.Chapter01ProjectiveSpaceIndex r → P.scheme.Opens
  affine : ∀ i, IsAffineHom ((chart i).ι ≫ P.bundle.projection)
  chart_is_coordinate : ∀ i,
    (chart i : Set P.scheme) =
      {x | Chapter01.Chapter01ModuleSectionGeneratesAt
        (Chapter01.chapter01RelativeProjectiveSpaceCoordinateSection P i) x}
  cover : ∀ x : P.scheme, ∃ i, x ∈ chart i

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
