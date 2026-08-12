import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Section03SectionsWithoutCommonZeros
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory

/-!
## 2.4 Closed subschemes from homogeneous ideals

For `S = Spec R`, the homogeneous-ideal construction is first stated using the canonical
`Ideal.IsHomogeneous` predicate for a selected graded algebra.  The quotient grading and the
relative base map are isolated as local dependencies because the pinned Proj API does not package
relative quotient gradings.
-/

abbrev chapter02Spec (R : Type u) [CommRing R] : Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of R)

def Chapter02IsHomogeneousIdeal
    {R A : Type u} [CommSemiring R] [Semiring A] [Algebra R A]
    (G : Chapter02GradedAlgebra R A) (I : Ideal A) : Prop := by
  letI : GradedAlgebra G.component := G.graded
  exact I.IsHomogeneous G.component

/-!
This structure is definitionally equivalent to a homogeneous ideal in Mathlib after installing
`G.graded`, while retaining the book's explicit ideal field.
-/
structure Chapter02HomogeneousIdealData
    {R A : Type u} [CommSemiring R] [CommRing A] [Algebra R A]
    (G : Chapter02GradedAlgebra R A) where
  ideal : Ideal A
  is_homogeneous : Chapter02IsHomogeneousIdeal G ideal
  /-- The grading on the quotient is part of the induced quotient construction. -/
  quotientGrading : Chapter02GradedAlgebra R (A ⧸ ideal)
  quotientGrading_component_iff :
    ∀ d (x : A ⧸ ideal),
      x ∈ quotientGrading.component d ↔
        ∃ a : A, a ∈ G.component d ∧ Ideal.Quotient.mk ideal a = x

def chapter02HomogeneousIdealToIdeal
    {R A : Type u} [CommSemiring R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) : Ideal A :=
  I.ideal

theorem chapter02_homogeneous_ideal_is_homogeneous
    {R A : Type u} [CommSemiring R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) :
    Chapter02IsHomogeneousIdeal G (chapter02HomogeneousIdealToIdeal I) :=
  I.is_homogeneous

abbrev Chapter02PolynomialHomogeneousIdealData (R : Type u) [CommRing R] (r : ℕ) :=
  Chapter02HomogeneousIdealData (chapter02PolynomialGradedAlgebra R r)

abbrev chapter02HomogeneousQuotientRing
    {R A : Type u} [CommSemiring R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) : Type u :=
  A ⧸ I.ideal

/- LOCAL_DEPENDENCY_GUESS: a homogeneous ideal induces the standard quotient grading. -/
theorem chapter02_homogeneous_quotient_grading_exists
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) :
    Nonempty (Chapter02GradedAlgebra R (chapter02HomogeneousQuotientRing I)) := by
  exact ⟨I.quotientGrading⟩

noncomputable def chapter02HomogeneousQuotientGrading
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) :
    Chapter02GradedAlgebra R (chapter02HomogeneousQuotientRing I) :=
  I.quotientGrading

def chapter02VPlus
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) : Scheme.{u} :=
  chapter02ProjOfGradedAlgebra (chapter02HomogeneousQuotientGrading I)

theorem chapter02_vplus_is_proj_of_homogeneous_quotient
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) :
    chapter02VPlus I =
      chapter02ProjOfGradedAlgebra (chapter02HomogeneousQuotientGrading I) :=
  rfl

/-!
The structure map is obtained from `Proj.toSpecZero` and the degree-zero projection of the
graded `R`-algebra.  This avoids choosing an unrelated morphism merely because one exists.
-/
noncomputable def chapter02GradedAlgebraProjection
    (R : Type u) [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    (G : Chapter02GradedAlgebra R A) :
    chapter02ProjOfGradedAlgebra G ⟶ chapter02Spec R := by
  exact chapter02GradedAlgebraToSpec R G

theorem chapter02_vplus_base_map_exists
    (R : Type u) [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) :
    Nonempty (chapter02VPlus I ⟶ chapter02Spec R) := by
  exact ⟨chapter02GradedAlgebraProjection R (chapter02HomogeneousQuotientGrading I)⟩

noncomputable def chapter02VPlusProjection
    (R : Type u) [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) : chapter02VPlus I ⟶ chapter02Spec R :=
  chapter02GradedAlgebraProjection R (chapter02HomogeneousQuotientGrading I)

def Chapter02HomogeneousPolynomial
    {R A : Type u} [CommSemiring R] [Semiring A] [Algebra R A]
    (G : Chapter02GradedAlgebra R A) (d : ℕ) :=
  {F : A // F ∈ G.component d}

def Chapter02HomogeneousPolynomialInIdeal
    {R A : Type u} [CommSemiring R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) (d : ℕ) :=
  {F : A // F ∈ I.ideal ∧ F ∈ G.component d}

/-!
The following point API is specialized to the source assertion `R[x_0, …, x_r]`; the polynomial
ring, its grading, and the coordinate module therefore share the same `r` instead of being
independent parameters.
-/
abbrev Chapter02PolynomialHomogeneousPolynomial (R : Type u) [CommRing R]
    (r d : ℕ) :=
  Chapter02HomogeneousPolynomial (chapter02PolynomialGradedAlgebra R r) d

abbrev Chapter02PolynomialHomogeneousPolynomialInIdeal (R : Type u) [CommRing R]
    (r : ℕ) (I : Chapter02PolynomialHomogeneousIdealData R r) (d : ℕ) :=
  Chapter02HomogeneousPolynomialInIdeal I d

abbrev Chapter02PolynomialVPlus
    (R : Type u) [CommRing R] (r : ℕ)
    (I : Chapter02PolynomialHomogeneousIdealData R r) : Scheme.{u} :=
  chapter02VPlus I

abbrev chapter02PolynomialVPlusProjection
    (R : Type u) [CommRing R] (r : ℕ)
    (I : Chapter02PolynomialHomogeneousIdealData R r) :
    Chapter02PolynomialVPlus R r I ⟶ chapter02Spec R :=
  chapter02VPlusProjection R I

/- LOCAL_DEPENDENCY_GUESS: the homogeneous quotient map induces the closed immersion into
the polynomial projective space, with the displayed structure morphism over `Spec R`. -/
theorem chapter02_polynomial_vplus_is_closed_subscheme
    (R : Type u) [CommRing R] (r : ℕ)
    (I : Chapter02PolynomialHomogeneousIdealData R r) :
    ∃ i : Chapter02PolynomialVPlus R r I ⟶ chapter02ProjectiveSpaceOverRing R r,
      i ≫ chapter02ProjectiveSpaceOverRingProjection R r =
          chapter02PolynomialVPlusProjection R r I ∧
        IsClosedImmersion i := by
  sorry

/-!
The value of a homogeneous polynomial on a quotient is the only sheaf-tensor operation needed
for the pointwise statement.  It is a named interface so that the later tensor-power API can
replace it without changing the `V_+(I)` point type.
-/
structure Chapter02PolynomialHomogeneousEvaluation
    (R : Type u) [CommRing R] (r : ℕ)
    (G : Chapter02GradedAlgebra R (chapter02PolynomialRing R r))
    {T : Scheme.{u}} (f : T ⟶ chapter02Spec R)
    (q : Chapter02InvertibleQuotientPair
      (chapter02FreeQuasiCoherentModule T (Chapter02ProjectiveSpaceIndex r)).carrier) where
  value : ∀ d, Chapter02HomogeneousPolynomial G d →
    (chapter02LineBundlePowerBundle q.line d).carrier.sections

/- LOCAL_DEPENDENCY_GUESS: evaluation of homogeneous polynomials in the quotient sections. -/
theorem chapter02_polynomial_homogeneous_evaluation_exists
    (R : Type u) [CommRing R] (r : ℕ)
    (G : Chapter02GradedAlgebra R (chapter02PolynomialRing R r))
    {T : Scheme.{u}} (f : T ⟶ chapter02Spec R)
    (q : Chapter02InvertibleQuotientPair
      (chapter02FreeQuasiCoherentModule T (Chapter02ProjectiveSpaceIndex r)).carrier) :
    Nonempty (Chapter02PolynomialHomogeneousEvaluation R r G f q) := by
  sorry

noncomputable def chapter02PolynomialHomogeneousEvaluation
    (R : Type u) [CommRing R] (r : ℕ)
    (G : Chapter02GradedAlgebra R (chapter02PolynomialRing R r))
    {T : Scheme.{u}} (f : T ⟶ chapter02Spec R)
    (q : Chapter02InvertibleQuotientPair
      (chapter02FreeQuasiCoherentModule T (Chapter02ProjectiveSpaceIndex r)).carrier) :
    Chapter02PolynomialHomogeneousEvaluation R r G f q :=
  Classical.choice (chapter02_polynomial_homogeneous_evaluation_exists R r G f q)

/-- A quotient-class point on `V_+(I)`, with all homogeneous elements of `I` evaluating to zero. -/
structure Chapter02PolynomialVPlusPoint
    (R : Type u) [CommRing R] (r : ℕ)
    (I : Chapter02PolynomialHomogeneousIdealData R r)
    {T : Scheme.{u}} (f : T ⟶ chapter02Spec R) where
  quotientClass :
    Chapter02InvertibleQuotientClass
      (chapter02FreeQuasiCoherentModule T (Chapter02ProjectiveSpaceIndex r)).carrier
  vanishes_on_ideal :
    ∃ q : Chapter02InvertibleQuotientPair
        (chapter02FreeQuasiCoherentModule T (Chapter02ProjectiveSpaceIndex r)).carrier,
      chapter02QuotientClassMk q = quotientClass ∧
        ∀ d (F : Chapter02PolynomialHomogeneousPolynomialInIdeal R r I d),
          (chapter02PolynomialHomogeneousEvaluation R r
            (chapter02PolynomialGradedAlgebra R r) f q).value d ⟨F.1, F.2.2⟩ =
            chapter02ZeroSection (chapter02LineBundlePowerBundle q.line d).carrier

abbrev Chapter02PolynomialVPlusPointOver
    (R : Type u) [CommRing R] (r : ℕ)
    (I : Chapter02PolynomialHomogeneousIdealData R r)
    {T : Scheme.{u}} (f : T ⟶ chapter02Spec R) :=
  {t : T ⟶ Chapter02PolynomialVPlus R r I //
    t ≫ chapter02PolynomialVPlusProjection R r I = f}

/- LOCAL_DEPENDENCY_GUESS: the quotient-point correspondence, including nilpotents and gluing. -/
theorem chapter02_polynomial_vplus_points_equiv
    (R : Type u) [CommRing R] (r : ℕ)
    (I : Chapter02PolynomialHomogeneousIdealData R r)
    {T : Scheme.{u}} (f : T ⟶ chapter02Spec R) :
    Nonempty (Chapter02PolynomialVPlusPointOver R r I f ≃
      Chapter02PolynomialVPlusPoint R r I f) := by
  sorry

/-!
### Veronese maps

The degree-`d` monomials are indexed by exponent vectors of total degree `d`.  This finite index
type has the binomial cardinality in the source, so its projective space is the displayed
`P^{binom{r+d}{d}-1}` up to the canonical finite-index reindexing.
-/

def Chapter02MonomialIndex (r d : ℕ) :=
  {a : Fin (r + 1) →₀ ℕ // a.sum (fun _ n => n) = d}

/- LOCAL_DEPENDENCY_GUESS: exponent vectors of fixed total degree form a finite type. -/
theorem chapter02_monomial_index_finite (r d : ℕ) :
    Finite (Chapter02MonomialIndex r d) := by
  sorry

noncomputable instance chapter02_monomial_index_fintype (r d : ℕ) :
    Fintype (Chapter02MonomialIndex r d) := by
  letI : Finite (Chapter02MonomialIndex r d) := chapter02_monomial_index_finite r d
  exact Fintype.ofFinite _

theorem chapter02_monomial_index_cardinality (r d : ℕ) :
    Fintype.card (Chapter02MonomialIndex r d) = Nat.choose (r + d) d := by
  sorry

def chapter02VeroneseTargetDimension (r d : ℕ) : ℕ :=
  Nat.choose (r + d) d - 1

theorem chapter02_veronese_target_dimension_succ (r d : ℕ) :
    chapter02VeroneseTargetDimension r d + 1 = Nat.choose (r + d) d := by
  sorry

theorem chapter02_veronese_target_index_reindexing (r d : ℕ) :
    Nonempty (Chapter02MonomialIndex r d ≃
      Fin (chapter02VeroneseTargetDimension r d + 1)) := by
  sorry

abbrev chapter02VeroneseTargetIndex (r d : ℕ) : Type u :=
  ULift.{u} (Chapter02MonomialIndex r d)

def chapter02VeroneseTargetData (S : Scheme.{u}) (r d : ℕ) :
    Chapter02ProjectiveSpaceData S (chapter02VeroneseTargetIndex r d) :=
  chapter02ProjectiveSpaceData S (chapter02VeroneseTargetIndex r d)

abbrev chapter02VeroneseTarget (S : Scheme.{u}) (r d : ℕ) : Scheme.{u} :=
  (chapter02VeroneseTargetData S r d).bundle.scheme

abbrev chapter02VeroneseStandardTarget (S : Scheme.{u}) (r d : ℕ) : Scheme.{u} :=
  chapter02ProjectiveSpace S (chapter02VeroneseTargetDimension r d)

/- LOCAL_DEPENDENCY_GUESS: reindexing a free projective bundle along the finite-coordinate equivalence. -/
theorem chapter02_veronese_target_reindexed_standard_projective_space
    (S : Scheme.{u}) (r d : ℕ) :
    Nonempty (chapter02VeroneseTarget S r d ≅
      chapter02VeroneseStandardTarget S r d) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: multiplication of sections in the tensor powers constructs monomial sections. -/
def chapter02VeroneseMonomialSection
    {S : Scheme.{u}}
    (P : Chapter02ProjectiveSpaceData S (Chapter02ProjectiveSpaceIndex r))
    (d : ℕ) (a : Chapter02MonomialIndex r d) :
    (chapter02LineBundlePowerBundle P.bundle.twistingLineBundle d).carrier.sections := by
  sorry

structure Chapter02VeroneseCoordinateData
    (S : Scheme.{u}) (r d : ℕ)
    (P : Chapter02ProjectiveSpaceData S (Chapter02ProjectiveSpaceIndex r)) where
  coordinateSections :
    Chapter02MonomialIndex r d →
      (chapter02LineBundlePowerBundle P.bundle.twistingLineBundle d).carrier.sections
  coordinate_is_monomial :
    ∀ a, coordinateSections a = chapter02VeroneseMonomialSection P d a
  sections_generate :
    Chapter02SectionsGenerate
      (chapter02LineBundlePowerBundle P.bundle.twistingLineBundle d)
      (fun a : chapter02VeroneseTargetIndex r d => coordinateSections a.down)

/- LOCAL_DEPENDENCY_GUESS: the monomial sections generate the degree-d power of `𝒪(1)`. -/
theorem chapter02_veronese_coordinate_data_exists
    (S : Scheme.{u}) (r d : ℕ)
    (P : Chapter02ProjectiveSpaceData S (Chapter02ProjectiveSpaceIndex r)) :
    Nonempty (Chapter02VeroneseCoordinateData S r d P) := by
  sorry

noncomputable def chapter02VeroneseCoordinateData
    (S : Scheme.{u}) (r d : ℕ)
    (P : Chapter02ProjectiveSpaceData S (Chapter02ProjectiveSpaceIndex r)) :
    Chapter02VeroneseCoordinateData S r d P :=
  Classical.choice (chapter02_veronese_coordinate_data_exists S r d P)

structure Chapter02VeroneseMapData
    (S : Scheme.{u}) (r d : ℕ) where
  source : Chapter02ProjectiveSpaceData S (Chapter02ProjectiveSpaceIndex r)
  coordinateData : Chapter02VeroneseCoordinateData S r d source
  map : source.bundle.scheme ⟶ (chapter02VeroneseTargetData S r d).bundle.scheme
  over : map ≫ (chapter02VeroneseTargetData S r d).bundle.projection =
    source.bundle.projection
  pullbackTwistingLineIso :
    (Scheme.Modules.pullback map).obj
        (chapter02VeroneseTargetData S r d).bundle.twistingLineBundle.carrier ≅
      (chapter02LineBundlePowerBundle source.bundle.twistingLineBundle d).carrier
  coordinate_pullback :
    ∀ a : chapter02VeroneseTargetIndex r d,
      SheafOfModules.sectionsMap pullbackTwistingLineIso.hom
        ((chapter02PullbackSectionData map
          (chapter02VeroneseTargetData S r d).bundle.twistingLineBundle.carrier).map
          ((chapter02VeroneseTargetData S r d).coordinateSections a)) =
        coordinateData.coordinateSections a.down

/- LOCAL_DEPENDENCY_GUESS: the universal-property construction of the Veronese morphism. -/
theorem chapter02_veronese_map_data_exists (S : Scheme.{u}) (r d : ℕ) :
    Nonempty (Chapter02VeroneseMapData S r d) := by
  sorry

noncomputable def chapter02VeroneseMapData (S : Scheme.{u}) (r d : ℕ) :
    Chapter02VeroneseMapData S r d :=
  Classical.choice (chapter02_veronese_map_data_exists S r d)

abbrev chapter02VeroneseMap (S : Scheme.{u}) (r d : ℕ) :
    (chapter02VeroneseMapData S r d).source.bundle.scheme ⟶
      (chapter02VeroneseTargetData S r d).bundle.scheme :=
  (chapter02VeroneseMapData S r d).map

theorem chapter02_veronese_map_is_over
    (S : Scheme.{u}) (r d : ℕ) :
    chapter02VeroneseMap S r d ≫
        (chapter02VeroneseTargetData S r d).bundle.projection =
      (chapter02VeroneseMapData S r d).source.bundle.projection :=
  (chapter02VeroneseMapData S r d).over

noncomputable def chapter02_veronese_pullback_of_twisting_line
    (S : Scheme.{u}) (r d : ℕ) :
    (Scheme.Modules.pullback (chapter02VeroneseMap S r d)).obj
        (chapter02VeroneseTargetData S r d).bundle.twistingLineBundle.carrier ≅
      (chapter02LineBundlePowerBundle
        (chapter02VeroneseMapData S r d).source.bundle.twistingLineBundle d).carrier :=
  (chapter02VeroneseMapData S r d).pullbackTwistingLineIso

theorem chapter02_veronese_map_is_closed_immersion
    (S : Scheme.{u}) (r d : ℕ) (hd : 0 < d) :
    IsClosedImmersion (chapter02VeroneseMap S r d) := by
  sorry

/-!
On each standard chart, the target ratios contain the original affine coordinates.  The
chart-level package below is the precise algebraic interface used by the closed-immersion proof.
-/
structure Chapter02VeroneseAffineChartData (R : Type u) [CommRing R] (r d : ℕ) where
  sourceRing : Type u
  targetRing : Type u
  [sourceRingCommRing : CommRing sourceRing]
  [targetRingCommRing : CommRing targetRing]
  [sourceRingAlgebra : Algebra R sourceRing]
  [targetRingAlgebra : Algebra R targetRing]
  chartMap : targetRing →ₐ[R] sourceRing
  sourceCoordinate : Fin (r + 1) → sourceRing
  targetCoordinate : Chapter02MonomialIndex r d → targetRing
  targetRatio : Chapter02MonomialIndex r d → sourceRing
  targetRatio_eq_chartMap :
    ∀ a, targetRatio a = chartMap (targetCoordinate a)
  sourceCoordinate_in_target_ratios :
    ∀ i, ∃ a, sourceCoordinate i = targetRatio a
  sourceCoordinate_generate : Algebra.adjoin R (Set.range sourceCoordinate) = ⊤

attribute [instance] Chapter02VeroneseAffineChartData.sourceRingCommRing
  Chapter02VeroneseAffineChartData.targetRingCommRing
  Chapter02VeroneseAffineChartData.sourceRingAlgebra
  Chapter02VeroneseAffineChartData.targetRingAlgebra

def Chapter02VeroneseRatiosContainOriginalCoordinates
    {R : Type u} [CommRing R] {r d : ℕ}
    (c : Chapter02VeroneseAffineChartData R r d) : Prop :=
  ∀ i, ∃ a, c.sourceCoordinate i = c.targetRatio a

theorem chapter02_veronese_chart_ratio_criterion
    {R : Type u} [CommRing R] {r d : ℕ}
    (c : Chapter02VeroneseAffineChartData R r d) :
    Chapter02VeroneseRatiosContainOriginalCoordinates c ↔
      ∀ i, ∃ a, c.sourceCoordinate i = c.targetRatio a :=
  Iff.rfl

/-!
The target-coordinate quadratic relations are the toric relations
`Y_a Y_b - Y_c Y_e` whenever `a+b=c+e` as exponent vectors.
-/
def chapter02VeroneseQuadraticRelation
    (R : Type u) [CommRing R] (r d : ℕ)
    (a b c e : Chapter02MonomialIndex r d) :
    MvPolynomial (Chapter02MonomialIndex r d) R :=
  MvPolynomial.monomial (Finsupp.single a 1 + Finsupp.single b 1) 1 -
    MvPolynomial.monomial (Finsupp.single c 1 + Finsupp.single e 1) 1

def Chapter02VeroneseQuadraticRelationPredicate
    (r d : ℕ) (a b c e : Chapter02MonomialIndex r d) : Prop :=
  a.1 + b.1 = c.1 + e.1

def chapter02VeroneseImageIdeal
    (R : Type u) [CommRing R] (r d : ℕ) :
    Ideal (MvPolynomial (Chapter02MonomialIndex r d) R) :=
  Ideal.span {F |
    ∃ a b c e : Chapter02MonomialIndex r d,
      Chapter02VeroneseQuadraticRelationPredicate r d a b c e ∧
        F = chapter02VeroneseQuadraticRelation R r d a b c e}

def chapter02VeroneseMonomialRingHom
    (R : Type u) [CommRing R] (r d : ℕ) :
    MvPolynomial (Chapter02MonomialIndex r d) R →ₐ[R]
      MvPolynomial (Fin (r + 1)) R :=
  MvPolynomial.aeval (fun a => MvPolynomial.monomial a.1 1)

theorem chapter02_veronese_quadratic_relation_maps_to_zero
    (R : Type u) [CommRing R] (r d : ℕ)
    (a b c e : Chapter02MonomialIndex r d)
    (h : Chapter02VeroneseQuadraticRelationPredicate r d a b c e) :
    chapter02VeroneseMonomialRingHom R r d
        (chapter02VeroneseQuadraticRelation R r d a b c e) = 0 := by
  sorry

theorem chapter02_veronese_image_ideal_le_kernel
    (R : Type u) [CommRing R] (r d : ℕ) :
    chapter02VeroneseImageIdeal R r d ≤
      RingHom.ker (chapter02VeroneseMonomialRingHom R r d).toRingHom := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the quadratic toric relations generate the full Veronese kernel. -/
theorem chapter02_veronese_image_ideal_eq_kernel
    (R : Type u) [CommRing R] (r d : ℕ) (hd : 0 < d) :
    chapter02VeroneseImageIdeal R r d =
      RingHom.ker (chapter02VeroneseMonomialRingHom R r d).toRingHom := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
