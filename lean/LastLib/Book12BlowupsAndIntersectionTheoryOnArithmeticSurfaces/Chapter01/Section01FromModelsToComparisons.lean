import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter01.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter01

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ## 1.1. From models to comparisons -/

/-- Book 11's regular proper-model existence theorem in the notation used here. -/
theorem chapter01_book11_constructs_regular_proper_model
    {K : Type u} [Field K]
    (C : Chapter13SmoothProjectiveCurve K)
    (S : Chapter13ExcellentDedekindScheme)
    (η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier) :
    Nonempty (Chapter13RegularProperModel C S η) :=
  chapter13_regular_proper_model_exists C S η

/-- The regular proper model retains the prescribed generic curve. -/
theorem chapter01_regular_proper_model_has_the_same_generic_curve
    {K : Type u} [Field K]
    {C : Chapter13SmoothProjectiveCurve K}
    {S : Chapter13ExcellentDedekindScheme}
    {η : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ S.carrier}
    (M : Chapter13RegularProperModel C S η) :
    Nonempty (pullback M.structureMap η ≅ C.carrier) :=
  ⟨M.generic_fiber_iso⟩

/- LOCAL_DEPENDENCY_GUESS: the relative point-blowup construction and the
regularity of the blowup of a regular surface at a closed point are not
bundled by the pinned scheme API.  The theorem exposes exactly that geometric
input and does not assume an intersection identity. -/
theorem chapter01_regular_surface_point_blowup_exists
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (p : Chapter01SurfacePoint X) :
    Nonempty (Chapter01PointBlowup p) := by
  sorry

theorem chapter01_point_blowup_preserves_generic_fiber
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    {p : Chapter01SurfacePoint X}
    (b : Chapter01PointBlowup p) :
    b.genericFiberIso.hom ≫
        pullback.snd b.target.structureMap (chapter01GenericPointMap B) =
      pullback.snd X.structureMap (chapter01GenericPointMap B) :=
  b.genericFiberIso_over

/-- A finite component-indexed symmetric integer matrix for a special fiber. -/
structure Chapter01SpecialFiberIntersectionMatrix
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    (X : Chapter01RegularArithmeticSurface B) where
  index : Type u
  [finiteIndex : Fintype index]
  component : index → Chapter01Curve X.carrier
  component_vertical : ∀ i, chapter01CurveIsVertical (component i)
  intersectionContext : Chapter01NumericalIntersectionContext X
  entry : index → index → ℤ
  entry_eq_intersection :
    ∀ i j, entry i j =
      intersectionContext.pairing
        (Finsupp.single (component i) 1)
        (Finsupp.single (component j) 1)
  symmetric : ∀ i j, entry i j = entry j i

attribute [instance] Chapter01SpecialFiberIntersectionMatrix.finiteIndex

theorem chapter01_special_fiber_matrix_is_symmetric
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    (M : Chapter01SpecialFiberIntersectionMatrix X) (i j : M.index) :
    M.entry i j = M.entry j i :=
  M.symmetric i j

/-! ### The central strict-transform calculation -/

/- LOCAL_DEPENDENCY_GUESS: this is the missing assembled compatibility between
the proper-map projection formula, total/strict transforms, and local curve
multiplicities.  The explicit no-common-component hypothesis prevents the
intersection from being assigned a finite number when the two divisors share a
component. -/
theorem chapter01_strict_transform_intersection_formula
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    {p : Chapter01SurfacePoint X}
    [Chapter01CurveMultiplicityTheory X.carrier]
    {b : Chapter01PointBlowup p}
    [Chapter01CurveMultiplicityTheory b.target.carrier]
    (P : Chapter01PointBlowupProjectionData b)
    (D G : Chapter01Divisor X.carrier)
    (hDG : chapter01NoCommonComponent D G)
    (hscope :
      (D, G) ∈ P.source.scope ∧
        (chapter01StrictTransformDivisor b D,
          chapter01StrictTransformDivisor b G) ∈ P.target.scope) :
    P.target.pairing
        (chapter01StrictTransformDivisor b D)
        (chapter01StrictTransformDivisor b G) =
      P.source.pairing D G -
        chapter01DivisorMultiplicity D p.point *
          chapter01DivisorMultiplicity G p.point *
            (chapter01ResidueDegree p : ℤ) := by
  sorry

/- The preceding theorem is stated for signed Weil divisors; this is its
curve-pair reading in the source notation. -/
theorem chapter01_curve_strict_transform_intersection_formula
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    {p : Chapter01SurfacePoint X}
    [Chapter01CurveMultiplicityTheory X.carrier]
    {b : Chapter01PointBlowup p}
    [Chapter01CurveMultiplicityTheory b.target.carrier]
    (P : Chapter01PointBlowupProjectionData b)
    (C G : Chapter01Curve X.carrier)
    (hCG : C ≠ G)
    (hscope :
      (Finsupp.single C 1, Finsupp.single G 1) ∈ P.source.scope ∧
        (chapter01StrictTransformDivisor b (Finsupp.single C 1),
          chapter01StrictTransformDivisor b (Finsupp.single G 1)) ∈ P.target.scope) :
    P.target.pairing
        (chapter01StrictTransformDivisor b (Finsupp.single C 1))
        (chapter01StrictTransformDivisor b (Finsupp.single G 1)) =
      P.source.pairing (Finsupp.single C 1) (Finsupp.single G 1) -
        (chapter01CurveMultiplicity C p.point : ℤ) *
          (chapter01CurveMultiplicity G p.point : ℤ) *
            (chapter01ResidueDegree p : ℤ) := by
  sorry

/-! ### Local intersections and the matrix viewpoint -/

noncomputable def chapter01LocalIntersectionMultiplicity
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    {D G : Chapter01Divisor X.carrier}
    (W : Chapter01LocalIntersectionWitness D G) : ℕ :=
  W.length.toNat

def chapter01LocalIntersectionContribution
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    {D G : Chapter01Divisor X.carrier}
    (W : Chapter01LocalIntersectionWitness D G) : ℤ :=
  (chapter01LocalIntersectionMultiplicity W : ℤ) *
    (chapter01ResidueDegree W.point : ℤ)

theorem chapter01_local_intersection_multiplicity_is_nonnegative
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    {D G : Chapter01Divisor X.carrier}
    (W : Chapter01LocalIntersectionWitness D G) :
    0 ≤ chapter01LocalIntersectionMultiplicity W :=
  Nat.zero_le _

theorem chapter01_local_intersection_contribution_has_residue_degree_weight
    {K : Type u} [Field K]
    {B : Chapter01ExcellentConnectedDedekindBaseData K}
    {X : Chapter01RegularArithmeticSurface B}
    {D G : Chapter01Divisor X.carrier}
    (W : Chapter01LocalIntersectionWitness D G) :
    chapter01LocalIntersectionContribution W =
      (chapter01LocalIntersectionMultiplicity W : ℤ) *
        (X.structureMap.residueDegree W.point.point : ℤ) := by
  rfl

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter01
