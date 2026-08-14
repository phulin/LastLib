import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
open scoped BigOperators

noncomputable section

/-! §5.3. Degree in proper flat families. -/

theorem chapter05_fiber_degree_formula
    (F : Chapter05ProjectiveFlatRelativeCurve)
    [Chapter05FiberEulerCharacteristicTheory F]
    (L : Chapter05LineBundle F.X) (s : F.S) :
    chapter05FiberDegree F L s =
      chapter05FiberEulerCharacteristic F s
          (chapter05FiberLineBundle F L s) -
        chapter05FiberEulerCharacteristic F s
          (chapter09StructureSheafLineBundle (F.f.fiber s)) := by
  rfl

theorem chapter05_line_bundle_module_is_flat_over_family
    (F : Chapter05ProjectiveFlatRelativeCurve)
    (L : Chapter05LineBundle F.X) :
    Chapter08FlatOver F.f L.module := by
  sorry

theorem chapter05_structure_sheaf_module_is_flat_over_family
    (F : Chapter05ProjectiveFlatRelativeCurve) :
    Chapter08FlatOver F.f (chapter09StructureSheafLineBundle F.X).module := by
  sorry

def chapter05GeometricallyReducedFibers {X S : Scheme} (f : X ⟶ S) : Prop :=
  ∀ s : S, GeometricallyReduced (f.fiberToSpecResidueField s)

theorem chapter05_locallyConstant_sub {α : Type u} [TopologicalSpace α]
    (g h : α → ℤ)
    (hg : Chapter05LocallyConstant g)
    (hh : Chapter05LocallyConstant h) :
    Chapter05LocallyConstant (fun x => g x - h x) := by
  sorry

/-! The Hilbert-polynomial route used in the proof is recorded with actual
polynomials and their values at zero, rather than with an unrelated numerical
function on the base. -/

structure Chapter05FiberHilbertPolynomialRoute
    (F : Chapter05ProjectiveFlatRelativeCurve)
    [Chapter05FiberEulerCharacteristicTheory F]
    [Chapter09LineBundleTensorTheory F.X]
    (L : Chapter05LineBundle F.X) where
  polarization : Chapter05LineBundle F.X
  polarization_relatively_ample : chapter09RelativelyAmple F.f polarization
  lineTwist : ℕ → Chapter05LineBundle F.X
  structureSheafTwist : ℕ → Chapter05LineBundle F.X
  lineTwist_eq : ∀ n,
    lineTwist n = chapter09Tensor L (chapter09LineBundlePower polarization n)
  structureSheafTwist_eq : ∀ n,
    structureSheafTwist n = chapter09LineBundlePower polarization n
  linePolynomial : F.S → Chapter08NumericalPolynomial
  structureSheafPolynomial : F.S → Chapter08NumericalPolynomial
  linePolynomial_locally_constant :
    Chapter05LocallyConstant linePolynomial
  structureSheafPolynomial_locally_constant :
    Chapter05LocallyConstant structureSheafPolynomial
  line_value_actual_twist : ∀ (s : F.S) (n : ℕ),
    (linePolynomial s).value n =
      chapter05FiberEulerCharacteristic F s
        (chapter05FiberLineBundle F (lineTwist n) s)
  structure_value_actual_twist : ∀ (s : F.S) (n : ℕ),
    (structureSheafPolynomial s).value n =
      chapter05FiberEulerCharacteristic F s
        (chapter05FiberLineBundle F (structureSheafTwist n) s)
  line_value_at_zero : ∀ s : F.S,
    (linePolynomial s).value 0 =
      chapter05FiberEulerCharacteristic F s
        (chapter05FiberLineBundle F L s)
  structure_value_at_zero : ∀ s : F.S,
    (structureSheafPolynomial s).value 0 =
      chapter05FiberEulerCharacteristic F s
        (chapter09StructureSheafLineBundle (F.f.fiber s))
  value_difference_is_degree : ∀ s : F.S,
    chapter05FiberDegree F L s =
      (linePolynomial s).value 0 - (structureSheafPolynomial s).value 0
  polynomial_difference_is_constant : ∀ s : F.S, ∀ n : ℕ,
    (linePolynomial s).value n - (structureSheafPolynomial s).value n =
      (linePolynomial s).value 0 - (structureSheafPolynomial s).value 0

theorem chapter05_fiber_degree_locally_constant_of_hilbert_route
    (F : Chapter05ProjectiveFlatRelativeCurve)
    [Chapter05FiberEulerCharacteristicTheory F]
    [Chapter09LineBundleTensorTheory F.X]
    (L : Chapter05LineBundle F.X)
    (H : Chapter05FiberHilbertPolynomialRoute F L) :
    Chapter05LocallyConstant (fun s => chapter05FiberDegree F L s) := by
  sorry

theorem chapter05_fiber_degree_locally_constant
    (F : Chapter05ProjectiveFlatRelativeCurve)
    [Chapter05FiberEulerCharacteristicTheory F]
    (L : Chapter05LineBundle F.X) :
    Chapter05LocallyConstant (fun s => chapter05FiberDegree F L s) := by
  sorry

/-! The nonflat warning is expressed as a witness profile: without sheaf
flatness, a coherent family can carry a genuinely non-locally-constant fiber
numerical function. -/

structure Chapter05NonflatDegreeJumpProfile
    (F : Chapter05ProjectiveFlatRelativeCurve)
    [Chapter05FiberEulerCharacteristicTheory F]
    [Chapter05RelativeCohomologyBaseChangeTheory F]
    (M : F.X.Modules) where
  coherent : Chapter08Coherent M
  not_flat_over : ¬ Chapter08FlatOver F.f M
  fiberValue : F.S → ℤ
  not_locally_constant : ¬ Chapter05LocallyConstant fiberValue
  fiberValue_eq_actual_fiber_invariant : ∀ s : F.S,
    fiberValue s =
      chapter05FiberModuleEulerCharacteristic F s
        (chapter05FiberModule F M s)

/-! Proper flat geometrically reduced families acquire projectivity after an
fpqc cover; this is the later projectivity bridge used when projectivity is
not part of the original family presentation. -/

theorem chapter05_proper_flat_geometrically_reduced_has_fpqc_projective_cover
    {X S : Scheme} (f : X ⟶ S)
    (hproper : IsProper f) (hflat : Flat f)
    (hfinitePresentation : LocallyOfFinitePresentation f)
    (hcurve : Chapter09RelativeCurve f)
    (hgeom : chapter05GeometricallyReducedFibers f) :
    Nonempty (Chapter05ProjectiveAfterFpqcCover f) := by
  sorry

structure Chapter05FpqcDegreeDescentProfile
    (F : Chapter05ProjectiveFlatRelativeCurve)
    [Chapter05FiberEulerCharacteristicTheory F]
    (L : Chapter05LineBundle F.X) where
  cover : Chapter05FpqcCover F.S
  coveredDegree : cover.total → ℤ
  coveredDegree_locally_constant :
    Chapter05LocallyConstant coveredDegree
  coveredDegree_eq_pullback_degree : ∀ t : cover.total,
    coveredDegree t = chapter05FiberDegree F L (cover.map t)

theorem chapter05_fpqc_cover_does_not_change_fiber_degree
    (F : Chapter05ProjectiveFlatRelativeCurve)
    [Chapter05FiberEulerCharacteristicTheory F]
    (L : Chapter05LineBundle F.X)
    (H : Chapter05FpqcDegreeDescentProfile F L) (t : H.cover.total) :
    H.coveredDegree t = chapter05FiberDegree F L (H.cover.map t) :=
  H.coveredDegree_eq_pullback_degree t

theorem chapter05_fiber_degree_descends_from_fpqc_cover
    (F : Chapter05ProjectiveFlatRelativeCurve)
    [Chapter05FiberEulerCharacteristicTheory F]
    (L : Chapter05LineBundle F.X)
    (H : Chapter05FpqcDegreeDescentProfile F L) :
    Chapter05LocallyConstant (fun s => chapter05FiberDegree F L s) := by
  sorry

/-! A multidegree is available after choosing component labels on a fiber;
only its total is canonical in the family. -/

structure Chapter05FiberMultidegreeProfile
    (F : Chapter05ProjectiveFlatRelativeCurve)
    [Chapter05FiberEulerCharacteristicTheory F]
    (L : Chapter05LineBundle F.X) (s : F.S)
  [IsNoetherian (F.f.fiber s)]
    (I : Type v) [Fintype I] where
  component : I → irreducibleComponents (F.f.fiber s)
  componentMap : ∀ i,
    (F.f.fiber s).irreducibleComponent (component i).1 (component i).2 ⟶
      F.f.fiber s
  componentMap_eq_canonical : ∀ i,
    componentMap i =
      (F.f.fiber s).irreducibleComponentι (component i).1 (component i).2
  componentMap_isClosedImmersion : ∀ i, IsClosedImmersion (componentMap i)
  componentMap_range : ∀ i,
    Set.range (componentMap i) = (component i : Set (F.f.fiber s))
  componentEulerCharacteristicTheory : ∀ i,
    Chapter05EulerCharacteristicTheory
      ((F.f.fiber s).irreducibleComponent (component i).1 (component i).2)
  componentDegree : I → ℤ
  componentDegree_eq_restricted_lineBundle : ∀ i,
    componentDegree i =
      letI := componentEulerCharacteristicTheory i
      chapter05LineBundleDegree
        (chapter09PullbackLineBundle (componentMap i)
          (chapter05FiberLineBundle F L s))
  total_degree :
    ∑ i, componentDegree i = chapter05FiberDegree F L s

theorem chapter05_total_degree_is_sum_of_component_degrees
    (F : Chapter05ProjectiveFlatRelativeCurve)
    [Chapter05FiberEulerCharacteristicTheory F]
    (L : Chapter05LineBundle F.X) (s : F.S)
    [IsNoetherian (F.f.fiber s)]
    (I : Type v) [Fintype I]
    (H : Chapter05FiberMultidegreeProfile F L s I) :
    ∑ i, H.componentDegree i = chapter05FiberDegree F L s :=
  H.total_degree

structure Chapter05ComponentDegreeSpecializationProfile
    (F : Chapter05ProjectiveFlatRelativeCurve)
    [Chapter05FiberEulerCharacteristicTheory F]
    (L : Chapter05LineBundle F.X) (s t : F.S)
    (I J : Type v) [Fintype I] [Fintype J]
    [IsNoetherian (F.f.fiber s)] [IsNoetherian (F.f.fiber t)] where
  specialization : I → J
  sourceProfile : Chapter05FiberMultidegreeProfile F L s I
  targetProfile : Chapter05FiberMultidegreeProfile F L t J
  sourceDegree : I → ℤ
  targetDegree : J → ℤ
  sourceDegree_eq_profile : ∀ i, sourceDegree i = sourceProfile.componentDegree i
  targetDegree_eq_profile : ∀ j, targetDegree j = targetProfile.componentDegree j
  target_degree_is_redistributed_source_degree :
    ∑ j, targetDegree j = ∑ i, sourceDegree i

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05
