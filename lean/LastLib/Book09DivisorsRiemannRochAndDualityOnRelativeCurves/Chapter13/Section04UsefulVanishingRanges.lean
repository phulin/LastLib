import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter13.Section03RelativeRiemannRoch

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter13

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09

noncomputable section

/-! ## 13.4. Useful vanishing ranges -/

/-! ### Smooth fibers -/

/-- A smooth proper relative curve with geometrically connected fibers. -/
structure Chapter13SmoothProperCurve extends Chapter13RelativeCurve where
  smooth : Smooth f
  proper : IsProper f
  geometrically_connected : GeometricallyConnected f
  genus : ℕ
  genus_data : Chapter13GeometricGenusData toChapter13RelativeCurve
  genus_data_genus_eq : genus_data.genus = genus
  relative_dualizing : Chapter13RelativeDualizingData toChapter13RelativeCurve
  differential_theory : Chapter09DifferentialSheafTheory f
  dualizing_is_relative_differentials :
    letI := relative_dualizing.derived_theory
    letI := differential_theory
    Nonempty (relative_dualizing.dualizing.omega ≅
      chapter09RelativeDifferentials f)

namespace Chapter13SmoothProperCurve

instance (C : Chapter13SmoothProperCurve) : Smooth C.f := C.smooth
instance (C : Chapter13SmoothProperCurve) : IsProper C.f := C.proper

end Chapter13SmoothProperCurve

/-- Relative cohomology data specialized to a line bundle. -/
structure Chapter13RelativeLineCohomologyData
    (C : Chapter13RelativeCurve) (L : Chapter04LineBundle C.X) where
  relative_cohomology :
    Chapter13RelativeCohomologyData C (chapter13LineBundleAsVectorBundle L)

namespace Chapter13RelativeLineCohomologyData

abbrev fiber {C : Chapter13RelativeCurve} {L : Chapter04LineBundle C.X}
    (D : Chapter13RelativeLineCohomologyData C L) :
    Chapter13FiberCohomologyProfile C L.sheaf :=
  D.relative_cohomology.fiber

abbrev firstHigherDirectImage {C : Chapter13RelativeCurve}
    {L : Chapter04LineBundle C.X}
    (D : Chapter13RelativeLineCohomologyData C L) : C.S.Modules :=
  D.relative_cohomology.firstHigherDirectImage

end Chapter13RelativeLineCohomologyData

/-- The degree-one relative direct image is zero. -/
def chapter13FirstHigherDirectImageIsZero
    {C : Chapter13RelativeCurve} {L : Chapter04LineBundle C.X}
    (D : Chapter13RelativeLineCohomologyData C L) : Prop :=
  IsZero D.firstHigherDirectImage

/-- The pushforward has the stated fiberwise rank. -/
def chapter13PushforwardFiberDimension
    {C : Chapter13RelativeCurve} (L : Chapter04LineBundle C.X) (s : C.S) : ℕ :=
  Module.finrank (C.S.residueField s)
    (chapter13ResidueFiberModule (chapter13PushforwardModule L.sheaf) s)

def chapter13PushforwardHasRank
    {C : Chapter13RelativeCurve} (L : Chapter04LineBundle C.X) (d g : ℤ) : Prop :=
  ∀ s : C.S,
    (chapter13PushforwardFiberDimension L s : ℤ) = d + 1 - g

/- LOCAL_DEPENDENCY_GUESS: relative Serre duality and negative-degree
vanishing for smooth proper fibers are not exposed by the earlier focused
imports, so the source-facing vanishing theorem remains the local bridge. -/

/-- Pushforward of a line bundle after a smooth high-degree vanishing. -/
theorem chapter13_smooth_high_degree_line_bundle_vanishes
    (C : Chapter13SmoothProperCurve)
    (deg : Chapter13FiberDegreeTheory C.toChapter13RelativeCurve)
    (L : Chapter04LineBundle C.X)
    (H : Chapter13RelativeLineCohomologyData C.toChapter13RelativeCurve L)
    (d : ℤ) (hd : chapter13LineBundleOfRelativeDegree deg L d)
    (hdegree : 2 * (C.genus : ℤ) - 2 < d) :
    chapter13FirstHigherDirectImageIsZero H := by
  sorry

/-! The pinned snapshot has no relative finite-locally-free cohomology theorem,
so the arbitrary-base-change comparison is kept as a named support predicate. -/

/-- The pushforward of a line bundle after an arbitrary base change. -/
noncomputable def chapter13BaseChangedLineBundlePushforward
    {C : Chapter13RelativeCurve} (L : Chapter04LineBundle C.X)
    {T : Scheme} (g : T ⟶ C.S) : T.Modules :=
  let L' := chapter04PullbackLineBundle (chapter13BaseChangeToSource C.f g) L
  (Scheme.Modules.pushforward (chapter13BaseChangeToTest C.f g)).obj L'.sheaf

/-- Commutation of `f_* L` with every test-scheme base change. -/
def chapter13PushforwardCommutesWithArbitraryBaseChange
    {C : Chapter13RelativeCurve} (L : Chapter04LineBundle C.X) : Prop :=
  ∀ {T : Scheme} (g : T ⟶ C.S),
    Nonempty (
      (Scheme.Modules.pullback g).obj (chapter13PushforwardModule L.sheaf) ≅
        chapter13BaseChangedLineBundlePushforward L g)

/-- The full smooth high-degree vector-bundle-of-sections package. -/
structure Chapter13SmoothHighDegreePushforwardData
    (C : Chapter13SmoothProperCurve) (L : Chapter04LineBundle C.X) (d : ℤ) where
  relative_cohomology :
    Chapter13RelativeLineCohomologyData C.toChapter13RelativeCurve L
  firstHigherDirectImage_is_zero :
    chapter13FirstHigherDirectImageIsZero relative_cohomology
  pushforward_locally_free :
    (chapter13PushforwardModule (C := C.toChapter13RelativeCurve) L.sheaf).IsLocallyFree
  pushforward_finite_type :
    (chapter13PushforwardModule (C := C.toChapter13RelativeCurve) L.sheaf).IsFiniteType
  pushforward_has_rank :
    chapter13PushforwardHasRank (C := C.toChapter13RelativeCurve) L d (C.genus : ℤ)
  pushforward_base_change :
    chapter13PushforwardCommutesWithArbitraryBaseChange
      (C := C.toChapter13RelativeCurve) L

/-- Local freeness, rank, and arbitrary base change in the vanishing range. -/
theorem chapter13_smooth_high_degree_pushforward_is_locally_free
    (C : Chapter13SmoothProperCurve)
    (deg : Chapter13FiberDegreeTheory C.toChapter13RelativeCurve)
    (L : Chapter04LineBundle C.X) (d : ℤ)
    (hd : chapter13LineBundleOfRelativeDegree deg L d)
    (hdegree : ∀ s : C.S, 2 * (C.genus : ℤ) - 2 < d) :
    Nonempty (Chapter13SmoothHighDegreePushforwardData C L d) := by
  sorry

/-- In the high-degree smooth range the degree-zero term commutes with all base changes. -/
theorem chapter13_smooth_high_degree_pushforward_commutes_with_base_change
    (C : Chapter13SmoothProperCurve)
    (deg : Chapter13FiberDegreeTheory C.toChapter13RelativeCurve)
    (L : Chapter04LineBundle C.X) (d : ℤ)
    (hd : chapter13LineBundleOfRelativeDegree deg L d)
    (hdegree : ∀ s : C.S, 2 * (C.genus : ℤ) - 2 < d) :
    chapter13PushforwardCommutesWithArbitraryBaseChange
      (C := C.toChapter13RelativeCurve) L := by
  sorry

/-- Relative generation in the degree range `d ≥ 2g`. -/
theorem chapter13_smooth_degree_two_genus_evaluation_surjective
    (C : Chapter13SmoothProperCurve)
    (deg : Chapter13FiberDegreeTheory C.toChapter13RelativeCurve)
    (L : Chapter04LineBundle C.X) (d : ℤ)
    (hd : chapter13LineBundleOfRelativeDegree deg L d)
    (hdegree : ∀ s : C.S, 2 * (C.genus : ℤ) ≤ d)
    (H : Chapter13RelativeLineCohomologyData C.toChapter13RelativeCurve L) :
    chapter04SheafSurjective (chapter04EvaluationMap C.f L.sheaf) := by
  sorry

/-! ### Length-two separation -/

/-- A finite flat length-two subscheme in a relative curve. -/
structure Chapter13RelativeLengthTwoSubscheme (C : Chapter13RelativeCurve) where
  Z : Scheme
  inclusion : Z ⟶ C.X
  closed : IsClosedImmersion inclusion
  projection : Z ⟶ C.S
  over : inclusion ≫ C.f = projection
  finite_locally_free : Chapter10FiniteLocallyFreeProfile projection 2

/-- Restriction of global sections to a relative length-two subscheme. -/
def chapter13LengthTwoRestriction
    {C : Chapter13RelativeCurve} (L : Chapter04LineBundle C.X)
    (Z : Chapter13RelativeLengthTwoSubscheme C) :
    L.sheaf.sections →
      ((Scheme.Modules.pullback Z.inclusion).obj L.sheaf).sections :=
  (chapter04PullbackSectionData Z.inclusion L.sheaf).map

/-- Relative separation of all length-two divisors. -/
def chapter13SeparatesEveryLengthTwo
    {C : Chapter13RelativeCurve} (L : Chapter04LineBundle C.X) : Prop :=
  ∀ Z : Chapter13RelativeLengthTwoSubscheme C,
    Function.Surjective (chapter13LengthTwoRestriction L Z)

/-- Degree at least `2g+1` separates every relative length-two divisor. -/
theorem chapter13_smooth_degree_two_genus_plus_one_separates_length_two
    (C : Chapter13SmoothProperCurve)
    (deg : Chapter13FiberDegreeTheory C.toChapter13RelativeCurve)
    (L : Chapter04LineBundle C.X) (d : ℤ)
    (hd : chapter13LineBundleOfRelativeDegree deg L d)
    (hdegree : ∀ s : C.S, 2 * (C.genus : ℤ) + 1 ≤ d)
    (H : Chapter13RelativeLineCohomologyData C.toChapter13RelativeCurve L) :
    chapter13SeparatesEveryLengthTwo (C := C.toChapter13RelativeCurve) L := by
  sorry

/-- The same high-degree hypothesis yields a relative very-ample embedding. -/
theorem chapter13_smooth_degree_two_genus_plus_one_is_very_ample
    (C : Chapter13SmoothProperCurve)
    (deg : Chapter13FiberDegreeTheory C.toChapter13RelativeCurve)
    (L : Chapter04LineBundle C.X) (d : ℤ)
    (hd : chapter13LineBundleOfRelativeDegree deg L d)
    (hdegree : ∀ s : C.S, 2 * (C.genus : ℤ) + 1 ≤ d)
    (H : Chapter13RelativeLineCohomologyData C.toChapter13RelativeCurve L) :
    chapter04VeryAmple C.f L := by
  sorry

/-! ### Nodal and reducible fibers -/

/-- A connected union of irreducible components of a geometric fiber. -/
structure Chapter13ConnectedComponentUnion
  (C : Chapter13RelativeCurve) (s : C.S) where
  Z : Scheme
  inclusion : Z ⟶ C.f.fiber s
  closed : IsClosedImmersion inclusion
  connected : _root_.IsConnected (Set.univ : Set Z)
  nonempty : Nonempty Z
  is_union_of_components : Prop
  is_union_of_components_holds : is_union_of_components
  is_whole_fiber : Prop
  is_whole_fiber_holds : is_whole_fiber
  boundary_branches : ℕ
  arithmetic_genus : ℕ
  degree_on_union : Chapter04LineBundle Z → ℤ
  canonical_degree : ℤ
  canonical_degree_formula :
    canonical_degree = 2 * (arithmetic_genus : ℤ) - 2 + boundary_branches

def chapter13ComponentDegree
    {C : Chapter13RelativeCurve} {s : C.S}
    (Z : Chapter13ConnectedComponentUnion C s)
    (L : Chapter04LineBundle (C.f.fiber s)) : ℤ :=
  Z.degree_on_union (chapter04PullbackLineBundle Z.inclusion L)

/-- Componentwise positivity of a line bundle on a fiber. -/
def chapter13ComponentwisePositiveOnFiber
    {C : Chapter13RelativeCurve} (s : C.S)
    (L : Chapter04LineBundle C.X)
    (components : Set (Chapter13ConnectedComponentUnion C s)) : Prop :=
  ∀ Z ∈ components,
    2 * (Z.arithmetic_genus : ℤ) - 2 <
      chapter13ComponentDegree Z (chapter13FiberLineBundle L s)

/-- The canonical bundle degree after removing the forced boundary zeros. -/
def chapter13InducedCanonicalSectionDegree
    {C : Chapter13RelativeCurve} {s : C.S}
    (Z : Chapter13ConnectedComponentUnion C s) : ℤ :=
  Z.canonical_degree - Z.boundary_branches

theorem chapter13_induced_canonical_section_degree_formula
    {C : Chapter13RelativeCurve} {s : C.S}
    (Z : Chapter13ConnectedComponentUnion C s) :
    chapter13InducedCanonicalSectionDegree Z =
      2 * (Z.arithmetic_genus : ℤ) - 2 := by
  simp [chapter13InducedCanonicalSectionDegree, Z.canonical_degree_formula]

/-- A componentwise bound forces the duality-twisted section degree to be negative. -/
theorem chapter13_componentwise_bound_forces_negative_twisted_degree
    {C : Chapter13RelativeCurve} {s : C.S}
    (Z : Chapter13ConnectedComponentUnion C s)
    (L : Chapter04LineBundle (C.f.fiber s))
    (hdegree : 2 * (Z.arithmetic_genus : ℤ) - 2 < chapter13ComponentDegree Z L) :
    chapter13InducedCanonicalSectionDegree Z - chapter13ComponentDegree Z L < 0 := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the pinned snapshot has no single predicate for a
family whose geometric fibers are nodal or reducible, nor a degree API for a
line bundle restricted to a connected union of components. -/

/-- A line-bundle cohomology package equipped with componentwise control. -/
structure Chapter13NodalVanishingData
    (C : Chapter13RelativeCurve) (L : Chapter04LineBundle C.X) where
  nodal_or_reducible_fibers : Prop
  nodal_or_reducible_fibers_holds : nodal_or_reducible_fibers
  relative_cohomology : Chapter13RelativeLineCohomologyData C L
  relative_dualizing : Chapter13RelativeDualizingData C
  components : ∀ s : C.S, Set (Chapter13ConnectedComponentUnion C s)
  components_complete : ∀ s Z, Z ∈ components s
  componentwise_bound : ∀ s, chapter13ComponentwisePositiveOnFiber s L (components s)
  includes_whole_fiber : ∀ s Z, Z.is_whole_fiber → Z ∈ components s
  component_dualizing : ∀ (s : C.S) (Z : Chapter13ConnectedComponentUnion C s),
    Chapter04LineBundle Z.Z
  component_dualizing_restriction : ∀ (s : C.S)
      (Z : Chapter13ConnectedComponentUnion C s),
    Nonempty (
      (chapter04PullbackLineBundle Z.inclusion
        (chapter04PullbackLineBundle (C.f.fiberι s) relative_dualizing.line_bundle)).sheaf ≅
      (component_dualizing s Z).sheaf)
  component_canonical_degree : ∀ (s : C.S)
      (Z : Chapter13ConnectedComponentUnion C s),
    Z.canonical_degree = Z.degree_on_union (component_dualizing s Z)

/-- Componentwise positivity implies `H¹ = 0` on nodal or reducible fibers. -/
theorem chapter13_componentwise_bound_gives_h1_vanishing
    {C : Chapter13RelativeCurve} {L : Chapter04LineBundle C.X}
    (D : Chapter13NodalVanishingData C L) :
    chapter13FirstHigherDirectImageIsZero D.relative_cohomology := by
  sorry

/-- Total degree alone does not provide componentwise positivity. -/
def chapter13TotalDegreeBoundInsufficientForReducibleFibers : Prop :=
  ∃ (a b : ℤ) (g₁ g₂ : ℕ),
    0 < a + b ∧
      a + b > 2 * ((g₁ + g₂ : ℕ) : ℤ) - 2 ∧
      a ≤ 2 * (g₁ : ℤ) - 2

/-- A positive total degree can coexist with a component at the critical bound. -/
theorem chapter13_total_degree_alone_is_insufficient :
    chapter13TotalDegreeBoundInsufficientForReducibleFibers := by
  sorry

/-- The componentwise criterion explicitly includes the whole fiber. -/
def chapter13ComponentwiseCriterionIncludesWholeFiber
    {C : Chapter13RelativeCurve}
    (s : C.S) (components : Set (Chapter13ConnectedComponentUnion C s)) : Prop :=
  ∀ Z, Z.is_whole_fiber → Z ∈ components

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter13
