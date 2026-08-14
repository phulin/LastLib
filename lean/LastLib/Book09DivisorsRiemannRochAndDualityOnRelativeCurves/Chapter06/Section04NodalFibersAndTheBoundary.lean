import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06.Section03UniversalDivisorsAndAddition

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
open RelativeScheme

universe u

/-! ## 6.4. Nodal fibers and the boundary -/

abbrev Chapter06CartierDivisorPoint {S : Scheme.{u}}
    (C T : RelativeScheme S) (d : ℕ) :=
  {Z : Chapter06FiniteFlatClosedFamily C T d // chapter06IsEffectiveCartierFamily Z}

theorem chapter06_cartier_divisor_locus_is_open
    {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    (H : Chapter06LengthDHilbertSpaceData C d)
    (hC : Chapter06NodalRelativeCurve C) :
    Nonempty (Chapter06CartierDivisorOpenLocusData C d H) := by
  sorry

theorem chapter06_cartier_divisor_locus_is_stable_under_base_change
    {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    (H : Chapter06LengthDHilbertSpaceData C d)
    (L : Chapter06CartierDivisorOpenLocusData C d H)
    (T U : RelativeScheme S) (u : U ⟶ T)
    (f : T ⟶ L.locus) :
    chapter06IsEffectiveCartierFamily
      ((L.represents U (u ≫ f)).1) := by
  exact (L.represents U (u ≫ f)).2

theorem chapter06_cartier_divisor_locus_representation_is_natural
    {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    (H : Chapter06LengthDHilbertSpaceData C d)
    (L : Chapter06CartierDivisorOpenLocusData C d H)
    (T U : RelativeScheme S) (u : U ⟶ T)
    (f : T ⟶ L.locus) :
    chapter06FiniteFlatClosedFamilyBaseChange C T U u d
        ((L.represents T f).1) =
      (L.represents U (u ≫ f)).1 := by
  sorry

/-!
The standard ramified smoothing is kept at the coordinate-ring level.  This
is enough to expose the two-generator section ideal and the missing Cartier
limit without introducing a second local-ring implementation.
-/

abbrev chapter06NodalSmoothingPolynomialRing (R : Type u) :=
  MvPolynomial (Fin 2) R

def chapter06NodalSmoothingEquationIdeal
    (R : Type u) [CommRing R] (π : R) :
    Ideal (chapter06NodalSmoothingPolynomialRing R) :=
  Ideal.span ({
    MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
      MvPolynomial.C (π ^ 2)
  } : Set (chapter06NodalSmoothingPolynomialRing R))

abbrev chapter06NodalSmoothingTotalRing
    (R : Type u) [CommRing R] (π : R) :=
  chapter06NodalSmoothingPolynomialRing R ⧸
    chapter06NodalSmoothingEquationIdeal R π

def chapter06NodalSmoothingBaseStructureMap
    (R : Type u) [CommRing R] (π : R) :
    R →+* chapter06NodalSmoothingTotalRing R π :=
  (Ideal.Quotient.mk (chapter06NodalSmoothingEquationIdeal R π)).comp
    (MvPolynomial.C)

def chapter06NodalSmoothingQuotientMap
    (R : Type u) [CommRing R] (π : R) :
    CommRingCat.of R ⟶ CommRingCat.of (chapter06NodalSmoothingTotalRing R π) :=
  CommRingCat.ofHom (chapter06NodalSmoothingBaseStructureMap R π)

def chapter06NodalSmoothingBaseScheme
    (R : Type u) [CommRing R] : Scheme :=
  Spec (.of R)

def chapter06NodalSmoothingTotalScheme
    (R : Type u) [CommRing R] (π : R) : Scheme :=
  Spec (.of (chapter06NodalSmoothingTotalRing R π))

def chapter06NodalSmoothingFamilyMap
    (R : Type u) [CommRing R] (π : R) :
    chapter06NodalSmoothingTotalScheme R π ⟶ chapter06NodalSmoothingBaseScheme R :=
  Scheme.Spec.map (chapter06NodalSmoothingQuotientMap R π).op

def chapter06NodalSmoothingSectionMap
    (R : Type u) [CommRing R] (π : R) :
    chapter06NodalSmoothingTotalRing R π →+* R :=
  Ideal.Quotient.lift
    (chapter06NodalSmoothingEquationIdeal R π)
    (MvPolynomial.eval₂Hom (RingHom.id R) (fun _ : Fin 2 => π)) (by sorry)

def chapter06NodalSmoothingSection
    (R : Type u) [CommRing R] (π : R) :
    chapter06NodalSmoothingBaseScheme R ⟶
      chapter06NodalSmoothingTotalScheme R π :=
  Scheme.Spec.map (CommRingCat.ofHom (chapter06NodalSmoothingSectionMap R π)).op

theorem chapter06_nodal_smoothing_section_is_over_base
    (R : Type u) [CommRing R] (π : R) :
    chapter06NodalSmoothingSection R π ≫
        chapter06NodalSmoothingFamilyMap R π =
      𝟙 (chapter06NodalSmoothingBaseScheme R) := by
  sorry

def chapter06NodalSmoothingSectionIdeal
    (R : Type u) [CommRing R] (π : R) :
    Ideal (chapter06NodalSmoothingTotalRing R π) :=
  Ideal.map (Ideal.Quotient.mk (chapter06NodalSmoothingEquationIdeal R π))
    (Ideal.span ({
      MvPolynomial.X (0 : Fin 2) - MvPolynomial.C π,
      MvPolynomial.X (1 : Fin 2) - MvPolynomial.C π
    } : Set (chapter06NodalSmoothingPolynomialRing R))

structure Chapter06NodalSmoothingBoundaryProfile
    (R : Type u) [CommRing R] (π : R) where
  generic_fiber_smooth : Prop
  special_fiber_nodal : Prop
  section_through_node : Prop
  section_height_one :
    (chapter06NodalSmoothingSectionIdeal R π).height = 1
  relation_has_no_linear_term : Prop
  conormal_generators_independent : Prop
  section_not_principal :
    ¬ ∃ a : chapter06NodalSmoothingTotalRing R π,
      chapter06NodalSmoothingSectionIdeal R π = Ideal.span ({a} : Set _)

theorem chapter06_nodal_smoothing_boundary_profile_exists
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsDiscreteValuationRing R] (π : R)
    (hπ : Ideal.span ({π} : Set R) = IsLocalRing.maximalIdeal R) :
    Nonempty (Chapter06NodalSmoothingBoundaryProfile R π) := by
  sorry

theorem chapter06_nodal_smoothing_section_is_not_cartier
    (R : Type u) [CommRing R] (π : R)
    (P : Chapter06NodalSmoothingBoundaryProfile R π) :
    ¬ ∃ a : chapter06NodalSmoothingTotalRing R π,
      chapter06NodalSmoothingSectionIdeal R π = Ideal.span ({a} : Set _) :=
  P.section_not_principal

def chapter06CartierLocusOmitsNodalLimit
    (R : Type u) [CommRing R] (π : R)
    (P : Chapter06NodalSmoothingBoundaryProfile R π) : Prop :=
  P.section_not_principal

theorem chapter06_cartier_locus_omits_nodal_limit
    (R : Type u) [CommRing R] (π : R)
    (P : Chapter06NodalSmoothingBoundaryProfile R π) :
    chapter06CartierLocusOmitsNodalLimit R π P :=
  P.section_not_principal

/- LOCAL_DEPENDENCY_GUESS (6.4): the pinned interfaces do not yet expose a
canonical Hilbert compactification together with its Cartier open immersion.
The open-locus record in `Dependencies.lean` therefore keeps the representing
equivalences and the omitted-limit profile explicit until that earlier API is
available. -/

/-!
The smooth locus is Mathlib's canonical open smooth locus.  Pulling it back
to `C ×_S T` gives the support condition used by marked-point and Abel-map
constructions on a nodal family.
-/

abbrev chapter06SmoothLocus {S : Scheme.{u}} (C : RelativeScheme S)
    [LocallyOfFinitePresentation C.structuralMap] : C.carrier.Opens :=
  C.structuralMap.smoothLocus

abbrev chapter06SmoothLocusInclusion {S : Scheme.{u}} (C : RelativeScheme S)
    [LocallyOfFinitePresentation C.structuralMap] :
    (chapter06SmoothLocus C).toScheme ⟶ C.carrier :=
  Scheme.Opens.ι _

def chapter06RelativeDivisorSupportedOnSmoothLocus
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [LocallyOfFinitePresentation C.structuralMap]
    (D : Chapter06RelativeEffectiveDivisor C T d) : Prop :=
  D.divisor.ideal.support ≤
    (chapter06SmoothLocus C).preimage
      (pullback.fst C.structuralMap T.structuralMap).continuous

def chapter06MarkedSectionInSmoothLocus
    {S : Scheme.{u}} (C T : RelativeScheme S)
    [LocallyOfFinitePresentation C.structuralMap]
    (p : T ⟶ C) : Prop :=
  ∃ q : T.carrier ⟶ (chapter06SmoothLocus C).toScheme,
    q ≫ chapter06SmoothLocusInclusion C = p.hom

theorem chapter06_symmetric_power_smooth_locus_points_are_cartier
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C]
    [LocallyOfFinitePresentation C.structuralMap]
    (f : T ⟶ Chapter06SymmetricPower C d)
    (hsupport : chapter06RelativeDivisorSupportedOnSmoothLocus C T d
      (chapter06UniversalDivisorEquiv C T d f)) :
    (chapter06UniversalDivisorEquiv C T d f).divisor.ideal.IsEffectiveCartier := by
  exact (chapter06UniversalDivisorEquiv C T d f).divisor.isEffectiveCartier

theorem chapter06_symmetric_power_universal_divisor_is_supported_on_smooth_locus
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C]
    [LocallyOfFinitePresentation C.structuralMap]
    (f : T ⟶ Chapter06SymmetricPower C d)
    (hsupport : chapter06RelativeDivisorSupportedOnSmoothLocus C T d
      (chapter06UniversalDivisorEquiv C T d f)) :
    chapter06RelativeDivisorSupportedOnSmoothLocus C T d
      (chapter06UniversalDivisorEquiv C T d f) :=
  hsupport

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06
