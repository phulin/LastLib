import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter13.Dependencies

/-!
## 13.2 Closed loci inside parameter spaces

The predicates in this section are deliberately quantified over arbitrary test
schemes.  Thus a locus interface records the scheme structure and its
infinitesimal test-scheme behavior, rather than only a set of geometric points.
-/

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter13

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

/-- The family over a test point of a universal family. -/
def chapter13TestFamilyProjection {H X T : Scheme}
    (U : Chapter13UniversalFamilyData H X) (t : T ⟶ H) :
    chapter13UniversalFamilyBaseChange U t ⟶ T :=
  pullback.snd U.projection t

/-- Schematic density of the universal family in its ambient scheme. -/
def chapter13UniversalFamilyMapIsSchemeTheoreticallyDominant {H X : Scheme}
    (U : Chapter13UniversalFamilyData H X) : Prop :=
  IsSchemeTheoreticallyDominant U.map

/-! ### Closed conditions -/

theorem chapter13_containment_is_closed {H X Z : Scheme}
    (U : Chapter13UniversalFamilyData H X) (j : Z ⟶ X)
    [IsClosedImmersion j] :
    Nonempty (Chapter13ClosedLocusData H (chapter13ContainsFixedSubscheme U j)) := by
  sorry

theorem chapter13_invariance_is_closed {H X : Scheme}
    (U : Chapter13UniversalFamilyData H X) (σ : X ⟶ X) :
    Nonempty (Chapter13ClosedLocusData H (chapter13InvariantUnder U σ)) := by
  sorry

theorem chapter13_incidence_is_closed {H X Z : Scheme}
    (U : Chapter13UniversalFamilyData H X) (j : Z ⟶ X)
    [IsClosedImmersion j] :
    Nonempty (Chapter13ClosedLocusData H (chapter13Incidence U j)) := by
  sorry

/-! ### Equality of maps and coefficient ideals -/

theorem chapter13_equality_of_maps_is_closed {H X Y : Scheme}
    (U : Chapter13UniversalFamilyData H X) (f g : X ⟶ Y)
    [Y.IsSeparated] :
    Nonempty (Chapter13ClosedLocusData H (chapter13UniversalFamilyMapsEqual U f g)) := by
  sorry

/-- A closed-locus datum detects the equation on every scheme-valued test point. -/
theorem chapter13_closed_locus_tests_schemes {H : Scheme}
    {Q : ∀ T : Scheme, (T ⟶ H) → Prop}
    (C : Chapter13ClosedLocusData H Q) (T : Scheme) (t : T ⟶ H) :
    Q T t ↔ ∃ q : T ⟶ chapter13ClosedLocus C,
      q ≫ chapter13ClosedLocusι C = t := by
  exact C.represents T t

theorem chapter13_coefficient_equation_is_scheme_theoretic
    {H : Scheme} {A B : H.Modules} (φ : A ⟶ B) :
    chapter13SheafEquation φ ↔ φ = 0 :=
  chapter13SheafEquation_iff φ

/-! ### Open conditions -/

theorem chapter13_avoidance_is_open {H X Z : Scheme}
    (U : Chapter13UniversalFamilyData H X) (j : Z ⟶ X)
    [IsClosedImmersion j] :
    Nonempty (Chapter13OpenLocusData H (chapter13Avoids U j)) := by
  sorry

def chapter13SmoothFiberCondition {H X : Scheme}
    (U : Chapter13UniversalFamilyData H X) (T : Scheme) (t : T ⟶ H) : Prop :=
  chapter13SmoothFibers (chapter13TestFamilyProjection U t)

def chapter13GeometricallyReducedFiberCondition {H X : Scheme}
    (U : Chapter13UniversalFamilyData H X) (T : Scheme) (t : T ⟶ H) : Prop :=
  chapter13GeometricallyReducedFibers (chapter13TestFamilyProjection U t)

theorem chapter13_smooth_fibers_is_open {H X : Scheme}
    (U : Chapter13UniversalFamilyData H X) :
    Nonempty (Chapter13OpenLocusData H (chapter13SmoothFiberCondition U)) := by
  sorry

theorem chapter13_geometrically_reduced_fibers_is_open {H X : Scheme}
    (U : Chapter13UniversalFamilyData H X) :
    Nonempty (Chapter13OpenLocusData H
      (chapter13GeometricallyReducedFiberCondition U)) := by
  sorry

/-!
The graph condition is the open condition of Section 13.1: after the fixed
polynomial Hilbert scheme has been chosen, it is represented by the open graph
locus whose defining map is `chapter13GraphParameterSpaceToHilbert`.
-/

/-! ### Locally closed conditions -/

def chapter13ClosedOpenCondition {H : Scheme}
    {Q : ∀ T : Scheme, (T ⟶ H) → Prop}
    (C : Chapter13ClosedLocusData H Q)
    (R : ∀ T : Scheme, (T ⟶ chapter13ClosedLocus C) → Prop)
    (T : Scheme) (t : T ⟶ H) : Prop :=
  ∃ q : T ⟶ chapter13ClosedLocus C,
    q ≫ chapter13ClosedLocusι C = t ∧ R T q

def chapter13LocallyClosedFromClosedOpen {H : Scheme}
    {Q : ∀ T : Scheme, (T ⟶ H) → Prop}
    (C : Chapter13ClosedLocusData H Q)
    {R : ∀ T : Scheme, (T ⟶ chapter13ClosedLocus C) → Prop}
    (O : Chapter13OpenLocusData (chapter13ClosedLocus C) R) :
    Chapter13LocallyClosedLocusData H (chapter13ClosedOpenCondition C R) where
  ideal := C.ideal
  locus := O.locus
  represents := by
    intro T t
    sorry

theorem chapter13_locally_closed_from_closed_open_is_open_after_closed
    {H : Scheme} {Q : ∀ T : Scheme, (T ⟶ H) → Prop}
    (C : Chapter13ClosedLocusData H Q)
    {R : ∀ T : Scheme, (T ⟶ chapter13ClosedLocus C) → Prop}
    (O : Chapter13OpenLocusData (chapter13ClosedLocus C) R) :
    IsOpenImmersion O.locus.ι := by
  infer_instance

/-! ### Infinitesimal test schemes -/

theorem chapter13_locus_representation_is_not_pointwise
    {H : Scheme} {Q : ∀ T : Scheme, (T ⟶ H) → Prop}
    (C : Chapter13ClosedLocusData H Q) :
    ∀ (T : Scheme) (t : T ⟶ H),
      Q T t ↔ ∃ q : T ⟶ chapter13ClosedLocus C,
        q ≫ chapter13ClosedLocusι C = t := by
  intro T t
  exact C.represents T t

/-!
SOURCE_NOTE: the prose uses "schematically dense fibers" without fixing a
book-level predicate.  The API records the canonical
`IsSchemeTheoreticallyDominant` condition for the universal family map in
`chapter13UniversalFamilyMapIsSchemeTheoreticallyDominant`.
-/

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter13
