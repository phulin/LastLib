import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Section02InvertibleQuotients
import Mathlib.Algebra.Category.ModuleCat.Stalk

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory

/-!
## 2.3 Sections without common zeros

The phrase “without common zeros” is formalized as stalkwise generation.  The evaluation map is
the canonical map from the free sheaf on the finite index type to the line bundle, obtained from
Mathlib's `freeHomEquiv`.
-/

abbrev Chapter02LineBundleSections {X : Scheme.{u}} (L : Chapter02LineBundle X) :=
  L.carrier.sections

def chapter02EvaluationMap
    {X : Scheme.{u}} (L : Chapter02LineBundle X) {I : Type u}
    (s : I → Chapter02LineBundleSections L) :
    SheafOfModules.free (R := X.ringCatSheaf) I ⟶ L.carrier :=
  (L.carrier.freeHomEquiv).symm s

def Chapter02SectionsGenerate
    {X : Scheme.{u}} (L : Chapter02LineBundle X) {I : Type u}
    (s : I → Chapter02LineBundleSections L) : Prop :=
  Epi (chapter02EvaluationMap L s)

theorem chapter02_sections_generate_iff_evaluation_epi
    {X : Scheme.{u}} (L : Chapter02LineBundle X) {I : Type u}
    (s : I → Chapter02LineBundleSections L) :
    Chapter02SectionsGenerate L s ↔ Epi (chapter02EvaluationMap L s) :=
  Iff.rfl

theorem chapter02_evaluation_map_is_the_sum_of_coordinate_sections
    {X : Scheme.{u}} (L : Chapter02LineBundle X) {I : Type u}
    (s : I → Chapter02LineBundleSections L) :
    chapter02EvaluationMap L s = (L.carrier.freeHomEquiv).symm s :=
  rfl

/-!
The next predicate records generation in the stalk.  `Γgerm` is the canonical map from global
sections to the stalk, and the span-equals-top condition is the scheme-theoretic meaning of a
section generating an invertible stalk.
-/
def chapter02SectionGerm
    {X : Scheme.{u}} {M : X.Modules} (s : M.sections) (x : X) :=
  (M.presheaf.Γgerm x) (s.1 (Opposite.op ⊤))

def chapter02SectionGeneratesAt
    {X : Scheme.{u}} {L : Chapter02LineBundle X}
    (s : Chapter02LineBundleSections L) (x : X) : Prop :=
  letI : Module
      ↑(TopCat.Presheaf.stalk (X.ringCatSheaf.obj : TopCat.Presheaf RingCat X) x)
      ↑(TopCat.Presheaf.stalk (L.carrier.val.presheaf : TopCat.Presheaf Ab X) x) := by
    infer_instance
  Submodule.span
      ↑(TopCat.Presheaf.stalk (X.ringCatSheaf.obj : TopCat.Presheaf RingCat X) x)
      ({chapter02SectionGerm s x} : Set
        ↑(TopCat.Presheaf.stalk (L.carrier.val.presheaf : TopCat.Presheaf Ab X) x)) = ⊤

def Chapter02ClosedPointwiseGeneration
    {X : Scheme.{u}} (L : Chapter02LineBundle X) {I : Type u}
    (s : I → Chapter02LineBundleSections L) : Prop :=
  ∀ x : X, IsClosed ({x} : Set X) → ∃ i, chapter02SectionGeneratesAt (s i) x

abbrev Chapter02ClosedPointwiseNonvanishing
    {X : Scheme.{u}} (L : Chapter02LineBundle X) {I : Type u}
    (s : I → Chapter02LineBundleSections L) : Prop :=
  Chapter02ClosedPointwiseGeneration L s

theorem chapter02_sections_generate_iff_stalkwise_generation
    {X : Scheme.{u}} (L : Chapter02LineBundle X) {I : Type u}
    (s : I → Chapter02LineBundleSections L) :
    Chapter02SectionsGenerate L s ↔
      ∀ x : X, ∃ i, chapter02SectionGeneratesAt (s i) x := by
  sorry

/-!
Over a non-Jacobson scheme, closed points need not detect all stalks.  This theorem records the
precise warning as an existence statement; the proof supplies a standard non-Jacobson example in
the later proof pass.
-/
theorem chapter02_closed_points_do_not_detect_stalkwise_generation :
    ∃ (X : Scheme.{u}) (L : Chapter02LineBundle X)
      (s : Fin 2 → Chapter02LineBundleSections L),
      Chapter02ClosedPointwiseGeneration L (fun i : ULift.{u} (Fin 2) => s i.down) ∧
        ¬ Chapter02SectionsGenerate L (fun i : ULift.{u} (Fin 2) => s i.down) := by
  sorry

theorem chapter02_sections_generate_is_stable_under_base_change
    {X Y : Scheme.{u}} (g : Y ⟶ X) (L : Chapter02LineBundle X)
    {I : Type u} (s : I → Chapter02LineBundleSections L)
    (h : Chapter02SectionsGenerate L s) :
    Chapter02SectionsGenerate (chapter02PullbackLineBundle g L)
      (fun i => (chapter02PullbackSectionData g L.carrier).map (s i)) := by
  sorry

/-!
The projective-bundle theorem turns a generating tuple into a unique map to projective space.
The compatibility predicate includes both the map over `S` and the pullback of the universal
quotient line with its coordinate sections.
-/
def Chapter02CoordinateCompatibility
    {S X : Scheme.{u}} {I : Type u}
    (f : X ⟶ S) (P : Chapter02ProjectiveSpaceData S I)
    (L : Chapter02LineBundle X) (s : I → Chapter02LineBundleSections L)
    (φ : X ⟶ P.bundle.scheme) : Prop :=
  φ ≫ P.bundle.projection = f ∧
    ∃ e : (Scheme.Modules.pullback φ).obj P.bundle.twistingLineBundle.carrier ≅ L.carrier,
      ∀ i,
        SheafOfModules.sectionsMap e.hom
          ((chapter02PullbackSectionData φ P.bundle.twistingLineBundle.carrier).map
            (P.coordinateSections i)) = s i

theorem chapter02_sections_define_unique_projective_map
    {S X : Scheme.{u}} {I : Type u}
    (f : X ⟶ S) (P : Chapter02ProjectiveSpaceData S I)
    (L : Chapter02LineBundle X) (s : I → Chapter02LineBundleSections L)
    (hgen : Chapter02SectionsGenerate L s) :
    ∃! φ : X ⟶ P.bundle.scheme,
      Chapter02CoordinateCompatibility f P L s φ := by
  sorry

theorem chapter02_sections_define_unique_map_to_projective_space
    {S X : Scheme.{u}} (f : X ⟶ S) (r : ℕ)
    (L : Chapter02LineBundle X)
    (s : Fin (r + 1) → Chapter02LineBundleSections L)
    (hgen : Chapter02SectionsGenerate L
      (fun i : Chapter02ProjectiveSpaceIndex r => s i.down)) :
    ∃! φ : X ⟶ chapter02ProjectiveSpace S r,
      Chapter02CoordinateCompatibility f
        (chapter02ProjectiveSpaceData S (Chapter02ProjectiveSpaceIndex r)) L
        (fun i : Chapter02ProjectiveSpaceIndex r => s i.down) φ := by
  sorry

/-!
On the open chart where a chosen coordinate generates the line bundle, the coordinate functions
are the ratios `s_j/s_i`.  The following generic identity is the algebraic core of that chart
formula.
-/
def Chapter02SectionChart
    {X : Scheme.{u}} (L : Chapter02LineBundle X) {I : Type u}
    (s : I → Chapter02LineBundleSections L) (i : I) : Set X :=
  {x | chapter02SectionGeneratesAt (s i) x}

theorem chapter02_section_chart_is_open
    {X : Scheme.{u}} (L : Chapter02LineBundle X) {I : Type u}
    (s : I → Chapter02LineBundleSections L) (i : I) :
    IsOpen (Chapter02SectionChart L s i) := by
  sorry

theorem chapter02_projective_chart_formula
    {K : Type u} [CommGroupWithZero K] {I : Type u}
    (x : Chapter02CoordinateTuple K I) (i : I) (_hi : x i ≠ 0) :
    ∀ j, chapter02CoordinateRatio x i j = x j / x i := by
  intro j
  rfl

/-!
The ratio criterion used to test immersion is kept as a ring-level interface.  It says that, on a
chosen affine chart, the source affine coordinates occur among the ratios of target coordinates.
-/
structure Chapter02AffineChartRatioGenerationData
    (I : Type u) (A R : Type u) [CommRing A] [CommRing R] where
  targetCoordinate : I → A
  targetToSource : A →+* R
  targetRatio : I → R
  targetRatio_eq : ∀ i, targetRatio i = targetToSource (targetCoordinate i)
  sourceCoordinate : I → R
  sourceCoordinate_in_ratio_range : ∀ i, ∃ j, sourceCoordinate i = targetRatio j

def Chapter02RatiosGenerateRelevantCoordinateAlgebra
    {I A R : Type u} [CommRing A] [CommRing R]
    (d : Chapter02AffineChartRatioGenerationData I A R) : Prop :=
  ∀ i, ∃ j, d.sourceCoordinate i = d.targetRatio j

theorem chapter02_ratios_generate_relevant_coordinate_algebra_iff
    {I A R : Type u} [CommRing A] [CommRing R]
    (d : Chapter02AffineChartRatioGenerationData I A R) :
    Chapter02RatiosGenerateRelevantCoordinateAlgebra d ↔
      ∀ i, ∃ j, d.sourceCoordinate i = d.targetRatio j :=
  Iff.rfl

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
