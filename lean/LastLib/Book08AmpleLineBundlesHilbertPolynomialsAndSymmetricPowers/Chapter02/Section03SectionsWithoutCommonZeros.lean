import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Section01ProjectiveBundles
import Mathlib.Algebra.Category.ModuleCat.Stalk

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory

/-!
## 2.3 Sections without common zeros

The phrase “without common zeros” is formalized as stalkwise generation.  The evaluation map is
the canonical map from the free sheaf on the chosen index type to the line bundle, obtained from
Mathlib's `freeHomEquiv`; finite index types recover the displayed finite tuples.
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
The following auxiliary predicate records only the weaker test on closed points.  It is not the
definition of generation: nonclosed points can carry information that closed points do not detect.
The `Γgerm` map is canonical, and the span-equals-top condition is the scheme-theoretic meaning of a
section generating an invertible stalk.
-/
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
The free presentation has to be transported across base change.  Merely pulling back the old
evaluation map gives an epimorphism from the pulled-back free sheaf, but the book's statement is
generation by the pulled-back sections, whose canonical source is the free sheaf on the target.
The comparison in `Dependencies.lean` records this replacement of presentations.
-/
def chapter02PullbackEvaluationMap
    {X Y : Scheme.{u}} (g : Y ⟶ X) (L : Chapter02LineBundle X)
    {I : Type u} (s : I → Chapter02LineBundleSections L) :
    SheafOfModules.free (R := Y.ringCatSheaf) I ⟶
      (Scheme.Modules.pullback g).obj L.carrier :=
  (chapter02FreePullbackComparisonData g I).comparison.hom ≫
    (Scheme.Modules.pullback g).map (chapter02EvaluationMap L s)

def Chapter02PullbackEvaluationIsEpi
    {X Y : Scheme.{u}} (g : Y ⟶ X) (L : Chapter02LineBundle X)
    {I : Type u} (s : I → Chapter02LineBundleSections L) : Prop :=
  Epi (chapter02PullbackEvaluationMap g L s)

theorem chapter02_sections_generate_is_stable_under_base_change
    {X Y : Scheme.{u}} (g : Y ⟶ X) (L : Chapter02LineBundle X)
    {I : Type u} (s : I → Chapter02LineBundleSections L)
    (h : Chapter02SectionsGenerate L s) :
    Chapter02PullbackEvaluationIsEpi g L s := by
  let e := (chapter02FreePullbackComparisonData g I).comparison
  have he : Epi e.hom := @IsIso.epi_of_iso _ _ _ _ e.hom e.isIso_hom
  exact epi_comp' he
    (@Functor.map_epi _ _ _ _ (Scheme.Modules.pullback g)
      (Functor.preservesEpimorphisms_of_adjunction
        (Scheme.Modules.pullbackPushforwardAdjunction g))
      _ _ (chapter02EvaluationMap L s) h)

theorem chapter02_pullback_evaluation_map_on_sections
    {X Y : Scheme.{u}} (g : Y ⟶ X) (L : Chapter02LineBundle X)
    {I : Type u} (s : I → Chapter02LineBundleSections L) (i : I) :
      ((Scheme.Modules.pullback g).obj L.carrier).freeHomEquiv
        (chapter02PullbackEvaluationMap g L s) i =
      chapter02PullbackSectionMap g L.carrier (s i) := by
  change SheafOfModules.sectionsMap ((Scheme.Modules.pullback g).map (chapter02EvaluationMap L s))
    (((Scheme.Modules.pullback g).obj (chapter02FreeQuasiCoherentModule X I).carrier).freeHomEquiv
      (chapter02FreePullbackComparisonData g I).comparison.hom i) =
    chapter02PullbackSectionMap g L.carrier (s i)
  rw [show (((Scheme.Modules.pullback g).obj (chapter02FreeQuasiCoherentModule X I).carrier).freeHomEquiv
      (chapter02FreePullbackComparisonData g I).comparison.hom i) =
      SheafOfModules.sectionsMap (chapter02FreePullbackComparisonData g I).comparison.hom
        (SheafOfModules.freeSection (R := Y.ringCatSheaf) i) from rfl]
  rw [(chapter02FreePullbackComparisonData g I).comparison_sections i]
  have hn := chapter02_pullback_section_map_natural
    (M := (chapter02FreeQuasiCoherentModule X I).carrier) (N := L.carrier)
    g (chapter02EvaluationMap L s) (SheafOfModules.freeSection (R := X.ringCatSheaf) i)
  exact hn.symm.trans (congrArg (chapter02PullbackSectionMap g L.carrier)
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection s i))

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
          (chapter02PullbackSectionMap φ P.bundle.twistingLineBundle.carrier
            (P.coordinateSections i)) = s i

theorem chapter02_sections_define_unique_projective_map
    {S X : Scheme.{u}} {I : Type u}
    (f : X ⟶ S) (P : Chapter02ProjectiveSpaceData S I)
    (L : Chapter02LineBundle X) (s : I → Chapter02LineBundleSections L)
    (hgen : Chapter02SectionsGenerate L s) :
    ∃! φ : X ⟶ P.bundle.scheme,
      Chapter02CoordinateCompatibility f P L s φ := by
  sorry

/-! Choose the universal coordinate map only after the stalkwise generation witness is supplied;
the specification and uniqueness declarations keep this choice usable without exposing a second
projective-map construction. -/
noncomputable def chapter02SectionsProjectiveMap
    {S X : Scheme.{u}} {I : Type u}
    (f : X ⟶ S) (P : Chapter02ProjectiveSpaceData S I)
    (L : Chapter02LineBundle X) (s : I → Chapter02LineBundleSections L)
    (hgen : Chapter02SectionsGenerate L s) : X ⟶ P.bundle.scheme :=
  Classical.choose
    (chapter02_sections_define_unique_projective_map f P L s hgen).exists

theorem chapter02SectionsProjectiveMap_spec
    {S X : Scheme.{u}} {I : Type u}
    (f : X ⟶ S) (P : Chapter02ProjectiveSpaceData S I)
    (L : Chapter02LineBundle X) (s : I → Chapter02LineBundleSections L)
    (hgen : Chapter02SectionsGenerate L s) :
    Chapter02CoordinateCompatibility f P L s
      (chapter02SectionsProjectiveMap f P L s hgen) := by
  sorry

theorem chapter02SectionsProjectiveMap_unique
    {S X : Scheme.{u}} {I : Type u}
    (f : X ⟶ S) (P : Chapter02ProjectiveSpaceData S I)
    (L : Chapter02LineBundle X) (s : I → Chapter02LineBundleSections L)
    (hgen : Chapter02SectionsGenerate L s)
    {φ : X ⟶ P.bundle.scheme}
    (hφ : Chapter02CoordinateCompatibility f P L s φ) :
    φ = chapter02SectionsProjectiveMap f P L s hgen := by
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
    (x : Chapter02CoordinateTuple K I) (i : I) (hi : x i ≠ 0) :
    ∀ j, chapter02CoordinateRatio x i j * x i = x j := by
  intro j
  exact chapter02CoordinateRatio_mul_denominator x i j hi

/-!
The ratio criterion used to test immersion is kept as a ring-level interface.  It says that, on a
chosen affine chart, the source affine coordinates occur among the ratios of target coordinates.
-/
structure Chapter02AffineChartRatioGenerationData
    (B I A R : Type u) [CommRing B] [CommRing A] [CommRing R]
    [Algebra B A] [Algebra B R] where
  targetCoordinate : I → A
  targetToSource : A →ₐ[B] R
  targetRatio : I → R
  targetRatio_eq : ∀ i, targetRatio i = targetToSource (targetCoordinate i)
  sourceCoordinate : I → R
  sourceCoordinate_in_ratio_range : ∀ i, ∃ j, sourceCoordinate i = targetRatio j
  sourceCoordinate_generate : Algebra.adjoin B (Set.range sourceCoordinate) = ⊤

def Chapter02RatiosGenerateRelevantCoordinateAlgebra
    {B I A R : Type u} [CommRing B] [CommRing A] [CommRing R]
    [Algebra B A] [Algebra B R]
    (d : Chapter02AffineChartRatioGenerationData B I A R) : Prop :=
  Algebra.adjoin B (Set.range d.targetRatio) = ⊤

theorem chapter02_ratios_generate_relevant_coordinate_algebra_iff
    {B I A R : Type u} [CommRing B] [CommRing A] [CommRing R]
    [Algebra B A] [Algebra B R]
    (d : Chapter02AffineChartRatioGenerationData B I A R) :
    Chapter02RatiosGenerateRelevantCoordinateAlgebra d ↔
      Algebra.adjoin B (Set.range d.targetRatio) = ⊤ :=
  Iff.rfl

theorem chapter02_ratios_generate_relevant_coordinate_algebra
    {B I A R : Type u} [CommRing B] [CommRing A] [CommRing R]
    [Algebra B A] [Algebra B R]
    (d : Chapter02AffineChartRatioGenerationData B I A R) :
    Chapter02RatiosGenerateRelevantCoordinateAlgebra d := by
  change Algebra.adjoin B (Set.range d.targetRatio) = ⊤
  apply le_antisymm
  · exact le_top
  · rw [← d.sourceCoordinate_generate]
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := d.sourceCoordinate_in_ratio_range i
    rw [hj]
    exact Algebra.subset_adjoin ⟨j, rfl⟩

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
