import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/-! ## 4.2. Very ampleness as separation -/

/-- The generation condition on a finite section system, exposed independently of separation. -/
def chapter04SectionSystemGenerates
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of K)} {L : Chapter04LineBundle X}
    (V : Chapter04FiniteSectionSystem K f L) : Prop :=
  Epi (L.sheaf.freeHomEquiv.symm (fun i => V.sectionMap i))

theorem chapter04SectionSystem_generates
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of K)} {L : Chapter04LineBundle X}
    (V : Chapter04FiniteSectionSystem K f L) :
    chapter04SectionSystemGenerates V :=
  V.generates

theorem chapter04_section_system_restriction_agrees_with_pullback_data
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of K)} {L : Chapter04LineBundle X}
    (V : Chapter04FiniteSectionSystem K f L)
    (Z : Chapter04LengthTwoClosedSubscheme K f) (i : V.I) :
    V.restriction Z i =
      (chapter04PullbackSectionData Z.inclusion L.sheaf).map (V.sectionMap i) :=
  V.restriction_eq Z i

/-- Separation of points and tangent directions is surjectivity on every length-two subscheme. -/
theorem chapter04_separates_length_two_of_restriction_surjective
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of K)} {L : Chapter04LineBundle X}
    (V : Chapter04FiniteSectionSystem K f L)
    (hV : chapter04SeparatesLengthTwoOverBase V) :
    ∀ Z : Chapter04LengthTwoClosedSubscheme K f,
      Function.Surjective (V.restriction Z) :=
  hV

/-! An induced projective map records the canonical pullback of the ambient
coordinate sections, so its immersion criterion is a statement about the
given section system rather than about unrelated restriction functions. -/
def chapter04SectionSystemMapCoordinateCompatible
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of K)} {L : Chapter04LineBundle X}
    (V : Chapter04FiniteSectionSystem K f L)
    (P : Chapter04ProjectiveBundle (AlgebraicGeometry.Spec (.of K)))
    (coordinateSections : V.I → P.tautological.val.sections)
    (u : X ⟶ P.space) : Prop :=
  u ≫ P.projection = f ∧
    ∃ e : (Scheme.Modules.pullback u).obj P.tautological ≅ L.sheaf,
      ∀ i,
        SheafOfModules.sectionsMap e.hom
          ((chapter04PullbackSectionData u P.tautological).map
            (coordinateSections i)) = V.sectionMap i

structure Chapter04InducedSectionSystemMap
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of K)} {L : Chapter04LineBundle X}
    (V : Chapter04FiniteSectionSystem K f L) where
  projectiveBundle : Chapter04ProjectiveBundle (AlgebraicGeometry.Spec (.of K))
  universalQuotientCompatible :
    chapter04ProjectiveBundleUniversalQuotientCompatible projectiveBundle
  map : X ⟶ projectiveBundle.space
  over : map ≫ projectiveBundle.projection = f
  pullback_iso : L.sheaf ≅
    (Scheme.Modules.pullback map).obj projectiveBundle.tautological
  coordinateSections : V.I → projectiveBundle.tautological.val.sections
  coordinate_sections_generate :
    Epi (projectiveBundle.tautological.freeHomEquiv.symm coordinateSections)
  section_compatibility : ∀ i,
    SheafOfModules.sectionsMap pullback_iso.symm.hom
      ((chapter04PullbackSectionData map projectiveBundle.tautological).map
        (coordinateSections i)) = V.sectionMap i
  map_is_unique_from_coordinates :
    ∀ u : X ⟶ projectiveBundle.space,
      chapter04SectionSystemMapCoordinateCompatible V projectiveBundle
        coordinateSections u →
      u = map

theorem chapter04_induced_section_system_map_exists
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of K)} {L : Chapter04LineBundle X}
    (V : Chapter04FiniteSectionSystem K f L)
    (hV : chapter04SectionSystemGenerates V) :
    Nonempty (Chapter04InducedSectionSystemMap V) := by
  sorry

noncomputable def chapter04InducedSectionSystemMap
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of K)} {L : Chapter04LineBundle X}
    (V : Chapter04FiniteSectionSystem K f L)
    (hV : chapter04SectionSystemGenerates V) :
    Chapter04InducedSectionSystemMap V :=
  Classical.choice (chapter04_induced_section_system_map_exists V hV)

theorem chapter04_induced_section_system_map_isImmersion_iff
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of K)} {L : Chapter04LineBundle X}
    [QuasiCompact f] [LocallyOfFiniteType f]
    (V : Chapter04FiniteSectionSystem K f L)
    (w : Chapter04InducedSectionSystemMap V) :
    IsImmersion w.map ↔
      chapter04SectionSystemGenerates V ∧ chapter04SeparatesLengthTwo V := by
  sorry

theorem chapter04_induced_section_system_map_isClosedImmersion_of_proper
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of K)} {L : Chapter04LineBundle X}
    [IsProper f] [QuasiCompact f]
    (V : Chapter04FiniteSectionSystem K f L)
    (w : Chapter04InducedSectionSystemMap V)
    (hV : chapter04SectionSystemGenerates V ∧ chapter04SeparatesLengthTwo V) :
    IsClosedImmersion w.map := by
  let : IsImmersion w.map :=
    (chapter04_induced_section_system_map_isImmersion_iff V w).2 hV
  have : IsProper (w.map ≫ w.projectiveBundle.projection) := by
    rw [w.over]
    infer_instance
  have : IsProper w.map := IsProper.of_comp w.map w.projectiveBundle.projection
  rw [IsClosedImmersion.iff_isProper_and_mono]
  exact ⟨inferInstance, inferInstance⟩

/-- Relative very ampleness descends along a faithfully flat quasi-compact base
change when the original morphism is qcqs and of finite presentation. -/
theorem chapter04_veryAmple_faithfullyFlat_descent
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (L : Chapter04LineBundle X)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hfp : LocallyOfFinitePresentation f)
    (hgflat : Flat g) (hgsurj : Surjective g) (hgqc : QuasiCompact g)
    (hL : chapter04VeryAmple (Limits.pullback.snd f g)
      (chapter04PullbackLineBundle (Limits.pullback.fst f g) L)) :
    chapter04VeryAmple f L := by
  sorry

/-- Immersions are detected after a faithfully flat quasi-compact base change
under the same qcqs finite-presentation hypotheses. -/
theorem chapter04_immersion_iff_faithfullyFlat_baseChange
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hfp : LocallyOfFinitePresentation f)
    (hgflat : Flat g) (hgsurj : Surjective g) (hgqc : QuasiCompact g) :
    IsImmersion f ↔ IsImmersion (Limits.pullback.snd f g) := by
  sorry

/-- The descent direction of the immersion criterion. -/
theorem chapter04_immersion_faithfullyFlat_descent
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hfp : LocallyOfFinitePresentation f)
    (hgflat : Flat g) (hgsurj : Surjective g) (hgqc : QuasiCompact g)
    (h : IsImmersion (Limits.pullback.snd f g)) :
    IsImmersion f := by
  exact (chapter04_immersion_iff_faithfullyFlat_baseChange f g
    hfqc hfqs hfp hgflat hgsurj hgqc).2 h

/-- A proper family turns the locally closed immersion from very ampleness into a closed immersion. -/
theorem chapter04_veryAmple_closed_immersion_of_proper
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (L : Chapter04LineBundle X) (w : Chapter04VeryAmpleWitness f L) :
    IsClosedImmersion w.map := by
  let : IsImmersion w.map := w.immersion
  have : IsProper (w.map ≫ w.projectiveBundle.projection) := by
    rw [w.over]
    infer_instance
  have : IsProper w.map := IsProper.of_comp w.map w.projectiveBundle.projection
  rw [IsClosedImmersion.iff_isProper_and_mono]
  exact ⟨inferInstance, inferInstance⟩

theorem chapter04_proper_veryAmple_is_projective
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (L : Chapter04LineBundle X) (hL : chapter04VeryAmple f L) :
    chapter04Projective f := by
  obtain ⟨w⟩ := hL
  exact ⟨{ projectiveBundle := w.projectiveBundle
           map := w.map
           closedImmersion := chapter04_veryAmple_closed_immersion_of_proper f L w
           over := w.over }⟩

/- The length-two condition simultaneously contains the reduced two-point
case and the doubled-point tangent-direction case.  The predicates below make
those two readings available to later chapters without replacing the single
scheme-theoretic criterion by a weaker pointwise slogan. -/

def chapter04SeparatesLengthTwoAt
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of K)} {L : Chapter04LineBundle X}
    (V : Chapter04FiniteSectionSystem K f L)
    (Z : Chapter04LengthTwoClosedSubscheme K f) : Prop :=
  Function.Surjective (V.restriction Z)

theorem chapter04_separates_length_two_iff_all_length_two_at
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of K)} {L : Chapter04LineBundle X}
    (V : Chapter04FiniteSectionSystem K f L) :
    chapter04SeparatesLengthTwoOverBase V ↔
      ∀ Z, chapter04SeparatesLengthTwoAt V Z := by
  rfl

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
