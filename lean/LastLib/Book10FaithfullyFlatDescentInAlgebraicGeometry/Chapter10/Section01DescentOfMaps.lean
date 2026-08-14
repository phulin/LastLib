import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Dependencies

/-!
## 10.1 Descent of maps

The declarations in this file expose the equalizer, saturated-open, section, and automorphism
forms of morphism descent.  The proofs are intentionally left for the later compilation pass.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u v

/-- The Hom sequence over an fpqc cover is an equalizer. -/
theorem chapter10_hom_equalizer {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) (X Y : Chapter10SchemeOver S) :
    IsLimit (chapter10HomEqualizerFork p X Y) := by
  sorry

/-- A map on the cover descends exactly when its two pullbacks to the double overlap agree. -/
theorem chapter10_morphism_descends_iff {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) (X Y : Chapter10SchemeOver S)
    (u : chapter10BaseChangeOver p X ⟶ chapter10BaseChangeOver p Y) :
    (∃ f : chapter10OverHom X Y, chapter10BaseChangeOverHom p f = u) ↔
      chapter10DescentCompatible p u := by
  sorry

/-- The descended map is unique. -/
theorem chapter10_morphism_descends_unique {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) (X Y : Chapter10SchemeOver S)
    {f g : chapter10OverHom X Y}
    (hfg : chapter10BaseChangeOverHom p f = chapter10BaseChangeOverHom p g) :
    f = g := by
  sorry

/-- The affine case is algebra descent with arrows reversed. -/
theorem chapter10_affine_morphism_descent {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) (X Y : Chapter10SchemeOver S)
    (hS : IsAffine S) (hX : IsAffine X.scheme) (hY : IsAffine Y.scheme)
    (u : chapter10BaseChangeOver p X ⟶ chapter10BaseChangeOver p Y)
    (hu : chapter10DescentCompatible p u) :
    ∃! f : chapter10OverHom X Y, chapter10BaseChangeOverHom p f = u := by
  sorry

/-- If only the target is affine, maps can be checked on affine opens of the source. -/
theorem chapter10_affine_target_morphism_descent {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) (X Y : Chapter10SchemeOver S)
    (hY : IsAffine Y.scheme)
    (u : chapter10BaseChangeOver p X ⟶ chapter10BaseChangeOver p Y)
    (hu : chapter10DescentCompatible p u) :
    ∃! f : chapter10OverHom X Y, chapter10BaseChangeOverHom p f = u := by
  sorry

/-- A surjective fpqc morphism is a quotient map on underlying spaces. -/
def chapter10QuotientMap {Z' Z : Scheme.{u}} (q : Z' ⟶ Z) : Prop :=
  Topology.IsQuotientMap q.base

theorem chapter10_fpqc_isQuotientMap {Z' Z : Scheme.{u}} (q : Z' ⟶ Z)
    (hq : Chapter10FpqcCover q) : chapter10QuotientMap q := by
  sorry

/-- Openness is detected by an fpqc quotient map. -/
theorem chapter10_open_iff_preimage_open {Z' Z : Scheme.{u}} (q : Z' ⟶ Z)
    (hq : Chapter10FpqcCover q) (U : Set Z) :
    IsOpen U ↔ IsOpen (q.base ⁻¹' U) := by
  sorry

/-- An open of the cover is saturated when its two inverse images on the overlap agree. -/
def chapter10SaturatedOpen {Z' Z : Scheme.{u}} (q : Z' ⟶ Z) (U' : Z'.Opens) : Prop :=
  (pullback.fst q q ⁻¹ᵁ U') = (pullback.snd q q ⁻¹ᵁ U')

/-- Every saturated open upstairs descends to a unique open downstairs. -/
theorem chapter10_saturated_open_descends {Z' Z : Scheme.{u}} (q : Z' ⟶ Z)
    (hq : Chapter10FpqcCover q) (U' : Z'.Opens) (hU' : chapter10SaturatedOpen q U') :
    ∃! U : Z.Opens, q ⁻¹ᵁ U = U' := by
  sorry

/-- General morphism descent, after descending the affine-open pieces of the target and gluing. -/
theorem chapter10_morphism_descent {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) (X Y : Chapter10SchemeOver S)
    (u : chapter10BaseChangeOver p X ⟶ chapter10BaseChangeOver p Y)
    (hu : chapter10DescentCompatible p u) :
    ∃! f : chapter10OverHom X Y, chapter10BaseChangeOverHom p f = u := by
  sorry

/-- A section of a morphism, bundled with its section identity. -/
structure Chapter10Section {X S : Scheme.{u}} (f : X ⟶ S) where
  hom : S ⟶ X
  isSection : hom ≫ f = 𝟙 S

/-- Pull a section back along a map to the base. -/
def chapter10PullbackSection {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (s : Chapter10Section f) : Chapter10Section (chapter10BaseChangeMorphism f p) where
  hom := pullback.lift (p ≫ s.hom) (𝟙 T) (by
    rw [Category.assoc, s.isSection, Category.comp_id])
  isSection := by simp

/-- The section-overlap condition can be tested after projecting the two pulled-back sections to
the original source `X`. -/
def chapter10SectionDescentCompatible {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (sT : Chapter10Section (chapter10BaseChangeMorphism f p)) : Prop :=
  chapter10DoubleOverlapFirst p ≫ sT.hom ≫ chapter10BaseChangeToSource f p =
    chapter10DoubleOverlapSecond p ≫ sT.hom ≫ chapter10BaseChangeToSource f p

/-- Sections form a sheaf for an fpqc cover. -/
theorem chapter10_section_descent {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) (sT : Chapter10Section (chapter10BaseChangeMorphism f p))
    (hs : chapter10SectionDescentCompatible f p sT) :
    ∃! s : Chapter10Section f, (chapter10PullbackSection f p s).hom = sT.hom := by
  sorry

/-- The overlap criterion for sections is equivalent to existence and uniqueness downstairs. -/
theorem chapter10_section_descent_iff {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) (sT : Chapter10Section (chapter10BaseChangeMorphism f p)) :
    chapter10SectionDescentCompatible f p sT ↔
      ∃! s : Chapter10Section f, (chapter10PullbackSection f p s).hom = sT.hom := by
  sorry

/-- Automorphisms over a base, expressed as isomorphisms in the over category. -/
abbrev Chapter10Automorphism {S : Scheme.{u}} (X : Chapter10SchemeOver S) :=
  chapter10OverObject X ≅ chapter10OverObject X

/-- Base change of an automorphism. -/
def chapter10PullbackAutomorphism {S T : Scheme.{u}} (p : T ⟶ S)
    {X : Chapter10SchemeOver S} (a : Chapter10Automorphism X) :
    chapter10BaseChangeOver p X ≅ chapter10BaseChangeOver p X :=
  (Over.pullback p).mapIso a

/-- Compatibility of an upstairs automorphism with the canonical comparison of the two overlap
pullbacks. -/
def chapter10AutomorphismDescentCompatible {S T : Scheme.{u}} (p : T ⟶ S)
    {X : Chapter10SchemeOver S}
    (aT : chapter10BaseChangeOver p X ≅ chapter10BaseChangeOver p X) : Prop :=
  chapter10OverlapFirstHom p (X := X) (Y := X) aT.hom ≫
      (chapter10DoubleOverlapComparison p X).hom =
    (chapter10DoubleOverlapComparison p X).hom ≫
      chapter10OverlapSecondHom p (X := X) (Y := X) aT.hom

/-- Compatibility is closed under taking inverses. -/
theorem chapter10_automorphism_inverse_compatible {S T : Scheme.{u}} (p : T ⟶ S)
    {X : Chapter10SchemeOver S}
    (aT : chapter10BaseChangeOver p X ≅ chapter10BaseChangeOver p X)
    (ha : chapter10AutomorphismDescentCompatible p aT) :
    chapter10AutomorphismDescentCompatible p aT.symm := by
  sorry

/-- Compatible automorphisms descend, and their inverses descend at the same time. -/
theorem chapter10_automorphism_descent {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) {X : Chapter10SchemeOver S}
    (aT : chapter10BaseChangeOver p X ≅ chapter10BaseChangeOver p X)
    (ha : chapter10AutomorphismDescentCompatible p aT) :
    ∃! a : Chapter10Automorphism X, chapter10PullbackAutomorphism p a = aT := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10
