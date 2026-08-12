import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

/-! ## 4.3. The affine-open definition of ampleness -/

/-- The standard-open construction sends a relative very ample bundle to an ample one. -/
theorem chapter04_veryAmple_implies_ample
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X)
    (hL : chapter04VeryAmple f L) :
    chapter04Ample f L := by
  sorry

/-- A quasi-compact finite-type ample family has a positive power with a projective-space immersion. -/
theorem chapter04_ample_has_quasiProjective_power
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    (L : Chapter04LineBundle X) (hL : chapter04Ample f L) :
    ∃ d : ℕ, 0 < d ∧ chapter04VeryAmple f (chapter04LineBundleTensorPower L d) := by
  sorry

/-- In this chapter, a quasi-projective section-map witness is an immersion into a relative projective bundle. -/
def chapter04QuasiProjective
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X) : Prop :=
  chapter04VeryAmple f L

theorem chapter04_ample_power_gives_quasiProjective_immersion
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    (L : Chapter04LineBundle X) (hL : chapter04Ample f L) :
    ∃ d : ℕ, 0 < d ∧ chapter04QuasiProjective f (chapter04LineBundleTensorPower L d) := by
  simpa [chapter04QuasiProjective] using
    chapter04_ample_has_quasiProjective_power f L hL

/-- The trivial bundle is ample for an affine morphism: its unit section gives the whole space. -/
theorem chapter04_trivial_line_bundle_ample_of_affine
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] :
    chapter04Ample f (chapter04TrivialLineBundle X) := by
  sorry

/-- A proper non-affine variety cannot have the trivial bundle as an ample bundle. -/
theorem chapter04_trivial_line_bundle_not_ample_of_proper_nonAffine
    {K : Type u} [Field K] (X : Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (.of K)) [IsProper f]
    (hX : ¬ IsAffine X) :
    ¬ chapter04Ample f (chapter04TrivialLineBundle X) := by
  sorry

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
