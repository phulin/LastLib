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

/-- Over a quasi-compact base, a quasi-compact finite-type ample family has a positive power with a projective-space immersion. -/
theorem chapter04_ample_has_quasiProjective_power
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiCompact f]
    [LocallyOfFiniteType f] [QuasiSeparated f]
    (L : Chapter04LineBundle X) (hL : chapter04Ample f L) :
    ∃ d : ℕ, 0 < d ∧ chapter04VeryAmple f (chapter04LineBundleTensorPower L d) := by
  sorry

/-- Quasi-projectivity is the existence of some relative projective immersion. -/
def chapter04QuasiProjective
    {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ L : Chapter04LineBundle X, chapter04VeryAmple f L

theorem chapter04_veryAmple_is_quasiProjective
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X)
    (hL : chapter04VeryAmple f L) :
    chapter04QuasiProjective f := by
  exact ⟨L, hL⟩

theorem chapter04_ample_power_gives_quasiProjective_immersion
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiCompact f]
    [LocallyOfFiniteType f] [QuasiSeparated f]
    (L : Chapter04LineBundle X) (hL : chapter04Ample f L) :
    ∃ d : ℕ, 0 < d ∧
      chapter04VeryAmple f (chapter04LineBundleTensorPower L d) ∧
      chapter04QuasiProjective f := by
  sorry

/-- The trivial bundle is ample for an affine morphism: its unit section gives the whole space. -/
theorem chapter04_trivial_line_bundle_ample_of_affine
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] :
    chapter04Ample f (chapter04TrivialLineBundle X) := by
  sorry

/-- A proper non-affine variety cannot have the trivial bundle as an ample bundle. -/
theorem chapter04_trivial_line_bundle_not_ample_of_proper_nonAffine
    {K : Type u} [Field K] (X : Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (.of K)) [IsProper f] [QuasiCompact f]
    (hX : ¬ IsAffine X) :
    ¬ chapter04Ample f (chapter04TrivialLineBundle X) := by
  sorry

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
