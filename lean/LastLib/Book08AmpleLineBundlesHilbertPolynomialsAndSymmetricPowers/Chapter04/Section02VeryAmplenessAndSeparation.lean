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

/-- Separation of points and tangent directions is surjectivity on every length-two subscheme. -/
theorem chapter04_separates_length_two_of_restriction_surjective
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of K)} {L : Chapter04LineBundle X}
    (V : Chapter04FiniteSectionSystem K f L)
    (hV : chapter04SeparatesLengthTwo V) :
    ∀ Z : Chapter04LengthTwoClosedSubscheme K f,
      Function.Surjective (V.restriction Z) :=
  hV

/-- The finite-section length-two criterion for an immersion into projective space. -/
theorem chapter04_immersion_criterion
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Chapter04LineBundle X) (V : Chapter04FiniteSectionSystem K f L)
    (hV : chapter04SeparatesLengthTwo V) :
    chapter04VeryAmple f L := by
  sorry

/-- Over a field, very ampleness is equivalent to a finite generating system separating length two. -/
theorem chapter04_veryAmple_iff_separates_length_two
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Chapter04LineBundle X) :
    chapter04VeryAmple f L ↔
      ∃ V : Chapter04FiniteSectionSystem K f L, chapter04SeparatesLengthTwo V := by
  sorry

/-- A proper family turns the locally closed immersion from very ampleness into a closed immersion. -/
theorem chapter04_veryAmple_closed_immersion_of_proper
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (L : Chapter04LineBundle X) (w : Chapter04VeryAmpleWitness f L) :
    IsClosedImmersion w.map := by
  sorry

theorem chapter04_proper_veryAmple_is_projective
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (L : Chapter04LineBundle X) (hL : chapter04VeryAmple f L) :
    chapter04Projective f := by
  sorry

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
    chapter04SeparatesLengthTwo V ↔
      ∀ Z, chapter04SeparatesLengthTwoAt V Z := by
  rfl

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
