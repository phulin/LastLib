import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

/-! ## 4.5. Tensor powers and operations -/

/-- Isomorphism of line bundles through their underlying module sheaves. -/
def chapter04LineBundleIsomorphic
    {X : Scheme.{u}} (L M : Chapter04LineBundle X) : Prop :=
  Nonempty (L.sheaf ≅ M.sheaf)

/-- Positive tensor powers preserve relative ampleness. -/
theorem chapter04_ample_tensorPower
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X)
    (hL : chapter04Ample f L) (d : ℕ) (hd : 0 < d) :
    chapter04Ample f (chapter04LineBundleTensorPower L d) := by
  sorry

/-- Relative ampleness descends from a positive tensor power. -/
theorem chapter04_ample_of_ample_tensorPower
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X)
    (d : ℕ) (hd : 0 < d)
    (hLd : chapter04Ample f (chapter04LineBundleTensorPower L d)) :
    chapter04Ample f L := by
  sorry

/- SOURCE_ISSUE (4.5, bounded twists): the source states "`L^n ⊗ M` is
ample for all sufficiently large `n`" without retaining the quasi-compact
separated context needed for a uniform bounded-twist threshold.  The minimal
correction below makes those hypotheses explicit. -/

/-- A fixed invertible twist does not affect ampleness in sufficiently high powers. -/
theorem chapter04_ample_eventually_tensor_twist
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [IsSeparated f]
    (L M : Chapter04LineBundle X) (hL : chapter04Ample f L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      chapter04Ample f
        (chapter04LineBundleTensor (chapter04LineBundleTensorPower L n) M) := by
  sorry

/-- An ample line bundle on a quasi-compact finite-type family has a very ample power. -/
theorem chapter04_ample_has_veryAmple_power
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [LocallyOfFiniteType f]
    (L : Chapter04LineBundle X) (hL : chapter04Ample f L) :
    ∃ d : ℕ, 0 < d ∧ chapter04VeryAmple f (chapter04LineBundleTensorPower L d) := by
  sorry

/-- If the family is proper, a sufficiently high ample power gives a closed projective embedding. -/
theorem chapter04_proper_ample_has_closed_projective_power
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [QuasiCompact f]
    (L : Chapter04LineBundle X) (hL : chapter04Ample f L) :
    ∃ d : ℕ, 0 < d ∧
      ∃ w : Chapter04VeryAmpleWitness f (chapter04LineBundleTensorPower L d),
        IsClosedImmersion w.map := by
  sorry

theorem chapter04_proper_ample_is_projective
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [QuasiCompact f]
    (L : Chapter04LineBundle X) (hL : chapter04Ample f L) :
    chapter04Projective f := by
  sorry

/-- Tensor products of ample line bundles are ample. -/
theorem chapter04_ample_tensor
    {X S : Scheme.{u}} (f : X ⟶ S)
    (L M : Chapter04LineBundle X)
    (hL : chapter04Ample f L) (hM : chapter04Ample f M) :
    chapter04Ample f (chapter04LineBundleTensor L M) := by
  sorry

/-- Pullback along a finite morphism preserves relative ampleness. -/
theorem chapter04_ample_pullback_of_finite
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) [IsFinite g]
    (L : Chapter04LineBundle X) (hL : chapter04Ample f L) :
    chapter04Ample (g ≫ f) (chapter04PullbackLineBundle g L) := by
  sorry

/-- A constant pullback can become the trivial bundle on a proper non-affine fibre. -/
theorem chapter04_constant_pullback_can_destroy_ample
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of K)) (g : Y ⟶ X) [IsProper (g ≫ f)]
    (L : Chapter04LineBundle X) (hL : chapter04Ample f L)
    (hconstant : chapter04UnderlyingConstant g)
    (htrivial : chapter04LineBundleIsomorphic
      (chapter04PullbackLineBundle g L) (chapter04TrivialLineBundle Y))
    (hY : ¬ IsAffine Y) :
    ¬ chapter04Ample (g ≫ f) (chapter04PullbackLineBundle g L) := by
  sorry

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
