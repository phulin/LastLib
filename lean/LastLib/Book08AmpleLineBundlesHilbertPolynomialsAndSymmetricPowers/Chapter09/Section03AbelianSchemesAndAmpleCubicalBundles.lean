import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09

open AlgebraicGeometry CategoryTheory

noncomputable section

/-! ### 9.3 Abelian schemes and ample cubical bundles -/

structure Chapter09ProperNonProjectiveWitness where
  base : Scheme
  carrier : Scheme
  map : carrier ⟶ base
  proper : IsProper map
  notProjective : ¬ Chapter09ProjectiveMorphism map

theorem chapter09_properness_alone_does_not_imply_projectivity :
    Nonempty Chapter09ProperNonProjectiveWitness := by
  sorry

theorem chapter09_ample_line_bundle_gives_finite_surjective_lambda
    {S : Scheme}
    (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    [Chapter09LineBundleTensorTheory S]
    [Chapter09RelativePositivityTheory A.structureMap]
    [Chapter09PolarizationMapTheory A]
    (L : Chapter09LineBundle A.carrier)
    (hL : chapter09RelativelyAmple A.structureMap L) :
    chapter09FiniteSurjective (chapter09AbelianMorphismMap (chapter09Lambda A L)) := by
  sorry

theorem chapter09_ample_line_bundle_gives_polarization
    {S : Scheme}
    (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    [Chapter09LineBundleTensorTheory S]
    [Chapter09RelativePositivityTheory A.structureMap]
    [Chapter09PolarizationMapTheory A]
    (L : Chapter09LineBundle A.carrier)
    (hL : chapter09RelativelyAmple A.structureMap L) :
    chapter09Polarization A L := by
  sorry

theorem chapter09_lambda_is_a_group_hom
    {S : Scheme}
    (A : Chapter09AbelianScheme S)
    [Chapter09PolarizationMapTheory A]
    (L : Chapter09LineBundle A.carrier) :
    chapter09AbelianMorphismIsGroupHom (chapter09Lambda A L) := by
  exact (chapter09Lambda A L).isGroupHom

theorem chapter09_polarization_is_locally_induced_by_a_rigidified_ample_bundle
    {S : Scheme}
    (A : Chapter09AbelianScheme S) (φ : Chapter09AbelianMorphism A)
    (hφ : chapter09PolarizationMapProperty A φ) :
    chapter09PolarizationLocallyInduced A φ := by
  sorry

theorem chapter09_polarization_bundle_gives_projective_embedding_after_a_power
    {S : Scheme}
    (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    [Chapter09LineBundleTensorTheory S]
    [Chapter09RelativePositivityTheory A.structureMap]
    [Chapter09PolarizationMapTheory A]
    (L : Chapter09LineBundle A.carrier)
    (hL : chapter09Polarization A L) :
    ∃ n : ℕ, 0 < n ∧
      chapter09RelativelyVeryAmple A.structureMap (chapter09LineBundlePower L n) := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
