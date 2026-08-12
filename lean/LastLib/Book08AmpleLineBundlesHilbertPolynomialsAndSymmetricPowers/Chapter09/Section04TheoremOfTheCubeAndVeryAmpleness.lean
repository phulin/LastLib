import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09

open AlgebraicGeometry CategoryTheory

noncomputable section

/-! ### 9.4 The theorem of the cube and very ampleness -/

theorem chapter09_theorem_of_cube_for_rigidified_bundle
    {S : Scheme}
    (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    [Chapter09LineBundleTensorTheory S]
    (L : Chapter09LineBundle A.carrier)
    (hL : chapter09Rigidified A L) :
    chapter09TheoremOfCubeStatement A L := by
  sorry

theorem chapter09_cube_power_formula
    {S : Scheme}
    (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    [Chapter09LineBundleTensorTheory S]
    (L : Chapter09LineBundle A.carrier)
    (hL : chapter09Rigidified A L) (m : ℤ) :
    chapter09LineBundleIsomorphic
      (chapter09PullbackLineBundle (chapter09ScalarMap A m) L)
      (chapter09Tensor
        (chapter09LineBundleIntPower L (m * (m + 1) / 2))
        (chapter09LineBundleIntPower
          (chapter09PullbackLineBundle (chapter09NegationMap A) L)
          (m * (m - 1) / 2))) := by
  sorry

theorem chapter09_symmetric_cube_power_formula
    {S : Scheme}
    (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    [Chapter09LineBundleTensorTheory S]
    (L : Chapter09LineBundle A.carrier)
    (hL : chapter09Rigidified A L) (hsym : chapter09Symmetric A L) (m : ℤ) :
    chapter09LineBundleIsomorphic
      (chapter09PullbackLineBundle (chapter09ScalarMap A m) L)
      (chapter09LineBundleIntPower L (m * m)) := by
  sorry

theorem chapter09_abelian_three_power_is_relatively_very_ample
    {S : Scheme} [IsNoetherian S]
    (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    [Chapter09LineBundleTensorTheory S]
    [Chapter09RelativePositivityTheory A.structureMap]
    (L : Chapter09LineBundle A.carrier)
    (hL : chapter09RelativelyAmple A.structureMap L) :
    chapter09RelativelyVeryAmple A.structureMap
      (chapter09LineBundlePower L 3) := by
  sorry

theorem chapter09_abelian_three_power_works_in_all_characteristics
    {S : Scheme} [IsNoetherian S]
    (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    [Chapter09LineBundleTensorTheory S]
    [Chapter09RelativePositivityTheory A.structureMap]
    (L : Chapter09LineBundle A.carrier)
    (hL : chapter09RelativelyAmple A.structureMap L) :
    chapter09RelativelyVeryAmple A.structureMap
      (chapter09LineBundlePower L 3) := by
  exact chapter09_abelian_three_power_is_relatively_very_ample A L hL

theorem chapter09_symmetric_square_is_relatively_generated
    {S : Scheme} [IsNoetherian S]
    (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    [Chapter09LineBundleTensorTheory S]
    [Chapter09RelativePositivityTheory A.structureMap]
    (L : Chapter09LineBundle A.carrier)
    (hL : chapter09RelativelyAmple A.structureMap L)
    (hsym : chapter09Symmetric A L) :
    chapter09RelativelyGenerated A.structureMap
      (chapter09LineBundlePower L 2) := by
  sorry

/- The warning is recorded as a precise existential predicate: symmetry and
ampleness alone do not force the square to be relatively very ample. -/
def chapter09SymmetricSquareMayFail
    {S : Scheme} (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    [Chapter09LineBundleTensorTheory S]
    [Chapter09RelativePositivityTheory A.structureMap] : Prop :=
  ∃ L : Chapter09LineBundle A.carrier,
    chapter09RelativelyAmple A.structureMap L ∧
      chapter09Symmetric A L ∧
        ¬ chapter09RelativelyVeryAmple A.structureMap
          (chapter09LineBundlePower L 2)

theorem chapter09_symmetric_square_failure_witness
    {S : Scheme} (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    [Chapter09LineBundleTensorTheory S]
    [Chapter09RelativePositivityTheory A.structureMap]
    (hfail : chapter09SymmetricSquareMayFail A) :
    ∃ L : Chapter09LineBundle A.carrier,
      chapter09RelativelyAmple A.structureMap L ∧
        chapter09Symmetric A L ∧
          ¬ chapter09RelativelyVeryAmple A.structureMap
            (chapter09LineBundlePower L 2) := by
  exact hfail

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
