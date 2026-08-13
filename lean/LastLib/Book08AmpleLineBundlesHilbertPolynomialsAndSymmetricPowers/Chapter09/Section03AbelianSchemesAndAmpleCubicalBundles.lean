import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09

open AlgebraicGeometry CategoryTheory
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

/-! ### 9.3 Polarized abelian schemes -/

/- The source keeps the Picard-theoretic polarization homomorphism for later
chapters.  The input used here is the relatively ample line bundle itself. -/
theorem chapter09_polarization_bundle_gives_projective_embedding_after_a_power
    {S : Scheme} [IsNoetherian S]
    (A : Chapter09AbelianScheme S)
    [Chapter09LineBundleTensorTheory A.carrier]
    (L : Chapter09LineBundle A.carrier)
    (hL : chapter09Polarization A L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      chapter04FiniteLocallyFree (chapter09AbelianPowerPushforward A L n) ∧
        chapter09PushforwardCommutesWithBaseChange A.structureMap
          (chapter09LineBundlePower L n).module ∧
          ∃ E : Chapter09EvaluationWitness A.structureMap
              (chapter09LineBundlePower L n)
              (chapter09AbelianPowerPushforward A L n),
            IsClosedImmersion E.map := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
