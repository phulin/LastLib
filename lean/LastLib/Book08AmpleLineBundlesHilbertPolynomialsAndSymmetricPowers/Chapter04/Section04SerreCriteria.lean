import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

/-! ## 4.4. Serre criteria -/

/-- Eventual global generation of a fixed module sheaf after twisting by `L`. -/
def chapter04EventuallyTwistGenerated
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (L : Chapter04LineBundle X) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    chapter04TwistGeneratedByRelativeGlobalSections f F L n

/-- The generation form of Serre's criterion for relative ampleness. -/
theorem chapter04_serre_generation_criterion
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [IsSeparated f]
    [IsAffine S] (L : Chapter04LineBundle X) :
    chapter04Ample f L ↔
      ∀ F : X.Modules, chapter04FiniteTypeQuasiCoherent F →
        chapter04EventuallyTwistGenerated f F L := by
  sorry

/-- The ideal-sheaf form of Serre's criterion on a noetherian scheme. -/
theorem chapter04_serre_coherent_ideal_criterion
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [IsSeparated f]
    [IsAffine S] [IsNoetherian X] (L : Chapter04LineBundle X) :
    chapter04Ample f L ↔
      ∀ I : Chapter04CoherentIdealSheaf X,
        chapter04EventuallyTwistGenerated f I.carrier L := by
  sorry

/-- Eventual vanishing of all positive higher cohomology groups in a chosen cohomology API. -/
def chapter04EventuallyHigherCohomologyVanishes
    {X S : Scheme.{u}} (C : Chapter04CohomologyContext X)
    (_f : X ⟶ S) (F : X.Modules) (L : Chapter04LineBundle X) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ i : ℕ, 0 < i →
      C.Vanishes (chapter04TwistedModule F L n) i

/-- Serre vanishing for a projective morphism over a noetherian affine base. -/
theorem chapter04_serre_vanishing
    {X S : Scheme.{u}} (C : Chapter04CohomologyContext X)
    (f : X ⟶ S) [IsAffine S] [IsNoetherian S]
    (hproj : chapter04Projective f) (L : Chapter04LineBundle X)
    (hL : chapter04Ample f L) (F : X.Modules)
    (hF : chapter04FiniteTypeQuasiCoherent F) :
    chapter04EventuallyHigherCohomologyVanishes C f F L := by
  sorry

/- SOURCE_ISSUE (4.4, converse paragraph): the source says only "if this
vanishing holds" before invoking eventual generation of all coherent ideals;
the projective/noetherian/affine hypotheses from the preceding vanishing theorem
are needed for a mathematically meaningful converse.  The declaration below
therefore carries those hypotheses and states both required conditions. -/

/-- The converse Serre criterion, with the projective and noetherian hypotheses made explicit. -/
theorem chapter04_serre_ampleness_converse
    {X S : Scheme.{u}} (C : Chapter04CohomologyContext X)
    (f : X ⟶ S) [IsAffine S] [IsNoetherian S]
    (hproj : chapter04Projective f) (L : Chapter04LineBundle X)
    (hvanish : ∀ F : X.Modules, chapter04FiniteTypeQuasiCoherent F →
      chapter04EventuallyHigherCohomologyVanishes C f F L)
    (hideal : ∀ I : Chapter04CoherentIdealSheaf X,
      chapter04EventuallyTwistGenerated f I.carrier L) :
    chapter04Ample f L := by
  sorry

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
