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

/-!
The pinned checkout does not provide a canonical coherent-cohomology object.
Consequently the vanishing assertion is exposed as a proposition rather than
as a theorem about an arbitrary type-valued placeholder.  The latter would be
false: a context may assign a nonzero module to every positive degree.
-/
def chapter04SerreVanishingStatement
    {X S : Scheme.{u}} (C : Chapter04CohomologyContext X)
    (f : X ⟶ S) [IsAffine S] [IsNoetherian S]
    [IsNoetherian X] [QuasiCompact f] [IsSeparated f]
    (hproj : chapter04Projective f) (L : Chapter04LineBundle X)
    (hL : chapter04Ample f L) : Prop :=
  ∀ F : X.Modules, chapter04FiniteTypeQuasiCoherent F →
    chapter04EventuallyHigherCohomologyVanishes C f F L

/-- The converse Serre criterion, with the projective and noetherian hypotheses made explicit. -/
theorem chapter04_serre_ampleness_converse
    {X S : Scheme.{u}} (C : Chapter04CohomologyContext X)
    (f : X ⟶ S) [IsAffine S] [IsNoetherian S]
    [IsNoetherian X] [QuasiCompact f] [IsSeparated f]
    (hproj : chapter04Projective f) (L : Chapter04LineBundle X)
    (hvanish : ∀ F : X.Modules, chapter04FiniteTypeQuasiCoherent F →
      chapter04EventuallyHigherCohomologyVanishes C f F L)
    (hideal : ∀ I : Chapter04CoherentIdealSheaf X,
      chapter04EventuallyTwistGenerated f I.carrier L) :
    chapter04Ample f L := by
  sorry

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
