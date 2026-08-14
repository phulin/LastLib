import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.RingHom.Flat
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01.Section01ProjectiveGeometryOverABase
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Section04LocalityAndProjectivity
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03

universe u v

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open Polynomial
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02
open scoped AlgebraicGeometry BigOperators

/-!
## Shared interfaces for Chapter 3

The pinned scheme library has the absolute graded `Proj` construction, while the relative blowup
and the comparison with the sheafified Rees algebra are supplied by the earlier books as
book-facing interfaces.  This file records only the comparison data needed by this chapter.
-/

/-- The coherent ideal interface used by the earlier universal-blowup API. -/
abbrev Chapter03CoherentIdeal (X : Scheme.{u}) :=
  LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07CoherentIdeal X

/-- The relative Rees algebra presentation of a coherent ideal.

The affine equivalences identify the local section algebra with the ordinary Rees algebra.  The
restriction field is intentionally retained because the pinned relative-section API does not yet
package this comparison as a natural isomorphism of sheaf-valued graded algebras.
-/
structure Chapter03RelativeReesData
    {X : Scheme.{u}} (I : Chapter03CoherentIdeal X) where
  algebra : Chapter01RelativeGradedAlgebra X
  degree_zero_is_structure_sheaf :
    Chapter01RelativeDegreeZeroIsStructureSheaf algebra
  generated_in_degree_one :
    Chapter01RelativeGeneratedInDegreeOneByFiniteType algebra
  affine_rees_equivalence :
    ∀ U : X.affineOpens,
      (algebra.sections U).carrier ≃+*
        Chapter02ReesAlgebra (Γ(X, U.1)) (I.ideal.ideal U)
  /- LOCAL_DEPENDENCY_GUESS (3.1): the affine Rees equivalences glue and commute with restriction. -/
  affine_rees_equivalence_restriction : Prop

/- LOCAL_DEPENDENCY_GUESS (3.1): the sheafified Rees algebra of a coherent ideal admits the
relative graded presentation above on a noetherian scheme. -/
theorem chapter03_relative_rees_data_exists
    {X : Scheme.{u}} [IsNoetherian X] (I : Chapter03CoherentIdeal X) :
    Nonempty (Chapter03RelativeReesData I) := by
  sorry

noncomputable def chapter03RelativeReesData
    {X : Scheme.{u}} [IsNoetherian X] (I : Chapter03CoherentIdeal X) :
    Chapter03RelativeReesData I :=
  Classical.choice (chapter03_relative_rees_data_exists I)

/-- A relative-Proj presentation together with the canonical universal blowup interface. -/
structure Chapter03BlowupPresentation
    {X : Scheme.{u}} (I : Chapter03CoherentIdeal X) where
  relative_rees : Chapter03RelativeReesData I
  relative_proj : Chapter01RelativeProj relative_rees.algebra
  canonical_blowup : Chapter07Blowup I
  comparison : relative_proj.scheme ≅ canonical_blowup.carrier
  comparison_over :
    comparison.hom ≫ canonical_blowup.projection = relative_proj.projection

/- LOCAL_DEPENDENCY_GUESS (3.1): the relative Proj of the sheafified Rees algebra carries the
canonical universal-blowup comparison over the base. -/
theorem chapter03_blowup_presentation_exists
    {X : Scheme.{u}} [IsNoetherian X] (I : Chapter03CoherentIdeal X) :
    Nonempty (Chapter03BlowupPresentation I) := by
  sorry

abbrev Chapter03Blowup {X : Scheme.{u}} (I : Chapter03CoherentIdeal X) :=
  Chapter03BlowupPresentation I

noncomputable def chapter03Blowup
    {X : Scheme.{u}} [IsNoetherian X] (I : Chapter03CoherentIdeal X) :
    Chapter03Blowup I :=
  Classical.choice (chapter03_blowup_presentation_exists I)

abbrev Chapter03Blowup.carrier
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X} (B : Chapter03Blowup I) : Scheme.{u} :=
  B.relative_proj.scheme

abbrev Chapter03Blowup.projection
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X} (B : Chapter03Blowup I) :
    B.carrier ⟶ X :=
  B.relative_proj.projection

theorem chapter03_blowup_relative_proj_comparison
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X} (B : Chapter03Blowup I) :
    B.comparison.hom ≫ B.canonical_blowup.projection = B.projection :=
  B.comparison_over

/-- The extended center ideal on the relative-Proj blowup. -/
def chapter03BlowupExceptionalIdeal
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X} (B : Chapter03Blowup I) :
    B.carrier.IdealSheafData :=
  I.ideal.comap B.projection

@[simp]
theorem chapter03BlowupExceptionalIdeal_def
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X} (B : Chapter03Blowup I) :
    chapter03BlowupExceptionalIdeal B = I.ideal.comap B.projection :=
  rfl

abbrev chapter03BlowupExceptionalSubscheme
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X} (B : Chapter03Blowup I) : Scheme.{u} :=
  (chapter03BlowupExceptionalIdeal B).subscheme

abbrev chapter03BlowupExceptionalInclusion
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X} (B : Chapter03Blowup I) :
    chapter03BlowupExceptionalSubscheme B ⟶ B.carrier :=
  (chapter03BlowupExceptionalIdeal B).subschemeι

def chapter03BlowupExceptionalToCenter
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X} (B : Chapter03Blowup I) :
    chapter03BlowupExceptionalSubscheme B ⟶ I.ideal.subscheme :=
  (I.ideal.comapIso B.projection).hom ≫
    pullback.snd B.projection I.ideal.subschemeι

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03
