import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01.Section01ProjectiveGeometryOverABase
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Section01ProjectiveBundles

/-!
# Chapter 3: projective and quasi-projective morphisms

This file contains the focused imports shared by the four source-order sections.  The projective
bundle interfaces below are tied to the canonical finite relative-projective-bundle and
quasi-projective data supplied by the preceding chapters; Chapter 3 only adds the source-order
compatibility vocabulary and permanence statements.
-/

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03

open CategoryTheory Limits AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02

noncomputable section

universe u

variable {X Y S T : Scheme.{u}}

/-- A finite locally free sheaf of modules on a scheme. -/
def chapter03FiniteLocallyFree (E : S.Modules) : Prop :=
  E.IsLocallyFree ∧ E.IsFiniteType

/-- The quasi-coherent wrapper consumed by the canonical Chapter 2 projective-bundle API. -/
noncomputable def chapter03QuasiCoherentModule
    (S : Scheme.{u}) (E : S.Modules) (hE : chapter03FiniteLocallyFree E) :
    Chapter02QuasiCoherentModule S where
  carrier := E
  is_quasi_coherent := by sorry

/-- A Chapter 3 vocabulary adapter for the canonical finite relative projective bundle.

The `canonical` field is the full Chapter 2 interface, including its universal quotient, properness,
and finite-presentation data.  The carrier equality keeps the source-facing API in terms of the
unbundled module used by this chapter.
-/
structure Chapter03RelativeProjectiveBundle (S : Scheme.{u}) (E : S.Modules) where
  module : Chapter02QuasiCoherentModule S
  module_carrier : module.carrier = E
  finiteLocallyFree : chapter03FiniteLocallyFree E
  canonical : Chapter02RelativeProjectiveBundle S module

/-- The underlying scheme of a relative projective bundle. -/
abbrev Chapter03RelativeProjectiveBundle.carrier
    (P : Chapter03RelativeProjectiveBundle S E) : Scheme.{u} :=
  P.canonical.carrier

/-- The structure morphism of a relative projective bundle. -/
abbrev Chapter03RelativeProjectiveBundle.projection
    (P : Chapter03RelativeProjectiveBundle S E) : P.carrier ⟶ S :=
  P.canonical.projection

/-- The canonical Chapter 2 projective-bundle data retained for compatibility. -/
abbrev Chapter03RelativeProjectiveBundle.data
    (P : Chapter03RelativeProjectiveBundle S E) :
    Chapter02ProjectiveBundleData S P.module :=
  P.canonical.data

/-- The tautological line bundle supplied by the canonical projective-bundle data. -/
abbrev Chapter03RelativeProjectiveBundle.twistingLineBundle
    (P : Chapter03RelativeProjectiveBundle S E) :
    Chapter02LineBundle P.carrier :=
  P.canonical.twistingLineBundle

/-- The universal quotient supplied by the canonical projective-bundle data. -/
abbrev Chapter03RelativeProjectiveBundle.universalQuotient
    (P : Chapter03RelativeProjectiveBundle S E) :
    (Scheme.Modules.pullback P.projection).obj P.module.carrier ⟶
      P.twistingLineBundle.carrier :=
  P.canonical.universalQuotient

/-- Properness inherited from the canonical finite relative projective bundle. -/
abbrev Chapter03RelativeProjectiveBundle.proper
    (P : Chapter03RelativeProjectiveBundle S E) : IsProper P.projection :=
  P.canonical.proper

/-- Finite presentation inherited from the canonical finite relative projective bundle. -/
abbrev Chapter03RelativeProjectiveBundle.finite_presentation
    (P : Chapter03RelativeProjectiveBundle S E) : LocallyOfFinitePresentation P.projection :=
  P.canonical.finite_presentation

instance Chapter03RelativeProjectiveBundle.projection_isProper
    (P : Chapter03RelativeProjectiveBundle S E) : IsProper P.projection :=
  P.proper

instance Chapter03RelativeProjectiveBundle.projection_locallyOfFinitePresentation
    (P : Chapter03RelativeProjectiveBundle S E) : LocallyOfFinitePresentation P.projection :=
  P.finite_presentation

/-- Existence of the canonical finite relative projective-bundle adapter. -/
theorem chapter03_relativeProjectiveBundle_exists
    (S : Scheme.{u}) (E : S.Modules) (hE : chapter03FiniteLocallyFree E) :
    Nonempty (Chapter03RelativeProjectiveBundle S E) := by
  sorry

/-- A chosen canonical finite relative projective-bundle adapter. -/
noncomputable def chapter03RelativeProjectiveBundle
    (S : Scheme.{u}) (E : S.Modules) (hE : chapter03FiniteLocallyFree E) :
    Chapter03RelativeProjectiveBundle S E :=
  Classical.choice (chapter03_relativeProjectiveBundle_exists S E hE)

/-- The Chapter 3 projective presentation is the canonical Chapter 2 presentation. -/
abbrev Chapter03ProjectivePresentation (f : X ⟶ S) :=
  Chapter02ProjectivePresentation f

/-- The Chapter 3 quasi-projective presentation is the canonical Chapter 2 presentation. -/
abbrev Chapter03QuasiProjectivePresentation (f : X ⟶ S) :=
  Chapter02QuasiProjectivePresentation f

/-- Chapter 3 re-exports the canonical projective-morphism predicate. -/
abbrev chapter03Projective (f : X ⟶ S) : Prop :=
  Chapter02ProjectiveMorphism f

/-- Chapter 3 re-exports the canonical quasi-projective-morphism predicate. -/
abbrev chapter03QuasiProjective (f : X ⟶ S) : Prop :=
  Chapter02QuasiProjectiveMorphism f

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03
