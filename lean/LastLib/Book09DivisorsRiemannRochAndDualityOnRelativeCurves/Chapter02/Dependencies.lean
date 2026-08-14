import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.Basic

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry nonZeroDivisors

universe u v

abbrev Chapter02TotalQuotientRing (X : Scheme.{u}) (U : X.Opens) :=
  Localization (nonZeroDivisors (Γ(X, U)))

/-!
Shared interfaces for Chapter 02.  Mathlib has the localization, ideal-sheaf,
flatness, fiber, and valuation primitives used below, but it does not yet
package the sheaf of total quotient rings or Cartier divisors themselves.
-/

/- LOCAL_DEPENDENCY_GUESS: the total quotient sheaf and its localization
   comparison are the missing earlier-book interface. -/
class Chapter02MeromorphicSheaf (X : Scheme.{u}) where
  carrier : TopCat.Sheaf CommRingCat X
  regularMap : X.sheaf ⟶ carrier
  sectionAlgebra : ∀ U : X.Opens,
    Algebra (Γ(X, U)) ((carrier.presheaf.obj (op U)).carrier)
  sectionIsLocalization : ∀ U : X.Opens,
    letI := sectionAlgebra U
    IsLocalization (nonZeroDivisors (Γ(X, U)))
      ((carrier.presheaf.obj (op U)).carrier)
  regularMap_eq_algebraMap : ∀ U : X.Opens,
    letI := sectionAlgebra U
    (regularMap.1.app (op U)).hom = algebraMap (Γ(X, U))
      ((carrier.presheaf.obj (op U)).carrier)

abbrev Chapter02MeromorphicSection (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] (U : X.Opens) :=
  (K.carrier.presheaf.obj (op U)).carrier

def chapter02RegularSectionMap (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] (U : X.Opens) :
    Γ(X, U) →+* Chapter02MeromorphicSection X U :=
  (K.regularMap.1.app (op U)).hom

noncomputable def chapter02TotalQuotientRingEquiv (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] (U : X.Opens) :
    Chapter02TotalQuotientRing X U ≃+*
      Chapter02MeromorphicSection X U :=
  letI := K.sectionAlgebra U
  letI := K.sectionIsLocalization U
  (IsLocalization.algEquiv (nonZeroDivisors (Γ(X, U)))
    (Chapter02TotalQuotientRing X U)
    (Chapter02MeromorphicSection X U)).toRingEquiv

def chapter02MeromorphicRestriction (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] {U V : X.Opens} (h : V ≤ U) :
    Chapter02MeromorphicSection X U →+* Chapter02MeromorphicSection X V :=
  (K.carrier.presheaf.map (homOfLE h).op).hom

def chapter02MeromorphicRestrictionUnit (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] {U V : X.Opens} (h : V ≤ U)
    (s : (Chapter02MeromorphicSection X U)ˣ) :
    (Chapter02MeromorphicSection X V)ˣ :=
  Units.map (chapter02MeromorphicRestriction X h) s

def chapter02RegularUnitMap (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] (U : X.Opens) :
    (Γ(X, U))ˣ →* (Chapter02MeromorphicSection X U)ˣ :=
  Units.map (chapter02RegularSectionMap X U)

def chapter02MeromorphicSectionIsRegular (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] (U : X.Opens)
    (s : Chapter02MeromorphicSection X U) : Prop :=
  ∃ f : Γ(X, U), f ∈ nonZeroDivisors (Γ(X, U)) ∧
    chapter02RegularSectionMap X U f = s

/- The local quotient `K_X^× / O_X^×` at an open is made explicit as a
   quotient of the unit group by the regular-unit relation. -/
def chapter02CartierUnitRelation (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] (U : X.Opens)
    (a b : (Chapter02MeromorphicSection X U)ˣ) : Prop :=
  ∃ u : (Γ(X, U))ˣ,
    chapter02RegularUnitMap X U u * a = b

def chapter02CartierUnitSetoid (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] (U : X.Opens) :
    Setoid ((Chapter02MeromorphicSection X U)ˣ) where
  r := chapter02CartierUnitRelation X U
  iseqv := by sorry

abbrev Chapter02CartierEquation (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] (U : X.Opens) :=
  Quotient (chapter02CartierUnitSetoid X U)

theorem chapter02_cartier_equation_eq_of_regular_unit
    (X : Scheme.{u}) [K : Chapter02MeromorphicSheaf X] (U : X.Opens)
    (a b : (Chapter02MeromorphicSection X U)ˣ)
    (h : chapter02CartierUnitRelation X U a b) :
    (Quotient.mk' a : Chapter02CartierEquation X U) = Quotient.mk' b := by
  exact Quotient.sound h

/-!
The concrete representative of a Cartier divisor is a cover and units in the
total quotient sheaf whose ratios are regular units on overlaps.  The quotient
description above records the book's `K_X^× / O_X^×` formulation.
-/
structure Chapter02CartierDivisor (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] where
  index : Type v
  openSet : index → X.Opens
  cover : iSup openSet = ⊤
  equation : ∀ i, (Chapter02MeromorphicSection X (openSet i))ˣ
  equationClass : ∀ i, Chapter02CartierEquation X (openSet i)
  equationClass_eq : ∀ i, equationClass i = Quotient.mk' (equation i)
  transition : ∀ i j,
    ∃ u : (Γ(X, openSet i ⊓ openSet j))ˣ,
      chapter02RegularUnitMap X (openSet i ⊓ openSet j) u =
        chapter02MeromorphicRestrictionUnit X inf_le_left (equation i) *
          (chapter02MeromorphicRestrictionUnit X inf_le_right (equation j))⁻¹

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02
