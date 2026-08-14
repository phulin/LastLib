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

abbrev Chapter02TotalQuotientRing (X : Scheme.{u}) (U : X.affineOpens) :=
  Localization (nonZeroDivisors (Γ(X, U.1)))

noncomputable abbrev Chapter02ComponentFunctionField (X : Scheme.{u})
    [IsReduced X] (i : irreducibleComponents X) :=
  X.presheaf.stalk i.2.1.genericPoint

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
  sectionAlgebra : ∀ U : X.affineOpens,
    Algebra (Γ(X, U.1)) ((carrier.presheaf.obj (Opposite.op U.1)).carrier)
  sectionIsLocalization : ∀ U : X.affineOpens,
    letI := sectionAlgebra U
    IsLocalization (nonZeroDivisors (Γ(X, U.1)))
      ((carrier.presheaf.obj (Opposite.op U.1)).carrier)
  regularMap_eq_algebraMap : ∀ U : X.affineOpens,
    letI := sectionAlgebra U
    (regularMap.1.app (Opposite.op U.1)).hom = algebraMap (Γ(X, U.1))
      ((carrier.presheaf.obj (Opposite.op U.1)).carrier)
  structureMap_injective : ∀ U : X.Opens,
    Function.Injective (regularMap.1.app (Opposite.op U)).hom
  regular_isUnit : ∀ (U : X.Opens) {f : Γ(X, U)},
    f ∈ nonZeroDivisors (Γ(X, U)) →
      IsUnit ((regularMap.1.app (Opposite.op U)).hom f)
  /-- Meromorphic sections are locally fractions on affine neighborhoods.
      A single fraction on an arbitrary open is not available in general. -/
  exists_fraction : ∀ (U : X.Opens)
    (s : (carrier.presheaf.obj (Opposite.op U)).carrier) (x : X) (_hx : x ∈ U),
    ∃ (V : X.affineOpens) (_hxV : x ∈ V.1) (hVU : V.1 ≤ U)
      (a b : Γ(X, V.1)), b ∈ nonZeroDivisors (Γ(X, V.1)) ∧
        (carrier.presheaf.map (homOfLE hVU).op).hom s *
            (regularMap.1.app (Opposite.op V.1)).hom b =
          (regularMap.1.app (Opposite.op V.1)).hom a
  /-- The canonical comparison with the function field on every nonempty open
      of an integral scheme, together with its restriction compatibility. -/
  functionFieldEquiv : ∀ [IsIntegral X] (U : X.Opens) (_hU : Nonempty U),
    (carrier.presheaf.obj (Opposite.op U)).carrier ≃+* X.functionField
  functionFieldEquiv_restrict : ∀ [IsIntegral X] {U V : X.Opens}
    (h : V ≤ U) (hU : Nonempty U) (hV : Nonempty V)
    (s : (carrier.presheaf.obj (Opposite.op U)).carrier),
    (functionFieldEquiv V hV)
        ((carrier.presheaf.map (homOfLE h).op).hom s) =
      (functionFieldEquiv U hU) s
  /-- The canonical componentwise comparison on a reduced locally noetherian
      scheme with finitely many irreducible components. -/
  componentFunctionFieldEquiv : ∀ [IsReduced X] [IsLocallyNoetherian X]
    [Finite (irreducibleComponents X)],
    (carrier.presheaf.obj (Opposite.op (⊤ : X.Opens))).carrier ≃+*
      (∀ i : irreducibleComponents X, Chapter02ComponentFunctionField X i)

abbrev Chapter02MeromorphicSection (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] (U : X.Opens) :=
  (K.carrier.presheaf.obj (Opposite.op U)).carrier

def chapter02StructureSheafPullbackMap {X Y : Scheme.{u}}
    (g : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U) :
    Γ(X, U) →+* Γ(Y, V) :=
  (g.appLE U V hV).hom

def chapter02RegularSectionMap (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] (U : X.Opens) :
    Γ(X, U) →+* Chapter02MeromorphicSection X U :=
  (K.regularMap.1.app (Opposite.op U)).hom

def chapter02RegularSectionIsRegularAt {X : Scheme.{u}}
    (U : X.Opens) (f : Γ(X, U)) (x : X) (hx : x ∈ U) : Prop :=
  Function.Injective (fun z : X.presheaf.stalk x =>
    X.presheaf.germ U x hx f * z)

noncomputable def chapter02TotalQuotientRingEquiv (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] (U : X.affineOpens) :
    Chapter02TotalQuotientRing X U ≃+*
      Chapter02MeromorphicSection X U.1 :=
  letI := K.sectionAlgebra U
  letI := K.sectionIsLocalization U
  (IsLocalization.algEquiv (nonZeroDivisors (Γ(X, U.1)))
    (Chapter02TotalQuotientRing X U)
    (Chapter02MeromorphicSection X U.1)).toRingEquiv

def chapter02MeromorphicRestriction (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] {U V : X.Opens} (h : V ≤ U) :
    Chapter02MeromorphicSection X U →+* Chapter02MeromorphicSection X V :=
  (K.carrier.presheaf.map (homOfLE h).op).hom

theorem chapter02_meromorphicRestriction_comp {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] {U V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V)
    (s : Chapter02MeromorphicSection X U) :
    chapter02MeromorphicRestriction X hWV
        (chapter02MeromorphicRestriction X hVU s) =
      chapter02MeromorphicRestriction X (hWV.trans hVU) s := by
  change (K.carrier.presheaf.map (homOfLE hWV).op).hom
      ((K.carrier.presheaf.map (homOfLE hVU).op).hom s) =
    (K.carrier.presheaf.map (homOfLE (hWV.trans hVU)).op).hom s
  have hle : (homOfLE hVU).op ≫ (homOfLE hWV).op =
      (homOfLE (hWV.trans hVU)).op := by
    subsingleton
  simpa only [hle, CommRingCat.comp_apply] using
    congrArg (fun z => z.hom s)
      (Functor.map_comp K.carrier.presheaf
        (homOfLE hVU).op (homOfLE hWV).op).symm

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
  ∀ (x : U),
    ∃ (V : X.Opens) (hxV : (x : X) ∈ V) (hV : V ≤ U) (f : Γ(X, V)),
      chapter02RegularSectionIsRegularAt V f (x : X) hxV ∧
        chapter02RegularSectionMap X V f =
          chapter02MeromorphicRestriction X hV s

/- The local quotient `K_X^× / O_X^×` at an open is made explicit as a
   quotient of the unit group by the regular-unit relation. -/
def chapter02CartierUnitRelation (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] (U : X.Opens)
    (a b : (Chapter02MeromorphicSection X U)ˣ) : Prop :=
  ∃ u : (Γ(X, U))ˣ,
    chapter02RegularUnitMap X U u * a = b

instance chapter02CartierUnitSetoid (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] (U : X.Opens) :
    Setoid ((Chapter02MeromorphicSection X U)ˣ) where
  r := chapter02CartierUnitRelation X U
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨1, by simp⟩
    · rintro a b ⟨u, h⟩
      refine ⟨u⁻¹, ?_⟩
      rw [← h]
      simp
    · rintro a b c ⟨u, hab⟩ ⟨v, hbc⟩
      refine ⟨v * u, ?_⟩
      rw [← hbc, ← hab]
      simp [mul_assoc]

abbrev Chapter02CartierEquation (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] (U : X.Opens) :=
  Quotient (chapter02CartierUnitSetoid X U)

theorem chapter02_cartier_equation_eq_of_regular_unit
    (X : Scheme.{u}) [K : Chapter02MeromorphicSheaf X] (U : X.Opens)
    (a b : (Chapter02MeromorphicSection X U)ˣ)
    (h : chapter02CartierUnitRelation X U a b) :
    (Quotient.mk' a : Chapter02CartierEquation X U) = Quotient.mk' b := by
  exact Quotient.sound h

theorem chapter02_cartier_equation_eq_iff
    (X : Scheme.{u}) [K : Chapter02MeromorphicSheaf X] (U : X.Opens)
    (a b : (Chapter02MeromorphicSection X U)ˣ) :
    (Quotient.mk' a : Chapter02CartierEquation X U) = Quotient.mk' b ↔
      chapter02CartierUnitRelation X U a b := by
  constructor
  · exact Quotient.exact
  · intro h
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
