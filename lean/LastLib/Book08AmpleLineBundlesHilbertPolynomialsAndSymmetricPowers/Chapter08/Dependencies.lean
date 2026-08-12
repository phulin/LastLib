import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Topology.GDelta.Basic

/-!
# Chapter 8: Hilbert polynomials in families

This file contains the common interfaces used by the chapter.  The current pinned
Mathlib snapshot has the scheme-theoretic notions of flatness, finite presentation,
and noetherianity, but not a projective-morphism API, relative ample line bundles,
associated points of coherent sheaves, or Fitting ideals for flattening strata.
The small `Chapter08...` interfaces below isolate those missing dependencies so
that the statements remain usable when the earlier chapters are reconciled.
-/

namespace LastLib
namespace Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers
namespace Chapter08

open AlgebraicGeometry CategoryTheory Limits
open scoped BigOperators

noncomputable section

/-- A polynomial with rational coefficients which takes integral values at all
nonnegative integers.  This is the numerical-polynomial interface used for
fiber Hilbert polynomials in this chapter. -/
structure Chapter08NumericalPolynomial where
  polynomial : Polynomial ℚ
  integer_valued : ∀ n : ℕ, ∃ z : ℤ, polynomial.eval (n : ℚ) = (z : ℚ)

namespace Chapter08NumericalPolynomial

/-- Evaluation of a numerical polynomial at a natural number. -/
def eval (P : Chapter08NumericalPolynomial) (n : ℕ) : ℚ :=
  P.polynomial.eval (n : ℚ)

/-- The integer represented by a numerical polynomial at a natural number. -/
def value (P : Chapter08NumericalPolynomial) (n : ℕ) : ℤ :=
  Classical.choose (P.integer_valued n)

theorem value_spec (P : Chapter08NumericalPolynomial) (n : ℕ) :
    (P.value n : ℚ) = P.eval n := by
  exact (Classical.choose_spec (P.integer_valued n)).symm

/-- A convenient degree bound for a numerical polynomial. -/
def degree (P : Chapter08NumericalPolynomial) : ℕ := P.polynomial.natDegree

@[ext]
theorem ext {P Q : Chapter08NumericalPolynomial}
    (h : P.polynomial = Q.polynomial) : P = Q := by
  cases P
  cases Q
  simp_all

end Chapter08NumericalPolynomial

/-- A map is locally constant in the elementary pointwise sense needed here. -/
def Chapter08LocallyConstant {α β : Type*} [TopologicalSpace α] (g : α → β) : Prop :=
  ∀ x, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, g y = g x

/-!
The following predicates are intentionally local.  They are the natural
interfaces for the projective/ample/coherent hypotheses in the book, while the
corresponding full relative constructions are not present in the pinned imports.
-/

/- LOCAL_DEPENDENCY_GUESS: replace the witness field by the canonical projective
   morphism API supplied by an earlier chapter when that API is available. -/
class Chapter08IsProjective {X S : Scheme} (f : X ⟶ S) where
  proper : IsProper f
  projective_witness : Prop

/- LOCAL_DEPENDENCY_GUESS: this packages the missing relative line-bundle
   interface; the local-freeness field is the canonical Mathlib component. -/
class Chapter08InvertibleSheaf {X : Scheme} (L : X.Modules) where
  locally_free : L.IsLocallyFree
  rank_one : Prop

/- LOCAL_DEPENDENCY_GUESS: the f-ample predicate is not available in the pinned
   scheme API, so retain it as a named book-facing hypothesis. -/
class Chapter08FAmple {X S : Scheme} (f : X ⟶ S) (L : X.Modules) where
  ample_witness : Prop

/- LOCAL_DEPENDENCY_GUESS: this is the missing sheaf-flat-over-the-base
   interface, distinct from flatness of a scheme morphism. -/
def chapter08StalkFlat {X S : Scheme} (f : X ⟶ S) (M : X.Modules) (x : X) : Prop :=
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk M.val.presheaf x)) := by
    exact PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier M.val x
  letI : Module (S.presheaf.stalk (f x))
      (↑(TopCat.Presheaf.stalk M.val.presheaf x)) :=
    Module.compHom (↑(TopCat.Presheaf.stalk M.val.presheaf x)) (f.stalkMap x).hom
  Module.Flat (S.presheaf.stalk (f x)) (↑(TopCat.Presheaf.stalk M.val.presheaf x))

class Chapter08FlatOver {X S : Scheme} (f : X ⟶ S) (M : X.Modules) : Prop where
  stalkwise_flat : ∀ x : X, chapter08StalkFlat f M x

/- LOCAL_DEPENDENCY_GUESS: the relative very-ampleness predicate used by the
   flattening theorem is not available in the pinned scheme API. -/
class Chapter08RelativelyVeryAmple {X S : Scheme} (f : X ⟶ S) (L : X.Modules) where
  very_ample_witness : Prop

/-- The coherent sheaf hypothesis used by the chapter, expressed through the
quasi-coherent and finite-presentation interfaces in the pinned Mathlib. -/
def Chapter08Coherent {X : Scheme} (M : X.Modules) : Prop :=
  M.IsQuasicoherent ∧ M.IsFinitePresentation

/-- A projective, finitely presented family over a locally noetherian base. -/
structure Chapter08ProjectiveFamily where
  S : Scheme
  X : Scheme
  f : X ⟶ S
  base_locally_noetherian : IsLocallyNoetherian S
  projective : Chapter08IsProjective f
  quasi_compact : QuasiCompact f
  locally_of_finite_presentation : LocallyOfFinitePresentation f
  fiber_dimension_bound : ℕ

namespace Chapter08ProjectiveFamily

instance (F : Chapter08ProjectiveFamily) : IsLocallyNoetherian F.S :=
  F.base_locally_noetherian
instance (F : Chapter08ProjectiveFamily) : Chapter08IsProjective F.f := F.projective
instance (F : Chapter08ProjectiveFamily) : IsProper F.f := F.projective.proper
instance (F : Chapter08ProjectiveFamily) : QuasiCompact F.f := F.quasi_compact
instance (F : Chapter08ProjectiveFamily) : LocallyOfFinitePresentation F.f :=
  F.locally_of_finite_presentation

end Chapter08ProjectiveFamily

/-- A projective family equipped with a relatively ample line bundle. -/
structure Chapter08PolarizedFamily where
  family : Chapter08ProjectiveFamily
  lineBundle : family.X.Modules
  lineBundle_invertible : Chapter08InvertibleSheaf lineBundle
  lineBundle_f_ample : Chapter08FAmple family.f lineBundle

namespace Chapter08PolarizedFamily

instance (F : Chapter08PolarizedFamily) : Chapter08InvertibleSheaf F.lineBundle :=
  F.lineBundle_invertible
instance (F : Chapter08PolarizedFamily) : Chapter08FAmple F.family.f F.lineBundle :=
  F.lineBundle_f_ample

end Chapter08PolarizedFamily

/-- The additional relative very-ampleness datum needed in §8.4. -/
structure Chapter08VeryAmplePolarizedFamily where
  polarized : Chapter08PolarizedFamily
  lineBundle_relatively_very_ample :
    Chapter08RelativelyVeryAmple polarized.family.f polarized.lineBundle

/-- A coherent sheaf on a polarized family. -/
structure Chapter08FamilySheaf (F : Chapter08PolarizedFamily) where
  sheaf : F.family.X.Modules
  coherent : Chapter08Coherent sheaf

/-- Fiberwise cohomological data representing the Euler characteristic and its
polynomial in the source chapter.  The finite alternating-sum field records the
usual definition of χ and the last field records the dimension bound. -/
structure Chapter08FiberwiseHilbertData
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F) where
  dimension_bound : ℕ
  dimension_bound_le_family_bound :
    dimension_bound ≤ F.family.fiber_dimension_bound
  eulerCharacteristic : F.family.S → ℕ → ℤ
  fiberPolynomial : F.family.S → Chapter08NumericalPolynomial
  fiberPolynomial_value :
    ∀ (s : F.family.S) (n : ℕ),
      (fiberPolynomial s).value n = eulerCharacteristic s n
  cohomologyRank : F.family.S → ℕ → ℕ → ℕ
  cohomology_vanishes_above_dimension :
    ∀ (s : F.family.S) (n i : ℕ), dimension_bound < i → cohomologyRank s n i = 0
  eulerCharacteristic_altSum :
    ∀ (s : F.family.S) (n : ℕ),
      eulerCharacteristic s n =
        Finset.sum (Finset.range (dimension_bound + 1))
          (fun i => (-1 : ℤ) ^ i * (cohomologyRank s n i : ℤ))
  polynomial_degree_le :
    ∀ s, (fiberPolynomial s).degree ≤ dimension_bound

/- LOCAL_DEPENDENCY_GUESS: this witness abstracts the coherent pushforward and
   cohomology-and-base-change theorem used for large twists. -/
structure Chapter08PushforwardWitness
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (D : Chapter08FiberwiseHilbertData E) (U : Set F.family.S) (n : ℕ) where
  rank : ℕ
  locally_free : Prop
  fiber_is_H0 : ∀ s ∈ U, rank = D.cohomologyRank s n 0
  rank_eq_eulerCharacteristic :
    ∀ s ∈ U, (rank : ℤ) = D.eulerCharacteristic s n

section BaseChange

variable {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)

include E

/-- The scheme-theoretic base change of the family along a morphism `T ⟶ S`. -/
def chapter08BaseChangeTotal {T : Scheme} (t : T ⟶ F.family.S) : Scheme :=
  Limits.pullback F.family.f t

/-- Projection from the base-changed family to the original total space. -/
def chapter08BaseChangeToTotal {T : Scheme} (t : T ⟶ F.family.S) :
    chapter08BaseChangeTotal t ⟶ F.family.X :=
  Limits.pullback.fst F.family.f t

/-- Projection from the base-changed family to the test scheme. -/
def chapter08BaseChangeToTest {T : Scheme} (t : T ⟶ F.family.S) :
    chapter08BaseChangeTotal t ⟶ T :=
  Limits.pullback.snd F.family.f t

/-- Pullback of the family sheaf to a test scheme. -/
def chapter08BaseChangeSheaf {T : Scheme} (t : T ⟶ F.family.S) :
    (chapter08BaseChangeTotal t).Modules :=
  (Scheme.Modules.pullback (chapter08BaseChangeToTotal t)).obj E.sheaf

/- LOCAL_DEPENDENCY_GUESS: sheaf flatness over a scheme morphism is not yet a
   canonical predicate in this project snapshot. -/
def chapter08BaseChangeFlatness {T : Scheme} (t : T ⟶ F.family.S) : Prop :=
  Chapter08FlatOver (chapter08BaseChangeToTest t) (chapter08BaseChangeSheaf E t)

end BaseChange

/-- A base-change package records flatness after every test-scheme base change
and the resulting fiber polynomial. -/
structure Chapter08BaseChangeHilbertData
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (D : Chapter08FiberwiseHilbertData E) where
  fiberPolynomialAfterBaseChange :
    ∀ {T : Scheme} (_t : T ⟶ F.family.S), T → Chapter08NumericalPolynomial
  fiberPolynomial_compatibility : Prop

/-- The book-facing condition that a base change has flat sheaf and constant
fiber polynomial `P`. -/
def Chapter08BaseChangeHasFlatPolynomial
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    {D : Chapter08FiberwiseHilbertData E}
    (B : Chapter08BaseChangeHilbertData E D) {T : Scheme}
    (t : T ⟶ F.family.S) (P : Chapter08NumericalPolynomial) : Prop :=
  chapter08BaseChangeFlatness (F := F) (E := E) (t := t) ∧
    ∀ s : T, B.fiberPolynomialAfterBaseChange t s = P

/-- A locally closed flattening stratum, represented by an immersion into the
base scheme.  It is deliberately not asserted to be open. -/
structure Chapter08FlatteningStratum (S : Scheme) where
  stratum : Scheme
  inclusion : stratum ⟶ S
  immersion : IsImmersion inclusion

/-- A stratum meets a subset of the base if one of its points maps into it. -/
def Chapter08StratumMeets {S : Scheme} (D : Chapter08FlatteningStratum S)
    (U : Set S) : Prop :=
  ∃ x : D.stratum, D.inclusion x ∈ U

end
end Chapter08
end Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers
end LastLib
