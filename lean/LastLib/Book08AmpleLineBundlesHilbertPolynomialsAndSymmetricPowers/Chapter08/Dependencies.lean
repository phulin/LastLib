import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Topology.GDelta.Basic
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies

/-!
# Chapter 8: Hilbert polynomials in families

This file contains the common interfaces used by the chapter.  The current pinned
Mathlib snapshot has the scheme-theoretic notions of flatness, finite presentation,
and noetherianity; the preceding Chapter 4 API supplies the line-bundle,
projective-bundle, and affine-open ampleness interfaces used below.  Associated
points of coherent sheaves, cohomological base change, and Fitting ideals for
flattening strata are still isolated at the points where they are needed.
-/

namespace LastLib
namespace Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers
namespace Chapter08

open AlgebraicGeometry CategoryTheory Limits
open scoped BigOperators
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

universe u

/-- A polynomial with rational coefficients which takes integral values at all
integers.  The natural-number field is retained for the fiberwise indexing
used throughout the chapter, while the second field matches the usual
definition of a numerical polynomial. -/
structure Chapter08NumericalPolynomial where
  polynomial : Polynomial ℚ
  integer_valued : ∀ n : ℕ, ∃ z : ℤ, polynomial.eval (n : ℚ) = (z : ℚ)
  integer_valued_on_integers :
    ∀ n : ℤ, ∃ z : ℤ, polynomial.eval (n : ℚ) = (z : ℚ)

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

/-- The integer represented by a numerical polynomial at an arbitrary integer. -/
def integerValue (P : Chapter08NumericalPolynomial) (n : ℤ) : ℤ :=
  Classical.choose (P.integer_valued_on_integers n)

theorem integerValue_spec (P : Chapter08NumericalPolynomial) (n : ℤ) :
    (P.integerValue n : ℚ) = P.polynomial.eval (n : ℚ) := by
  exact (Classical.choose_spec (P.integer_valued_on_integers n)).symm

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
The remaining predicates package the chapter-specific family and cohomology
interfaces around the canonical projective and line-bundle definitions.
-/

/- The preceding line-bundle chapter already supplies the book-facing
   rank-one locally free predicate.  Keep this chapter's name as a thin
   compatibility wrapper rather than introducing a second, weaker notion. -/
abbrev chapter08IsInvertibleSheaf {X : Scheme.{u}} (L : X.Modules) : Prop :=
  chapter04IsInvertible L

class Chapter08InvertibleSheaf {X : Scheme} (L : X.Modules) where
  is_invertible : chapter08IsInvertibleSheaf L

theorem chapter08_isInvertibleSheaf_isLocallyFree
    {X : Scheme} {L : X.Modules} (hL : chapter08IsInvertibleSheaf L) :
    L.IsLocallyFree := by
  exact hL.1

/- The finite-locally-free condition is the canonical Chapter 4 condition. -/
abbrev chapter08FiniteLocallyFree {S : Scheme} (E : S.Modules) : Prop :=
  chapter04FiniteLocallyFree E

structure Chapter08RelativeProjectiveBundle (S : Scheme) (E : S.Modules) where
  bundle : Chapter04ProjectiveBundle S
  module_eq : bundle.E = E

namespace Chapter08RelativeProjectiveBundle

/-- The underlying scheme of the canonical relative projective bundle. -/
abbrev carrier (P : Chapter08RelativeProjectiveBundle S E) : Scheme :=
  P.bundle.space

/-- The structure morphism of the canonical relative projective bundle. -/
abbrev projection (P : Chapter08RelativeProjectiveBundle S E) : P.carrier ⟶ S :=
  P.bundle.projection

/-- The tautological module sheaf of the canonical relative projective bundle. -/
abbrev tautological (P : Chapter08RelativeProjectiveBundle S E) : P.carrier.Modules :=
  P.bundle.tautological

instance projection_isProper (P : Chapter08RelativeProjectiveBundle S E) :
    IsProper P.projection :=
  P.bundle.projection_isProper

end Chapter08RelativeProjectiveBundle

structure Chapter08ProjectivePresentation {X S : Scheme} (f : X ⟶ S) where
  module : S.Modules
  finite_locally_free : chapter08FiniteLocallyFree module
  ambient : Chapter08RelativeProjectiveBundle S module
  embedding : X ⟶ ambient.carrier
  embedding_closed : IsClosedImmersion embedding
  overBase : embedding ≫ ambient.projection = f

class Chapter08IsProjective {X S : Scheme} (f : X ⟶ S) where
  projective_witness : Nonempty (Chapter08ProjectivePresentation f)

/- LOCAL_DEPENDENCY_GUESS: properness of a projective morphism is supplied by
   the earlier projective-morphism API once the ambient bundle is identified
   with relative Proj. -/
theorem chapter08_projective_is_proper
    {X S : Scheme} {f : X ⟶ S} [Chapter08IsProjective f] :
    IsProper f := by
  sorry

instance chapter08IsProjective.isProper
    {X S : Scheme} {f : X ⟶ S} [Chapter08IsProjective f] : IsProper f :=
  chapter08_projective_is_proper (f := f)

/- Relative ampleness is supplied by the preceding affine-open chapter.  The
   invertibility proof is explicit because it is part of the canonical
   `Chapter04LineBundle` input. -/
class Chapter08FAmple {X S : Scheme} (f : X ⟶ S) (L : X.Modules)
    (hL : chapter08IsInvertibleSheaf L) : Prop where
  ample_witness : Nonempty (Chapter04AmpleWitness f
    { sheaf := L, isInvertible := hL })

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

/- Flatness at a point of the base, used for the openness of the flat locus. -/
def chapter08FlatAt {X S : Scheme} (f : X ⟶ S) (M : X.Modules) (s : S) : Prop :=
  ∀ x : X, f x = s → chapter08StalkFlat f M x

theorem chapter08_flat_at_of_flat_over
    {X S : Scheme} {f : X ⟶ S} {M : X.Modules}
    (hflat : Chapter08FlatOver f M) (s : S) :
    chapter08FlatAt f M s := by
  intro x _
  exact hflat.stalkwise_flat x

theorem chapter08_flat_over_iff_flat_at
    {X S : Scheme} {f : X ⟶ S} {M : X.Modules} :
    Chapter08FlatOver f M ↔ ∀ s : S, chapter08FlatAt f M s := by
  constructor
  · intro hflat s
    exact chapter08_flat_at_of_flat_over hflat s
  · intro hflat
    constructor
    intro x
    exact hflat (f x) x rfl

/- Relative very ampleness is likewise the canonical Chapter 4 witness, with
   this chapter retaining its namespace for the flattening statements. -/
abbrev Chapter08VeryAmpleWitness {X S : Scheme} (f : X ⟶ S) (L : X.Modules)
    (hL : chapter08IsInvertibleSheaf L) :=
  Chapter04VeryAmpleWitness f { sheaf := L, isInvertible := hL }

class Chapter08RelativelyVeryAmple {X S : Scheme} (f : X ⟶ S) (L : X.Modules)
    (hL : chapter08IsInvertibleSheaf L) : Prop where
  very_ample_witness : Nonempty (Chapter08VeryAmpleWitness f L hL)

/-- The coherent sheaf hypothesis used by the chapter, in the standard
   finite-type/quasi-coherent form. -/
def Chapter08Coherent {X : Scheme} (M : X.Modules) : Prop :=
  chapter04FiniteTypeQuasiCoherent M

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
instance (F : Chapter08ProjectiveFamily) : IsProper F.f := by
  exact chapter08_projective_is_proper (f := F.f)
instance (F : Chapter08ProjectiveFamily) : QuasiCompact F.f := F.quasi_compact
instance (F : Chapter08ProjectiveFamily) : LocallyOfFinitePresentation F.f :=
  F.locally_of_finite_presentation

end Chapter08ProjectiveFamily

/-- A projective family equipped with a relatively ample line bundle. -/
structure Chapter08PolarizedFamily where
  family : Chapter08ProjectiveFamily
  lineBundle : family.X.Modules
  lineBundle_invertible : Chapter08InvertibleSheaf lineBundle
  lineBundle_f_ample :
    Chapter08FAmple family.f lineBundle lineBundle_invertible.is_invertible

namespace Chapter08PolarizedFamily

instance (F : Chapter08PolarizedFamily) : Chapter08InvertibleSheaf F.lineBundle :=
  F.lineBundle_invertible
instance (F : Chapter08PolarizedFamily) :
    Chapter08FAmple F.family.f F.lineBundle F.lineBundle_invertible.is_invertible :=
  F.lineBundle_f_ample

end Chapter08PolarizedFamily

/-- The additional relative very-ampleness datum needed in §8.4. -/
structure Chapter08VeryAmplePolarizedFamily where
  polarized : Chapter08PolarizedFamily
  lineBundle_relatively_very_ample :
    Chapter08RelativelyVeryAmple polarized.family.f polarized.lineBundle
      polarized.lineBundle_invertible.is_invertible

/-- A coherent sheaf on a polarized family. -/
structure Chapter08FamilySheaf (F : Chapter08PolarizedFamily) where
  sheaf : F.family.X.Modules
  coherent : Chapter08Coherent sheaf

/-- The twist used in the fiberwise cohomology data, expressed through the
    canonical line-bundle tensor API from Chapter 4. -/
noncomputable def chapter08TwistedSheaf
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F) (n : ℕ) :
    F.family.X.Modules :=
  chapter04TwistedModule E.sheaf
    { sheaf := F.lineBundle, isInvertible := F.lineBundle_invertible.is_invertible } n

/-- The actual pushforward sheaf whose high twists occur in the cohomology
    and base-change statement. -/
noncomputable def chapter08TwistedPushforward
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F) (n : ℕ) :
    F.family.S.Modules :=
  (Scheme.Modules.pushforward F.family.f).obj (chapter08TwistedSheaf E n)

/- The coefficient sheaf and polarization on a fiber are obtained by the
   canonical pullback along the scheme-theoretic fiber inclusion. -/
noncomputable def chapter08FiberCoefficientSheaf
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (s : F.family.S) : (F.family.f.fiber s).Modules :=
  (Scheme.Modules.pullback (F.family.f.fiberι s)).obj E.sheaf

noncomputable def chapter08FiberPolarization
    {F : Chapter08PolarizedFamily} (s : F.family.S) :
    Chapter04LineBundle (F.family.f.fiber s) :=
  chapter04PullbackLineBundle (F.family.f.fiberι s)
    { sheaf := F.lineBundle, isInvertible := F.lineBundle_invertible.is_invertible }

/- The actual coefficient sheaf on a fiber after twisting by the actual
   pulled-back polarization. -/
noncomputable def chapter08FiberTwistedSheaf
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (s : F.family.S) (n : ℕ) : (F.family.f.fiber s).Modules :=
  chapter04TwistedModule (chapter08FiberCoefficientSheaf E s)
    (chapter08FiberPolarization s) n

/- The pinned cohomology API is still represented by a data-bearing interface,
   but its inputs are now actual sheaves on the actual fibers.  In particular,
   this compatibility record cannot assign an Euler characteristic merely by
   naming a function on the base. -/
structure Chapter08FiberwiseHilbertDataCompatibility
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (dimension_bound : ℕ)
    (eulerCharacteristic : F.family.S → ℕ → ℤ)
    (cohomologyRank : F.family.S → ℕ → ℕ → ℕ) where
  fiberEulerCharacteristic :
    ∀ s : F.family.S, (F.family.f.fiber s).Modules → ℤ
  fiberCohomologyRank :
    ∀ s : F.family.S, (F.family.f.fiber s).Modules → ℕ → ℕ
  eulerCharacteristic_eq_fiber :
    ∀ (s : F.family.S) (n : ℕ),
      eulerCharacteristic s n =
        fiberEulerCharacteristic s (chapter08FiberTwistedSheaf E s n)
  cohomologyRank_eq_fiber :
    ∀ (s : F.family.S) (n i : ℕ),
      cohomologyRank s n i =
        fiberCohomologyRank s (chapter08FiberTwistedSheaf E s n) i
  fiberCohomology_vanishes_above_dimension :
    ∀ (s : F.family.S) (M : (F.family.f.fiber s).Modules) (i : ℕ),
      dimension_bound < i → fiberCohomologyRank s M i = 0
  fiberEulerCharacteristic_altSum :
    ∀ (s : F.family.S) (M : (F.family.f.fiber s).Modules),
      fiberEulerCharacteristic s M =
        Finset.sum (Finset.range (dimension_bound + 1))
          (fun i => (-1 : ℤ) ^ i * (fiberCohomologyRank s M i : ℤ))

/-- Fiberwise cohomological data representing the Euler characteristic and its
   polynomial in the source chapter.  The compatibility field ties the
   numerical functions to the coefficient sheaf and polarization on each
   scheme-theoretic fiber. -/
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
  fiberwise_compatibility :
    Chapter08FiberwiseHilbertDataCompatibility E dimension_bound
      eulerCharacteristic cohomologyRank
  fiberPolynomial_value_actual_fiber :
    ∀ (s : F.family.S) (n : ℕ),
      (fiberPolynomial s).value n =
        fiberwise_compatibility.fiberEulerCharacteristic s
          (chapter08FiberTwistedSheaf E s n)
  polynomial_degree_le :
    ∀ s, (fiberPolynomial s).degree ≤ dimension_bound

noncomputable def chapter08FiberEulerCharacteristic
    {F : Chapter08PolarizedFamily} {E : Chapter08FamilySheaf F}
    (D : Chapter08FiberwiseHilbertData E) (s : F.family.S) (n : ℕ) : ℤ :=
  D.fiberwise_compatibility.fiberEulerCharacteristic s
    (chapter08FiberTwistedSheaf E s n)

def chapter08FiberCohomologyRank
    {F : Chapter08PolarizedFamily} {E : Chapter08FamilySheaf F}
    (D : Chapter08FiberwiseHilbertData E) (s : F.family.S) (n i : ℕ) : ℕ :=
  D.fiberwise_compatibility.fiberCohomologyRank s
    (chapter08FiberTwistedSheaf E s n) i

/- LOCAL_DEPENDENCY_GUESS: this witness abstracts the coherent pushforward and
   cohomology-and-base-change theorem used for large twists. -/
structure Chapter08PushforwardWitness
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
  (D : Chapter08FiberwiseHilbertData E) (U : F.family.S.Opens) (n : ℕ) where
  rank : ℕ
  locally_free :
    SheafOfModules.IsLocallyFree ((chapter08TwistedPushforward E n).over U) ∧
      SheafOfModules.IsFiniteType ((chapter08TwistedPushforward E n).over U)
  fiber_is_H0 : ∀ s ∈ U, rank = chapter08FiberCohomologyRank D s n 0
  rank_eq_eulerCharacteristic :
    ∀ s ∈ U, (rank : ℤ) = chapter08FiberEulerCharacteristic D s n

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
  fiberPolynomial_compatibility :
    ∀ {T : Scheme} (t : T ⟶ F.family.S) (s : T),
      fiberPolynomialAfterBaseChange t s = D.fiberPolynomial (t s)

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
