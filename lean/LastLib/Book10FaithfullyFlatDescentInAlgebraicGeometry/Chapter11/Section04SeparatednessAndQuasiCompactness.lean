import Mathlib.AlgebraicGeometry.Morphisms.Descent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.MorphismProperty.Descent

import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.Section01TheoremAndHypotheses

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme

universe u

namespace SchemeDescent

/-- The morphism property represented by an fpqc singleton cover. -/
def FpqcProperty : MorphismProperty Scheme.{u} :=
  @Surjective ⊓ @Flat ⊓ @QuasiCompact

theorem IsFpqcMorphism.toFpqcProperty {S T : Scheme.{u}} {p : T ⟶ S}
    (hp : Scheme.IsFpqcMorphism p) : FpqcProperty p :=
  ⟨⟨hp.2.1, hp.1⟩, hp.2.2⟩

theorem fpqcProperty_iff_isFpqcMorphism {S T : Scheme.{u}} (p : T ⟶ S) :
    FpqcProperty p ↔ Scheme.IsFpqcMorphism p := by
  constructor
  · intro hp
    exact ⟨hp.1.2, hp.1.1, hp.2⟩
  · intro hp
    exact IsFpqcMorphism.toFpqcProperty hp

/-- A property that can be checked upstairs and descended along an fpqc cover. -/
def DescendsAlongFpqc (P : MorphismProperty Scheme.{u}) : Prop :=
  P.DescendsAlong FpqcProperty

theorem property_descends_from_fpqc {P : MorphismProperty Scheme.{u}}
    [P.DescendsAlong FpqcProperty]
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (hf : FpqcProperty f) (hP : P (pullback.fst f g)) : P g := by
  exact MorphismProperty.of_pullback_fst_of_descendsAlong hf hP

/-- The local condition needed to turn affine overlaps into finite affine overlap data. -/
def AffineIntersectionsAreQuasiCompact (X : Scheme.{u}) : Prop :=
  ∀ U V : X.Opens, IsAffineOpen U → IsAffineOpen V →
    IsCompact ((U : Set X) ∩ (V : Set X))

/-- This proposition records exactly the extra hypothesis that the shortcut through finite affine
intersections would require. The effective descent theorem itself does not assume it. -/
def NeedsQuasiSeparatedAffineIntersections (X : Scheme.{u}) : Prop :=
  AffineIntersectionsAreQuasiCompact X

theorem affine_intersections_are_quasi_compact_of_quasiSeparatedSpace
    (X : Scheme.{u}) [QuasiSeparatedSpace X] :
    AffineIntersectionsAreQuasiCompact X := by
  intro U V hU hV
  exact QuasiSeparatedSpace.inter_isCompact (U : Set X) (V : Set X)
    U.2 hU.isCompact V.2 hV.isCompact

/-- A quotient presentation has affine neighborhoods when every point is contained in an affine
open chart. This is the scheme-side criterion that must be retained for quotient constructions. -/
def HasAffineNeighbourhoods (X : Scheme.{u}) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U

theorem scheme_has_affine_neighbourhoods (X : Scheme.{u}) : HasAffineNeighbourhoods X := by
  intro x
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (by simp)
  exact ⟨U, hxU, hU⟩

/-- Pairwise transition isomorphisms for three charts. -/
structure PairwiseTransitionSystem (X : Scheme.{u}) where
  transition : ∀ _i _j : Fin 3, X ≅ X
  inverse : ∀ i j : Fin 3, (transition i j) ≪≫ (transition j i) = Iso.refl X

def SatisfiesTripleCocycle {X : Scheme.{u}} (τ : PairwiseTransitionSystem X) : Prop :=
  ∀ i j k : Fin 3,
    (τ.transition i j ≪≫ τ.transition j k) ≪≫ τ.transition k i = Iso.refl X

structure NonCocyclicPairwiseGluing (X : Scheme.{u}) extends PairwiseTransitionSystem X where
  nontrivial_triple :
    ∃ i j k,
      (toPairwiseTransitionSystem.transition i j ≪≫
          toPairwiseTransitionSystem.transition j k) ≪≫
            toPairwiseTransitionSystem.transition k i ≠ Iso.refl X

theorem noncocyclic_pairwise_gluing_has_no_descent
    {X : Scheme.{u}} (G : NonCocyclicPairwiseGluing X) :
    ¬ SatisfiesTripleCocycle G.toPairwiseTransitionSystem := by
  intro h
  obtain ⟨i, j, k, hijk⟩ := G.nontrivial_triple
  exact hijk (h i j k)

/-- Effectivity has no separatedness, quasi-compactness, finite-type, or noetherian hypothesis on
the object being descended. -/
theorem effective_without_object_finiteness_assumptions {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Scheme.IsFpqcMorphism p) :
    SchemeDescent.IsEffective (fun _ : PUnit => p) := by
  exact SchemeDescent.singleton_effective_of_fpqc p hp

end SchemeDescent

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11
