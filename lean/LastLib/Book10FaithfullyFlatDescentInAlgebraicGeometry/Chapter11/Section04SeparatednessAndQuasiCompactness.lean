import Mathlib.AlgebraicGeometry.Morphisms.Descent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.MorphismProperty.Descent

import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.Section03GluingTheQuotient

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme

universe u

namespace SchemeDescent

/-- The morphism property represented by an fpqc singleton cover. -/
def FpqcProperty : MorphismProperty Scheme :=
  @Surjective ⊓ @Flat ⊓ @QuasiCompact

theorem IsFpqcMorphism.toFpqcProperty {S T : Scheme} {p : T ⟶ S}
    (hp : Scheme.IsFpqcMorphism p) : FpqcProperty p :=
  ⟨hp.2.1, hp.1, hp.2.2⟩

theorem fpqcProperty_iff_isFpqcMorphism {S T : Scheme} (p : T ⟶ S) :
    FpqcProperty p ↔ Scheme.IsFpqcMorphism p := by
  constructor
  · intro hp
    exact ⟨hp.2.1, hp.1, hp.2.2⟩
  · intro hp
    exact hp.toFpqcProperty

/-- A property that can be checked upstairs and descended along an fpqc cover. -/
def DescendsAlongFpqc (P : MorphismProperty Scheme) : Prop :=
  P.DescendsAlong FpqcProperty

theorem property_descends_from_fpqc {P : MorphismProperty Scheme}
    [P.DescendsAlong FpqcProperty]
    {X Y S : Scheme} {f : X ⟶ S} {g : Y ⟶ S}
    (hf : FpqcProperty f) (hP : P (pullback.fst f g)) : P g := by
  exact MorphismProperty.of_pullback_fst_of_descendsAlong hf hP

/-- The local condition needed to turn affine overlaps into finite affine overlap data. -/
def AffineIntersectionsAreQuasiCompact (X : Scheme) : Prop :=
  ∀ U V : X.Opens, IsAffineOpen U → IsAffineOpen V →
    IsCompact ((U : Set X) ∩ (V : Set X))

/-- This proposition records exactly the extra hypothesis that the shortcut through finite affine
intersections would require. The effective descent theorem itself does not assume it. -/
def NeedsQuasiSeparatedAffineIntersections (X : Scheme) : Prop :=
  ¬ AffineIntersectionsAreQuasiCompact X

theorem affine_intersections_are_quasi_compact_of_quasiSeparatedSpace
    (X : Scheme) [QuasiSeparatedSpace X] :
    AffineIntersectionsAreQuasiCompact X := by
  sorry

/-- A quotient presentation has affine neighborhoods when every point is contained in an affine
open chart. This is the scheme-side criterion that must be retained for quotient constructions. -/
def HasAffineNeighbourhoods (X : Scheme) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U

theorem scheme_has_affine_neighbourhoods (X : Scheme) : HasAffineNeighbourhoods X := by
  sorry

/-- Pairwise transition isomorphisms for three charts. -/
structure PairwiseTransitionSystem (X : Scheme) where
  transition : Fin 3 → Fin 3 → X ≅ X
  inverse : ∀ i j, transition i j ≪≫ transition j i = Iso.refl X

def SatisfiesTripleCocycle {X : Scheme} (τ : PairwiseTransitionSystem X) : Prop :=
  ∀ i j k,
    (τ.transition i j ≪≫ τ.transition j k) ≪≫ τ.transition k i = Iso.refl X

structure NonCocyclicPairwiseGluing (X : Scheme) extends PairwiseTransitionSystem X where
  nontrivial_triple :
    ∃ i j k,
      (toPairwiseTransitionSystem.transition i j ≪≫
          toPairwiseTransitionSystem.transition j k) ≪≫
            toPairwiseTransitionSystem.transition k i ≠ Iso.refl X

theorem noncocyclic_pairwise_gluing_has_no_descent
    {X : Scheme} (G : NonCocyclicPairwiseGluing X) :
    ¬ SatisfiesTripleCocycle G.toPairwiseTransitionSystem := by
  intro h
  obtain ⟨i, j, k, hijk⟩ := G.nontrivial_triple
  exact hijk (h i j k)

/-- Effectivity has no separatedness, quasi-compactness, finite-type, or noetherian hypothesis on
the object being descended. -/
theorem effective_without_object_finiteness_assumptions {S T : Scheme} (p : T ⟶ S)
    (hp : Scheme.IsFpqcMorphism p) :
    SchemeDescent.IsEffective (fun _ : PUnit => p) := by
  exact SchemeDescent.singleton_effective_of_fpqc p hp

end SchemeDescent

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11
