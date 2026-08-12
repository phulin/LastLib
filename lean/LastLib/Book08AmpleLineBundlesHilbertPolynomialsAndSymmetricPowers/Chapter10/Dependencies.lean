import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Comma.Over.Basic

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits SheafOfModules TopologicalSpace

universe u

/-!
The source chapter uses "finite locally free of rank `d`" throughout.  The
current pinned Mathlib API exposes this through the finite, flat, locally
finitely presented morphism and its `finrank` function, so the profile below
keeps those four pieces together instead of introducing a competing notion of
rank.
-/

abbrev Chapter10ClosedSubscheme (X : Scheme) := X.IdealSheafData

noncomputable def chapter10ClosedSubschemeCarrier {X : Scheme}
    (Z : Chapter10ClosedSubscheme X) : Scheme :=
  Z.subscheme

noncomputable def chapter10ClosedSubschemeInclusion {X : Scheme}
    (Z : Chapter10ClosedSubscheme X) : Z.subscheme ⟶ X :=
  Z.subschemeι

theorem chapter10_closedSubscheme_inclusion_isClosedImmersion {X : Scheme}
    (Z : Chapter10ClosedSubscheme X) : IsClosedImmersion Z.subschemeι := by
  infer_instance

theorem chapter10_closedSubscheme_ext {X : Scheme}
    {Z W : Chapter10ClosedSubscheme X} : Z = W ↔ Z.ideal = W.ideal := by
  constructor
  · intro h
    cases h
    rfl
  · exact fun h => Scheme.IdealSheafData.ext h

theorem chapter10_closedSubscheme_comap_comp {X Y Z : Scheme}
    (I : Chapter10ClosedSubscheme Z) (f : X ⟶ Y) (g : Y ⟶ Z) :
    I.comap (f ≫ g) = (I.comap g).comap f := by
  simp

theorem chapter10_closedSubscheme_comap_id {X : Scheme}
    (I : Chapter10ClosedSubscheme X) : I.comap (𝟙 X) = I := by
  simp

theorem chapter10_closedSubscheme_comap_support {X Y : Scheme}
    (I : Chapter10ClosedSubscheme Y) (f : X ⟶ Y) :
    (I.comap f).support = I.support.preimage f.continuous := by
  simp

structure Chapter10FiniteLocallyFreeProfile {X Y : Scheme} (q : X ⟶ Y) (d : ℕ) : Prop where
  finite : IsFinite q
  flat : Flat q
  locallyOfFinitePresentation : LocallyOfFinitePresentation q
  rank : ∀ y : Y, Scheme.Hom.finrank q y = d

abbrev Chapter10FiniteLocallyFree {X Y : Scheme} (q : X ⟶ Y) (d : ℕ) :=
  Chapter10FiniteLocallyFreeProfile q d

def Chapter10FiniteLocallyFreeMorphism {X Y : Scheme} (q : X ⟶ Y) : Prop :=
  ∃ d : ℕ, Chapter10FiniteLocallyFreeProfile q d

abbrev Chapter10FiberLength {X Y : Scheme} (q : X ⟶ Y) (y : Y) : ℕ :=
  Scheme.Hom.finrank q y

theorem chapter10_finiteLocallyFree_rank {X Y : Scheme} {q : X ⟶ Y} {d : ℕ}
    (h : Chapter10FiniteLocallyFreeProfile q d) (y : Y) :
    Chapter10FiberLength q y = d :=
  h.rank y

theorem chapter10_finiteLocallyFree_isFinite {X Y : Scheme} {q : X ⟶ Y} {d : ℕ}
    (h : Chapter10FiniteLocallyFreeProfile q d) : IsFinite q :=
  h.finite

theorem chapter10_finiteLocallyFree_isFlat {X Y : Scheme} {q : X ⟶ Y} {d : ℕ}
    (h : Chapter10FiniteLocallyFreeProfile q d) : Flat q :=
  h.flat

theorem chapter10_finiteLocallyFree_isLocallyOfFinitePresentation
    {X Y : Scheme} {q : X ⟶ Y} {d : ℕ}
    (h : Chapter10FiniteLocallyFreeProfile q d) : LocallyOfFinitePresentation q :=
  h.locallyOfFinitePresentation

theorem chapter10_finiteLocallyFree_baseChange {X Y S : Scheme} (q : X ⟶ S) (g : Y ⟶ S)
    (d : ℕ) (h : Chapter10FiniteLocallyFreeProfile q d) :
    Chapter10FiniteLocallyFreeProfile (pullback.snd q g) d := by
  sorry

theorem chapter10_finiteLocallyFree_rank_isLocallyConstant {X Y : Scheme}
    (q : X ⟶ Y) (d : ℕ) (h : Chapter10FiniteLocallyFreeProfile q d) :
    IsLocallyConstant (Scheme.Hom.finrank q) := by
  exact @Scheme.Hom.isLocallyConstant_finrank _ _ q h.flat h.finite
    h.locallyOfFinitePresentation

theorem chapter10_finiteLocallyFree_geometric_fibers {X Y : Scheme} (q : X ⟶ Y) (d : ℕ)
    (h : Chapter10FiniteLocallyFreeProfile q d) :
    ∀ y : Y, Scheme.Hom.finrank q y = d ∧ IsArtinianScheme (q.fiber y) := by
  sorry

def chapter10BaseChangeMap {X S T T' : Scheme} (q : X ⟶ S) (t : T ⟶ S) (u : T' ⟶ T) :
    pullback q (u ≫ t) ⟶ pullback q t :=
  pullback.map q (u ≫ t) q t (𝟙 X) u (𝟙 S) (by simp) (by simp)

def chapter10StructureSheaf (X : Scheme) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-!
`IsLocallyFree` is already the canonical pinned-Mathlib predicate.  The
rank-one clause records the usual one-generator local presentation, rather
than replacing it with an opaque proposition.
-/

def Chapter10RankOne {X : Scheme.{u}} (M : Scheme.Modules X) : Prop :=
  ∃ q : M.LocalGeneratorsData.{u}, q.IsLocallyFreeData ∧
    ∀ i : q.I, Nonempty ((q.generators i).I ≃ Unit)

structure Chapter10LineBundle (X : Scheme.{u}) where
  module : X.Modules
  locallyFree : module.IsLocallyFree
  rankOne : Chapter10RankOne module

abbrev Chapter10LineBundleSection {X : Scheme} (L : Chapter10LineBundle X) :=
  chapter10StructureSheaf X ⟶ L.module

def Chapter10LineBundleIso {X : Scheme} (L M : Chapter10LineBundle X) : Prop :=
  Nonempty (L.module ≅ M.module)

/- LOCAL_DEPENDENCY_GUESS (10.2, 10.4): the pinned Mathlib snapshot has the
  local-freeness predicate but not yet the Picard/tensor and inverse-line-bundle
  constructors used by the textbook.  These explicit operations are the
  smallest book-facing interface needed by the Cartier and norm statements;
  their coherence and comparison with sheaf tensor products belong in the
  later dependency/fixup pass. -/
class Chapter10PicardOperations (X : Scheme) where
  tensor : Chapter10LineBundle X → Chapter10LineBundle X → Chapter10LineBundle X
  dual : Chapter10LineBundle X → Chapter10LineBundle X

class Chapter10IdealDualAPI (X : Scheme) where
  inverseIdeal : X.IdealSheafData → Chapter10LineBundle X

class Chapter10DeterminantLineAPI {X Y : Scheme} (q : X ⟶ Y) where
  finiteLocallyFree : Chapter10FiniteLocallyFreeMorphism q
  determinant : Y.Modules → Chapter10LineBundle Y

class Chapter10LineBundlePullbackAPI {X Y : Scheme} (f : X ⟶ Y) where
  pullback : Chapter10LineBundle Y → Chapter10LineBundle X

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
