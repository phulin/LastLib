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
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.CategoryTheory.Abelian.Exact
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits SheafOfModules TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09

universe u

/-!
The source chapter uses "finite locally free of rank `d`" throughout.  The
current pinned Mathlib API exposes this through the finite, flat, locally
finitely presented morphism and its `finrank` function, so the profile below
keeps those four pieces together instead of introducing a competing notion of
rank.
-/

/-!
The finite-flat and Cartier predicates were introduced in Chapter 9. Reuse
those chapter interfaces here rather than creating definitionally similar
records with a separate notion of the same data.
-/
abbrev Chapter10ClosedSubscheme (X : Scheme) := Chapter09ClosedSubscheme X

abbrev Chapter10FiniteLocallyFreeProfile {X Y : Scheme} (q : X ⟶ Y) (d : ℕ) :=
  Chapter09FiniteLocallyFreeProfile q d

abbrev Chapter10LocallyRegularPrincipal {X : Scheme}
    (D : Chapter10ClosedSubscheme X) : Prop :=
  Chapter09LocallyRegularPrincipal D

abbrev Chapter10EffectiveCartierDivisor (X : Scheme) :=
  Chapter09EffectiveCartierDivisor X

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

abbrev Chapter10FiniteLocallyFree {X Y : Scheme} (q : X ⟶ Y) (d : ℕ) :=
  Chapter10FiniteLocallyFreeProfile q d

def Chapter10FiniteLocallyFreeMorphism {X Y : Scheme} (q : X ⟶ Y) : Prop :=
  IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q

theorem chapter10_finiteLocallyFreeProfile_to_morphism {X Y : Scheme}
    {q : X ⟶ Y} {d : ℕ} (h : Chapter10FiniteLocallyFreeProfile q d) :
    Chapter10FiniteLocallyFreeMorphism q :=
  ⟨h.finite, h.flat, h.locallyOfFinitePresentation⟩

theorem chapter10_finiteLocallyFreeMorphism_rank_isLocallyConstant {X Y : Scheme}
    {q : X ⟶ Y} (h : Chapter10FiniteLocallyFreeMorphism q) :
    IsLocallyConstant (Scheme.Hom.finrank q) := by
  exact @Scheme.Hom.isLocallyConstant_finrank _ _ q h.2.1 h.1 h.2.2

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

abbrev Chapter10LineBundle (X : Scheme.{u}) := Chapter09LineBundle X

/-!
The norm compares the determinant of a line bundle with the determinant of the
structure sheaf.  Keep the latter as a book-facing line bundle rather than
allowing the determinant interface to accept arbitrary module sheaves.
-/
noncomputable def chapter10StructureSheafLineBundle (X : Scheme.{u}) :
    Chapter10LineBundle X :=
  chapter09StructureSheafLineBundle X

@[ext]
theorem chapter10_lineBundle_ext {X : Scheme} {L M : Chapter10LineBundle X}
    (h : L.module = M.module) : L = M := by
  cases L
  cases M
  cases h
  rfl

abbrev Chapter10LineBundleSection {X : Scheme} (L : Chapter10LineBundle X) :=
  chapter10StructureSheaf X ⟶ L.module

abbrev Chapter10LineBundleIso {X : Scheme}
    (L M : Chapter10LineBundle X) := Chapter09LineBundleIso L M

def chapter10_lineBundleIso_refl {X : Scheme} (L : Chapter10LineBundle X) :
    Chapter10LineBundleIso L L :=
  ⟨Iso.refl L.module⟩

def chapter10_lineBundleIso_symm {X : Scheme}
    {L M : Chapter10LineBundle X} (h : Chapter10LineBundleIso L M) :
    Chapter10LineBundleIso M L := by
  exact ⟨h.hom.symm⟩

def chapter10_lineBundleIso_trans {X : Scheme}
    {L M N : Chapter10LineBundle X} (hLM : Chapter10LineBundleIso L M)
    (hMN : Chapter10LineBundleIso M N) : Chapter10LineBundleIso L N := by
  exact ⟨hLM.hom.trans hMN.hom⟩

/- LOCAL_DEPENDENCY_GUESS (10.4): the pinned Mathlib snapshot does not expose
  the inverse operation needed by the norm formula. Chapter 9 already
  supplies the canonical tensor theory, including its module-level comparison
  and coherence laws; only dualization remains a Chapter 10 interface. -/
class Chapter10PicardOperations (X : Scheme) extends Chapter09LineBundleTensorTheory X where
  dual : Chapter10LineBundle X → Chapter10LineBundle X
  dual_module_iso : ∀ L,
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04Tensor
        (dual L).module L.module ≅ chapter10StructureSheaf X

def chapter10PicardTensor {X : Scheme} [Chapter10PicardOperations X]
    (L M : Chapter10LineBundle X) : Chapter10LineBundle X :=
  Chapter09LineBundleTensorTheory.tensor L M

class Chapter10DeterminantLineAPI {X Y : Scheme} (q : X ⟶ Y) where
  finiteLocallyFree : Chapter10FiniteLocallyFreeMorphism q
  determinant : Chapter10LineBundle X → Chapter10LineBundle Y

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
