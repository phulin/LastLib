import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.RingHom.Flat

/-!
# Chapter 5: base change and descent

This file contains the book-facing interfaces used by the four sections of the chapter.  The
scheme-theoretic operations are the pinned Mathlib operations; the positivity vocabulary is kept
small so that it can be replaced by the canonical line-bundle API supplied by the earlier chapters.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05

noncomputable section

/- LOCAL_DEPENDENCY_GUESS: Mathlib exposes `Flat` and `Surjective` separately for scheme
morphisms, while the book uses the combined phrase faithfully flat.  This is the weakest
book-facing proposition needed in this chapter. -/
def IsFaithfullyFlat {S T : Scheme.{u}} (g : T ⟶ S) : Prop :=
  Flat g ∧ Surjective g

def IsFpqcCover {S T : Scheme.{u}} (g : T ⟶ S) : Prop :=
  IsFaithfullyFlat g ∧ QuasiCompact g

/- LOCAL_DEPENDENCY_GUESS: The pinned Mathlib API has locally free sheaves but no rank-one
invertible-sheaf predicate.  The following is the direct local-triviality interface needed for a
line bundle. -/
def IsInvertibleSheaf (X : Scheme.{u}) (M : X.Modules) : Prop :=
  ∃ (ι : Type u) (U : ι → X.Opens),
    iSup U = ⊤ ∧
      ∀ i, Nonempty
        (M.restrict (U i).ι ≅ SheafOfModules.unit (U i).toScheme.ringCatSheaf)

structure LineBundle (X : Scheme.{u}) where
  sheaf : X.Modules
  invertible : IsInvertibleSheaf X sheaf

instance {X : Scheme.{u}} : Coe (LineBundle X) X.Modules := ⟨LineBundle.sheaf⟩

noncomputable def LineBundle.trivial (X : Scheme.{u}) : LineBundle X where
  sheaf := SheafOfModules.unit X.ringCatSheaf
  invertible := by
    refine ⟨X.Opens, (fun U => U), ?_, ?_⟩
    · apply le_antisymm le_top
      exact le_iSup (fun U : X.Opens => U) ⊤
    · intro U
      exact ⟨Scheme.Modules.restrictUnitIso U.ι⟩

def LineBundle.Isomorphic {X : Scheme.{u}} (L M : LineBundle X) : Prop :=
  Nonempty (L.sheaf ≅ M.sheaf)

@[ext]
theorem LineBundle.ext {X : Scheme.{u}} {L M : LineBundle X}
    (h : L.sheaf = M.sheaf) : L = M := by
  cases L
  cases M
  cases h
  rfl

theorem lineBundle_isomorphic_refl {X : Scheme.{u}} (L : LineBundle X) :
    L.Isomorphic L :=
  ⟨Iso.refl _⟩

theorem lineBundle_isomorphic_symm {X : Scheme.{u}} {L M : LineBundle X}
    (h : L.Isomorphic M) : M.Isomorphic L := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

theorem lineBundle_isomorphic_trans {X : Scheme.{u}} {L M N : LineBundle X}
    (hLM : L.Isomorphic M) (hMN : M.Isomorphic N) : L.Isomorphic N := by
  rcases hLM with ⟨eLM⟩
  rcases hMN with ⟨eMN⟩
  exact ⟨eLM ≪≫ eMN⟩

noncomputable def LineBundle.pullback {X Y : Scheme.{u}} (L : LineBundle Y) (f : X ⟶ Y) :
    LineBundle X where
  sheaf := (Scheme.Modules.pullback f).obj L.sheaf
  invertible := by sorry

@[simp]
theorem LineBundle.pullback_sheaf {X Y : Scheme.{u}} (L : LineBundle Y) (f : X ⟶ Y) :
    (L.pullback f).sheaf = (Scheme.Modules.pullback f).obj L.sheaf := rfl

theorem lineBundle_pullback_id {X : Scheme.{u}} (L : LineBundle X) :
    (L.pullback (𝟙 X)).Isomorphic L := by sorry

theorem lineBundle_pullback_comp {X Y Z : Scheme.{u}} (L : LineBundle Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((L.pullback g).pullback f).Isomorphic (L.pullback (f ≫ g)) := by sorry

/- LOCAL_DEPENDENCY_GUESS: Earlier book chapters are expected to supply tensor products of line
bundles.  Since the pinned Mathlib sheaf category does not yet expose that monoidal interface,
this chapter records the minimum coherent power data it consumes. -/
structure LineBundlePowers {X : Scheme.{u}} (L : LineBundle X) where
  power : ℕ → LineBundle X
  power_zero : (power 0).Isomorphic (LineBundle.trivial X)
  power_one : (power 1).Isomorphic L

noncomputable def LineBundlePowers.pullback {X Y : Scheme.{u}} {L : LineBundle Y}
    (P : LineBundlePowers L) (f : X ⟶ Y) : LineBundlePowers (L.pullback f) where
  power n := (P.power n).pullback f
  power_zero := by sorry
  power_one := by sorry

/- LOCAL_DEPENDENCY_GUESS: This is the earlier-chapter projective-bundle interface abstracted to
the fields actually used here.  Its `rank` field records finite-dimensionality locally on the
base; a later reconciliation should identify it with the canonical relative Proj construction. -/
structure RelativeProjectiveBundleData (S : Scheme.{u}) where
  /- The finite rank fields are intentional: dropping them permits the possibly infinite-rank
  ambient projective bundle mentioned in §5.2, but no finite-dimensional conclusion. -/
  ambient : Scheme.{u}
  projection : ambient ⟶ S
  tautological : LineBundle ambient
  rank : S → ℕ
  rank_pos : ∀ x, 0 < rank x
  rank_locally_constant : ∀ x, ∃ U : S.Opens, x ∈ U ∧
    ∀ y : S, y ∈ U → rank y = rank x

def IsFiniteDimensionalLocallyOnBase {S : Scheme.{u}}
    (P : RelativeProjectiveBundleData S) : Prop :=
  ∀ x, ∃ U : S.Opens, x ∈ U ∧ ∀ y : S, y ∈ U → P.rank y = P.rank x

theorem relativeProjectiveBundleData_finiteDimensional {S : Scheme.{u}}
    (P : RelativeProjectiveBundleData S) : IsFiniteDimensionalLocallyOnBase P :=
  P.rank_locally_constant

structure RelativeImmersionWitness {X S : Scheme.{u}} (f : X ⟶ S) where
  projectiveBundle : RelativeProjectiveBundleData S
  embedding : X ⟶ projectiveBundle.ambient
  over : embedding ≫ projectiveBundle.projection = f
  immersion : IsImmersion embedding

structure RelativeClosedImmersionWitness {X S : Scheme.{u}} (f : X ⟶ S) where
  projectiveBundle : RelativeProjectiveBundleData S
  embedding : X ⟶ projectiveBundle.ambient
  over : embedding ≫ projectiveBundle.projection = f
  closedImmersion : IsClosedImmersion embedding

structure RelativeVeryAmpleWitness {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) where
  projectiveBundle : RelativeProjectiveBundleData S
  embedding : X ⟶ projectiveBundle.ambient
  over : embedding ≫ projectiveBundle.projection = f
  immersion : IsImmersion embedding
  pullback_iso : L.Isomorphic (projectiveBundle.tautological.pullback embedding)

def IsVeryAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) : Prop :=
  Nonempty (RelativeVeryAmpleWitness f L)

def IsQuasiProjectiveMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Nonempty (RelativeImmersionWitness f)

def IsProjectiveMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Nonempty (RelativeClosedImmersionWitness f)

structure RelativeAmpleWitness {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) where
  powers : LineBundlePowers L
  index : Type u
  opens : index → S.Opens
  cover : iSup opens = ⊤
  power : index → ℕ
  positive : ∀ i, 0 < power i
  local_veryAmple : ∀ i,
    IsVeryAmple (f ∣_ (opens i))
      ((powers.power (power i)).pullback ((f ⁻¹ᵁ (opens i)).ι))

def IsAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) : Prop :=
  Nonempty (RelativeAmpleWitness f L)

theorem isVeryAmple_congr {X S : Scheme.{u}} (f : X ⟶ S)
    {L M : LineBundle X} (hLM : L.Isomorphic M) :
    IsVeryAmple f L ↔ IsVeryAmple f M := by sorry

theorem isAmple_congr {X S : Scheme.{u}} (f : X ⟶ S)
    {L M : LineBundle X} (hLM : L.Isomorphic M) :
    IsAmple f L ↔ IsAmple f M := by sorry

noncomputable def baseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) : Scheme.{u} :=
  pullback f g

def baseChangeToSource {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    baseChange f g ⟶ X :=
  pullback.fst f g

def baseChangeToBase {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    baseChange f g ⟶ T :=
  pullback.snd f g

noncomputable def baseChangeLineBundle {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (L : LineBundle X) : LineBundle (baseChange f g) :=
  L.pullback (baseChangeToSource f g)

def IsBaseChangeOf {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (L : LineBundle X)
    (M : LineBundle (baseChange f g)) : Prop :=
  M.Isomorphic (baseChangeLineBundle f g L)

theorem baseChangeLineBundle_isBaseChangeOf {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (L : LineBundle X) : IsBaseChangeOf f g L (baseChangeLineBundle f g L) :=
  lineBundle_isomorphic_refl _

structure FiniteAffineOpenCover (X : Scheme.{u}) where
  index : Type u
  finite_index : Finite index
  opens : index → X.Opens
  affine : ∀ i, IsAffineOpen (opens i)
  cover : iSup opens = ⊤

structure FiniteSectionFamily {X : Scheme.{u}} (M : X.Modules) where
  index : Type u
  finite_index : Finite index
  sections : index → Γ(M, ⊤)

def IsFiberwiseVeryAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) : Prop :=
  ∀ s, IsVeryAmple (f.fiberToSpecResidueField s) (L.pullback (f.fiberι s))

def IsFiberwiseAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) : Prop :=
  ∀ s, IsAmple (f.fiberToSpecResidueField s) (L.pullback (f.fiberι s))

def IsVeryAmpleAfterPositivePower {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X)
    (P : LineBundlePowers L) : Prop :=
  ∃ n, 0 < n ∧ IsVeryAmple f (P.power n)

def PowerRootSeparationFailure {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X)
    (P : LineBundlePowers L) : Prop :=
  ∃ n, 0 < n ∧ IsVeryAmple f (P.power n) ∧ ¬ IsVeryAmple f L

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
