import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.Section01TheoremAndHypotheses

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme
open scoped BigOperators TensorProduct

universe u v

namespace SchemeDescent

variable {S T : Scheme.{u}}

/-! ### Affine-local reduction -/

/-- A finite affine refinement of an affine open in the target of a quasi-compact cover. -/
structure FiniteAffineRefinement (p : T ⟶ S) (U : S.Opens) where
  base_affine : IsAffineOpen U
  cardinal : ℕ
  source_open : Fin cardinal → T.Opens
  source_affine : ∀ i, IsAffineOpen (source_open i)
  source_over_base : ∀ i, source_open i ≤ p ⁻¹ᵁ U
  images_cover : ⋃ i, p '' (source_open i) = (U : Set S)

theorem exists_finite_affine_refinement {p : T ⟶ S}
    (hp : Scheme.IsFpqcMorphism p) {U : S.Opens} (hU : IsAffineOpen U) :
    Nonempty (FiniteAffineRefinement p U) := by
  sorry

def refinementSourceScheme {p : T ⟶ S} {U : S.Opens}
    (r : FiniteAffineRefinement p U) (i : Fin r.cardinal) : Scheme :=
  (r.source_open i).toScheme

def refinementSourceMap {p : T ⟶ S} {U : S.Opens}
    (r : FiniteAffineRefinement p U) (i : Fin r.cardinal) :
    refinementSourceScheme r i ⟶ S :=
  (r.source_open i).ι ≫ p

/-- Pairwise fiber products of the finite affine refinement. -/
def refinementPairwiseFiberProduct {p : T ⟶ S} {U : S.Opens}
    (r : FiniteAffineRefinement p U) (i j : Fin r.cardinal) : Scheme :=
  pullback (refinementSourceMap r i) (refinementSourceMap r j)

def refinementPairwiseFst {p : T ⟶ S} {U : S.Opens}
    (r : FiniteAffineRefinement p U) (i j : Fin r.cardinal) :
    refinementPairwiseFiberProduct r i j ⟶ refinementSourceScheme r i :=
  pullback.fst (refinementSourceMap r i) (refinementSourceMap r j)

def refinementPairwiseSnd {p : T ⟶ S} {U : S.Opens}
    (r : FiniteAffineRefinement p U) (i j : Fin r.cardinal) :
    refinementPairwiseFiberProduct r i j ⟶ refinementSourceScheme r j :=
  pullback.snd (refinementSourceMap r i) (refinementSourceMap r j)

/-- The affine faithfully flat model obtained after choosing the finite affine refinement.

The ring presentation is kept as an explicit interface so later proofs can use the usual
`Spec.map` and Amitsur equalizer APIs without assuming that the original fpqc morphism was affine.
-/
structure AffineFaithfullyFlatModel {S T : Scheme.{u}} (p : T ⟶ S) where
  A B : CommRingCat.{u}
  base : Scheme.{u} ≅ Scheme.Spec A
  cover : Scheme.{u} ≅ Scheme.Spec B
  ring_map : A ⟶ B
  compatible : cover.hom ≫ Scheme.Spec.map ring_map.hom =
    p ≫ base.hom
  faithfully_flat : RingHom.FaithfullyFlat ring_map.hom

/-- The kernel pair of a morphism of schemes. -/
def kernelPair (p : T ⟶ S) : Scheme :=
  pullback p p

def kernelPairFst (p : T ⟶ S) : kernelPair p ⟶ T :=
  pullback.fst p p

def kernelPairSnd (p : T ⟶ S) : kernelPair p ⟶ T :=
  pullback.snd p p

def kernelPairToBase (p : T ⟶ S) : kernelPair p ⟶ S :=
  kernelPairFst p ≫ p

@[simp]
theorem kernelPairFst_comp (p : T ⟶ S) :
    kernelPairFst p ≫ p = kernelPairSnd p ≫ p := by
  simp [kernelPairFst, kernelPairSnd]

def descentObject {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p) : Over T :=
  D.obj PUnit

/-- The comparison isomorphism on the kernel pair, with the first projection as source. -/
noncomputable def kernelPairIso {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p) :
    (Over.pullback (kernelPairFst p)).obj (descentObject D) ≅
      (Over.pullback (kernelPairSnd p)).obj (descentObject D) := by
  exact D.iso (kernelPairToBase p) (kernelPairFst p) (kernelPairSnd p)

def relationScheme {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p) : Scheme :=
  ((Over.pullback (kernelPairFst p)).obj (descentObject D)).left

def relationFirst {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p) :
    relationScheme D ⟶ (descentObject D).left :=
  pullback.fst (descentObject D).hom (kernelPairFst p)

def relationSecond {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p) :
    relationScheme D ⟶ (descentObject D).left :=
  (kernelPairIso D).hom.left ≫
    pullback.fst (descentObject D).hom (kernelPairSnd p)

/-- The stable-open condition on an affine open of the object upstairs. -/
def IsDatumStableAffineOpen {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p)
    (V : (descentObject D).left.Opens) : Prop :=
  IsAffineOpen V ∧
    (pullback.fst (descentObject D).hom (kernelPairFst p) ⁻¹ᵁ V) =
      (kernelPairIso D).hom.left ⁻¹ᵁ
        (pullback.fst (descentObject D).hom (kernelPairSnd p) ⁻¹ᵁ V)

@[simp]
theorem isDatumStableAffineOpen_iff {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p)
    (V : (descentObject D).left.Opens) :
    IsDatumStableAffineOpen D V ↔
      IsAffineOpen V ∧
        (pullback.fst (descentObject D).hom (kernelPairFst p) ⁻¹ᵁ V) =
          (kernelPairIso D).hom.left ⁻¹ᵁ
            (pullback.fst (descentObject D).hom (kernelPairSnd p) ⁻¹ᵁ V) :=
  Iff.rfl

theorem relationFirst_isFaithfullyFlat {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Datum p) (hp : Scheme.IsFpqcMorphism p) :
    Scheme.IsFaithfullyFlat (relationFirst D) := by
  sorry

theorem relationSecond_isFaithfullyFlat {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Datum p) (hp : Scheme.IsFpqcMorphism p) :
    Scheme.IsFaithfullyFlat (relationSecond D) := by
  sorry

theorem relationFirst_quasiCompact {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Datum p) (hp : Scheme.IsFpqcMorphism p) :
    QuasiCompact (relationFirst D) := by
  sorry

theorem relationSecond_quasiCompact {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Datum p) (hp : Scheme.IsFpqcMorphism p) :
    QuasiCompact (relationSecond D) := by
  sorry

def orbit {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p)
    (x : (descentObject D).left) : Set (descentObject D).left :=
  { y | ∃ z : relationScheme D, relationFirst D z = x ∧ relationSecond D z = y }

/-- A finite affine cover of the target orbit of a point under the descent relation. -/
structure FiniteAffineOrbitCover {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p)
    (x : (descentObject D).left) where
  cardinal : ℕ
  open : Fin cardinal → (descentObject D).left.Opens
  affine : ∀ i, IsAffineOpen (open i)
  covers : orbit D x ⊆ ⋃ i, (open i : Set (descentObject D).left)

theorem exists_finite_affine_orbit_cover {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Datum p) (hp : Scheme.IsFpqcMorphism p) (x : (descentObject D).left) :
    Nonempty (FiniteAffineOrbitCover D x) := by
  sorry

theorem exists_stable_affine_open_mem {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Datum p) (hp : Scheme.IsFpqcMorphism p) (x : (descentObject D).left) :
    ∃ V : (descentObject D).left.Opens,
      x ∈ V ∧ IsDatumStableAffineOpen D V := by
  sorry

/-- A cover by affine opens that are stable under the descent datum. -/
structure StableAffineOpenCover {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p) where
  index : Type v
  open : index → (descentObject D).left.Opens
  affine : ∀ i, IsAffineOpen (open i)
  stable : ∀ i, IsDatumStableAffineOpen D (open i)
  covers : ∀ x : (descentObject D).left, ∃ i, x ∈ open i

theorem stableAffineOpenCover {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p)
    (hp : Scheme.IsFpqcMorphism p) :
    Nonempty (StableAffineOpenCover D) := by
  sorry

def StableAffineOpenCover.openCover {S T : Scheme.{u}} {p : T ⟶ S} {D : Datum p}
    (𝒱 : StableAffineOpenCover D) :
    (descentObject D).left.OpenCover :=
  Scheme.Cover.mkOfCovers 𝒱.index (fun i => (𝒱.open i).toScheme)
    (fun i => (𝒱.open i).ι) (by
      intro x
      obtain ⟨i, hi⟩ := 𝒱.covers x
      exact ⟨i, ⟨x, hi, rfl⟩⟩)

theorem StableAffineOpenCover.openCover_exists_eq {S T : Scheme.{u}} {p : T ⟶ S}
    {D : Datum p} (𝒱 : StableAffineOpenCover D) :
    ∀ x : (descentObject D).left, ∃ i y, 𝒱.openCover.f i y = x := by
  intro x
  exact 𝒱.openCover.exists_eq x

/-- Normalization of a descent datum on a diagonal pullback. -/
theorem datum_identity {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (D : Data f) {Y : Scheme} (q : Y ⟶ S)
    {i : ι} (g : Y ⟶ X i) (hg : g ≫ f i = q) :
    D.hom q g g hg hg = 𝟙 _ := by
  exact D.hom_self q g hg

/-- The cocycle identity on the triple overlap. -/
theorem datum_cocycle {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (D : Data f) {Y : Scheme} (q : Y ⟶ S)
    {i₁ i₂ i₃ : ι} (g₁ : Y ⟶ X i₁) (g₂ : Y ⟶ X i₂) (g₃ : Y ⟶ X i₃)
    (hg₁ : g₁ ≫ f i₁ = q) (hg₂ : g₂ ≫ f i₂ = q) (hg₃ : g₃ ≫ f i₃ = q) :
    D.hom q g₁ g₂ hg₁ hg₂ ≫ D.hom q g₂ g₃ hg₂ hg₃ =
      D.hom q g₁ g₃ hg₁ hg₃ := by
  exact D.hom_comp q g₁ g₂ g₃ hg₁ hg₂ hg₃

/-- The Amitsur equalizer condition for an algebra. -/
def AmitsurEqualizerCondition (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] : Prop :=
  Algebra.IsEffective A B

theorem AmitsurEqualizerCondition.of_faithfullyFlat (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B] :
    AmitsurEqualizerCondition A B := by
  exact Algebra.IsEffective.of_faithfullyFlat A B

theorem amitsur_exact (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : AmitsurEqualizerCondition A B) :
    Function.Exact (Algebra.linearMap A B)
      (Algebra.TensorProduct.includeLeftSubRight A B) := by
  exact h

theorem amitsur_equalizer_eq_range (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (h : AmitsurEqualizerCondition A B) :
    Algebra.TensorProduct.includeLeftRingHom.eqLocus
        Algebra.TensorProduct.includeRight.toRingHom (S := B ⊗[A] B) =
      Set.range (algebraMap A B) := by
  exact Algebra.IsEffective.eqLocus_includeLeft_includeRight h

/-- The basic-open normalization used in the simultaneous shrinking argument. -/
theorem basicOpen_finset_iInf_eq_prod (R : Type u) [CommRing R] (s : Finset R) :
    (⨅ f ∈ s, PrimeSpectrum.basicOpen f) =
      PrimeSpectrum.basicOpen (∏ f in s, f) := by
  sorry

end SchemeDescent

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11
