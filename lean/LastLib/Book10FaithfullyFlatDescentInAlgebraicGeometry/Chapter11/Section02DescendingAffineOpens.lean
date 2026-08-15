import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.Section01TheoremAndHypotheses

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme
open scoped BigOperators TensorProduct

universe u v

namespace SchemeDescent

noncomputable section

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
  have hspec : IsSpectralMap p := @Scheme.Hom.isSpectralMap _ _ p hp.quasiCompact
  have hcov : IsCompactOpenCovered (fun _ : Unit => p) (U : Set S) :=
    IsCompactOpenCovered.of_finite_of_isSpectralMap
      (fun _ : Unit => hspec)
      (by
        intro x hx
        obtain ⟨y, hy⟩ := hp.surjective.surj x
        exact ⟨(), ⟨y, hy⟩⟩)
      U.2 hU.isCompact
  obtain ⟨n, a, V, hV, hcover⟩ := hcov.exists_mem_of_isBasis
    (fun _ : Unit => T.isBasis_affineOpens)
    (fun _ _ h => h.isCompact)
  refine ⟨{
    base_affine := hU
    cardinal := n
    source_open := V
    source_affine := fun i => hV i
    source_over_base := ?_
    images_cover := hcover
  }⟩
  intro i x hx
  change p x ∈ (U : Set S)
  rw [← hcover]
  exact Set.mem_iUnion.mpr ⟨i, ⟨x, hx, rfl⟩⟩

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

/-- A ring presentation for the affine case. After an affine-local finite refinement, later proofs
can use the usual `Spec.map` and Amitsur equalizer APIs; existence of this record is not asserted
for an arbitrary original fpqc morphism.
-/
structure AffineFaithfullyFlatModel {S T : Scheme.{u}} (p : T ⟶ S) where
  A : CommRingCat.{u}
  B : CommRingCat.{u}
  base : S ≅ Scheme.Spec.obj (Opposite.op (A : CommRingCat.{u}))
  cover : T ≅ Scheme.Spec.obj (Opposite.op (B : CommRingCat.{u}))
  ring_map : A ⟶ B
  compatible : cover.hom ≫ Scheme.Spec.map ring_map.op =
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
  exact pullback.condition

def descentObject {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p) : Over T :=
  D.obj PUnit.unit

/-- The comparison isomorphism on the kernel pair, with the first projection as source. -/
noncomputable def kernelPairIso {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p) :
    (Over.pullback (kernelPairFst p)).obj (descentObject D) ≅
      (Over.pullback (kernelPairSnd p)).obj (descentObject D) := by
  exact D.iso (kernelPairToBase p) (kernelPairFst p) (kernelPairSnd p) (by rfl)
    (by
      change kernelPairSnd p ≫ p = kernelPairFst p ≫ p
      exact (kernelPairFst_comp p).symm)

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
  change Flat (pullback.fst (descentObject D).hom (kernelPairFst p)) ∧
    Surjective (pullback.fst (descentObject D).hom (kernelPairFst p))
  exact ⟨
    @AlgebraicGeometry.Flat.instFstScheme _ _ _ (descentObject D).hom (kernelPairFst p)
      (@AlgebraicGeometry.Flat.instFstScheme _ _ _ p p hp.1),
    @AlgebraicGeometry.Surjective.instFstScheme _ _ _ (descentObject D).hom (kernelPairFst p)
      (@AlgebraicGeometry.Surjective.instFstScheme _ _ _ p p hp.2.1)⟩

theorem relationSecond_isFaithfullyFlat {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Datum p) (hp : Scheme.IsFpqcMorphism p) :
    Scheme.IsFaithfullyFlat (relationSecond D) := by
  have hIso : IsIso (kernelPairIso D).hom.left := IsIso.mk' ⟨
    (kernelPairIso D).inv.left,
    Over.inv_left_hom_left (kernelPairIso D),
    Over.hom_left_inv_left (kernelPairIso D)⟩
  have hpull : IsPullback (kernelPairIso D).hom.left (kernelPairIso D).hom.left
      (𝟙 _) (𝟙 _) :=
    @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ hIso (by infer_instance)
      (CommSq.mk (by simp))
  have hflat : Flat (kernelPairIso D).hom.left :=
    AlgebraicGeometry.Flat.isStableUnderBaseChange.of_isPullback hpull
      (AlgebraicGeometry.Flat.instIsMultiplicativeScheme.id_mem _)
  have hsurj : Surjective (kernelPairIso D).hom.left :=
    AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme.of_isPullback hpull
      ⟨Function.surjective_id⟩
  constructor
  · change Flat ((kernelPairIso D).hom.left ≫
      pullback.fst (descentObject D).hom (kernelPairSnd p))
    exact @AlgebraicGeometry.Flat.comp _ _ _ (kernelPairIso D).hom.left
      (pullback.fst (descentObject D).hom (kernelPairSnd p))
      hflat
      (@AlgebraicGeometry.Flat.instFstScheme _ _ _ (descentObject D).hom (kernelPairSnd p)
        (@AlgebraicGeometry.Flat.instSndScheme _ _ _ p p hp.1))
  · change Surjective ((kernelPairIso D).hom.left ≫
      pullback.fst (descentObject D).hom (kernelPairSnd p))
    let hpb : Surjective (pullback.fst (descentObject D).hom (kernelPairSnd p)) :=
      @AlgebraicGeometry.Surjective.instFstScheme _ _ _ (descentObject D).hom (kernelPairSnd p)
        (@AlgebraicGeometry.Surjective.instSndScheme _ _ _ p p hp.2.1)
    exact ⟨hpb.surj.comp hsurj.surj⟩

theorem relationFirst_quasiCompact {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Datum p) (hp : Scheme.IsFpqcMorphism p) :
    QuasiCompact (relationFirst D) := by
  change QuasiCompact (pullback.fst (descentObject D).hom (kernelPairFst p))
  exact @AlgebraicGeometry.instQuasiCompactFstScheme _ _ _ (descentObject D).hom
    (kernelPairFst p) (@AlgebraicGeometry.instQuasiCompactFstScheme _ _ _ p p hp.2.2)

theorem relationSecond_quasiCompact {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Datum p) (hp : Scheme.IsFpqcMorphism p) :
    QuasiCompact (relationSecond D) := by
  have hIso : IsIso (kernelPairIso D).hom.left := IsIso.mk' ⟨
    (kernelPairIso D).inv.left,
    Over.inv_left_hom_left (kernelPairIso D),
    Over.hom_left_inv_left (kernelPairIso D)⟩
  have hpull : IsPullback (kernelPairIso D).hom.left (kernelPairIso D).hom.left
      (𝟙 _) (𝟙 _) :=
    @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ hIso (by infer_instance)
      (CommSq.mk (by simp))
  have hqc : QuasiCompact (kernelPairIso D).hom.left :=
    AlgebraicGeometry.quasiCompact_isStableUnderBaseChange.of_isPullback hpull
      (by infer_instance)
  have hpb : QuasiCompact (pullback.fst (descentObject D).hom (kernelPairSnd p)) :=
    @AlgebraicGeometry.instQuasiCompactFstScheme _ _ _ (descentObject D).hom
      (kernelPairSnd p)
      (@AlgebraicGeometry.instQuasiCompactSndScheme _ _ _ p p hp.2.2)
  change QuasiCompact ((kernelPairIso D).hom.left ≫
    pullback.fst (descentObject D).hom (kernelPairSnd p))
  exact AlgebraicGeometry.quasiCompact_isStableUnderComposition.comp_mem _ _ hqc hpb

theorem relationFirst_isAffineHom_of_affine {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Datum p) [IsAffine S] [IsAffine T] :
    IsAffineHom (relationFirst D) := by
  have hKernelPairFst : IsAffineHom (kernelPairFst p) :=
    AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback p p).flip (inferInstance : IsAffineHom p)
  have hRelationFirst : IsAffineHom
      (pullback.fst (descentObject D).hom (kernelPairFst p)) :=
    AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback _ _).flip hKernelPairFst
  change IsAffineHom (pullback.fst (descentObject D).hom (kernelPairFst p))
  exact hRelationFirst

theorem relationSecond_isAffineHom_of_affine {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Datum p) [IsAffine S] [IsAffine T] :
    IsAffineHom (relationSecond D) := by
  have hKernelPairSnd : IsAffineHom (kernelPairSnd p) :=
    AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback p p) (inferInstance : IsAffineHom p)
  have hRelationSecondBase : IsAffineHom
      (pullback.fst (descentObject D).hom (kernelPairSnd p)) :=
    AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback _ _).flip hKernelPairSnd
  have hIso : IsIso (kernelPairIso D).hom.left := IsIso.mk' ⟨
    (kernelPairIso D).inv.left,
    Over.inv_left_hom_left (kernelPairIso D),
    Over.hom_left_inv_left (kernelPairIso D)⟩
  have hAffineIso : IsAffineHom (kernelPairIso D).hom.left :=
    ⟨fun U hU ↦ @IsAffineOpen.preimage_of_isIso _ _ _ hU (kernelPairIso D).hom.left hIso⟩
  change IsAffineHom ((kernelPairIso D).hom.left ≫
    pullback.fst (descentObject D).hom (kernelPairSnd p))
  exact {
    isAffine_preimage := fun U hU ↦ by
      rw [Scheme.Hom.comp_base, TopologicalSpace.Opens.map_comp_obj]
      exact hAffineIso.isAffine_preimage _
        (hRelationSecondBase.isAffine_preimage _ hU) }

def orbit {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p)
    (x : (descentObject D).left) : Set (descentObject D).left :=
  { y | ∃ z : relationScheme D, relationFirst D z = x ∧ relationSecond D z = y }

/-- A finite affine cover of the target orbit of a point under the descent relation. -/
structure FiniteAffineOrbitCover {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p)
    (x : (descentObject D).left) where
  cardinal : ℕ
  openSet : Fin cardinal → (descentObject D).left.Opens
  affine : ∀ i, IsAffineOpen (openSet i)
  covers : orbit D x ⊆ ⋃ i, (openSet i : Set (descentObject D).left)

theorem exists_finite_affine_orbit_cover {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Datum p) (hp : Scheme.IsFpqcMorphism p) (x : (descentObject D).left) :
    Nonempty (FiniteAffineOrbitCover D x) := by
  classical
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : (descentObject D).left.Opens)) (by simp)
  have hq : QuasiCompact (relationFirst D) := relationFirst_quasiCompact D hp
  let W : (relationScheme D).Opens := relationFirst D ⁻¹ᵁ U
  have hW : IsCompact (W : Set (relationScheme D)) := by
    dsimp [W]
    exact hq.isCompact_preimage (U : Set (descentObject D).left) U.2 hU.isCompact
  let K : Set (descentObject D).left := relationSecond D '' (W : Set (relationScheme D))
  have hK : IsCompact K := by
    dsimp [K]
    exact hW.image (relationSecond D).continuous
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun V : (descentObject D).left.affineOpens => (V : Set (descentObject D).left))
    (fun V => V.1.2)
    (by
      intro y hy
      exact Set.mem_iUnion.mpr
        ((descentObject D).left.isBasis_affineOpens.isOpenCover.exists_mem y))
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  refine ⟨{
    cardinal := Fintype.card s
    openSet := fun i => ((e.symm i).1 : (descentObject D).left.Opens)
    affine := fun i => (e.symm i).1.2
    covers := ?_
  }⟩
  intro y hy
  rcases hy with ⟨z, hzx, hzy⟩
  have hzW : z ∈ (W : Set (relationScheme D)) := by
    change relationFirst D z ∈ (U : Set (descentObject D).left)
    rw [hzx]
    exact hxU
  have hyK : y ∈ K := by
    exact ⟨z, hzW, hzy⟩
  obtain ⟨V, hVs, hyV⟩ := Set.mem_iUnion₂.mp (hs hyK)
  obtain ⟨i, hi⟩ := e.symm.surjective ⟨V, hVs⟩
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  simpa [hi] using hyV

theorem exists_stable_affine_open_mem {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Datum p) (hp : Scheme.IsFpqcMorphism p) (x : (descentObject D).left) :
    ∃ V : (descentObject D).left.Opens,
      x ∈ V ∧ IsDatumStableAffineOpen D V := by
  sorry

/-- A cover by affine opens that are stable under the descent datum. -/
structure StableAffineOpenCover {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p) where
  index : Type (max u v)
  openSet : index → (descentObject D).left.Opens
  affine : ∀ i, IsAffineOpen (openSet i)
  stable : ∀ i, IsDatumStableAffineOpen D (openSet i)
  covers : ∀ x : (descentObject D).left, ∃ i, x ∈ openSet i

theorem stableAffineOpenCover {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p)
    (hp : Scheme.IsFpqcMorphism p) :
    Nonempty (StableAffineOpenCover D) := by
  classical
  let V : ∀ x : (descentObject D).left, (descentObject D).left.Opens := fun x ↦
    (Classical.choose (exists_stable_affine_open_mem D hp x))
  have hV : ∀ x : (descentObject D).left,
      x ∈ V x ∧ IsDatumStableAffineOpen D (V x) := by
    intro x
    exact Classical.choose_spec (exists_stable_affine_open_mem D hp x)
  refine ⟨{
    index := ULift ((descentObject D).left : Type u)
    openSet := fun x => V x.down
    affine := fun x => (hV x.down).2.1
    stable := fun x => (hV x.down).2
    covers := fun x => ⟨ULift.up x, (hV x).1⟩
  }⟩

def StableAffineOpenCover.openCover {S T : Scheme.{u}} {p : T ⟶ S} {D : Datum p}
    (𝒱 : StableAffineOpenCover D) :
    (descentObject D).left.OpenCover :=
  Scheme.Cover.mkOfCovers 𝒱.index (fun i => (𝒱.openSet i).toScheme)
    (fun i => (𝒱.openSet i).ι) (by
      intro x
      obtain ⟨i, hi⟩ := 𝒱.covers x
      exact ⟨i, ⟨⟨x, hi⟩, rfl⟩⟩)

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

theorem amitsur_unit_injective (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B] :
    Function.Injective (Algebra.linearMap A B) := by
  exact FaithfulSMul.algebraMap_injective A B

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
      PrimeSpectrum.basicOpen (s.prod id) := by
  classical
  rw [← Finset.inf_eq_iInf]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ih, PrimeSpectrum.basicOpen_mul, ha]

end

end SchemeDescent

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11
