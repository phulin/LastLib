import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Restrict

import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.Section02DescendingAffineOpens

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme

universe u v

namespace SchemeDescent

variable {S T : Scheme.{u}}

/-! ### Compatibility of affine chart comparisons -/

/-- The canonical singleton descent datum carried by the pullback of an object over `S`. -/
noncomputable def canonicalPullbackDatum {S T : Scheme.{u}} (p : T ⟶ S) (descended : Over S) :
    Datum.{u, 0} p :=
  (overPseudofunctor.toDescentData (fun _ : PUnit => p)).obj descended

/-- A comparison of a stable affine open with the pullback of a candidate affine chart must
intertwine the overlap datum.  The first equation says that the overlap is over the pair
overlap, the second identifies it with the restriction of `D`'s kernel-pair isomorphism, and
the third identifies it with the canonical overlap of the pullback of the candidate downstairs
scheme.  Keeping these equations in the interface prevents an arbitrary isomorphism over `T`
from being used as descent data. -/
def AffineChartComparisonCompatible {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p)
    (V : (descentObject D).left.Opens) {descended : Over S}
    (comparison : V.toScheme ≅ ((Over.pullback p).obj descended).left)
    (comparison_over :
      comparison.hom ≫ ((Over.pullback p).obj descended).hom =
        V.ι ≫ (descentObject D).hom) : Prop :=
  let vMap : V.toScheme ⟶ T := V.ι ≫ (descentObject D).hom
  ∃ overlap :
      pullback vMap (kernelPairFst p) ≅ pullback vMap (kernelPairSnd p),
    overlap.hom ≫ pullback.snd vMap (kernelPairSnd p) =
        pullback.snd vMap (kernelPairFst p) ∧
      pullback.map vMap (kernelPairFst p) (descentObject D).hom (kernelPairFst p)
          V.ι (𝟙 _) (𝟙 _) (by simp [vMap]) (by simp) ≫
          ((Over.forget (kernelPair p)).mapIso (kernelPairIso D)).hom =
        overlap.hom ≫
          pullback.map vMap (kernelPairSnd p) (descentObject D).hom (kernelPairSnd p)
            V.ι (𝟙 _) (𝟙 _) (by simp [vMap]) (by simp) ∧
      pullback.map vMap (kernelPairFst p)
          ((Over.pullback p).obj descended).hom (kernelPairFst p)
          comparison.hom (𝟙 _) (𝟙 _) (by simpa [vMap] using comparison_over.symm) (by simp) ≫
          ((Over.forget (kernelPair p)).mapIso
            ((canonicalPullbackDatum p descended).iso
              (i₁ := (PUnit.unit : PUnit.{1})) (i₂ := (PUnit.unit : PUnit.{1}))
              (kernelPairToBase p) (kernelPairFst p) (kernelPairSnd p)
              (by rfl)
              (by
                change kernelPairSnd p ≫ p = kernelPairFst p ≫ p
                exact (kernelPairFst_comp p).symm))).hom =
        overlap.hom ≫
          pullback.map vMap (kernelPairSnd p)
            ((Over.pullback p).obj descended).hom (kernelPairSnd p)
            comparison.hom (𝟙 _) (𝟙 _) (by simpa [vMap] using comparison_over.symm) (by simp)

/-- The affine chart obtained in the central affine faithfully flat reduction from a
datum-stable affine open. -/
structure AffineChartDescent {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p)
    (V : (descentObject D).left.Opens) (hV : IsDatumStableAffineOpen D V) where
  descended : Over S
  descendedAffine : IsAffine descended.left
  comparison : V.toScheme ≅ ((Over.pullback p).obj descended).left
  comparison_over :
    comparison.hom ≫ ((Over.pullback p).obj descended).hom =
      V.ι ≫ (descentObject D).hom
  comparison_compatible :
    AffineChartComparisonCompatible D V comparison comparison_over

theorem affine_stable_open_descends {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p)
    (hS : IsAffine S) (hT : IsAffine T) (hp : Scheme.IsFpqcMorphism p)
    {V : (descentObject D).left.Opens} (hV : IsDatumStableAffineOpen D V) :
    Nonempty (AffineChartDescent D V hV) := by
  sorry

theorem stable_affine_opens_cover_intersection {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Datum p) (hp : Scheme.IsFpqcMorphism p)
    {V W : (descentObject D).left.Opens}
    (hV : IsDatumStableAffineOpen D V) (hW : IsDatumStableAffineOpen D W) :
    ∀ x : (descentObject D).left, x ∈ V ⊓ W →
      ∃ U : (descentObject D).left.Opens,
        x ∈ U ∧ U ≤ V ⊓ W ∧ IsDatumStableAffineOpen D U := by
  sorry

/-- The compatibility data used to glue the descended affine charts.

`Scheme.GlueData` already contains the overlap open immersions, the transition isomorphisms,
their identities, and the triple-overlap cocycle. -/
abbrev SchemeGluingData := Scheme.GlueData

noncomputable def gluedScheme (G : SchemeGluingData) : Scheme :=
  G.glued

theorem glued_chart_is_open (G : SchemeGluingData) (i : G.J) :
    IsOpenImmersion (G.ι i) := by
  exact G.ι_isOpenImmersion i

theorem glued_charts_jointly_surjective (G : SchemeGluingData) :
    ∀ x : G.glued, ∃ i y, G.ι i y = x := by
  intro x
  exact G.ι_jointly_surjective x

noncomputable def glued_overlap_is_pullback (G : SchemeGluingData) (i j : G.J) :
    IsLimit (G.vPullbackCone i j) := by
  exact G.vPullbackConeIsLimit i j

theorem glued_transition_condition (G : SchemeGluingData) (i j : G.J) :
    G.t i j ≫ G.f j i ≫ G.ι j = G.f i j ≫ G.ι i := by
  exact G.glue_condition i j

theorem glued_overlap_is_open (G : SchemeGluingData) (i j : G.J) :
    IsOpenImmersion (G.f i j) := by
  exact G.f_open i j

theorem glued_triple_cocycle (G : SchemeGluingData) (i j k : G.J) :
    G.t' i j k ≫ G.t' j k i ≫ G.t' k i j = 𝟙 _ := by
  exact G.cocycle i j k

theorem glued_open_iff (G : SchemeGluingData) (U : Set G.glued.carrier) :
    IsOpen U ↔ ∀ i, IsOpen (G.ι i ⁻¹' U) := by
  exact G.isOpen_iff U

noncomputable def gluedOpenCover (G : SchemeGluingData) : G.glued.OpenCover :=
  G.openCover

theorem glued_openCover_is_cover (G : SchemeGluingData) :
    ∀ x : G.glued, ∃ i y, (gluedOpenCover G).f i y = x := by
  intro x
  exact (gluedOpenCover G).exists_eq x

theorem glue_stable_affine_charts {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p)
    (hp : Scheme.IsFpqcMorphism p) :
    Nonempty (Effective (fun _ : PUnit => p) D) := by
  sorry

theorem open_cover_gluing_is_canonical {X : Scheme.{u}} (𝒰 : X.OpenCover) :
    IsIso 𝒰.fromGlued := by
  infer_instance

theorem open_cover_gluing_hom_ext {X : Scheme.{u}} (𝒰 : X.OpenCover)
    {Y : Scheme.{u}} (f g : X ⟶ Y)
    (h : ∀ i, 𝒰.f i ≫ f = 𝒰.f i ≫ g) : f = g := by
  exact 𝒰.hom_ext f g h

end SchemeDescent

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11
