import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Restrict

import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.Section02DescendingAffineOpens

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme

universe u v

namespace SchemeDescent

variable {S T : Scheme.{u}}

/-- The affine chart obtained by descending a datum-stable affine open. -/
structure AffineChartDescent {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p)
    (V : (descentObject D).left.Opens) (hV : IsDatumStableAffineOpen D V) where
  descended : Over S
  descendedAffine : IsAffine descended.left
  comparison : V.toScheme ≅ ((Over.pullback p).obj descended).left
  comparison_over :
    comparison.hom ≫ ((Over.pullback p).obj descended).hom =
      V.ι ≫ (descentObject D).hom

theorem affine_stable_open_descends {S T : Scheme.{u}} {p : T ⟶ S} (D : Datum p)
    {V : (descentObject D).left.Opens} (hV : IsDatumStableAffineOpen D V) :
    Nonempty (AffineChartDescent D V hV) := by
  sorry

theorem stable_affine_opens_cover_intersection {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Datum p) {V W : (descentObject D).left.Opens}
    (hV : IsDatumStableAffineOpen D V) (hW : IsDatumStableAffineOpen D W) :
    ∀ x : (descentObject D).left, x ∈ V ⊓ W →
      ∃ U : (descentObject D).left.Opens,
        x ∈ U ∧ IsDatumStableAffineOpen D U := by
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

theorem glued_overlap_is_pullback (G : SchemeGluingData) (i j : G.J) :
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

def gluedOpenCover (G : SchemeGluingData) : G.glued.OpenCover :=
  G.openCover

theorem glued_openCover_is_cover (G : SchemeGluingData) :
    ∀ x : G.glued, ∃ i y, G.gluedOpenCover.f i y = x := by
  intro x
  exact G.gluedOpenCover.exists_eq x

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
