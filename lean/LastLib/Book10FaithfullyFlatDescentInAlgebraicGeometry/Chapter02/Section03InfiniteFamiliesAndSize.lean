import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.Section01CoveringFamilies

/-!
## 2.3 Infinite families and size

The declarations here separate a valid family cover from the single coproduct morphism.  They also
make the set-sized and finite-product hypotheses visible in later APIs.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open scoped AlgebraicGeometry

universe u v

variable {S : Scheme.{u}} {I : Type v}

noncomputable def SchemeFamily.coproductMap
    (F : SchemeFamily S I) [Small.{u} I] :
    (∐ F.obj) ⟶ S :=
  Sigma.desc F.map

@[simp]
theorem SchemeFamily.ι_comp_coproductMap
    (F : SchemeFamily S I) [Small.{u} I] (i : I) :
    Sigma.ι F.obj i ≫ F.coproductMap = F.map i := by
  simp [SchemeFamily.coproductMap]

/-- An infinitely indexed family of redundant identity copies of one scheme. -/
def redundantIdentityFamily (S : Scheme.{u}) (I : Type v) : SchemeFamily S I where
  obj := fun _ ↦ S
  map := fun _ ↦ 𝟙 S

theorem redundantIdentityFamily_is_fpqc
    (S : Scheme.{u}) (I : Type v) [Nonempty I] :
    FpqcCoveringFamily (redundantIdentityFamily S I) := by
  sorry

theorem redundantIdentityFamily_is_fpqc_of_infinite
    (S : Scheme.{u}) (I : Type v) [Nonempty I] [Infinite I] :
    FpqcCoveringFamily (redundantIdentityFamily S I) := by
  exact redundantIdentityFamily_is_fpqc S I

theorem redundantIdentityFamily_coproductMap_not_quasiCompact
    (S : Scheme.{u}) (I : Type v) [Small.{u} I] [Infinite I] [Nonempty I]
    [Nonempty S] :
    ¬ QuasiCompact (redundantIdentityFamily S I).coproductMap := by
  sorry

/-- The infinite disjoint union of affine schemes used in the family-level example. -/
noncomputable def disjointAffineScheme
    (A : I → CommRingCat.{u}) [Small.{u} I] : Scheme.{u} :=
  ∐ fun i ↦ Spec (A i)

noncomputable def disjointAffineComponentFamily
    (A : I → CommRingCat.{u}) [Small.{u} I] :
    SchemeFamily (disjointAffineScheme A) I where
  obj := fun i ↦ Spec (A i)
  map := fun i ↦ Sigma.ι (fun i ↦ Spec (A i)) i

def componentSupport
    (A : I → CommRingCat.{u}) [Small.{u} I]
    (U : (disjointAffineScheme A).Opens) : Set I :=
  {i | ((U : Set (disjointAffineScheme A)) ∩
      Set.range (Sigma.ι (fun j ↦ Spec (A j)) i)).Nonempty}

theorem componentSupport_finite_of_compactOpen
    (A : I → CommRingCat.{u}) [Small.{u} I]
    (U : (disjointAffineScheme A).Opens) (hU : IsCompact (U : Set (disjointAffineScheme A))) :
    (componentSupport A U).Finite := by
  sorry

theorem disjointAffineComponentFamily_is_fpqc
    (A : I → CommRingCat.{u}) [Small.{u} I] :
    FpqcCoveringFamily (disjointAffineComponentFamily A) := by
  sorry

theorem disjointAffineComponentFamily_coproductMap_eq_id
    (A : I → CommRingCat.{u}) [Small.{u} I] :
    (disjointAffineComponentFamily A).coproductMap =
      𝟙 (disjointAffineScheme A) := by
  sorry

/-- Adding redundant identity members leaves the family-level fpqc condition unchanged. -/
def addRedundantMembers {S : Scheme.{u}} {I J : Type v}
    (F : SchemeFamily S I) : SchemeFamily S (I ⊕ J) where
  obj := fun ij ↦ match ij with
    | Sum.inl i => F.obj i
    | Sum.inr _ => S
  map := fun ij ↦ match ij with
    | Sum.inl i => F.map i
    | Sum.inr _ => 𝟙 S

theorem addRedundantMembers_is_fpqc
    {S : Scheme.{u}} {I J : Type v} {F : SchemeFamily S I}
    (hF : FpqcCoveringFamily F) :
    FpqcCoveringFamily (addRedundantMembers F J) := by
  sorry

/-- A bundled sequence of flat modules whose infinite product is not flat. -/
structure FlatModuleSequence (R : Type u) [CommRing R] where
  moduleType : ℕ → Type u
  addCommMonoid : ∀ n, AddCommMonoid (moduleType n)
  module : ∀ n, Module R (moduleType n)
  flat : ∀ n, @Module.Flat R (moduleType n) (addCommMonoid n) (module n)
  product_not_flat :
    letI : ∀ n, AddCommMonoid (moduleType n) := addCommMonoid
    letI : ∀ n, Module R (moduleType n) := module
    ¬ Module.Flat R (∀ n, moduleType n)

def InfiniteProductFlatnessFailure : Prop :=
  ∃ (R : Type u) (hR : CommRing R), Nonempty (@FlatModuleSequence R hR)

theorem exists_infinite_product_of_flat_modules_not_flat :
    InfiniteProductFlatnessFailure (u := u) := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02
