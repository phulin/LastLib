import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.Dependencies

/-!
## 2.1 Covering families

This file records the family-level fpqc and fppf interfaces.  The finite reduction is indexed by a
natural number rather than a finite set of family members, because the source allows several
quasi-compact opens in the same member of a family.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open scoped AlgebraicGeometry

universe u v

/-- A set-indexed family of morphisms into a fixed scheme. -/
structure SchemeFamily (S : Scheme.{u}) (I : Type v) where
  obj : I → Scheme.{u}
  map : ∀ i, obj i ⟶ S

def SchemeFamily.presieve {S : Scheme.{u}} {I : Type v}
    (F : SchemeFamily S I) : Presieve S :=
  Presieve.ofArrows F.obj F.map

/-- A finite amount of a family lying over a quasi-compact open of the base. -/
structure FiniteFamilyReduction {S : Scheme.{u}} {I : Type v}
    (F : SchemeFamily S I) (U : S.Opens) where
  cardinality : ℕ
  member : Fin cardinality → I
  sourceOpen : ∀ j, (F.obj (member j)).Opens
  quasiCompact : ∀ j, IsCompact (sourceOpen j : Set (F.obj (member j)))
  covers : (U : Set S) =
    ⋃ j : Fin cardinality,
      F.map (member j) '' (sourceOpen j : Set (F.obj (member j)))

/-- The book's family-level definition of an fpqc cover. -/
structure FpqcCoveringFamily {S : Scheme.{u}} {I : Type v}
    (F : SchemeFamily S I) : Prop where
  flat : ∀ i, Flat (F.map i)
  finite_reduction : ∀ (U : S.Opens), IsCompact (U : Set S) →
    Nonempty (FiniteFamilyReduction F U)

/-- The image condition used for family-level joint surjectivity. -/
def JointlySurjective {S : Scheme.{u}} {I : Type v} (F : SchemeFamily S I) : Prop :=
  ∀ s : S, ∃ i, ∃ x : F.obj i, F.map i x = s

theorem jointlySurjective_iff_iUnion_range_eq_univ
    {S : Scheme.{u}} {I : Type v} (F : SchemeFamily S I) :
    JointlySurjective F ↔
      (⋃ i, Set.range (F.map i)) = (Set.univ : Set S) := by
  sorry

/-- A family of flat morphisms locally of finite presentation which is jointly surjective. -/
structure FppfCoveringFamily {S : Scheme.{u}} {I : Type v}
    (F : SchemeFamily S I) : Prop where
  jointly_surjective : JointlySurjective F
  flat : ∀ i, Flat (F.map i)
  locally_of_finite_presentation : ∀ i, LocallyOfFinitePresentation (F.map i)

/-- A family of open immersions covering its target. -/
def IsZariskiCoveringFamily {S : Scheme.{u}} {I : Type v}
    (F : SchemeFamily S I) : Prop :=
  (∀ i, IsOpenImmersion (F.map i)) ∧ JointlySurjective F

/-- A jointly surjective family of étale morphisms. -/
def IsEtaleCoveringFamily {S : Scheme.{u}} {I : Type v}
    (F : SchemeFamily S I) : Prop :=
  JointlySurjective F ∧ ∀ i, Etale (F.map i)

theorem fppf_member_image_isOpen
    {S T : Scheme.{u}} {p : T ⟶ S} (hflat : Flat p)
    (hfp : LocallyOfFinitePresentation p) (V : T.Opens) :
    IsOpen (p '' (V : Set T)) := by
  sorry

theorem fpqcCoveringFamily_iff_affine_reductions
    {S : Scheme.{u}} {I : Type v} (F : SchemeFamily S I) :
    FpqcCoveringFamily F ↔
      (∀ i, Flat (F.map i)) ∧
        (∀ (U : S.Opens), IsAffineOpen U →
          Nonempty (FiniteFamilyReduction F U)) := by
  sorry

theorem fppfCoveringFamily_is_fpqc
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hF : FppfCoveringFamily F) : FpqcCoveringFamily F := by
  sorry

theorem zariskiCoveringFamily_is_fpqc
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hF : IsZariskiCoveringFamily F) : FpqcCoveringFamily F := by
  sorry

theorem zariskiCoveringFamily_is_etale
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hF : IsZariskiCoveringFamily F) :
    IsEtaleCoveringFamily F := by
  sorry

theorem zariskiCoveringFamily_is_fppf
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hF : IsZariskiCoveringFamily F) : FppfCoveringFamily F := by
  sorry

theorem etaleCoveringFamily_is_fppf
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hF : IsEtaleCoveringFamily F) : FppfCoveringFamily F := by
  sorry

theorem etaleCoveringFamily_is_fpqc
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hF : IsEtaleCoveringFamily F) : FpqcCoveringFamily F := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02
