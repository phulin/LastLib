import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Separation.Profinite

namespace LastLib.Book06GlobalClassFieldTheory.Chapter10

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u v w

/-!
## Shared interfaces for Chapter 10

The preceding chapters of the global class-field-theory book are not present in
this checkout. The records below are deliberately small book-facing interfaces
for the idele class group, the finite Artin system, local reciprocity, and ray
class fields. They expose canonical Mathlib groups and inverse limits without
assuming any of the infinite reciprocity theorem that this chapter is meant to
state.
-/

/- LOCAL_DEPENDENCY_GUESS: replace this open finite-index subgroup wrapper by
the canonical idele-class topology from the preceding global class-field
chapters when those declarations are merged. -/
structure Chapter10OpenFiniteIndexNormalSubgroup
    (C : Type u) [Group C] [TopologicalSpace C]
    extends FiniteIndexNormalSubgroup C where
  /-- The finite-index subgroup is open in the idele-class topology. -/
  isOpen : IsOpen (toSubgroup : Set C)

namespace Chapter10OpenFiniteIndexNormalSubgroup

variable {C : Type u} [Group C] [TopologicalSpace C]

instance (H : Chapter10OpenFiniteIndexNormalSubgroup C) :
    H.toSubgroup.Normal := H.isNormal'

instance (H : Chapter10OpenFiniteIndexNormalSubgroup C) :
    H.toSubgroup.FiniteIndex := H.isFiniteIndex'

instance : SetLike (Chapter10OpenFiniteIndexNormalSubgroup C) C where
  coe H := H.toSubgroup
  coe_injective A B h := by
    cases A with
    | mk A hA =>
      cases B with
      | mk B hB =>
        have hAB : A.toSubgroup = B.toSubgroup := by
          ext c
          exact Set.ext_iff.mp h c
        cases FiniteIndexNormalSubgroup.toSubgroup_injective hAB
        rfl

instance : PartialOrder (Chapter10OpenFiniteIndexNormalSubgroup C) :=
  .ofSetLike (Chapter10OpenFiniteIndexNormalSubgroup C) C

@[simp]
theorem mem_toSubgroup_iff {H : Chapter10OpenFiniteIndexNormalSubgroup C}
    {c : C} : c ∈ H.toSubgroup ↔ c ∈ H :=
  Iff.rfl

end Chapter10OpenFiniteIndexNormalSubgroup

/- The quotient system indexed by the open finite-index subgroups is the
topology-sensitive completion used by the chapter. -/
noncomputable def chapter10OpenFiniteIndexDiagram
    (C : Type u) [CommGroup C] [TopologicalSpace C] :
    Chapter10OpenFiniteIndexNormalSubgroup C ⥤ FiniteGrp where
  obj H := FiniteGrp.of (C ⧸ H.toSubgroup)
  map f := FiniteGrp.ofHom <|
    QuotientGroup.map _ _ (MonoidHom.id C) (by
      intro c hc
      exact f.le hc)
  map_id H := by
    ext ⟨c⟩
    rfl
  map_comp f g := by
    ext ⟨c⟩
    rfl

noncomputable def chapter10OpenFiniteIndexProfiniteDiagram
    (C : Type u) [CommGroup C] [TopologicalSpace C] :
    Chapter10OpenFiniteIndexNormalSubgroup C ⥤ ProfiniteGrp :=
  chapter10OpenFiniteIndexDiagram C ⋙ forget₂ FiniteGrp ProfiniteGrp

/-- The inverse limit over open finite-index quotients of an abelian group. -/
noncomputable def chapter10ProfiniteCompletion
    (C : Type u) [CommGroup C] [TopologicalSpace C] : ProfiniteGrp :=
  ProfiniteGrp.limit (chapter10OpenFiniteIndexProfiniteDiagram C)

/-- The component of the completion map at a group element. -/
noncomputable def chapter10ProfiniteCompletionEtaFn
    (C : Type u) [CommGroup C] [TopologicalSpace C] (c : C) :
    chapter10ProfiniteCompletion C :=
  ⟨fun H => QuotientGroup.mk c, by
    intro H K f
    rfl⟩

/-- The canonical homomorphism from the idele class group to its profinite
completion. -/
noncomputable def chapter10ProfiniteCompletionEta
    (C : Type u) [CommGroup C] [TopologicalSpace C] :
    C →* chapter10ProfiniteCompletion C where
  toFun := chapter10ProfiniteCompletionEtaFn C
  map_one' := by
    apply ProfiniteGrp.limit_ext
    intro H
    rfl
  map_mul' c d := by
    apply ProfiniteGrp.limit_ext
    intro H
    rfl

@[simp]
theorem chapter10ProfiniteCompletionEta_apply
    (C : Type u) [CommGroup C] [TopologicalSpace C] (c : C) :
    chapter10ProfiniteCompletionEta C c =
      chapter10ProfiniteCompletionEtaFn C c :=
  rfl

/- LOCAL_DEPENDENCY_GUESS: the usual universal property of this open-quotient
inverse limit, including density of the canonical map, will be identified with
the canonical completion API once the preceding global topology is merged. -/
theorem chapter10ProfiniteCompletionEta_denseRange
    (C : Type u) [CommGroup C] [TopologicalSpace C] :
    DenseRange (chapter10ProfiniteCompletionEta C) := by
  sorry

/- The projections are exposed as maps so later compatibility statements can
refer to the finite quotients without unpacking the categorical limit. -/
noncomputable def chapter10ProfiniteCompletionProjection
    (C : Type u) [CommGroup C] [TopologicalSpace C]
    (H : Chapter10OpenFiniteIndexNormalSubgroup C) :
    chapter10ProfiniteCompletion C →* (C ⧸ H.toSubgroup) :=
  (((ProfiniteGrp.limitCone
      (chapter10OpenFiniteIndexProfiniteDiagram C)).π.app H).hom).toMonoidHom

theorem chapter10ProfiniteCompletionProjection_eta
    (C : Type u) [CommGroup C] [TopologicalSpace C]
    (H : Chapter10OpenFiniteIndexNormalSubgroup C) (c : C) :
    chapter10ProfiniteCompletionProjection C H
        (chapter10ProfiniteCompletionEta C c) = QuotientGroup.mk c := by
  rfl

/- LOCAL_DEPENDENCY_GUESS: this is the finite-dimensional/Galois realization
of the compositum `K^ab`. The ambient extension is Galois and abelian, and
every element lies in a finite abelian Galois intermediate field. -/
def chapter10IsAbelianFiniteGaloisExtension
    {K : Type u} {Kab : Type v} [Field K] [Field Kab] [Algebra K Kab]
    (L : FiniteGaloisIntermediateField K Kab) : Prop :=
  ∀ σ τ : Gal(L / K), σ * τ = τ * σ

structure Chapter10AbelianClosureData
    (K : Type u) (Kab : Type v) [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] where
  /-- The Galois group of `K^ab/K` is abelian. -/
  ambient_commutative : ∀ σ τ : Gal(Kab / K), σ * τ = τ * σ
  /-- The compositum is locally finite: every element belongs to a finite
  abelian Galois subextension. -/
  finite_abelian_subextension :
    ∀ x : Kab, ∃ L : FiniteGaloisIntermediateField K Kab,
      chapter10IsAbelianFiniteGaloisExtension L ∧
        x ∈ L.toIntermediateField

def chapter10AbelianClosureUnion
    {K : Type u} {Kab : Type v} [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] : Set Kab :=
  {x | ∃ L : FiniteGaloisIntermediateField K Kab,
    chapter10IsAbelianFiniteGaloisExtension L ∧ x ∈ L.toIntermediateField}

theorem chapter10AbelianClosureUnion_eq_univ
    {K : Type u} {Kab : Type v} [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] (A : Chapter10AbelianClosureData K Kab) :
    chapter10AbelianClosureUnion (K := K) (Kab := Kab) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  exact A.finite_abelian_subextension x

/-- Restriction of an automorphism of `K^ab` to a finite Galois subfield. -/
noncomputable def chapter10RestrictionMap
    {K : Type u} {Kab : Type v} [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] (L : FiniteGaloisIntermediateField K Kab) :
    Gal(Kab / K) →* Gal(L / K) :=
  by
    haveI : Normal K L := IsGalois.to_normal
    exact AlgEquiv.restrictNormalHom L

/- The corresponding restriction inside a finite tower. -/
noncomputable def chapter10FiniteRestrictionMap
    {K : Type u} {Kab : Type v} [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab]
    {L₁ L₂ : FiniteGaloisIntermediateField K Kab} (h : L₂ ≤ L₁) :
    Gal(L₁ / K) →* Gal(L₂ / K) := by
  haveI : Normal K L₂ := IsGalois.to_normal
  letI : Algebra L₂ L₁ := RingHom.toAlgebra (Subsemiring.inclusion h)
  letI : IsScalarTower K L₂ L₁ := IsScalarTower.of_algebraMap_eq' rfl
  exact AlgEquiv.restrictNormalHom L₂

theorem chapter10FiniteRestrictionMap_comp
    {K : Type u} {Kab : Type v} [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab]
    {L₁ L₂ L₃ : FiniteGaloisIntermediateField K Kab}
    (h₂₁ : L₂ ≤ L₁) (h₃₂ : L₃ ≤ L₂) :
    (chapter10FiniteRestrictionMap (K := K) (Kab := Kab) h₃₂).comp
        (chapter10FiniteRestrictionMap (K := K) (Kab := Kab) h₂₁) =
      chapter10FiniteRestrictionMap (K := K) (Kab := Kab) (h₃₂.trans h₂₁) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: this record is the finite Artin reciprocity API
from the preceding chapters. Its fields are finite-level facts only; no
infinite surjectivity or kernel identification is assumed here. -/
structure Chapter10FiniteArtinFamily
    (C : Type u) (K : Type v) (Kab : Type w) [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] where
  map : ∀ L : FiniteGaloisIntermediateField K Kab, C →* Gal(L / K)
  /-- The finite levels of the chosen abelian closure are abelian. -/
  map_target_abelian :
    ∀ L : FiniteGaloisIntermediateField K Kab,
      chapter10IsAbelianFiniteGaloisExtension L
  map_continuous : ∀ L, Continuous (map L)
  map_surjective : ∀ L, Function.Surjective (map L)
  map_kernel_finiteIndex : ∀ L, ((map L).ker).FiniteIndex
  map_kernel_open : ∀ L, IsOpen ((map L).ker : Set C)
  compatible : ∀ {L₁ L₂} (h : L₂ ≤ L₁),
    (chapter10FiniteRestrictionMap h).comp (map L₁) = map L₂

namespace Chapter10FiniteArtinFamily

variable {C : Type u} {K : Type v} {Kab : Type w} [CommGroup C] [TopologicalSpace C]
  [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
  [IsGalois K Kab]

noncomputable def quotientEquiv
    (F : Chapter10FiniteArtinFamily C K Kab)
    (L : FiniteGaloisIntermediateField K Kab) :
    C ⧸ (F.map L).ker ≃* Gal(L / K) :=
  QuotientGroup.quotientKerEquivOfSurjective (F.map L) (F.map_surjective L)

@[simp]
theorem quotientEquiv_mk
    (F : Chapter10FiniteArtinFamily C K Kab)
    (L : FiniteGaloisIntermediateField K Kab) (c : C) :
    quotientEquiv F L (QuotientGroup.mk c) = F.map L c := by
  rfl

end Chapter10FiniteArtinFamily

/- The finite Artin maps are assembled first in the canonical inverse limit of
finite Galois groups. -/
noncomputable def chapter10ArtinLimitMap
    {C : Type u} {K : Type v} {Kab : Type w} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] (F : Chapter10FiniteArtinFamily C K Kab) :
    C →* ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor K Kab) where
  toFun c :=
    { val := fun L => F.map L.unop c
      property := by
        intro L₁ L₂ f
        sorry }
  map_one' := by
    apply ProfiniteGrp.limit_ext
    intro L
    exact map_one (F.map L.unop)
  map_mul' c d := by
    apply ProfiniteGrp.limit_ext
    intro L
    exact map_mul (F.map L.unop) c d

/-- The assembled global Artin homomorphism. -/
noncomputable def chapter10GlobalArtinMap
    {C : Type u} {K : Type v} {Kab : Type w} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] (F : Chapter10FiniteArtinFamily C K Kab) :
    C →* Gal(Kab / K) :=
  (InfiniteGalois.mulEquivToLimit K Kab).symm.toMonoidHom.comp
    (chapter10ArtinLimitMap F)

theorem chapter10GlobalArtinMap_restrict
    {C : Type u} {K : Type v} {Kab : Type w} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] (F : Chapter10FiniteArtinFamily C K Kab)
    (L : FiniteGaloisIntermediateField K Kab) :
    (chapter10RestrictionMap L).comp (chapter10GlobalArtinMap F) = F.map L := by
  sorry

theorem chapter10GlobalArtinMap_continuous
    {C : Type u} {K : Type v} {Kab : Type w} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] (F : Chapter10FiniteArtinFamily C K Kab) :
    Continuous (chapter10GlobalArtinMap F) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: finite reciprocity plus the existence theorem say
that the kernels of the finite Artin maps are exactly a cofinal family of open
finite-index subgroups. -/
structure Chapter10FiniteReciprocityData
    {C : Type u} {K : Type v} {Kab : Type w} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab] (F : Chapter10FiniteArtinFamily C K Kab) where
  kernel_cofinal :
    ∀ H : Chapter10OpenFiniteIndexNormalSubgroup C,
      ∃ L : FiniteGaloisIntermediateField K Kab,
        H.toSubgroup = (F.map L).ker

/- A local-field warning is kept separate from the global completion API. -/
structure Chapter10LocalReciprocityScope
    (Kv Gv : Type u) [Group Kv] [TopologicalSpace Kv]
    [Group Gv] [TopologicalSpace Gv] where
  reciprocity : Kv →* Gv
  dense_range : DenseRange reciprocity
  valuation_copy : Multiplicative ℤ →* Kv
  valuation_target : Gv →*
      ProfiniteGrp.ProfiniteCompletion.completion
        (GrpCat.of (Multiplicative ℤ))
  valuation_compatibility :
    valuation_target.comp (reciprocity.comp valuation_copy) =
      (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (Multiplicative ℤ))).hom
  not_surjective : ¬ Function.Surjective reciprocity

theorem chapter10_local_reciprocity_dense_not_surjective
    {Kv Gv : Type u} [Group Kv] [TopologicalSpace Kv]
    [Group Gv] [TopologicalSpace Gv]
    (D : Chapter10LocalReciprocityScope Kv Gv) :
    DenseRange D.reciprocity ∧ ¬ Function.Surjective D.reciprocity :=
  ⟨D.dense_range, D.not_surjective⟩

/- The connected-component and norm-one data used in §10.2. -/
/- Mathlib's canonical multiplicative model for the strictly positive reals. -/
abbrev Chapter10PositiveReal := NNRealˣ

structure Chapter10IdeleClassTopologyData
    (C : Type u) [CommGroup C] [TopologicalSpace C]
  [IsTopologicalGroup C] where
  norm : C →* Chapter10PositiveReal
  norm_continuous : Continuous norm
  norm_surjective : Function.Surjective norm
  split : ∃ s : Chapter10PositiveReal →* C,
    norm.comp s = MonoidHom.id _ ∧ Continuous s
  norm_one_compact : IsCompact (norm.ker : Set C)

namespace Chapter10IdeleClassTopologyData

variable {C : Type u} [CommGroup C] [TopologicalSpace C]
  [IsTopologicalGroup C]

def normOneSubgroup (T : Chapter10IdeleClassTopologyData C) : Subgroup C :=
  T.norm.ker

noncomputable def positiveRealComponent
    (T : Chapter10IdeleClassTopologyData C) : Subgroup C :=
  (Classical.choose T.split).range

theorem normOneSubgroup_compact (T : Chapter10IdeleClassTopologyData C) :
    IsCompact (T.normOneSubgroup : Set C) :=
  T.norm_one_compact

theorem norm_exact_sequence (T : Chapter10IdeleClassTopologyData C) :
    Function.MulExact (T.normOneSubgroup.subtype : T.normOneSubgroup → C) T.norm ∧
      Function.Surjective T.norm := by
  constructor
  · sorry
  · exact T.norm_surjective

end Chapter10IdeleClassTopologyData

/- Ray moduli are the finite ideal together with a set of real infinite places. -/
structure Chapter10RayModulus
    (K : Type u) [Field K] [NumberField K] where
  finitePart : Ideal (NumberField.RingOfIntegers K)
  finitePart_nonzero : finitePart ≠ ⊥
  infinitePart : Finset (NumberField.InfinitePlace K)
  infinitePart_real : ∀ v ∈ infinitePart, v.IsReal

namespace Chapter10RayModulus

variable {K : Type u} [Field K] [NumberField K]

instance : LE (Chapter10RayModulus K) where
  le m n := n.finitePart ≤ m.finitePart ∧ m.infinitePart ⊆ n.infinitePart

instance : PartialOrder (Chapter10RayModulus K) where
  le_refl m := ⟨le_rfl, Finset.Subset.rfl⟩
  le_trans a b c hab hbc :=
    ⟨hbc.1.trans hab.1, hab.2.trans hbc.2⟩
  le_antisymm a b hab hba := by
    sorry

theorem finitePart_le_of_le {m n : Chapter10RayModulus K} (h : m ≤ n) :
    n.finitePart ≤ m.finitePart :=
  h.1

theorem infinitePart_subset_of_le {m n : Chapter10RayModulus K} (h : m ≤ n) :
    m.infinitePart ⊆ n.infinitePart :=
  h.2

end Chapter10RayModulus

/- LOCAL_DEPENDENCY_GUESS: ray class fields and the conductor theorem from
§§7--8 are represented by this cofinal system of finite abelian intermediate
fields. The system does not assume the Chapter 10 conclusion. -/
structure Chapter10RayClassFieldSystem
    (K : Type u) (Kab : Type v) [Field K] [NumberField K] [Field Kab]
    [Algebra K Kab] [IsGalois K Kab] where
  rayField : Chapter10RayModulus K → FiniteGaloisIntermediateField K Kab
  rayField_abelian : ∀ m,
    chapter10IsAbelianFiniteGaloisExtension (rayField m)
  rayField_mono : ∀ {m n}, m ≤ n → rayField m ≤ rayField n
  contains_every_finite_abelian :
    ∀ L : FiniteGaloisIntermediateField K Kab,
      chapter10IsAbelianFiniteGaloisExtension L →
        ∃ m, L ≤ rayField m

def chapter10RayClassFieldUnion
    {K : Type u} {Kab : Type v} [Field K] [NumberField K] [Field Kab]
    [Algebra K Kab] [IsGalois K Kab]
    (R : Chapter10RayClassFieldSystem K Kab) : Set Kab :=
  {x | ∃ m, x ∈ (R.rayField m).toIntermediateField}

theorem chapter10RayClassFieldUnion_eq_univ
    {K : Type u} {Kab : Type v} [Field K] [NumberField K] [Field Kab]
    [Algebra K Kab] [IsGalois K Kab]
    (A : Chapter10AbelianClosureData K Kab)
    (R : Chapter10RayClassFieldSystem K Kab) :
    chapter10RayClassFieldUnion R = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨L, hL, hx⟩ := A.finite_abelian_subextension x
  obtain ⟨m, hm⟩ := R.contains_every_finite_abelian L hL
  exact ⟨m, hm hx⟩

/- A functor for the unit groups of the cyclotomic quotients. The positive
index avoids the exceptional infinite ring `ZMod 0`. -/
def Chapter10PositiveNatural := {n : ℕ // 0 < n}

namespace Chapter10PositiveNatural

instance : LE Chapter10PositiveNatural where
  le m n := m.1 ∣ n.1

instance : PartialOrder Chapter10PositiveNatural where
  le_refl n := dvd_refl n.1
  le_trans a b c hab hbc := dvd_trans hab hbc
  le_antisymm a b hab hba := by
    apply Subtype.ext
    exact Nat.dvd_antisymm hab hba

end Chapter10PositiveNatural

noncomputable def chapter10CyclotomicUnitFunctor :
    Chapter10PositiveNaturalᵒᵖ ⥤ FiniteGrp where
  obj m := by
    letI : NeZero m.unop.1 := ⟨Nat.ne_of_gt m.unop.2⟩
    exact FiniteGrp.of ((ZMod m.unop.1)ˣ)
  map {m n} f := by
    letI : NeZero m.unop.1 := ⟨Nat.ne_of_gt m.unop.2⟩
    letI : NeZero n.unop.1 := ⟨Nat.ne_of_gt n.unop.2⟩
    exact FiniteGrp.ofHom
      (ZMod.unitsMap (n := n.unop.1) (m := m.unop.1)
        (show n.unop.1 ∣ m.unop.1 from leOfHom f.unop))
  map_id m := by
    ext x
    simp only [ZMod.unitsMap_self]
    rfl
  map_comp {X Y Z} f g := by
    have hf : Y.unop.1 ∣ X.unop.1 := leOfHom f.unop
    have hg : Z.unop.1 ∣ Y.unop.1 := leOfHom g.unop
    ext x
    change
      ZMod.unitsMap (n := Z.unop.1) (m := X.unop.1) (dvd_trans hg hf) x =
        ZMod.unitsMap (n := Z.unop.1) (m := Y.unop.1) hg
          (ZMod.unitsMap (n := Y.unop.1) (m := X.unop.1) hf x)
    rw [← ZMod.unitsMap_comp hg hf]
    rfl

noncomputable def chapter10CyclotomicUnitInverseLimit : ProfiniteGrp :=
  ProfiniteGrp.limit (chapter10CyclotomicUnitFunctor ⋙ forget₂ FiniteGrp ProfiniteGrp)

noncomputable def chapter10CyclotomicMinusOne :
    chapter10CyclotomicUnitInverseLimit :=
  ⟨fun m => (-1 : (ZMod m.unop.1)ˣ), by
    intro m n f
    change
      ZMod.unitsMap (n := n.unop.1) (m := m.unop.1)
          (show n.unop.1 ∣ m.unop.1 from leOfHom f.unop)
          (-1 : (ZMod m.unop.1)ˣ) =
        (-1 : (ZMod n.unop.1)ˣ)
    rw [ZMod.unitsMap_def, Units.map_neg_one]⟩

end

end LastLib.Book06GlobalClassFieldTheory.Chapter10
