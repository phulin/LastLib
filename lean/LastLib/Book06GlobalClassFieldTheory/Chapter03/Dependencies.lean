import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import LastLib.Book06GlobalClassFieldTheory.Chapter01.Dependencies
import LastLib.Book06GlobalClassFieldTheory.Chapter01.Section01OneGaloisActionSeenAtEveryPlace
import LastLib.Book06GlobalClassFieldTheory.Chapter02.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter03

noncomputable section

open LastLib.Book06GlobalClassFieldTheory.Chapter02
open Filter Set
open scoped BigOperators IsMulCommutative RestrictedProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe uLocal

/-!
## Shared interfaces for Chapter 3

The earlier Chapter 1 interface supplies the canonical idèle group, field norm, and
maximal-abelian-subfield declarations.  The structures below keep the still-abstract
local-factor comparison data explicit rather than silently identifying it with that
canonical model.  They are deliberately phrased as local-field and restricted-product
data, so that the later identification with canonical completions is an API comparison
rather than a second definition of places.
-/

/-- The finite and infinite places used by the book-facing idèle interface. -/
abbrev Chapter03Place (K : Type*) [Field K] [NumberField K] :=
  NumberField.FinitePlace K ⊕ NumberField.InfinitePlace K

/-- One local multiplicative factor together with its topology and integral-unit subgroup.

The carrier is intentionally the multiplicative local group.  A later comparison theorem can
identify it with the units of the canonical completion attached to a finite or infinite place. -/
structure Chapter03LocalFactor where
  carrier : Type*
  [group : CommGroup carrier]
  [topology : TopologicalSpace carrier]
  [topologicalGroup : IsTopologicalGroup carrier]
  [locallyCompact : LocallyCompactSpace carrier]
  unit : Subgroup carrier
  unit_isOpen : IsOpen (unit : Set carrier)

attribute [instance] Chapter03LocalFactor.group Chapter03LocalFactor.topology
  Chapter03LocalFactor.topologicalGroup Chapter03LocalFactor.locallyCompact

/-- The restricted product attached to a chosen family of local factors.  It is kept
separate from `Chapter03Ideles` so that the canonical comparison can be recorded in
`Chapter03FieldIdeleData` without a circular structure reference. -/
abbrev Chapter03RawIdeles
    {K : Type*} [Field K] [NumberField K]
    (localFactor : Chapter03Place K → Chapter03LocalFactor.{uLocal}) :=
  Πʳ v : Chapter03Place K, [(localFactor v).carrier, (localFactor v).unit]

/-- Local factors for a number field, including the diagonal embedding of global units. -/
structure Chapter03FieldIdeleData (K : Type*) [Field K] [NumberField K] where
  localFactor : Chapter03Place K → Chapter03LocalFactor.{uLocal}
  embedding : ∀ v, Units K →* (localFactor v).carrier
  embedding_injective :
    Function.Injective (fun a : Units K => fun v => embedding v a)
  /-- A principal idèle is integral at almost every place, not at every place. -/
  embedding_eventually_mem_unit : ∀ a : Units K, ∀ᶠ v in cofinite,
    embedding v a ∈ (localFactor v).unit
  /-- The finite-place predicate is the canonical left summand of `Chapter03Place`. -/
  finitePlace : Chapter03Place K → Prop
  finitePlace_iff : ∀ v, finitePlace v ↔
    ∃ p : NumberField.FinitePlace K, v = Sum.inl p
  finitePlace_cofinite : ∀ᶠ v in cofinite, finitePlace v
  unit_compact_cofinite :
    ∀ᶠ v in cofinite,
      IsCompact ((localFactor v).unit : Set (localFactor v).carrier)
  /-- Comparison with the canonical place index from Chapter 1. -/
  canonicalPlace : Chapter03Place K ≃
    LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace K
  canonicalPlace_finitePlace_iff :
    ∀ v, finitePlace v ↔
      LastLib.Book06GlobalClassFieldTheory.Chapter01.bookPlaceIsFinite
        (canonicalPlace v)
  /-- Every local carrier is the canonical completed local unit group, with its topology. -/
  canonicalFactor : ∀ v,
    (localFactor v).carrier ≃*
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace.completion
        (canonicalPlace v))ˣ
  canonicalFactor_continuous : ∀ v, Continuous (canonicalFactor v)
  canonicalFactor_inverse_continuous : ∀ v, Continuous (canonicalFactor v).symm
  canonicalFactor_unit_iff : ∀ v (x : (localFactor v).carrier),
    x ∈ (localFactor v).unit ↔
      canonicalFactor v x ∈
        (LastLib.Book06GlobalClassFieldTheory.Chapter01.bookPlaceUnitSubgroup
          (canonicalPlace v) : Set
            (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace.completion
              (canonicalPlace v))ˣ)
  canonicalFactor_embedding : ∀ v (a : Units K),
    canonicalFactor v (embedding v a) =
      LastLib.Book06GlobalClassFieldTheory.Chapter01.bookPlaceUnitEmbedding
        (canonicalPlace v) a
  /-- The whole restricted product is topologically identified with the canonical idèles. -/
  canonicalIdele : Chapter03RawIdeles localFactor ≃*
    LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleGroup K
  canonicalIdele_continuous : Continuous canonicalIdele
  canonicalIdele_inverse_continuous : Continuous canonicalIdele.symm
  canonicalIdele_component : ∀ (x : Chapter03RawIdeles localFactor) (v),
    LastLib.Book06GlobalClassFieldTheory.Chapter01.bookIdeleUnitComponent
        (canonicalIdele x) (canonicalPlace v) =
      canonicalFactor v (x v)
  canonicalIdele_principal : ∀ a : Units K,
    canonicalIdele
        (⟨fun v => embedding v a, embedding_eventually_mem_unit a⟩ :
          Chapter03RawIdeles localFactor) =
      LastLib.Book06GlobalClassFieldTheory.Chapter01.principalIdele a

instance chapter03UnitOpenFact
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) :
    Fact (∀ v, IsOpen ((S.localFactor v).unit : Set (S.localFactor v).carrier)) where
  out v := (S.localFactor v).unit_isOpen

/-- The idèles of a field datum, as the classical restricted product of local multiplicative
groups with respect to the integral-unit subgroups. -/
abbrev Chapter03Ideles
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) :=
  Chapter03RawIdeles S.localFactor

instance chapter03IdelesCommGroup
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) : CommGroup (Chapter03Ideles S) := by
  dsimp [Chapter03Ideles]
  infer_instance

instance chapter03IdelesTopologicalSpace
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) : TopologicalSpace (Chapter03Ideles S) := by
  dsimp [Chapter03Ideles]
  infer_instance

instance chapter03IdelesTopologicalGroup
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) : IsTopologicalGroup (Chapter03Ideles S) := by
  dsimp [Chapter03Ideles]
  infer_instance

instance chapter03IdelesLocallyCompact
  {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) : LocallyCompactSpace (Chapter03Ideles S) := by
  dsimp [Chapter03Ideles]
  exact RestrictedProduct.locallyCompactSpace_of_group
    (R := fun v => (S.localFactor v).carrier)
    (B := fun v => (S.localFactor v).unit)
    S.unit_compact_cofinite

/-- The principal idèle attached to a global unit.  The corresponding map from `Kˣ` is the
book-facing model of the diagonal embedding of `Kˣ` in the idèles. -/
noncomputable def chapter03PrincipalIdele
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) (a : Units K) : Chapter03Ideles S :=
  ⟨fun v => S.embedding v a, S.embedding_eventually_mem_unit a⟩

@[simp] theorem chapter03PrincipalIdele_apply
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) (a : Units K) (v : Chapter03Place K) :
    chapter03PrincipalIdele S a v = S.embedding v a :=
  rfl

noncomputable def chapter03PrincipalIdeleHom
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) : Units K →* Chapter03Ideles S where
  toFun := chapter03PrincipalIdele S
  map_one' := by
    ext v
    simp [chapter03PrincipalIdele]
  map_mul' := by
    intro a b
    ext v
    simp only [chapter03PrincipalIdele_apply, RestrictedProduct.mul_apply]
    exact (S.embedding v).map_mul a b

@[simp] theorem chapter03PrincipalIdeleHom_apply
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) (a : Units K) (v : Chapter03Place K) :
    chapter03PrincipalIdeleHom S a v = S.embedding v a :=
  rfl

theorem chapter03PrincipalIdeleHom_injective
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) :
    Function.Injective (chapter03PrincipalIdeleHom S) := by
  intro a b hab
  apply S.embedding_injective
  funext v
  simpa using congrArg (fun x : Chapter03Ideles S => x v) hab

/-- The principal-idèle subgroup and the idèle class group. -/
def chapter03PrincipalSubgroup
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) : Subgroup (Chapter03Ideles S) :=
  (chapter03PrincipalIdeleHom S).range

/- The diagonal is discrete and closed because the field datum now contains a topological
comparison with the canonical idèles. -/
theorem chapter03PrincipalSubgroup_discrete_closed
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) :
    DiscreteTopology (chapter03PrincipalSubgroup S) ∧
      IsClosed (chapter03PrincipalSubgroup S : Set (Chapter03Ideles S)) := by
  have hcanonical :=
    LastLib.Book06GlobalClassFieldTheory.Chapter01.principalIdele_discrete_closed
      (K := K)
  have hmem : ∀ x : chapter03PrincipalSubgroup S,
      S.canonicalIdele x.1 ∈
        LastLib.Book06GlobalClassFieldTheory.Chapter01.principalIdeleSubgroup K := by
    intro x
    rcases x.2 with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    calc
      LastLib.Book06GlobalClassFieldTheory.Chapter01.principalIdele a =
          S.canonicalIdele (chapter03PrincipalIdele S a) :=
        (S.canonicalIdele_principal a).symm
      _ = S.canonicalIdele x.1 := congrArg S.canonicalIdele ha
  have hcont : Continuous (fun x : chapter03PrincipalSubgroup S =>
      (⟨S.canonicalIdele x.1, hmem x⟩ :
        LastLib.Book06GlobalClassFieldTheory.Chapter01.principalIdeleSubgroup K)) := by
    exact Continuous.subtype_mk
      (S.canonicalIdele_continuous.comp continuous_subtype_val) hmem
  have hinj : Function.Injective (fun x : chapter03PrincipalSubgroup S =>
      (⟨S.canonicalIdele x.1, hmem x⟩ :
        LastLib.Book06GlobalClassFieldTheory.Chapter01.principalIdeleSubgroup K)) := by
    intro x y hxy
    apply Subtype.ext
    apply S.canonicalIdele.injective
    exact congrArg
      (fun z : LastLib.Book06GlobalClassFieldTheory.Chapter01.principalIdeleSubgroup K =>
        (z : LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleGroup K)) hxy
  constructor
  · exact @DiscreteTopology.of_continuous_injective
      (chapter03PrincipalSubgroup S)
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.principalIdeleSubgroup K)
      _ _ hcanonical.1 _ hcont hinj
  · have hset : (chapter03PrincipalSubgroup S : Set (Chapter03Ideles S)) =
        S.canonicalIdele ⁻¹'
          (LastLib.Book06GlobalClassFieldTheory.Chapter01.principalIdeleSubgroup K :
            Set (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleGroup K)) := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        calc
          LastLib.Book06GlobalClassFieldTheory.Chapter01.principalIdele a =
              S.canonicalIdele (chapter03PrincipalIdele S a) :=
            (S.canonicalIdele_principal a).symm
          _ = S.canonicalIdele x := congrArg S.canonicalIdele ha
      · intro hx
        rcases hx with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        apply S.canonicalIdele.injective
        calc
          S.canonicalIdele (chapter03PrincipalIdele S a) =
              LastLib.Book06GlobalClassFieldTheory.Chapter01.principalIdele a :=
            S.canonicalIdele_principal a
          _ = S.canonicalIdele x := ha
    rw [hset]
    exact hcanonical.2.preimage S.canonicalIdele_continuous

theorem chapter03_mem_principalSubgroup_iff
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) (x : Chapter03Ideles S) :
    x ∈ chapter03PrincipalSubgroup S ↔
      ∃ a : Units K, chapter03PrincipalIdeleHom S a = x :=
  Iff.rfl

abbrev Chapter03ClassGroup
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) :=
  Chapter03Ideles S ⧸ chapter03PrincipalSubgroup S

theorem chapter03ClassGroup_locallyCompact_hausdorff
    {K : Type*} [Field K] [NumberField K]
  (S : Chapter03FieldIdeleData K) :
    LocallyCompactSpace (Chapter03ClassGroup S) ∧ T2Space (Chapter03ClassGroup S) := by
  have hclosed := (chapter03PrincipalSubgroup_discrete_closed S).2
  exact ⟨inferInstance,
    @QuotientGroup.instT2Space (Chapter03Ideles S) _ _ _
      (chapter03PrincipalSubgroup S) hclosed⟩

theorem chapter03ClassGroup_not_compact
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) :
    ¬ IsCompact (Set.univ : Set (Chapter03ClassGroup S)) := by
  let P : Subgroup (Chapter03Ideles S) := chapter03PrincipalSubgroup S
  let Q : Subgroup
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleGroup K) :=
    LastLib.Book06GlobalClassFieldTheory.Chapter01.principalIdeleSubgroup K
  have hPQ : P.map S.canonicalIdele = Q := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      rcases hy with ⟨a, rfl⟩
      refine ⟨a, ?_⟩
      change LastLib.Book06GlobalClassFieldTheory.Chapter01.principalIdele a =
        S.canonicalIdele (chapter03PrincipalIdele S a)
      exact (S.canonicalIdele_principal a).symm
    · intro hx
      rcases hx with ⟨a, rfl⟩
      apply Subgroup.mem_map.mpr
      refine ⟨chapter03PrincipalIdele S a, ⟨a, rfl⟩, ?_⟩
      change S.canonicalIdele (chapter03PrincipalIdele S a) =
        LastLib.Book06GlobalClassFieldTheory.Chapter01.principalIdele a
      exact S.canonicalIdele_principal a
  let e : Chapter03ClassGroup S ≃*
      LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleClassGroup K :=
    QuotientGroup.congr P Q S.canonicalIdele hPQ
  have hecont : Continuous e := by
    apply QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff.mpr
    change Continuous (fun x => QuotientGroup.mk' Q (S.canonicalIdele x))
    exact QuotientGroup.continuous_mk.comp S.canonicalIdele_continuous
  intro hcompact
  have himage : IsCompact
      (e '' (Set.univ : Set (Chapter03ClassGroup S))) :=
    hcompact.image hecont
  have hcompactCanonical : IsCompact
      (Set.univ : Set (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleClassGroup K)) := by
    rw [Set.image_univ, e.surjective.range_eq] at himage
    exact himage
  exact LastLib.Book06GlobalClassFieldTheory.Chapter01.idelicClassGroup_not_compact
    (K := K) hcompactCanonical

@[simp] theorem chapter03_class_of_principal
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) (a : Units K) :
    (QuotientGroup.mk' (chapter03PrincipalSubgroup S)
      (chapter03PrincipalIdeleHom S a)) = 1 := by
  exact (QuotientGroup.eq_one_iff (N := chapter03PrincipalSubgroup S)
    (chapter03PrincipalIdeleHom S a)).2 ⟨a, rfl⟩

/-!
### Local decomposition and the global norm data
-/

/-- A ring-level form of the displayed local tensor-product decomposition
`L ⊗_K K_v ≅ ∏_{w | v} L_w`.  The later completion comparison supplies the concrete
local fields and upgrades this to the canonical algebra equivalence. -/
structure Chapter03TensorProductDecomposition
    (K L V : Type*) [Field K] [Field L] [Field V]
    [Algebra K L] [Algebra K V] [FiniteDimensional K L]
    (W : Type*) [Fintype W] (E : W → Type*) [∀ w, Field (E w)]
    [∀ w, Algebra V (E w)] [∀ w, FiniteDimensional V (E w)] where
  equiv : TensorProduct K L V ≃ₐ[V] (∀ w, E w)

/- LOCAL_DEPENDENCY_GUESS: the canonical local-completion and local-reciprocity chapters supply
these finite place fibres, local norm maps, openness, and unramified unit-surjectivity facts.
No global norm, module identity, or class-kernel conclusion is stored as a field. -/
structure Chapter03NormData
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (S_K : Chapter03FieldIdeleData K)
    (S_L : Chapter03FieldIdeleData L) where
  /-- The canonical Chapter 1 norm interface to which this model is compared. -/
  canonicalNorm :
    LastLib.Book06GlobalClassFieldTheory.Chapter01.GlobalNormInterface K L
  /-- The finite fibre of places of `L` lying over a base place. -/
  above : ∀ _ : Chapter03Place K, Finset (Chapter03Place L)
  above_nonempty : ∀ v, (above v).Nonempty
  below : Chapter03Place L → Chapter03Place K
  mem_above_iff :
    ∀ (v : Chapter03Place K) (w : Chapter03Place L), w ∈ above v ↔ below w = v
  above_canonical_iff :
    ∀ (v : Chapter03Place K) (w : Chapter03Place L),
      w ∈ above v ↔
        S_L.canonicalPlace w ∈
          canonicalNorm.above (S_K.canonicalPlace v)
  below_canonical :
    ∀ w : Chapter03Place L,
      S_K.canonicalPlace (below w) =
        canonicalNorm.below (S_L.canonicalPlace w)
  /-- A place above a finite place is finite, and a place above an infinite place is infinite. -/
  finitePlace_above_iff :
    ∀ (v : Chapter03Place K) (w : Chapter03Place L), w ∈ above v →
      (S_L.finitePlace w ↔ S_K.finitePlace v)
  /-- The local norm on a factor; values away from the indicated fibre are irrelevant. -/
  localNorm : ∀ (v : Chapter03Place K) (w : Chapter03Place L),
    (S_L.localFactor w).carrier →* (S_K.localFactor v).carrier
  /-- The product of local norms of a diagonal element is its global norm component. -/
  principal_norm_component :
    ∀ (a : Units L) (v : Chapter03Place K),
      (above v).prod (fun w => localNorm v w (S_L.embedding w a)) =
      S_K.embedding v
          (LastLib.Book06GlobalClassFieldTheory.Chapter01.fieldNormUnits K L a)
  localNorm_canonical :
    ∀ (v : Chapter03Place K) (w : Chapter03Place L), w ∈ above v →
      ∀ x : (S_L.localFactor w).carrier,
        S_K.canonicalFactor v (localNorm v w x) =
          canonicalNorm.localNorm (S_K.canonicalPlace v)
            (S_L.canonicalPlace w) (S_L.canonicalFactor w x)
  localNorm_continuous :
    ∀ (v : Chapter03Place K) (w : Chapter03Place L), Continuous (localNorm v w)
  localNorm_range_isOpen :
    ∀ (v : Chapter03Place K) (w : Chapter03Place L), w ∈ above v →
      IsOpen (MonoidHom.range (localNorm v w) : Set (S_K.localFactor v).carrier)
  localNorm_maps_units :
    ∀ (v : Chapter03Place K) (w : Chapter03Place L), w ∈ above v →
      Set.MapsTo (localNorm v w)
        ((S_L.localFactor w).unit : Set (S_L.localFactor w).carrier)
        ((S_K.localFactor v).unit : Set (S_K.localFactor v).carrier)
  unramified : Chapter03Place K → Prop
  eventually_finite_unramified :
    ∀ᶠ v in cofinite, S_K.finitePlace v ∧ unramified v
  /-- Norms on units are onto at an unramified finite place. -/
  localNorm_units_surjective :
    ∀ {v : Chapter03Place K} (_hv : S_K.finitePlace v) (_hu : unramified v)
      (w : Chapter03Place L) (_hw : w ∈ above v)
      (x : (S_K.localFactor v).carrier), x ∈ (S_K.localFactor v).unit →
      ∃ y : (S_L.localFactor w).carrier,
        y ∈ (S_L.localFactor w).unit ∧ localNorm v w y = x
  /- The eventual-unit assertion is discharged by the restricted-product construction below.
  The componentwise diagonal compatibility above is local input; the global class-norm
    conclusions remain chapter statements rather than fields here. -/

theorem chapter03_eventually_above_mem_unit
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (y : Chapter03Ideles S_L) :
    ∀ᶠ v in cofinite, ∀ w ∈ N.above v,
      y w ∈ (S_L.localFactor w).unit := by
  have hbad : {w : Chapter03Place L |
      y w ∉ (S_L.localFactor w).unit}.Finite :=
    Filter.eventually_cofinite.mp y.2
  let bad : Set (Chapter03Place L) := {w |
    y w ∉ (S_L.localFactor w).unit}
  have hbadBelow : (N.below '' bad).Finite := by
    exact hbad.image N.below
  filter_upwards [hbadBelow.eventually_cofinite_notMem] with v hv w hw
  by_contra hwy
  apply hv
  exact ⟨w, hwy, (N.mem_above_iff v w).1 hw⟩

theorem chapter03_eventually_localNorm_mem_unit
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (y : Chapter03Ideles S_L) :
    ∀ᶠ v in cofinite, ∀ w ∈ N.above v,
      N.localNorm v w (y w) ∈ (S_K.localFactor v).unit := by
  filter_upwards [chapter03_eventually_above_mem_unit N y] with v hv w hw
  exact N.localNorm_maps_units v w hw (hv w hw)

theorem chapter03_finitePlace_above_iff
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (v : Chapter03Place K)
    (w : Chapter03Place L) (hw : w ∈ N.above v) :
    S_L.finitePlace w ↔ S_K.finitePlace v :=
  N.finitePlace_above_iff v w hw

/- LOCAL_DEPENDENCY_GUESS: the next definition is the restricted-product realization of
the local norm formula.  The eventual-unit property in its constructor is the natural
finite-support bridge that will be discharged from the canonical completions and unramified
unit norm theorem. -/
noncomputable def chapter03IdeleNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) : Chapter03Ideles S_L →* Chapter03Ideles S_K := by
  classical
  let f : Chapter03Ideles S_L →
      (∀ v : Chapter03Place K, (S_K.localFactor v).carrier) := fun y v =>
    (N.above v).prod (fun w => N.localNorm v w (y w))
  have hf : ∀ y : Chapter03Ideles S_L, ∀ᶠ v in cofinite,
      f y v ∈ (S_K.localFactor v).unit := by
    intro y
    filter_upwards [chapter03_eventually_localNorm_mem_unit N y] with v hv
    exact (S_K.localFactor v).unit.prod_mem hv
  refine
    { toFun := fun y => ⟨f y, hf y⟩
      map_one' := by
        apply RestrictedProduct.ext
        intro v
        simp [f]
      map_mul' := by
        intro x y
        apply RestrictedProduct.ext
        intro v
        change (N.above v).prod (fun w => N.localNorm v w ((x * y) w)) =
          (N.above v).prod (fun w => N.localNorm v w (x w)) *
            (N.above v).prod (fun w => N.localNorm v w (y w))
        simp [RestrictedProduct.mul_apply, Finset.prod_mul_distrib] }

theorem chapter03IdeleNorm_apply
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (y : Chapter03Ideles S_L)
    (v : Chapter03Place K) :
    chapter03IdeleNorm N y v =
      (N.above v).prod (fun w => N.localNorm v w (y w)) := by
  unfold chapter03IdeleNorm
  rfl

theorem chapter03IdeleNorm_canonical_compatibility
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (y : Chapter03Ideles S_L) :
    S_K.canonicalIdele (chapter03IdeleNorm N y) =
      LastLib.Book06GlobalClassFieldTheory.Chapter01.componentwiseIdeleNorm
        N.canonicalNorm (S_L.canonicalIdele y) := by
  classical
  have hcomponent : ∀ v : Chapter03Place K,
      S_K.canonicalFactor v (chapter03IdeleNorm N y v) =
        (N.canonicalNorm.above (S_K.canonicalPlace v)).prod
          (fun p => N.canonicalNorm.localNorm (S_K.canonicalPlace v) p
            (LastLib.Book06GlobalClassFieldTheory.Chapter01.bookIdeleUnitComponent
              (S_L.canonicalIdele y) p)) := by
    intro v
    rw [chapter03IdeleNorm_apply]
    calc
      S_K.canonicalFactor v
          ((N.above v).prod (fun w => N.localNorm v w (y w))) =
          (N.above v).prod
            (fun w => S_K.canonicalFactor v (N.localNorm v w (y w))) := by
        simp
      _ = (N.above v).prod
          (fun w => N.canonicalNorm.localNorm
            (S_K.canonicalPlace v) (S_L.canonicalPlace w)
            (S_L.canonicalFactor w (y w))) := by
        apply Finset.prod_congr rfl
        intro w hw
        exact N.localNorm_canonical v w hw (y w)
      _ = (N.canonicalNorm.above (S_K.canonicalPlace v)).prod
          (fun p => N.canonicalNorm.localNorm (S_K.canonicalPlace v) p
            (LastLib.Book06GlobalClassFieldTheory.Chapter01.bookIdeleUnitComponent
              (S_L.canonicalIdele y) p)) := by
        apply Finset.prod_nbij (fun w => S_L.canonicalPlace w)
        · intro w hw
          exact (N.above_canonical_iff v w).1 hw
        · intro w₁ hw₁ w₂ hw₂ h
          exact S_L.canonicalPlace.injective h
        · intro p hp
          refine ⟨S_L.canonicalPlace.symm p, ?_, ?_⟩
          · exact (N.above_canonical_iff v (S_L.canonicalPlace.symm p)).2
              (by simpa using hp)
          · exact S_L.canonicalPlace.apply_symm_apply p
        · intro w hw
          rw [S_L.canonicalIdele_component]
  have hunitComponent_injective :
      Function.Injective (fun x :
          LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleGroup K =>
        fun v : LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace K =>
          LastLib.Book06GlobalClassFieldTheory.Chapter01.bookIdeleUnitComponent x v) := by
    intro x z h
    apply Units.ext
    apply Prod.ext
    · funext v
      exact congrArg
        (fun u :
            (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace.completion
              (Sum.inr v))ˣ =>
          (u : LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace.completion
            (Sum.inr v))) (congrFun h (Sum.inr v))
    · apply IsDedekindDomain.FiniteAdeleRing.ext
      intro v
      exact congrArg
        (fun u :
            (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace.completion
              (Sum.inl v))ˣ =>
          (u : LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace.completion
            (Sum.inl v))) (congrFun h (Sum.inl v))
  apply hunitComponent_injective
  funext p
  obtain ⟨v, rfl⟩ := S_K.canonicalPlace.surjective p
  change
    LastLib.Book06GlobalClassFieldTheory.Chapter01.bookIdeleUnitComponent
        (S_K.canonicalIdele (chapter03IdeleNorm N y)) (S_K.canonicalPlace v) =
      LastLib.Book06GlobalClassFieldTheory.Chapter01.bookIdeleUnitComponent
        (N.canonicalNorm.ideleNorm (S_L.canonicalIdele y)) (S_K.canonicalPlace v)
  rw [S_K.canonicalIdele_component, N.canonicalNorm.ideleNorm_component]
  exact hcomponent v

noncomputable def chapter03ContinuousIdeleNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    Chapter03Ideles S_L →ₜ* Chapter03Ideles S_K :=
  ⟨chapter03IdeleNorm N, by
    classical
    apply RestrictedProduct.continuous_dom.mpr
    intro T hT
    let U : Set (Chapter03Place K) := {v |
      ∀ w ∈ N.above v, w ∈ T}
    have hTevent : ∀ᶠ w in cofinite, w ∈ T :=
      Filter.le_principal_iff.mp hT
    have hTbad : Tᶜ.Finite := by
      exact Filter.eventually_cofinite.mp hTevent
    have hbad : (N.below '' Tᶜ).Finite := hTbad.image N.below
    have hUevent : ∀ᶠ v in cofinite, v ∈ U := by
      filter_upwards [hbad.eventually_cofinite_notMem] with v hv
      change ∀ w ∈ N.above v, w ∈ T
      intro w hw
      by_contra hwt
      apply hv
      exact ⟨w, hwt, (N.mem_above_iff v w).1 hw⟩
    have hU : cofinite ≤ 𝓟 U := Filter.le_principal_iff.mpr hUevent
    let g :
        (Πʳ w : Chapter03Place L,
          [(S_L.localFactor w).carrier, (S_L.localFactor w).unit]_[𝓟 T]) →
        (Πʳ v : Chapter03Place K,
          [(S_K.localFactor v).carrier, (S_K.localFactor v).unit]_[𝓟 U]) :=
      fun y => ⟨
        fun v => (N.above v).prod (fun w => N.localNorm v w (y w)),
        by
          rw [Filter.eventually_principal]
          intro v hv
          apply (S_K.localFactor v).unit.prod_mem
          intro w hw
          apply N.localNorm_maps_units v w hw
          exact (Filter.eventually_principal.mp y.2) w (hv w hw)
      ⟩
    have hg : Continuous g := by
      apply RestrictedProduct.continuous_rng_of_principal.mpr
      exact continuous_pi fun v =>
        continuous_finsetProd (N.above v) (fun w hw =>
          (N.localNorm_continuous v w).comp
            (RestrictedProduct.continuous_eval w))
    have hfactor :
        (chapter03IdeleNorm N).toFun ∘
            RestrictedProduct.inclusion
              (fun w => (S_L.localFactor w).carrier)
              (fun w => (S_L.localFactor w).unit) hT =
          RestrictedProduct.inclusion
              (fun v => (S_K.localFactor v).carrier)
              (fun v => (S_K.localFactor v).unit) hU ∘ g := by
      funext y
      apply RestrictedProduct.ext
      intro v
      change (chapter03IdeleNorm N
        (RestrictedProduct.inclusion
          (fun w => (S_L.localFactor w).carrier)
          (fun w => (S_L.localFactor w).unit) hT y)) v = (g y) v
      rw [chapter03IdeleNorm_apply]
      rfl
    rw [hfactor]
    exact (RestrictedProduct.continuous_inclusion hU).comp hg⟩

theorem chapter03_ideleNorm_principal
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units L) :
    chapter03IdeleNorm N (chapter03PrincipalIdeleHom S_L a) =
      chapter03PrincipalIdeleHom S_K
        (LastLib.Book06GlobalClassFieldTheory.Chapter01.fieldNormUnits K L a) := by
  apply RestrictedProduct.ext
  intro v
  rw [chapter03IdeleNorm_apply]
  simp only [chapter03PrincipalIdeleHom_apply]
  exact N.principal_norm_component a v

noncomputable def chapter03ClassNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    Chapter03ClassGroup S_L →* Chapter03ClassGroup S_K :=
  QuotientGroup.lift
    (chapter03PrincipalSubgroup S_L)
    ((QuotientGroup.mk' (chapter03PrincipalSubgroup S_K)).comp (chapter03IdeleNorm N))
    (by
      intro x hx
      rcases hx with ⟨a, rfl⟩
      change (QuotientGroup.mk' (chapter03PrincipalSubgroup S_K))
        (chapter03IdeleNorm N (chapter03PrincipalIdeleHom S_L a)) = 1
      rw [chapter03_ideleNorm_principal]
      exact chapter03_class_of_principal S_K
        (LastLib.Book06GlobalClassFieldTheory.Chapter01.fieldNormUnits K L a))

@[simp] theorem chapter03ClassNorm_mk
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (y : Chapter03Ideles S_L) :
    chapter03ClassNorm N (QuotientGroup.mk' (chapter03PrincipalSubgroup S_L) y) =
      QuotientGroup.mk' (chapter03PrincipalSubgroup S_K) (chapter03IdeleNorm N y) := by
  rfl

noncomputable def chapter03ContinuousClassNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    Chapter03ClassGroup S_L →ₜ* Chapter03ClassGroup S_K :=
  ⟨chapter03ClassNorm N, by
    apply QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff.mpr
    have hnorm : Continuous (chapter03IdeleNorm N) :=
      (chapter03ContinuousIdeleNorm N).continuous_toFun
    have hcomp : Continuous
        ((QuotientGroup.mk' (chapter03PrincipalSubgroup S_K)) ∘
          (chapter03IdeleNorm N)) :=
      QuotientGroup.continuous_mk.comp hnorm
    convert hcomp using 1
    funext x
    change chapter03ClassNorm N
      (QuotientGroup.mk' (chapter03PrincipalSubgroup S_L) x) = _
    exact chapter03ClassNorm_mk N x⟩

/-!
### Adelic module norms and reciprocity interfaces
-/

/-- The positive multiplicative real group used for normalized adelic module norms. -/
abbrev Chapter03PositiveReals := Units NNReal

/- LOCAL_DEPENDENCY_GUESS: normalized adelic volume supplies these two multiplicative maps,
their triviality on principal idèles, and the displayed norm identity. -/
structure Chapter03AdelicModuleData
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) where
  canonicalPositiveReal : Chapter03PositiveReals ≃*
    LastLib.Book06GlobalClassFieldTheory.Chapter01.PositiveReal
  baseModuleNorm : Chapter03Ideles S_K →* Chapter03PositiveReals
  topModuleNorm : Chapter03Ideles S_L →* Chapter03PositiveReals
  baseModuleNorm_surjective : Function.Surjective baseModuleNorm
  /-- The positive module direction is also reached by the norm from the extension. -/
  topModuleNorm_surjective : Function.Surjective topModuleNorm
  baseModuleNorm_continuous : Continuous baseModuleNorm
  topModuleNorm_continuous : Continuous topModuleNorm
  base_principal_norm_one :
    ∀ a : Units K, baseModuleNorm (chapter03PrincipalIdeleHom S_K a) = 1
  top_principal_norm_one :
    ∀ a : Units L, topModuleNorm (chapter03PrincipalIdeleHom S_L a) = 1
  /-- Compatibility of the normalized module with the componentwise norm. -/
  module_norm_compatibility :
    ∀ y : Chapter03Ideles S_L,
      baseModuleNorm (chapter03IdeleNorm N y) = topModuleNorm y
  baseModuleNorm_canonical :
    ∀ x : Chapter03Ideles S_K,
      canonicalPositiveReal (baseModuleNorm x) =
        LastLib.Book06GlobalClassFieldTheory.Chapter01.ideleModule
          (S_K.canonicalIdele x)
  topModuleNorm_canonical :
    ∀ x : Chapter03Ideles S_L,
      canonicalPositiveReal (topModuleNorm x) =
        LastLib.Book06GlobalClassFieldTheory.Chapter01.ideleModule
          (S_L.canonicalIdele x)

theorem chapter03_ideleNorm_moduleNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) (y : Chapter03Ideles S_L) :
    A.baseModuleNorm (chapter03IdeleNorm N y) = A.topModuleNorm y :=
  A.module_norm_compatibility y

/- Chapters 1--2 provide the local and global reciprocity interfaces.  The local maps below are
required to factor through Chapter 2's abelianized local reciprocity data, so norm triviality is
derived from the local norm-kernel theorem rather than stored as an unrelated field. -/
structure Chapter03ArtinReciprocityData
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) where
  globalArtin : Chapter03Ideles S_K →* Abelianization (Gal(L / K))
  localArtin : ∀ v : Chapter03Place K,
    (S_K.localFactor v).carrier →* Abelianization (Gal(L / K))
  localDecompositionGroup :
    ∀ (_v : Chapter03Place K) (_w : Chapter03Place L),
      Subgroup (Gal(L / K))
  localReciprocity :
    ∀ (v : Chapter03Place K) (w : Chapter03Place L)
      (_hw : w ∈ N.above v),
      Chapter02LocalReciprocityData
        ((LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace.completion
          (S_K.canonicalPlace v))ˣ)
        ((LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace.completion
          (S_L.canonicalPlace w))ˣ)
        (localDecompositionGroup v w)
  localReciprocity_norm :
    ∀ (v : Chapter03Place K) (w : Chapter03Place L) (hw : w ∈ N.above v),
      (localReciprocity v w hw).norm =
        N.canonicalNorm.localNorm (S_K.canonicalPlace v)
          (S_L.canonicalPlace w)
  localArtin_canonical :
    ∀ (v : Chapter03Place K) (w : Chapter03Place L) (hw : w ∈ N.above v)
      (x : (S_K.localFactor v).carrier),
      localArtin v x =
        chapter02AbelianizedLocalArtinMap
          (localDecompositionGroup v w).subtype (localReciprocity v w hw)
          (S_K.canonicalFactor v x)
  globalArtin_principal :
    ∀ a : Units K, globalArtin (chapter03PrincipalIdeleHom S_K a) = 1
  globalArtin_local_product :
    ∀ x : Chapter03Ideles S_K, ∃ s : Finset (Chapter03Place K),
      (∀ v ∉ s, localArtin v (x v) = 1) ∧
        globalArtin x = s.prod (fun v => localArtin v (x v))

theorem chapter03_abelianized_local_artin_kills_norm
    {B E G D : Type*} [CommGroup B] [CommGroup E] [Group G] [Group D]
    (inclusion : D →* G)
    (R : Chapter02LocalReciprocityData B E D) (x : E) :
  chapter02AbelianizedLocalArtinMap inclusion R (R.norm x) = 1 := by
  change Abelianization.map inclusion (R.reciprocity (R.norm x)) = 1
  have hx : R.reciprocity (R.norm x) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [R.kernel_eq_norm_range]
    exact ⟨x, rfl⟩
  rw [hx]
  exact (Abelianization.map inclusion).map_one

noncomputable def chapter03ClassArtin
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03ArtinReciprocityData N) :
    Chapter03ClassGroup S_K →* Abelianization (Gal(L / K)) :=
  QuotientGroup.lift (chapter03PrincipalSubgroup S_K) A.globalArtin (by
    intro x hx
    rcases hx with ⟨a, rfl⟩
    exact A.globalArtin_principal a)

@[simp] theorem chapter03ClassArtin_mk
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03ArtinReciprocityData N) (x : Chapter03Ideles S_K) :
    chapter03ClassArtin A
        (QuotientGroup.mk' (chapter03PrincipalSubgroup S_K) x) =
      A.globalArtin x := by
  rfl

/-!
### Towers
-/

structure Chapter03NormTowerData
    {K L M : Type*} [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsScalarTower K L M]
    (S_K : Chapter03FieldIdeleData K)
    (S_L : Chapter03FieldIdeleData L)
    (S_M : Chapter03FieldIdeleData M) where
  norm_L_over_K : Chapter03NormData S_K S_L
  norm_M_over_L : Chapter03NormData S_L S_M
  norm_M_over_K : Chapter03NormData S_K S_M
  canonicalTower :
    LastLib.Book06GlobalClassFieldTheory.Chapter01.GlobalNormTowerInterface K L M
  canonical_norm_L_over_K :
    norm_L_over_K.canonicalNorm = canonicalTower.norm_L_over_K
  canonical_norm_M_over_L :
    norm_M_over_L.canonicalNorm = canonicalTower.norm_M_over_L
  canonical_norm_M_over_K :
    norm_M_over_K.canonicalNorm = canonicalTower.norm_M_over_K
  /-- Componentwise transitivity of the three local norm products. -/
  localNorm_product_transitive :
    ∀ (v : Chapter03Place K) (y : Chapter03Ideles S_M),
      (norm_L_over_K.above v).prod
          (fun w => norm_L_over_K.localNorm v w
            ((norm_M_over_L.above w).prod
              (fun z => norm_M_over_L.localNorm w z (y z)))) =
        (norm_M_over_K.above v).prod
          (fun z => norm_M_over_K.localNorm v z (y z))

theorem chapter03_ideleNorm_transitive
    {K L M : Type*} [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsScalarTower K L M]
    {S_K : Chapter03FieldIdeleData K}
    {S_L : Chapter03FieldIdeleData L}
    {S_M : Chapter03FieldIdeleData M}
    (T : Chapter03NormTowerData S_K S_L S_M) :
    (chapter03IdeleNorm T.norm_L_over_K).comp
        (chapter03IdeleNorm T.norm_M_over_L) =
      chapter03IdeleNorm T.norm_M_over_K := by
  ext y v
  simpa [MonoidHom.comp_apply, chapter03IdeleNorm_apply] using
    T.localNorm_product_transitive v y

end
end LastLib.Book06GlobalClassFieldTheory.Chapter03
