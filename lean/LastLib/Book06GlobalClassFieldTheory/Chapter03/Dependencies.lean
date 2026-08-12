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
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

namespace LastLib.Book06GlobalClassFieldTheory.Chapter03

noncomputable section

open Filter Set
open scoped BigOperators RestrictedProduct

universe uLocal

/-!
## Shared interfaces for Chapter 3

Mathlib has the canonical finite and infinite place types and the restricted-product
construction, but it does not yet package the full idèle group, its local norm maps,
or the global Artin map.  The structures below keep those missing interfaces explicit.
They are deliberately phrased as local-field and restricted-product data, so that the
later identification with the canonical completions is an API comparison rather than a
second definition of places.
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

/-- Local factors for a number field, including the diagonal embedding of global units. -/
structure Chapter03FieldIdeleData (K : Type*) [Field K] [NumberField K] where
  localFactor : Chapter03Place K → Chapter03LocalFactor.{uLocal}
  embedding : ∀ v, Units K →* (localFactor v).carrier
  embedding_mem_unit : ∀ v (a : Units K), embedding v a ∈ (localFactor v).unit
  finitePlace : Chapter03Place K → Prop
  finitePlace_cofinite : ∀ᶠ v in cofinite, finitePlace v
  unit_compact_cofinite :
    ∀ᶠ v in cofinite,
      IsCompact ((localFactor v).unit : Set (localFactor v).carrier)

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
  Πʳ v : Chapter03Place K,
    [(S.localFactor v).carrier, (S.localFactor v).unit]

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
  sorry

/-- The principal idèle attached to a global unit.  The corresponding map from `Kˣ` is the
book-facing model of the diagonal embedding of `Kˣ` in the idèles. -/
noncomputable def chapter03PrincipalIdele
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) (a : Units K) : Chapter03Ideles S :=
  RestrictedProduct.structureMap
    (fun v => (S.localFactor v).carrier) (fun v => (S.localFactor v).unit) cofinite
    (fun v => ⟨S.embedding v a, S.embedding_mem_unit v a⟩)

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
  map_mul' a b := by
    ext v
    simp [chapter03PrincipalIdele]

/-- The principal-idèle subgroup and the idèle class group. -/
def chapter03PrincipalSubgroup
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) : Subgroup (Chapter03Ideles S) :=
  (chapter03PrincipalIdeleHom S).range

abbrev Chapter03ClassGroup
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) :=
  Chapter03Ideles S ⧸ chapter03PrincipalSubgroup S

@[simp] theorem chapter03_class_of_principal
    {K : Type*} [Field K] [NumberField K]
    (S : Chapter03FieldIdeleData K) (a : Units K) :
    (QuotientGroup.mk' (chapter03PrincipalSubgroup S)
      (chapter03PrincipalIdeleHom S a)) = 1 := by
  sorry

/-!
### Local decomposition and the global norm data
-/

/-- A ring-level form of the displayed local tensor-product decomposition
`L ⊗_K K_v ≅ ∏_{w | v} L_w`.  The later completion comparison supplies the concrete
local fields and upgrades this to the canonical algebra equivalence. -/
structure Chapter03TensorProductDecomposition
    (K L V : Type*) [Field K] [Field L] [Field V]
    [Algebra K L] [Algebra K V]
    (W : Type*) [Fintype W] (E : W → Type*) [∀ w, CommRing (E w)] where
  equiv : TensorProduct K L V ≃+* (∀ w, E w)

/- LOCAL_DEPENDENCY_GUESS: the canonical local-completion and local-reciprocity chapters supply
these finite place fibres, local norm maps, openness, and unramified unit-surjectivity facts.
No global norm, module identity, or class-kernel conclusion is stored as a field. -/
structure Chapter03NormData
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (S_K : Chapter03FieldIdeleData K)
    (S_L : Chapter03FieldIdeleData L) where
  /-- The finite fibre of places of `L` lying over a base place. -/
  above : ∀ _ : Chapter03Place K, Finset (Chapter03Place L)
  below : Chapter03Place L → Chapter03Place K
  mem_above_iff :
    ∀ (v : Chapter03Place K) (w : Chapter03Place L), w ∈ above v ↔ below w = v
  /-- The local norm on a factor; values away from the indicated fibre are irrelevant. -/
  localNorm : ∀ (v : Chapter03Place K) (w : Chapter03Place L),
    (S_L.localFactor w).carrier →* (S_K.localFactor v).carrier
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
  /- The eventual-unit and principal-compatibility assertions are chapter theorems below,
  rather than fields here: storing them as fields would make the global norm conclusions
  hypotheses instead of interfaces to be proved. -/

/- LOCAL_DEPENDENCY_GUESS: the next definition is the restricted-product realization of
the local norm formula.  The eventual-unit property in its constructor is the natural
finite-support bridge that will be discharged from the canonical completions and unramified
unit norm theorem. -/
noncomputable def chapter03IdeleNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) : Chapter03Ideles S_L →* Chapter03Ideles S_K := by
  sorry

noncomputable def chapter03ContinuousIdeleNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    Chapter03Ideles S_L →ₜ* Chapter03Ideles S_K :=
  ⟨chapter03IdeleNorm N, by sorry⟩

theorem chapter03_ideleNorm_principal
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units L) :
    chapter03IdeleNorm N (chapter03PrincipalIdeleHom S_L a) =
      chapter03PrincipalIdeleHom S_K (Units.map (Algebra.norm K (S := L)) a) := by
  sorry

noncomputable def chapter03ClassNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    Chapter03ClassGroup S_L →* Chapter03ClassGroup S_K :=
  QuotientGroup.lift
    (chapter03PrincipalSubgroup S_L)
    ((QuotientGroup.mk' (chapter03PrincipalSubgroup S_K)).comp (chapter03IdeleNorm N))
    (by sorry)

@[simp] theorem chapter03ClassNorm_mk
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (y : Chapter03Ideles S_L) :
    chapter03ClassNorm N (QuotientGroup.mk' (chapter03PrincipalSubgroup S_L) y) =
      QuotientGroup.mk' (chapter03PrincipalSubgroup S_K) (chapter03IdeleNorm N y) := by
  sorry

noncomputable def chapter03ContinuousClassNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    Chapter03ClassGroup S_L →ₜ* Chapter03ClassGroup S_K :=
  ⟨chapter03ClassNorm N, by sorry⟩

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
  baseModuleNorm : Chapter03Ideles S_K →* Chapter03PositiveReals
  topModuleNorm : Chapter03Ideles S_L →* Chapter03PositiveReals
  baseModuleNorm_surjective : Function.Surjective baseModuleNorm
  base_principal_norm_one :
    ∀ a : Units K, baseModuleNorm (chapter03PrincipalIdeleHom S_K a) = 1

theorem chapter03_ideleNorm_moduleNorm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03AdelicModuleData N) (y : Chapter03Ideles S_L) :
    A.baseModuleNorm (chapter03IdeleNorm N y) = A.topModuleNorm y :=
  by sorry

/- LOCAL_DEPENDENCY_GUESS: Chapters 1--2 provide the local and global reciprocity maps.
Only their local norm-kernel compatibility is stored here; the global kernel conclusion is
proved below as a chapter statement rather than assumed in this interface. -/
structure Chapter03ArtinReciprocityData
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) where
  globalArtin : Chapter03Ideles S_K →* Gal(L / K)
  localArtin : ∀ v : Chapter03Place K, (S_K.localFactor v).carrier →* Gal(L / K)
  local_norm_trivial :
    ∀ (v : Chapter03Place K) (w : Chapter03Place L) (_hw : w ∈ N.above v)
      (x : (S_L.localFactor w).carrier),
      localArtin v (N.localNorm v w x) = 1

noncomputable def chapter03ClassArtin
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    {N : Chapter03NormData S_K S_L}
    (A : Chapter03ArtinReciprocityData N) :
    Chapter03ClassGroup S_K →* Gal(L / K) :=
  QuotientGroup.lift (chapter03PrincipalSubgroup S_K) A.globalArtin (by sorry)

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
  sorry

end
end LastLib.Book06GlobalClassFieldTheory.Chapter03
