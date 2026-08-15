import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Finsupp.Defs
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Group.Quotient
import LastLib.Book04AdelesAndIdeles.Chapter09.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter09.Section01TheGlobalModuleAndDegree

namespace LastLib.Book06GlobalClassFieldTheory.Chapter01

open scoped BigOperators NumberField

noncomputable section

universe uK

abbrev GroupAbelianization (G : Type*) [Group G] :=
  Abelianization G

/-!
Shared interfaces for Chapter 1.

Mathlib now supplies the number-field places, completions, restricted finite
adeles, the adele ring, the product formula, and the topological abelianization
of the absolute Galois group.  The preceding LastLib books do not yet expose
idele norms, local reciprocity, Brauer invariants, or Tate cohomology, so the
small interfaces below are the natural dependency boundary for this chapter.
-/

/-! ### Canonical adelic objects -/

abbrev FinitePlaceIndex (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.HeightOneSpectrum (𝓞 K)

abbrev InfinitePlaceIndex (K : Type*) [Field K] [NumberField K] :=
  NumberField.InfinitePlace K

abbrev BookAdeleRing (K : Type*) [Field K] [NumberField K] :=
  NumberField.AdeleRing (𝓞 K) K

abbrev BookIdeleGroup (K : Type*) [Field K] [NumberField K] :=
  (BookAdeleRing K)ˣ

def principalIdele {K : Type*} [Field K] [NumberField K] :
    Kˣ →* BookIdeleGroup K :=
  Units.map (algebraMap K (BookAdeleRing K))

def principalIdeleSubgroup (K : Type*) [Field K] [NumberField K] :
    Subgroup (BookIdeleGroup K) :=
  (principalIdele (K := K)).range

abbrev BookIdeleClassGroup (K : Type*) [Field K] [NumberField K] :=
  BookIdeleGroup K ⧸ principalIdeleSubgroup K

/-! The standard book-facing names are shared by every section.  Keeping them
in the dependency leaf avoids making later sections import earlier prose
sections merely to recover these aliases. -/
abbrev I_K (K : Type*) [Field K] [NumberField K] := BookIdeleGroup K

abbrev C_K (K : Type*) [Field K] [NumberField K] := BookIdeleClassGroup K

instance bookIdeleClassGroupCommGroup
    (K : Type*) [Field K] [NumberField K] :
    CommGroup (BookIdeleClassGroup K) := by
  infer_instance

def classQuotient {K : Type*} [Field K] [NumberField K] :
    BookIdeleGroup K →* BookIdeleClassGroup K :=
  QuotientGroup.mk' (principalIdeleSubgroup K)

@[simp]
theorem classQuotient_principal {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) : classQuotient (principalIdele (K := K) a) = 1 := by
  exact (QuotientGroup.eq_one_iff _).2 ⟨a, rfl⟩

theorem classQuotient_eq_one_iff {K : Type*} [Field K] [NumberField K]
    (x : BookIdeleGroup K) :
    classQuotient x = 1 ↔ x ∈ principalIdeleSubgroup K := by
  exact QuotientGroup.eq_one_iff x

theorem principalIdele_injective {K : Type*} [Field K] [NumberField K] :
    Function.Injective (principalIdele (K := K)) := by
  exact Units.map_injective
    (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K))

/-! ### Places and their local fields -/

def BookPlace (K : Type*) [Field K] [NumberField K] :=
  Sum (FinitePlaceIndex K) (InfinitePlaceIndex K)

abbrev BookPlace.completion {K : Type*} [Field K] [NumberField K]
    (v : BookPlace K) : Type _ :=
  match v with
  | Sum.inl w => w.adicCompletion K
  | Sum.inr w => w.Completion

instance BookPlace.completion.field {K : Type*} [Field K] [NumberField K]
    (v : BookPlace K) : Field (BookPlace.completion v) := by
  cases v <;> infer_instance

instance BookPlace.completion.algebra {K : Type*} [Field K] [NumberField K]
    (v : BookPlace K) : Algebra K (BookPlace.completion v) := by
  cases v <;> infer_instance

instance BookPlace.completion.normedField {K : Type*} [Field K] [NumberField K]
    (v : BookPlace K) : NormedField (BookPlace.completion v) := by
  cases v <;> infer_instance

def bookIdeleComponent {K : Type*} [Field K] [NumberField K]
    (x : BookIdeleGroup K) (v : BookPlace K) : BookPlace.completion v :=
  match v with
  | Sum.inl w => (x : BookAdeleRing K).2 w
  | Sum.inr w => (x : BookAdeleRing K).1 w

def bookIdeleUnitComponent {K : Type*} [Field K] [NumberField K]
    (x : BookIdeleGroup K) (v : BookPlace K) : (BookPlace.completion v)ˣ := by
  cases v with
  | inl w =>
      exact
        { val := (x : BookAdeleRing K).2 w
          inv := ((x⁻¹ : BookIdeleGroup K) : BookAdeleRing K).2 w
          val_inv := congrArg (fun a : BookAdeleRing K => a.2 w) x.val_inv
          inv_val := congrArg (fun a : BookAdeleRing K => a.2 w) x.inv_val }
  | inr w =>
      exact
        { val := (x : BookAdeleRing K).1 w
          inv := ((x⁻¹ : BookIdeleGroup K) : BookAdeleRing K).1 w
          val_inv := congrArg (fun a : BookAdeleRing K => a.1 w) x.val_inv
          inv_val := congrArg (fun a : BookAdeleRing K => a.1 w) x.inv_val }

def bookPlaceUnitEmbedding {K : Type*} [Field K] [NumberField K]
    (v : BookPlace K) : Kˣ →* (BookPlace.completion v)ˣ :=
  Units.map (algebraMap K (BookPlace.completion v))

def bookFinitePlaceUnitSubgroup {K : Type*} [Field K] [NumberField K]
    (v : FinitePlaceIndex K) : Subgroup (BookPlace.completion (Sum.inl v))ˣ :=
  (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom).range

abbrev finitePlaceUnitSubgroup {K : Type*} [Field K] [NumberField K]
    (v : FinitePlaceIndex K) : Subgroup (BookPlace.completion (Sum.inl v))ˣ :=
  bookFinitePlaceUnitSubgroup v

def bookPlaceUnitSubgroup {K : Type*} [Field K] [NumberField K]
    (v : BookPlace K) : Subgroup (BookPlace.completion v)ˣ :=
  match v with
  | Sum.inl w => bookFinitePlaceUnitSubgroup w
  | Sum.inr _ => ⊤

def bookPlaceIsFinite {K : Type*} [Field K] [NumberField K]
    (v : BookPlace K) : Prop := ∃ w : FinitePlaceIndex K, v = Sum.inl w

/- The integral-unit subgroup at a finite place, viewed in its completion. -/
def finitePlaceUnitSet {K : Type*} [Field K] [NumberField K]
    (v : FinitePlaceIndex K) : Set (BookPlace.completion (Sum.inl v)) :=
  Set.range (fun u : (v.adicCompletionIntegers K)ˣ =>
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (u : v.adicCompletionIntegers K))

/-! ### The idelic module and its class quotient -/

abbrev PositiveReal := {r : ℝ // 0 < r}

instance : CommGroup PositiveReal where
  mul x y := ⟨x.1 * y.1, mul_pos x.2 y.2⟩
  one := ⟨1, zero_lt_one⟩
  inv x := ⟨x.1⁻¹, inv_pos.mpr x.2⟩
  mul_assoc x y z := by
    apply Subtype.ext
    simp [mul_assoc]
  one_mul x := by
    apply Subtype.ext
    simp
  mul_one x := by
    apply Subtype.ext
    simp
  inv_mul_cancel x := by
    apply Subtype.ext
    exact inv_mul_cancel₀ (ne_of_gt x.2)
  mul_comm x y := by
    apply Subtype.ext
    exact mul_comm _ _

@[ext]
theorem positiveReal_ext {x y : PositiveReal} (h : (x : ℝ) = y) : x = y := by
  exact Subtype.ext h

def ideleModuleValue {K : Type*} [Field K] [NumberField K]
    (x : BookIdeleGroup K) : ℝ :=
  ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModule x).val : ℝ)

/- The preceding adelic chapter supplies the normalized finite-place factors
 and the product formula.  Reuse that module here rather than the raw norm on
 an adic completion: Mathlib's raw norm has exponential normalization, while
 the global idelic module uses `q_v ^ (-ord_v)`. -/
noncomputable def ideleModule {K : Type*} [Field K] [NumberField K] :
    BookIdeleGroup K →* PositiveReal where
  toFun x := ⟨ideleModuleValue x, by
    change (0 : ℝ) <
      ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModule x).val : ℝ)
    exact NNReal.coe_pos.2 (pos_iff_ne_zero.2
      (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModule_ne_zero x))⟩
  map_one' := by
    apply positiveReal_ext
    change ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModule
      (1 : BookIdeleGroup K)).val : ℝ) = 1
    change ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModuleHom K
      (1 : BookIdeleGroup K)).val : ℝ) = 1
    exact congrArg
      (fun u : LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09PositiveReal =>
        (u.val : ℝ))
      ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModuleHom K).map_one)
  map_mul' x y := by
    apply positiveReal_ext
    change ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModule
      (x * y)).val : ℝ) =
      ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModule x).val : ℝ) *
        ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModule y).val : ℝ)
    change ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModuleHom K
      (x * y)).val : ℝ) =
      ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModuleHom K x).val : ℝ) *
        ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModuleHom K y).val : ℝ)
    rw [(LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModuleHom K).map_mul]
    rfl

theorem ideleModule_apply {K : Type*} [Field K] [NumberField K]
    (x : BookIdeleGroup K) :
    (ideleModule x : ℝ) = ideleModuleValue x := rfl

/- The ordinary product formula is the reason the module descends to classes. -/
theorem principal_idele_module_eq_one {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) : ideleModule (principalIdele a) = 1 := by
  apply positiveReal_ext
  exact congrArg
    (fun u : LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09PositiveReal =>
      (u.val : ℝ))
    (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09PrincipalIdele_module_eq_one a)

noncomputable def classModule {K : Type*} [Field K] [NumberField K] :
    BookIdeleClassGroup K →* PositiveReal :=
  QuotientGroup.lift (principalIdeleSubgroup K) (ideleModule (K := K)) (by
    intro x hx
    rcases hx with ⟨a, rfl⟩
    exact principal_idele_module_eq_one a)

abbrev classModuleOneSubgroup (K : Type*) [Field K] [NumberField K] :
    Subgroup (BookIdeleClassGroup K) :=
  (classModule (K := K)).ker

/- LOCAL_DEPENDENCY_GUESS: surjectivity is the archimedean positive-real
direction of the idelic module. -/
theorem classModule_surjective {K : Type*} [Field K] [NumberField K] :
    Function.Surjective (classModule (K := K)) := by
  intro t
  let u : LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09PositiveReal :=
    Units.mk0 ⟨(t : ℝ), le_of_lt t.2⟩ (by
      exact ne_of_gt t.2)
  rcases LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModule_surjective K u with
    ⟨x, hx⟩
  refine ⟨classQuotient x, ?_⟩
  change ideleModule x = t
  apply positiveReal_ext
  change ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModuleHom K x).val : ℝ) = t
  rw [hx]
  rfl

/-! ### Global norm and finite-level reciprocity interfaces -/

/- The field norm on units is the canonical multiplicative norm used by the
idele norm and by the element-norm predicates later in the chapter. -/
noncomputable def fieldNormUnits
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K (S := L))

@[simp]
theorem fieldNormUnits_apply
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (y : Lˣ) :
    ((fieldNormUnits K L y : Kˣ) : K) = Algebra.norm K (y : L) := by
  rfl

def IsFiniteAbelianExtension (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] : Prop :=
  FiniteDimensional K L ∧ IsAbelianGalois K L

/- The canonical maximal abelian subextension is the fixed field of the
commutator subgroup; norm limitation compares this field with the original
Galois extension over the same base. -/
def globalMaximalAbelianSubextension
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] : IntermediateField K L :=
  IntermediateField.fixedField (commutator (Gal(L / K)))

/- The branch norm is tied to the canonical finite-dimensional algebra norm.
The place interface below supplies the local algebra structure because the
completion API does not yet choose an embedding of a completion above `v` over
the completion at `v`. -/
structure BookLocalNormData (F E : Type*) [Field F] [Field E] where
  [algebra : Algebra F E]
  [finiteDimensional : FiniteDimensional F E]
  norm : Eˣ →* Fˣ
  norm_eq : norm = Units.map (Algebra.norm F (S := E))

/- The component formula is recorded in the structure so the map cannot be
replaced by a free unrelated homomorphism. -/
structure GlobalNormInterface (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] where
  above : ∀ _v : BookPlace K, Finset (BookPlace L)
  above_nonempty : ∀ v, (above v).Nonempty
  below : BookPlace L → BookPlace K
  mem_above_iff :
    ∀ (v : BookPlace K) (w : BookPlace L), w ∈ above v ↔ below w = v
  localNorm : ∀ (v : BookPlace K) (w : BookPlace L),
    (BookPlace.completion w)ˣ →* (BookPlace.completion v)ˣ
  localNormData : ∀ (v : BookPlace K) (w : BookPlace L), w ∈ above v →
    BookLocalNormData (BookPlace.completion v) (BookPlace.completion w)
  localNorm_is_field_norm : ∀ (v : BookPlace K) (w : BookPlace L)
      (hw : w ∈ above v),
      localNorm v w = (localNormData v w hw).norm
  principal_norm_component :
    ∀ (a : Lˣ) (v : BookPlace K),
      (above v).prod (fun w => localNorm v w (bookPlaceUnitEmbedding w a)) =
        bookPlaceUnitEmbedding v (fieldNormUnits K L a)
  localNorm_continuous :
    ∀ (v : BookPlace K) (w : BookPlace L), Continuous (localNorm v w)
  localNorm_maps_units :
    ∀ (v : BookPlace K) (w : BookPlace L), w ∈ above v →
      Set.MapsTo (localNorm v w)
        (bookPlaceUnitSubgroup w : Set (BookPlace.completion w)ˣ)
        (bookPlaceUnitSubgroup v : Set (BookPlace.completion v)ˣ)
  /- The idele norm is the homomorphism whose local unit components are the
     products of the local norms over all places above a base place.  Keeping
     this equation in the interface prevents the later class norm from being
     built from an unrelated arbitrary homomorphism. -/
  ideleNorm : BookIdeleGroup L →* BookIdeleGroup K
  ideleNorm_component :
    ∀ (x : BookIdeleGroup L) (v : BookPlace K),
      bookIdeleUnitComponent (ideleNorm x) v =
        (above v).prod (fun w =>
          localNorm v w (bookIdeleUnitComponent x w))
  unramified : BookPlace K → Prop
  eventually_finite_unramified :
    ∀ᶠ v in Filter.cofinite, bookPlaceIsFinite v ∧ unramified v
  localNorm_units_surjective :
    ∀ {v : BookPlace K} (_hv : bookPlaceIsFinite v) (_hu : unramified v)
      (w : BookPlace L) (_hw : w ∈ above v)
      (x : (BookPlace.completion v)ˣ),
      x ∈ bookPlaceUnitSubgroup v →
        ∃ y : (BookPlace.completion w)ˣ,
          y ∈ bookPlaceUnitSubgroup w ∧ localNorm v w y = x

noncomputable def componentwiseIdeleNorm
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) : BookIdeleGroup L →* BookIdeleGroup K :=
  N.ideleNorm

theorem GlobalNormInterface.principal_compatibility_apply
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) (y : Lˣ) :
    componentwiseIdeleNorm N (principalIdele y) =
      principalIdele (fieldNormUnits K L y) := by
  apply Units.ext
  apply Prod.ext
  · funext v
    have hcomp : ∀ w : BookPlace L,
        bookIdeleUnitComponent (principalIdele y) w = bookPlaceUnitEmbedding w y := by
      intro w
      cases w <;> rfl
    have h := N.ideleNorm_component (principalIdele y) (Sum.inr v)
    simp_rw [hcomp] at h
    have hp := N.principal_norm_component y (Sum.inr v)
    have h' := h.trans hp
    change ((N.ideleNorm (principalIdele y) : BookIdeleGroup K).val).1 v =
      ((principalIdele (fieldNormUnits K L y) : BookIdeleGroup K).val).1 v
    simpa [bookIdeleUnitComponent, principalIdele, bookPlaceUnitEmbedding] using
      congrArg Units.val h'
  · apply IsDedekindDomain.FiniteAdeleRing.ext
    intro v
    have hcomp : ∀ w : BookPlace L,
        bookIdeleUnitComponent (principalIdele y) w = bookPlaceUnitEmbedding w y := by
      intro w
      cases w <;> rfl
    have h := N.ideleNorm_component (principalIdele y) (Sum.inl v)
    simp_rw [hcomp] at h
    have hp := N.principal_norm_component y (Sum.inl v)
    have h' := h.trans hp
    change ((N.ideleNorm (principalIdele y) : BookIdeleGroup K).val).2 v =
      (bookPlaceUnitEmbedding (Sum.inl v) (fieldNormUnits K L y)).val
    exact congrArg Units.val h'

noncomputable def classNorm {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) :
  BookIdeleClassGroup L →* BookIdeleClassGroup K :=
  QuotientGroup.lift (principalIdeleSubgroup L)
    ((classQuotient (K := K)).comp (componentwiseIdeleNorm N)) (by
      intro x hx
      rcases hx with ⟨y, rfl⟩
      rw [MonoidHom.mem_ker]
      change classQuotient (componentwiseIdeleNorm N (principalIdele y)) = 1
      rw [N.principal_compatibility_apply y]
      exact classQuotient_principal (fieldNormUnits K L y))

@[simp]
theorem classNorm_apply_classQuotient
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) (x : BookIdeleGroup L) :
    classNorm N (classQuotient x) =
      classQuotient (componentwiseIdeleNorm N x) := by
  rfl

def ideleNormGroup {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) : Subgroup (BookIdeleGroup K) :=
  (componentwiseIdeleNorm N).range

def classNormGroup {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) : Subgroup (BookIdeleClassGroup K) :=
  (classNorm N).range

/- The class-field existence theorem returns an extension together with the
norm interface whose class norm subgroup is the prescribed subgroup. -/
structure ClassFieldNormRealization
    (K : Type uK) [Field K] [NumberField K]
    (H : Subgroup (BookIdeleClassGroup K)) where
  L : Type uK
  [field_L : Field L]
  [numberField_L : NumberField L]
  [algebra_K_L : Algebra K L]
  [finiteDimensional_K_L : FiniteDimensional K L]
  [abelianGalois_K_L : IsAbelianGalois K L]
  normData : GlobalNormInterface K L
  norm_eq : classNormGroup normData = H

/- Componentwise transitivity is recorded at the local level and then lifted
to the idele maps.  This is the tower law for the canonical norm interface. -/
structure GlobalNormTowerInterface
    (K L M : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsScalarTower K L M] where
  norm_L_over_K : GlobalNormInterface K L
  norm_M_over_L : GlobalNormInterface L M
  norm_M_over_K : GlobalNormInterface K M
  localNorm_product_transitive :
    ∀ (v : BookPlace K) (y : BookIdeleGroup M),
      (norm_L_over_K.above v).prod
          (fun w => norm_L_over_K.localNorm v w
            ((norm_M_over_L.above w).prod
              (fun z => norm_M_over_L.localNorm w z
                (bookIdeleUnitComponent y z)))) =
        (norm_M_over_K.above v).prod
          (fun z => norm_M_over_K.localNorm v z
            (bookIdeleUnitComponent y z))
  fieldNorm_transitive :
    (fieldNormUnits K L).comp (fieldNormUnits L M) = fieldNormUnits K M

/- A global norm-limitation assertion must compare compatible norm interfaces.
   In particular, equality of two unrelated class-norm subgroups is not enough:
   the interfaces for the extension and its maximal abelian subextension must be
   the two legs of one norm tower. -/
structure GlobalClassNormLimitationData
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] where
  norm_L : GlobalNormInterface K L
  norm_maximal :
    GlobalNormInterface K (globalMaximalAbelianSubextension K L)
  tower :
    GlobalNormTowerInterface K (globalMaximalAbelianSubextension K L) L
  norm_L_eq_tower : norm_L = tower.norm_M_over_K
  norm_maximal_eq_tower : norm_maximal = tower.norm_L_over_K

theorem global_class_norm_limitation
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : GlobalClassNormLimitationData K L) :
    classNormGroup D.norm_L = classNormGroup D.norm_maximal := by
  sorry

theorem componentwiseIdeleNorm_transitive
    {K L M : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsScalarTower K L M]
    (T : GlobalNormTowerInterface K L M) :
    (componentwiseIdeleNorm T.norm_L_over_K).comp
        (componentwiseIdeleNorm T.norm_M_over_L) =
      componentwiseIdeleNorm T.norm_M_over_K := by
  apply MonoidHom.ext
  intro y
  have hcomponent : ∀ v : BookPlace K,
      bookIdeleUnitComponent
          ((componentwiseIdeleNorm T.norm_L_over_K).comp
            (componentwiseIdeleNorm T.norm_M_over_L) y) v =
        bookIdeleUnitComponent (componentwiseIdeleNorm T.norm_M_over_K y) v := by
    intro v
    have hinner : ∀ w : BookPlace L,
        bookIdeleUnitComponent (T.norm_M_over_L.ideleNorm y) w =
          (T.norm_M_over_L.above w).prod
            (fun z => T.norm_M_over_L.localNorm w z
              (bookIdeleUnitComponent y z)) := by
      intro w
      exact T.norm_M_over_L.ideleNorm_component y w
    have hleft := T.norm_L_over_K.ideleNorm_component
      (T.norm_M_over_L.ideleNorm y) v
    simp_rw [hinner] at hleft
    have htrans := T.localNorm_product_transitive v y
    have hright := T.norm_M_over_K.ideleNorm_component y v
    exact hleft.trans (htrans.trans hright.symm)
  apply Units.ext
  apply Prod.ext
  · funext v
    have h := hcomponent (Sum.inr v)
    change ((T.norm_L_over_K.ideleNorm (T.norm_M_over_L.ideleNorm y) :
        BookIdeleGroup K).val).1 v =
      ((T.norm_M_over_K.ideleNorm y : BookIdeleGroup K).val).1 v
    exact congrArg Units.val h
  · apply IsDedekindDomain.FiniteAdeleRing.ext
    intro v
    have h := hcomponent (Sum.inl v)
    change ((T.norm_L_over_K.ideleNorm (T.norm_M_over_L.ideleNorm y) :
        BookIdeleGroup K).val).2 v =
      ((T.norm_M_over_K.ideleNorm y : BookIdeleGroup K).val).2 v
    exact congrArg Units.val h

def principalTimesIdeleNormGroup {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) : Subgroup (BookIdeleGroup K) :=
  principalIdeleSubgroup K ⊔ ideleNormGroup N

theorem classNormGroup_eq_principal_times_norm_quotient
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) :
    classNormGroup N =
      (Subgroup.map (classQuotient (K := K))
        (principalTimesIdeleNormGroup N)) := by
  change (classNorm N).range =
    (principalIdeleSubgroup K ⊔ (componentwiseIdeleNorm N).range).map
      (classQuotient (K := K))
  rw [Subgroup.map_sup]
  have hprincipal :
      (principalIdeleSubgroup K).map (classQuotient (K := K)) = ⊥ := by
    apply Subgroup.ext
    intro c
    constructor
    · intro hc
      rcases Subgroup.mem_map.mp hc with ⟨x, ⟨a, rfl⟩, hx⟩
      rw [classQuotient_principal] at hx
      rw [← hx]
      exact Subgroup.one_mem _
    · intro hc
      have hc' : c = 1 := by simpa using hc
      rw [hc']
      exact Subgroup.mem_map_of_mem (classQuotient (K := K))
        (show principalIdele (1 : Kˣ) ∈ principalIdeleSubgroup K from ⟨1, rfl⟩)
  rw [hprincipal, bot_sup_eq]
  apply Subgroup.ext
  intro c
  constructor
  · intro hc
    rcases hc with ⟨q, rfl⟩
    rcases QuotientGroup.mk'_surjective (principalIdeleSubgroup L) q with ⟨x, rfl⟩
    refine Subgroup.mem_map.mpr ⟨componentwiseIdeleNorm N x, ⟨x, rfl⟩, ?_⟩
    exact (classNorm_apply_classQuotient N x).symm
  · intro hc
    rcases Subgroup.mem_map.mp hc with ⟨z, ⟨x, rfl⟩, rfl⟩
    refine ⟨classQuotient x, ?_⟩
    exact classNorm_apply_classQuotient N x

/- The global Artin map is constructed from the local reciprocity family and
its finite unit tail.  It is not an independent homomorphism field. -/
noncomputable def finiteLevelGlobalArtin
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (localArtin : ∀ v : BookPlace K,
      (BookPlace.completion v)ˣ →* GroupAbelianization (Gal(L / K)))
    (finite_product :
      ∀ x : BookIdeleGroup K, ∃ s : Finset (BookPlace K),
        ∀ v ∉ s, localArtin v (bookIdeleUnitComponent x v) = 1) :
    BookIdeleGroup K →* GroupAbelianization (Gal(L / K)) where
  toFun x :=
    Finset.prod (Classical.choose (finite_product x))
      (fun v => localArtin v (bookIdeleUnitComponent x v))
  map_one' := by
    classical
    have hunit : ∀ v : BookPlace K,
        bookIdeleUnitComponent (1 : BookIdeleGroup K) v = 1 := by
      intro v
      cases v with
      | inl w =>
          apply Units.ext
          change ((1 : BookAdeleRing K).2 w) = 1
          rfl
      | inr w =>
          apply Units.ext
          change ((1 : BookAdeleRing K).1 w) = 1
          rfl
    simp_rw [hunit]
    simp
  map_mul' := by
    classical
    intro x y
    let sxy : Finset (BookPlace K) :=
      Classical.choose (finite_product (x * y))
    let sx : Finset (BookPlace K) :=
      Classical.choose (finite_product x)
    let sy : Finset (BookPlace K) :=
      Classical.choose (finite_product y)
    let s : Finset (BookPlace K) := sxy ∪ sx ∪ sy
    let fxy : BookPlace K → GroupAbelianization (Gal(L / K)) :=
      fun v => localArtin v (bookIdeleUnitComponent (x * y) v)
    let fx : BookPlace K → GroupAbelianization (Gal(L / K)) :=
      fun v => localArtin v (bookIdeleUnitComponent x v)
    let fy : BookPlace K → GroupAbelianization (Gal(L / K)) :=
      fun v => localArtin v (bookIdeleUnitComponent y v)
    have hxy : ∀ v ∉ sxy, fxy v = 1 := by
      intro v hv
      exact Classical.choose_spec (finite_product (x * y)) v hv
    have hx : ∀ v ∉ sx, fx v = 1 := by
      intro v hv
      exact Classical.choose_spec (finite_product x) v hv
    have hy : ∀ v ∉ sy, fy v = 1 := by
      intro v hv
      exact Classical.choose_spec (finite_product y) v hv
    have hsxy : sxy ⊆ s := by
      intro v hv
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inl hv)))
    have hsx : sx ⊆ s := by
      intro v hv
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inr hv)))
    have hsy : sy ⊆ s := by
      intro v hv
      exact Finset.mem_union.mpr (Or.inr hv)
    have hprod_xy : Finset.prod sxy fxy = Finset.prod s fxy := by
      apply Finset.prod_subset hsxy
      intro v hv hnot
      exact hxy v hnot
    have hprod_x : Finset.prod sx fx = Finset.prod s fx := by
      apply Finset.prod_subset hsx
      intro v hv hnot
      exact hx v hnot
    have hprod_y : Finset.prod sy fy = Finset.prod s fy := by
      apply Finset.prod_subset hsy
      intro v hv hnot
      exact hy v hnot
    have hcomponent : ∀ v : BookPlace K,
        bookIdeleUnitComponent (x * y) v =
          bookIdeleUnitComponent x v * bookIdeleUnitComponent y v := by
      intro v
      cases v with
      | inl w =>
          apply Units.ext
          rfl
      | inr w =>
          apply Units.ext
          rfl
    have hlocal : ∀ v : BookPlace K, fxy v = fx v * fy v := by
      intro v
      change localArtin v (bookIdeleUnitComponent (x * y) v) =
        localArtin v (bookIdeleUnitComponent x v) *
          localArtin v (bookIdeleUnitComponent y v)
      rw [hcomponent]
      exact (localArtin v).map_mul _ _
    change Finset.prod sxy fxy = Finset.prod sx fx * Finset.prod sy fy
    rw [hprod_xy, hprod_x, hprod_y, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    exact hlocal v

structure FiniteLevelArtinData (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] where
  localArtin : ∀ v : BookPlace K,
    (BookPlace.completion v)ˣ →* GroupAbelianization (Gal(L / K))
  decomposition : ∀ _v : BookPlace K,
    Subgroup (GroupAbelianization (Gal(L / K)))
  local_artin_range : ∀ v, (localArtin v).range = decomposition v
  ramified : Finset (BookPlace K)
  local_units_killed_outside_ramification :
    ∀ {v : BookPlace K}, v ∉ ramified → ∀ u,
      u ∈ bookPlaceUnitSubgroup v → localArtin v u = 1
  finite_product :
    ∀ x : BookIdeleGroup K, ∃ s : Finset (BookPlace K),
      ∀ v ∉ s, localArtin v (bookIdeleUnitComponent x v) = 1
  principal_trivial :
    ∀ a : Kˣ,
      finiteLevelGlobalArtin localArtin finite_product (principalIdele a) = 1

noncomputable def FiniteLevelArtinData.globalArtin
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (A : FiniteLevelArtinData K L) :
    BookIdeleGroup K →* GroupAbelianization (Gal(L / K)) :=
  finiteLevelGlobalArtin A.localArtin A.finite_product

noncomputable def classArtin {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (A : FiniteLevelArtinData K L) :
    BookIdeleClassGroup K →* GroupAbelianization (Gal(L / K)) :=
  QuotientGroup.lift (principalIdeleSubgroup K) A.globalArtin (by
    intro x hx
    rcases hx with ⟨a, rfl⟩
    exact A.principal_trivial a)

@[simp]
theorem classArtin_apply_classQuotient
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (A : FiniteLevelArtinData K L) (x : BookIdeleGroup K) :
    classArtin A (classQuotient x) = A.globalArtin x := by
  rfl

abbrev finiteClassArtinQuotient {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) :=
  BookIdeleClassGroup K ⧸ classNormGroup N

structure ContinuousBookArtinMap (K : Type*) [Field K] [NumberField K] where
  map : BookIdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K
  continuous_map : Continuous map

/-! ### Small reusable exactness and abelianization interfaces -/

structure AdditiveShortExact (A B C : Type*) [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] where
  left : A →+ B
  right : B →+ C
  exact : Function.Exact left right
  left_injective : Function.Injective left
  right_surjective : Function.Surjective right

abbrev RationalModuloIntegers :=
  ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

end
end LastLib.Book06GlobalClassFieldTheory.Chapter01
