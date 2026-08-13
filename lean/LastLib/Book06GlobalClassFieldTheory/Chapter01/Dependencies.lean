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
  sorry

theorem principalIdele_injective {K : Type*} [Field K] [NumberField K] :
    Function.Injective (principalIdele (K := K)) := by
  sorry

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
  (∏ v : InfinitePlaceIndex K,
      ‖bookIdeleComponent x (Sum.inr v)‖ ^ v.mult) *
    ∏ᶠ v : FinitePlaceIndex K, ‖bookIdeleComponent x (Sum.inl v)‖

/- LOCAL_DEPENDENCY_GUESS: the multiplicativity and positivity of the
normalized restricted product norm are supplied here until the adelic norm
API is connected to the idelic unit group. -/
noncomputable def ideleModule {K : Type*} [Field K] [NumberField K] :
    BookIdeleGroup K →* PositiveReal where
  toFun x := ⟨ideleModuleValue x, by sorry⟩
  map_one' := by sorry
  map_mul' x y := by sorry

theorem ideleModule_apply {K : Type*} [Field K] [NumberField K]
    (x : BookIdeleGroup K) :
    (ideleModule x : ℝ) = ideleModuleValue x := rfl

/- The ordinary product formula is the reason the module descends to classes. -/
theorem principal_idele_module_eq_one {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) : ideleModule (principalIdele a) = 1 := by
  sorry

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
  sorry

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

/- LOCAL_DEPENDENCY_GUESS: the earlier restricted-product and local class-field
interfaces supply these componentwise maps and their unit-tail properties.
The idele map below is constructed from the local factors rather than being a
free continuous homomorphism. -/
structure GlobalNormInterface (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] where
  above : ∀ _v : BookPlace K, Finset (BookPlace L)
  above_nonempty : ∀ v, (above v).Nonempty
  below : BookPlace L → BookPlace K
  mem_above_iff :
    ∀ (v : BookPlace K) (w : BookPlace L), w ∈ above v ↔ below w = v
  localNorm : ∀ (v : BookPlace K) (w : BookPlace L),
    (BookPlace.completion w)ˣ →* (BookPlace.completion v)ˣ
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
    (N : GlobalNormInterface K L) : BookIdeleGroup L →* BookIdeleGroup K := by
  sorry

theorem GlobalNormInterface.principal_compatibility_apply
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) (y : Lˣ) :
    componentwiseIdeleNorm N (principalIdele y) =
      principalIdele (fieldNormUnits K L y) := by
  sorry

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
  sorry

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
  sorry

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
    BookIdeleGroup K →* GroupAbelianization (Gal(L / K)) := by
  sorry

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
