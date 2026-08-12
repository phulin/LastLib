import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.DirectSum.Module
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
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Group.Quotient

namespace LastLib.Book06GlobalClassFieldTheory.Chapter01

open scoped BigOperators NumberField

noncomputable section

universe uK

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

def IsFiniteAbelianExtension (K L : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] : Prop :=
  FiniteDimensional K L ∧ IsAbelianGalois K L

/- LOCAL_DEPENDENCY_GUESS: this is the missing componentwise norm interface
from the adelic/local class-field chapters.  Its compatibility field is the
minimal condition needed to descend from ideles to idelic classes. -/
structure GlobalNormInterface (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] where
  ideleNorm : BookIdeleGroup L →* BookIdeleGroup K
  principal_compatibility :
    ∀ y : Lˣ, ∃ x : Kˣ,
      ideleNorm (principalIdele y) = principalIdele x

noncomputable def classNorm {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) :
    BookIdeleClassGroup L →* BookIdeleClassGroup K :=
  QuotientGroup.lift (principalIdeleSubgroup L)
    ((classQuotient (K := K)).comp N.ideleNorm) (by
      intro x hx
      rcases hx with ⟨y, rfl⟩
      rcases N.principal_compatibility y with ⟨z, hz⟩
      rw [MonoidHom.mem_ker]
      change classQuotient (N.ideleNorm (principalIdele y)) = 1
      rw [hz]
      exact classQuotient_principal z)

def ideleNormGroup {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) : Subgroup (BookIdeleGroup K) :=
  N.ideleNorm.range

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

/- LOCAL_DEPENDENCY_GUESS: the local symbols have been multiplied into a
single finite-level homomorphism; the principal relation is retained as a
field so the quotient construction is explicit. -/
structure FiniteLevelArtinData (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] where
  localProduct : BookIdeleGroup K →* Gal(L / K)
  principal_trivial :
    ∀ a : Kˣ, localProduct (principalIdele a) = 1

noncomputable def classArtin {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (A : FiniteLevelArtinData K L) :
    BookIdeleClassGroup K →* Gal(L / K) :=
  QuotientGroup.lift (principalIdeleSubgroup K) A.localProduct (by
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

abbrev GroupAbelianization (G : Type*) [Group G] :=
  G ⧸ commutator G

end
end LastLib.Book06GlobalClassFieldTheory.Chapter01
