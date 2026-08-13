import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Mathlib.Topology.Instances.Sign
import LastLib.Book04AdelesAndIdeles.Chapter09.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter11

open scoped BigOperators nonZeroDivisors RestrictedProduct
open NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-! The common vocabulary for Chapter 11.  The definitions in this file are
deliberately book-facing: later chapters can replace the provisional idele-
ideal bridge without changing the ray-modulus and local-unit interfaces. -/

abbrev Chapter11RingOfIntegers (K : Type*) [Field K] [NumberField K] := 𝓞 K

abbrev Chapter11AdeleRing (K : Type*) [Field K] [NumberField K] :=
  NumberField.AdeleRing (𝓞 K) K

abbrev Chapter11FiniteAdeleRing (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.FiniteAdeleRing (𝓞 K) K

abbrev Chapter11IdeleGroup (K : Type*) [Field K] [NumberField K] :=
  (Chapter11AdeleRing K)ˣ

abbrev Chapter11FiniteIdeleGroup (K : Type*) [Field K] [NumberField K] :=
  (Chapter11FiniteAdeleRing K)ˣ

/-! The unit group of a restricted product needs its graph topology: the
finite tail must control both a unit and its inverse.  The ambient unit
subspace topology on the finite adele ring is too coarse for this purpose.
Chapter 8 already packages the required finite graph topology, so reuse it
here rather than introducing a second local model. -/
@[instance_reducible]
noncomputable def chapter11FiniteIdeleGraphTopology
    (K : Type*) [Field K] [NumberField K] :
    TopologicalSpace (Chapter11FiniteIdeleGroup K) :=
  LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleGraphTopology K

noncomputable instance chapter11FiniteIdeleTopologicalSpace
    (K : Type*) [Field K] [NumberField K] :
  TopologicalSpace (Chapter11FiniteIdeleGroup K) :=
  chapter11FiniteIdeleGraphTopology K

noncomputable instance chapter11AdicCompletionUnitOpenFact
    (K : Type*) [Field K] [NumberField K] :
    Fact (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      IsOpen ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
        Set ((v.adicCompletion K)ˣ))) := ⟨by
  intro v
  exact Submonoid.isOpen_units
    (Valued.isOpen_valuationSubring (v.adicCompletion K))⟩

noncomputable instance chapter11FiniteIdeleTopologicalGroup
    (K : Type*) [Field K] [NumberField K] :
    @IsTopologicalGroup (Chapter11FiniteIdeleGroup K)
      (chapter11FiniteIdeleGraphTopology K) Units.instGroup := by
  exact topologicalGroup_induced
    (RestrictedProduct.unitsEquiv
      (𝓕 := Filter.cofinite)
      (B := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
        v.adicCompletionIntegers K)
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
        v.adicCompletion K))

/-! Transport the product of the archimedean unit topology and the finite
graph topology across the canonical decomposition of a full idele. -/
@[instance_reducible]
noncomputable def chapter11IdeleGraphTopology
    (K : Type*) [Field K] [NumberField K] :
    TopologicalSpace (Chapter11IdeleGroup K) := by
  letI : TopologicalSpace (Chapter11FiniteIdeleGroup K) :=
    chapter11FiniteIdeleGraphTopology K
  exact TopologicalSpace.induced
    (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K)
    inferInstance

noncomputable instance chapter11IdeleTopologicalSpace
    (K : Type*) [Field K] [NumberField K] :
    TopologicalSpace (Chapter11IdeleGroup K) :=
  chapter11IdeleGraphTopology K

noncomputable instance chapter11IdeleTopologicalGroup
    (K : Type*) [Field K] [NumberField K] :
    @IsTopologicalGroup (Chapter11IdeleGroup K)
      (chapter11IdeleGraphTopology K) Units.instGroup := by
  exact topologicalGroup_induced
    (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K)

abbrev Chapter11OrdinaryClassGroup (K : Type*) [Field K] [NumberField K] :=
  ClassGroup (𝓞 K)

abbrev Chapter11FractionalIdealUnitGroup (K : Type*) [Field K] [NumberField K] :=
  (FractionalIdeal (𝓞 K)⁰ K)ˣ

/-- A modulus has a finite ideal part and a set of selected real places.

The field recording reality is intentional: complex places are not silently
accepted as sign conditions. -/
structure RayModulus (K : Type*) [Field K] [NumberField K] where
  finiteExponent : IsDedekindDomain.HeightOneSpectrum (𝓞 K) →₀ ℕ
  infinitePart : Finset (NumberField.InfinitePlace K)
  infinitePart_isReal : ∀ v ∈ infinitePart, NumberField.InfinitePlace.IsReal v

namespace RayModulus

instance : Inhabited (RayModulus K) where
  default :=
    { finiteExponent := 0
      infinitePart := ∅
      infinitePart_isReal := by simp }

def finiteIdeal (m : RayModulus K) : Ideal (𝓞 K) := by
  classical
  exact Finset.prod m.finiteExponent.support (fun v => v.asIdeal ^ m.finiteExponent v)

def trivial : RayModulus K :=
  { finiteExponent := 0
    infinitePart := ∅
    infinitePart_isReal := by simp }

def narrow : RayModulus K := by
  classical
  refine
    { finiteExponent := 0
      infinitePart := Finset.univ.filter NumberField.InfinitePlace.IsReal
      infinitePart_isReal := ?_ }
  intro v hv
  exact (Finset.mem_filter.mp hv).2

def LE (m n : RayModulus K) : Prop :=
  (∀ v, m.finiteExponent v ≤ n.finiteExponent v) ∧
    (∀ v, v ∈ m.infinitePart → v ∈ n.infinitePart)

theorem le_refl (m : RayModulus K) : LE m m := by
  constructor <;> intro <;> simp

theorem le_trans {m n r : RayModulus K} : LE m n → LE n r → LE m r := by
  intro hmn hnr
  constructor
  · intro v
    exact Nat.le_trans (hmn.1 v) (hnr.1 v)
  · intro v hv
    exact hnr.2 v (hmn.2 v hv)

theorem le_antisymm {m n : RayModulus K} : LE m n → LE n m → m = n := by
  sorry

instance : _root_.LE (RayModulus K) := ⟨RayModulus.LE⟩

instance : PartialOrder (RayModulus K) where
  le := RayModulus.LE
  le_refl := fun m => RayModulus.le_refl m
  le_trans := by
    intro m n r hmn hnr
    exact RayModulus.le_trans hmn hnr
  le_antisymm := by
    intro m n hmn hnm
    exact RayModulus.le_antisymm hmn hnm

theorem finiteExponent_support_finite (m : RayModulus K) :
    (m.finiteExponent.support : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))).Finite := by
  exact Finset.finite_toSet _

theorem infinitePart_is_real (m : RayModulus K) {v} :
    v ∈ m.infinitePart → NumberField.InfinitePlace.IsReal v :=
  m.infinitePart_isReal v

end RayModulus

/-- The local unit filtration used at a finite place.  Level zero is the full
unit group; positive levels are principal units modulo powers of the maximal
ideal. -/
def chapter11LocalUnitFiltration {A : Type*} [CommRing A] [IsLocalRing A]
    (n : ℕ) : Subgroup Aˣ :=
  if h : n = 0 then ⊤ else
    { carrier := {u | (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n}
      one_mem' := by simp
      mul_mem' := by
        intro u v hu hv
        sorry
      inv_mem' := by
        intro u hu
        sorry }

theorem chapter11LocalUnitFiltration_zero {A : Type*} [CommRing A] [IsLocalRing A] :
    chapter11LocalUnitFiltration (A := A) 0 = ⊤ := by
  simp [chapter11LocalUnitFiltration]

theorem chapter11LocalUnitFiltration_mem_iff {A : Type*} [CommRing A] [IsLocalRing A]
    (u : Aˣ) (n : ℕ) :
    u ∈ chapter11LocalUnitFiltration (A := A) n ↔
      n = 0 ∨ (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n := by
  sorry

def chapter11AdditiveLocalDepth {A : Type*} [CommRing A] [IsLocalRing A]
    (n : ℕ) : Submodule A A :=
  (IsLocalRing.maximalIdeal A) ^ n

abbrev chapter11AdditiveLocalLayer {A : Type*} [CommRing A] [IsLocalRing A]
    (n : ℕ) :=
  (chapter11AdditiveLocalDepth (A := A) n) ⧸
    (Submodule.comap (chapter11AdditiveLocalDepth (A := A) n).subtype
      (chapter11AdditiveLocalDepth (A := A) (n + 1)))

abbrev chapter11MultiplicativeLocalLayer {A : Type*} [CommRing A] [IsLocalRing A]
    (n : ℕ) :=
  (chapter11LocalUnitFiltration (A := A) n) ⧸
    (Subgroup.comap (chapter11LocalUnitFiltration (A := A) n).subtype
      (chapter11LocalUnitFiltration (A := A) (n + 1)))

def chapter11FiniteLocalUnitGroup (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Subgroup (v.adicCompletion K)ˣ :=
  (chapter11LocalUnitFiltration (A := v.adicCompletionIntegers K) n).map
    (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom)

theorem chapter11FiniteLocalUnitGroup_zero (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter11FiniteLocalUnitGroup K v 0 =
      (v.adicCompletionIntegers K).unitGroup := by
  sorry

theorem chapter11FiniteLocalUnitGroup_one (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter11FiniteLocalUnitGroup K v 1 =
      (v.adicCompletionIntegers K).principalUnitGroup := by
  sorry

def chapter11FiniteAdeleComponent (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Chapter11FiniteAdeleRing K →+* v.adicCompletion K where
  toFun x := x v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def chapter11FiniteIdeleComponent (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Chapter11FiniteIdeleGroup K →* (v.adicCompletion K)ˣ :=
  Units.map (chapter11FiniteAdeleComponent K v).toMonoidHom

def chapter11IdeleFiniteComponent (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Chapter11IdeleGroup K →* (v.adicCompletion K)ˣ :=
  Units.map
    (({ toFun := fun x : Chapter11AdeleRing K => x.2 v
        map_one' := rfl
        map_mul' _ _ := rfl
        map_zero' := rfl
        map_add' _ _ := rfl } :
        Chapter11AdeleRing K →+* v.adicCompletion K).toMonoidHom)

def chapter11InfiniteAdeleComponent (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) :
    Chapter11AdeleRing K →+* v.Completion where
  toFun x := x.1 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def chapter11InfiniteIdeleComponent (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) :
    Chapter11IdeleGroup K →* v.Completionˣ :=
  Units.map (chapter11InfiniteAdeleComponent K v).toMonoidHom

def chapter11RealSignHom : ℝˣ →* SignTypeˣ :=
  Units.map (signHom : ℝ →*₀ SignType).toMonoidHom

def chapter11RealSignComponent (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K)
    (hv : NumberField.InfinitePlace.IsReal v) :
    Chapter11IdeleGroup K →* SignTypeˣ :=
  chapter11RealSignHom.comp
    (Units.map
      ((NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).comp
        (chapter11InfiniteAdeleComponent K v)).toMonoidHom)

def chapter11FiniteGlobalComponent (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Kˣ →* (v.adicCompletion K)ˣ :=
  Units.map (FinitePlace.embedding v).toMonoidHom

def chapter11RealGlobalComponent (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K)
    (hv : NumberField.InfinitePlace.IsReal v) : Kˣ →* ℝˣ :=
  Units.map (NumberField.InfinitePlace.embedding_of_isReal hv).toMonoidHom

/-- The idelic unit subgroup attached to a modulus. -/
def chapter11RayUnitSubgroup (m : RayModulus K) : Subgroup (Chapter11IdeleGroup K) where
  carrier := {x |
    (∀ v, chapter11IdeleFiniteComponent K v x ∈
      chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)) ∧
      ∀ v (hv : v ∈ m.infinitePart),
        chapter11RealSignComponent K v (m.infinitePart_isReal v hv) x = 1}
  one_mem' := by
    sorry
  mul_mem' := by
    intro x y hx hy
    sorry
  inv_mem' := by
    intro x hx
    sorry

def chapter11FullFiniteUnitSubgroup : Subgroup (Chapter11IdeleGroup K) :=
  chapter11RayUnitSubgroup (RayModulus.trivial (K := K))

def chapter11PrincipalIdeleHom : Kˣ →* Chapter11IdeleGroup K :=
  Units.map (algebraMap K (Chapter11AdeleRing K)).toMonoidHom

def chapter11PrincipalIdeleSubgroup : Subgroup (Chapter11IdeleGroup K) :=
  (chapter11PrincipalIdeleHom (K := K)).range

abbrev Chapter11IdeleClassGroup (K : Type*) [Field K] [NumberField K] :=
  Chapter11IdeleGroup K ⧸ chapter11PrincipalIdeleSubgroup (K := K)

abbrev chapter11RayClassGroup (m : RayModulus K) :=
  Chapter11IdeleGroup K ⧸
    (chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup m)

def chapter11IdeleClassProjection : Chapter11IdeleGroup K →* Chapter11IdeleClassGroup K :=
  QuotientGroup.mk' (chapter11PrincipalIdeleSubgroup (K := K))

def chapter11RayClassProjection (m : RayModulus K) :
    Chapter11IdeleGroup K →* chapter11RayClassGroup m :=
  QuotientGroup.mk'
    (chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup m)

def chapter11IdeleClassToRayClass (m : RayModulus K) :
    Chapter11IdeleClassGroup K →* chapter11RayClassGroup m := by
  sorry

def chapter11IdealPrimeToModulus (m : RayModulus K) :
    Subgroup (Chapter11FractionalIdealUnitGroup K) where
  carrier := {I |
    ∀ v, m.finiteExponent v ≠ 0 →
      FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0}
  one_mem' := by
    sorry
  mul_mem' := by
    intro I J hI hJ
    sorry
  inv_mem' := by
    intro I hI
    sorry

abbrev Chapter11IdealGroup (m : RayModulus K) :=
  chapter11IdealPrimeToModulus m

def chapter11RayGenerator (m : RayModulus K) (a : Kˣ) : Prop :=
  (∀ v, m.finiteExponent v ≠ 0 →
      chapter11FiniteGlobalComponent K v a ∈
        chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)) ∧
    ∀ v (hv : v ∈ m.infinitePart),
      chapter11RealSignHom
          (chapter11RealGlobalComponent K v (m.infinitePart_isReal v hv) a) = 1

def chapter11RayPrincipalIdealSubgroup (m : RayModulus K) :
  Subgroup (Chapter11IdealGroup m) where
  carrier := {I |
    ∃ a : Kˣ, chapter11RayGenerator m a ∧
      ((I : Chapter11FractionalIdealUnitGroup K) : FractionalIdeal (𝓞 K)⁰ K) =
        (toPrincipalIdeal (𝓞 K) K a : FractionalIdeal (𝓞 K)⁰ K)}
  one_mem' := by
    sorry
  mul_mem' := by
    intro I J hI hJ
    sorry
  inv_mem' := by
    intro I hI
    sorry

abbrev chapter11IdealRayClassGroup (m : RayModulus K) :=
  Chapter11IdealGroup m ⧸ chapter11RayPrincipalIdealSubgroup m

/-!
`LOCAL_DEPENDENCY_GUESS`: `Chapter11IdeleIdealMap` is a narrow local dependency
interface for the canonical idele-to-fractional-ideal map developed in the
preceding book chapters.  In addition to its kernel and principal-image
equations, the local-unit/count bridge is recorded explicitly because the ray
normalization argument needs it at the modulus primes.
-/
structure Chapter11IdeleIdealMap (K : Type*) [Field K] [NumberField K] where
  toIdeal : Chapter11IdeleGroup K →* Chapter11FractionalIdealUnitGroup K
  map_principal : ∀ a : Kˣ,
    toIdeal (chapter11PrincipalIdeleHom (K := K) a) =
      toPrincipalIdeal (𝓞 K) K a
  kernel_eq_full_finite_units :
    toIdeal.ker = chapter11FullFiniteUnitSubgroup (K := K)
  count_eq_zero_of_local_unit :
    ∀ (x : Chapter11IdeleGroup K)
      (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ),
      chapter11IdeleFiniteComponent K v x ∈
        chapter11FiniteLocalUnitGroup K v n →
      FractionalIdeal.count K v
        (toIdeal x : FractionalIdeal (𝓞 K)⁰ K) = 0
  surjective : Function.Surjective toIdeal

/-! The preceding chapters already provide the canonical finite-idele ideal map.
The specialization below keeps the ray-class API source-facing while making its
ideal-theoretic bridge an actual number-field construction rather than an
uninstantiated parameter. -/
noncomputable def chapter11CanonicalIdeleIdealMap
    (K : Type*) [Field K] [NumberField K] : Chapter11IdeleIdealMap K where
  toIdeal :=
    (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K).comp
      (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteIdelePartHom K)
  map_principal := by
    intro a
    sorry
  kernel_eq_full_finite_units := by
    sorry
  count_eq_zero_of_local_unit := by
    intro x v n hx
    sorry
  surjective := by
    sorry

/- A ray normalizer only imposes the congruence conditions at the finite
places in the modulus and the selected real signs.  It must not require the
whole normalized idele to be a finite unit: doing so would force an arbitrary
idele's finite ideal to be principal, which is not true in general. -/
def Chapter11RayNormalizer (m : RayModulus K)
    (x : Chapter11IdeleGroup K) (a : Kˣ) : Prop :=
  (∀ v, m.finiteExponent v ≠ 0 →
      chapter11IdeleFiniteComponent K v
        (chapter11PrincipalIdeleHom (K := K) a * x) ∈
        chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)) ∧
    ∀ v (hv : v ∈ m.infinitePart),
      chapter11RealSignComponent K v (m.infinitePart_isReal v hv)
        (chapter11PrincipalIdeleHom (K := K) a * x) = 1

abbrev chapter11RayResidueGroup (m : RayModulus K) :=
  (𝓞 K ⧸ m.finiteIdeal)ˣ

abbrev chapter11RaySignGroup (m : RayModulus K) :=
  m.infinitePart → SignTypeˣ

abbrev chapter11RayResidueSignGroup (m : RayModulus K) :=
  chapter11RayResidueGroup m × chapter11RaySignGroup m

def chapter11GlobalUnitResidueSignHom (m : RayModulus K) :
    (𝓞 K)ˣ →* chapter11RayResidueSignGroup m := by
  sorry

def chapter11ResidueSignToRayClassHom (m : RayModulus K) :
    chapter11RayResidueSignGroup m →* chapter11RayClassGroup m := by
  sorry

def chapter11RayClassToOrdinaryClassHom (m : RayModulus K) :
    chapter11RayClassGroup m →* Chapter11OrdinaryClassGroup K := by
  sorry

end
