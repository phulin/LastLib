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
import LastLib.Book04AdelesAndIdeles.Chapter08.Section86
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
  intro hmn hnm
  cases m with
  | mk mf mi hm =>
    cases n with
    | mk nf ni hn =>
      simp only [RayModulus.mk.injEq]
      constructor
      · apply Finsupp.ext
        intro v
        exact Nat.le_antisymm (hmn.1 v) (hnm.1 v)
      · ext v
        exact ⟨fun hv => hmn.2 v hv, fun hv => hnm.2 v hv⟩

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
        change ((u : A) * (v : A) - 1) ∈ (IsLocalRing.maximalIdeal A) ^ n
        change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n at hu
        change (v : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n at hv
        rw [show (u : A) * (v : A) - 1 =
          ((u : A) - 1) * (v : A) + ((v : A) - 1) by ring]
        exact ((IsLocalRing.maximalIdeal A) ^ n).add_mem
          (((IsLocalRing.maximalIdeal A) ^ n).mul_mem_right (v : A) hu) hv
      inv_mem' := by
        intro u hu
        change ((↑(u⁻¹) : A) - 1) ∈ (IsLocalRing.maximalIdeal A) ^ n
        change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n at hu
        simpa [sub_mul] using
          ((IsLocalRing.maximalIdeal A) ^ n).neg_mem
            (((IsLocalRing.maximalIdeal A) ^ n).mul_mem_right (↑(u⁻¹) : A) hu) }

theorem chapter11LocalUnitFiltration_zero {A : Type*} [CommRing A] [IsLocalRing A] :
    chapter11LocalUnitFiltration (A := A) 0 = ⊤ := by
  simp [chapter11LocalUnitFiltration]

theorem chapter11LocalUnitFiltration_mem_iff {A : Type*} [CommRing A] [IsLocalRing A]
    (u : Aˣ) (n : ℕ) :
    u ∈ chapter11LocalUnitFiltration (A := A) n ↔
      n = 0 ∨ (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n := by
  classical
  by_cases hn : n = 0
  · simp [hn, chapter11LocalUnitFiltration]
  · simp [hn, chapter11LocalUnitFiltration]

theorem chapter11LocalUnitFiltration_antitone {A : Type*} [CommRing A] [IsLocalRing A]
    {m n : ℕ} (hmn : m ≤ n) :
    chapter11LocalUnitFiltration (A := A) n ≤
      chapter11LocalUnitFiltration (A := A) m := by
  intro u hu
  rw [chapter11LocalUnitFiltration_mem_iff] at hu ⊢
  by_cases hn : n = 0
  · have hm0 : m ≤ 0 := by simpa [hn] using hmn
    exact Or.inl (Nat.eq_zero_of_le_zero hm0)
  · by_cases hm : m = 0
    · exact Or.inl hm
    · exact Or.inr ((Ideal.pow_le_pow_right hmn) (hu.resolve_left hn))

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
  rw [chapter11FiniteLocalUnitGroup, chapter11LocalUnitFiltration_zero]
  ext x
  constructor
  · rintro ⟨u, -, rfl⟩
    rw [ValuationSubring.mem_unitGroup_iff]
    change (v.adicCompletionIntegers K).valuation
      ((Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom u :
        (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1
    simp
  · intro hx
    let x' : (v.adicCompletionIntegers K).unitGroup := ⟨x, hx⟩
    refine ⟨(v.adicCompletionIntegers K).unitGroupMulEquiv x', trivial, ?_⟩
    apply Units.ext
    change (((v.adicCompletionIntegers K).unitGroupMulEquiv x' :
      (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) = (x : v.adicCompletion K)
    exact (v.adicCompletionIntegers K).coe_unitGroupMulEquiv_apply x'

theorem chapter11FiniteLocalUnitGroup_one (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter11FiniteLocalUnitGroup K v 1 =
      (v.adicCompletionIntegers K).principalUnitGroup := by
  rw [chapter11FiniteLocalUnitGroup]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [ValuationSubring.mem_principalUnitGroup_iff]
    change (u : v.adicCompletionIntegers K) - 1 ∈
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ 1 at hu
    rw [pow_one] at hu
    exact (ValuationSubring.valuation_lt_one_iff (v.adicCompletionIntegers K)
      ((u : v.adicCompletionIntegers K) - 1)).1 hu
  · intro hx
    let x' : (v.adicCompletionIntegers K).unitGroup :=
      ⟨x, (v.adicCompletionIntegers K).principal_units_le_units hx⟩
    refine ⟨(v.adicCompletionIntegers K).unitGroupMulEquiv x', ?_, ?_⟩
    · change ((↑((v.adicCompletionIntegers K).unitGroupMulEquiv x') :
      v.adicCompletionIntegers K) - 1) ∈
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ 1
      rw [pow_one]
      exact (ValuationSubring.valuation_lt_one_iff (v.adicCompletionIntegers K) _).2
        (by
          have hx' : (v.adicCompletionIntegers K).valuation
              ((x : v.adicCompletion K) - 1) < 1 :=
            (ValuationSubring.mem_principalUnitGroup_iff
              (v.adicCompletionIntegers K) x).1 hx
          simpa [(v.adicCompletionIntegers K).coe_unitGroupMulEquiv_apply x'] using hx')
    · apply Units.ext
      change (((v.adicCompletionIntegers K).unitGroupMulEquiv x' :
        (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) =
        (x : v.adicCompletion K)
      exact (v.adicCompletionIntegers K).coe_unitGroupMulEquiv_apply x'

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
    constructor
    · intro v
      simpa only [map_one] using
        (chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)).one_mem
    · intro v hv
      simp
  mul_mem' := by
    intro x y hx hy
    constructor
    · intro v
      simpa only [map_mul] using
        (chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)).mul_mem
          (hx.1 v) (hy.1 v)
    · intro v hv
      rw [map_mul, hx.2 v hv, hy.2 v hv, one_mul]
  inv_mem' := by
    intro x hx
    constructor
    · intro v
      simpa only [map_inv] using
        (chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)).inv_mem (hx.1 v)
    · intro v hv
      rw [map_inv, hx.2 v hv, inv_one]

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
  exact QuotientGroup.map (chapter11PrincipalIdeleSubgroup (K := K))
    (chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup m)
    (MonoidHom.id _) (by
      intro x hx
      exact (show chapter11PrincipalIdeleSubgroup (K := K) ≤
          chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup m from
        le_sup_left) hx)

def chapter11IdealPrimeToModulus (m : RayModulus K) :
    Subgroup (Chapter11FractionalIdealUnitGroup K) where
  carrier := {I |
    ∀ v, m.finiteExponent v ≠ 0 →
      FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0}
  one_mem' := by
    intro v hv
    exact FractionalIdeal.count_one K v
  mul_mem' := by
    intro I J hI hJ v hv
    change FractionalIdeal.count K v
      ((I : FractionalIdeal (𝓞 K)⁰ K) * (J : FractionalIdeal (𝓞 K)⁰ K)) = 0
    rw [FractionalIdeal.count_mul K v (Units.ne_zero _) (Units.ne_zero _),
      hI v hv, hJ v hv, add_zero]
  inv_mem' := by
    intro I hI v hv
    rw [Units.val_inv_eq_inv_val]
    rw [FractionalIdeal.count_inv K v, hI v hv, neg_zero]

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
    refine ⟨1, ?_, ?_⟩
    · simp [chapter11RayGenerator]
    · simp
  mul_mem' := by
    intro I J hI hJ
    rcases hI with ⟨a, ha, hIa⟩
    rcases hJ with ⟨b, hb, hJb⟩
    refine ⟨a * b, ?_, ?_⟩
    · constructor
      · intro v hv
        simpa only [map_mul] using
          (chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)).mul_mem
            (ha.1 v hv) (hb.1 v hv)
      · intro v hv
        simp only [map_mul]
        rw [ha.2 v hv, hb.2 v hv, one_mul]
    · change ((I : Chapter11FractionalIdealUnitGroup K) *
        (J : Chapter11FractionalIdealUnitGroup K) :
          FractionalIdeal (𝓞 K)⁰ K) =
        (toPrincipalIdeal (𝓞 K) K (a * b) : FractionalIdeal (𝓞 K)⁰ K)
      rw [hIa, hJb]
      simpa only [Units.val_mul] using
        congrArg (fun z : Chapter11FractionalIdealUnitGroup K =>
          (z : FractionalIdeal (𝓞 K)⁰ K))
          ((toPrincipalIdeal (𝓞 K) K).map_mul a b).symm
  inv_mem' := by
    intro I hI
    rcases hI with ⟨a, ha, hIa⟩
    refine ⟨a⁻¹, ?_, ?_⟩
    · constructor
      · intro v hv
        simpa only [map_inv] using
          (chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)).inv_mem (ha.1 v hv)
      · intro v hv
        simp only [map_inv]
        rw [ha.2 v hv, inv_one]
    · rw [Subgroup.coe_inv, Units.val_inv_eq_inv_val, hIa]
      simpa only [Units.val_inv_eq_inv_val] using
        congrArg (fun z : Chapter11FractionalIdealUnitGroup K =>
          (z : FractionalIdeal (𝓞 K)⁰ K))
          ((toPrincipalIdeal (𝓞 K) K).map_inv a).symm

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
    have hfinite :
        LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteIdelePartHom K
          (chapter11PrincipalIdeleHom (K := K) a) =
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a := by
      apply Units.ext
      rfl
    change LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K
      (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteIdelePartHom K
        (chapter11PrincipalIdeleHom (K := K) a)) =
        toPrincipalIdeal (𝓞 K) K a
    rw [hfinite]
    exact LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_principal a
  kernel_eq_full_finite_units := by
    ext x
    constructor
    · intro hx
      change LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K
        (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteIdelePartHom K x) = 1 at hx
      have hunit :
          LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteIdelePartHom K x ∈
            LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIntegralUnits := by
        rw [← LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_kernel]
        exact (MonoidHom.mem_ker).2 hx
      change
        (∀ v, chapter11IdeleFiniteComponent K v x ∈
          chapter11FiniteLocalUnitGroup K v 0) ∧
          (∀ v (hv : v ∈ (RayModulus.trivial (K := K)).infinitePart),
            chapter11RealSignComponent K v
              ((RayModulus.trivial (K := K)).infinitePart_isReal v hv) x = 1)
      constructor
      · intro v
        rw [chapter11FiniteLocalUnitGroup_zero]
        have hval :=
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_integral_unit_iff_local_valued_eq_one
            (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteIdelePartHom K x)).1 hunit v
        have hval' :
            Valued.v ((chapter11IdeleFiniteComponent K v x :
              (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
          simpa only [show LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent
              (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteIdelePartHom K x) v =
                (chapter11IdeleFiniteComponent K v x : v.adicCompletion K) by rfl] using hval
        have hmem :
            chapter11IdeleFiniteComponent K v x ∈ Valued.v.valuationSubring.unitGroup :=
          (Valuation.mem_unitGroup_iff (v.adicCompletion K) (Valued.v) _).2 hval'
        simpa only [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers] using hmem
      · simp [RayModulus.trivial]
    · intro hx
      change (∀ v, chapter11IdeleFiniteComponent K v x ∈
        chapter11FiniteLocalUnitGroup K v 0) ∧ _ at hx
      change LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K
        (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteIdelePartHom K x) = 1
      rw [← MonoidHom.mem_ker]
      rw [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_kernel]
      apply (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_integral_unit_iff_local_valued_eq_one
        (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteIdelePartHom K x)).2
      intro v
      have hxv : chapter11IdeleFiniteComponent K v x ∈
          chapter11FiniteLocalUnitGroup K v 0 := hx.1 v
      rw [chapter11FiniteLocalUnitGroup_zero K v] at hxv
      have hxv' :
          chapter11IdeleFiniteComponent K v x ∈ Valued.v.valuationSubring.unitGroup := by
        simpa only [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers] using hxv
      have hval' := (Valuation.mem_unitGroup_iff (v.adicCompletion K) (Valued.v) _).1 hxv'
      have hlocal :
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent
              (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteIdelePartHom K x) v =
            (chapter11IdeleFiniteComponent K v x : v.adicCompletion K) := by
        rfl
      simpa only [hlocal] using hval'
  count_eq_zero_of_local_unit := by
    intro x v n hx
    change FractionalIdeal.count K v
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K
        (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteIdelePartHom K x) :
          FractionalIdeal (𝓞 K)⁰ K) = 0
    rw [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_count]
    apply (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_local_order_eq_zero_iff_valued_eq_one
      v _ (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_component_ne_zero
        (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteIdelePartHom K x) v)).2
    have hlocal :
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent
            (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteIdelePartHom K x) v =
          (chapter11IdeleFiniteComponent K v x : v.adicCompletion K) := by
      rfl
    rw [hlocal]
    change (chapter11FiniteLocalUnitGroup K v n).carrier
      (chapter11IdeleFiniteComponent K v x) at hx
    rcases hx with ⟨u, hu, hux⟩
    rw [← hux]
    change Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = 1
    exact (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).1
      u.isUnit
  surjective := by
    intro I
    obtain ⟨y, hy⟩ :=
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_surjective K I
    refine ⟨
      (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).symm (1, y), ?_⟩
    change LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K
      (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteIdelePartHom K
        ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).symm (1, y))) = I
    rw [show LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteIdelePartHom K
        ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).symm (1, y)) = y by
      rfl, hy]

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
  let q : 𝓞 K →+* (𝓞 K ⧸ m.finiteIdeal) := Ideal.Quotient.mk m.finiteIdeal
  let r : (𝓞 K)ˣ →* chapter11RayResidueGroup m :=
    Units.map q.toMonoidHom
  let s : (𝓞 K)ˣ →* chapter11RaySignGroup m :=
    { toFun := fun u v =>
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignOfUnit
          (Units.map (algebraMap (𝓞 K) K).toMonoidHom u)
          ⟨v, m.infinitePart_isReal v v.property⟩
      map_one' := by
        funext v
        apply Units.ext
        simp [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignOfUnit]
      map_mul' := by
        intro x y
        funext v
        apply Units.ext
        simp [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08SignOfUnit,
          sign_mul] }
  refine
    { toFun := fun u => (r u, s u)
      map_one' := ?_
      map_mul' := ?_ }
  · apply Prod.ext
    · exact r.map_one
    · exact s.map_one
  · intro x y
    apply Prod.ext
    · exact r.map_mul x y
    · exact s.map_mul x y

def chapter11ResidueSignToRayClassHom (m : RayModulus K) :
    chapter11RayResidueSignGroup m →* chapter11RayClassGroup m := by
  sorry

def chapter11RayClassToOrdinaryClassHom (m : RayModulus K) :
    chapter11RayClassGroup m →* Chapter11OrdinaryClassGroup K := by
  let f : Chapter11IdeleGroup K →* Chapter11OrdinaryClassGroup K :=
    (ClassGroup.mk K).comp (chapter11CanonicalIdeleIdealMap K).toIdeal
  refine QuotientGroup.lift
    (chapter11PrincipalIdeleSubgroup (K := K) ⊔ chapter11RayUnitSubgroup m) f ?_
  apply sup_le
  · rintro x ⟨a, rfl⟩
    rw [MonoidHom.mem_ker]
    change ClassGroup.mk K
      ((chapter11CanonicalIdeleIdealMap K).toIdeal
        (chapter11PrincipalIdeleHom (K := K) a)) = 1
    rw [(chapter11CanonicalIdeleIdealMap K).map_principal]
    apply (ClassGroup.mk_eq_one_iff).2
    refine ⟨(a : K), ?_⟩
    simp [coe_toPrincipalIdeal]
  · intro x hx
    rw [MonoidHom.mem_ker]
    change ClassGroup.mk K
      ((chapter11CanonicalIdeleIdealMap K).toIdeal x) = 1
    have hxker : x ∈ (chapter11CanonicalIdeleIdealMap K).toIdeal.ker := by
      rw [(chapter11CanonicalIdeleIdealMap K).kernel_eq_full_finite_units]
      change
        (∀ v, chapter11IdeleFiniteComponent K v x ∈
          chapter11FiniteLocalUnitGroup K v 0) ∧
          (∀ v (hv : v ∈ (RayModulus.trivial (K := K)).infinitePart),
            chapter11RealSignComponent K v
              ((RayModulus.trivial (K := K)).infinitePart_isReal v hv) x = 1)
      constructor
      · intro v
        apply (show chapter11FiniteLocalUnitGroup K v (m.finiteExponent v) ≤
            chapter11FiniteLocalUnitGroup K v 0 from ?_) (hx.1 v)
        intro z hz
        rcases hz with ⟨u, hu, hzu⟩
        exact ⟨u, chapter11LocalUnitFiltration_antitone (Nat.zero_le _) hu, hzu⟩
      · simp [RayModulus.trivial]
    rw [MonoidHom.mem_ker.mp hxker]
    simp

end
