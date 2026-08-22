import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Prod
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import LastLib.Book04AdelesAndIdeles.Chapter04.Section06AdelicTrace
import LastLib.Book04AdelesAndIdeles.Chapter09.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter11.Dependencies

/-!
# Chapter 13: shared interfaces

This file contains the small amount of shared notation used by the six source-order sections.
The canonical adelic and idele carriers are reused from Chapter 9.  The remaining interfaces here
are limited to chapter-13 character and additive-trace data that are not supplied by those earlier
chapters.
-/

open scoped BigOperators NumberField NumberField.AdeleRing RestrictedProduct

namespace LastLib.Book04AdelesAndIdeles.Chapter13

noncomputable section

abbrev Chapter13Adele (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter11.Chapter11AdeleRing K

abbrev Chapter13FiniteAdele (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter11.Chapter11FiniteAdeleRing K

abbrev Chapter13InfiniteAdele (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K

abbrev Chapter13FiniteIdele (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter11.Chapter11FiniteIdeleGroup K

abbrev Chapter13InfiniteIdele (K : Type*) [Field K] [NumberField K] :=
  (LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ

abbrev Chapter13Idele (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter11.Chapter11IdeleGroup K

abbrev Chapter13PositiveReal : Type :=
  LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09PositiveReal

abbrev Chapter13LocalUnitSubgroup (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Subgroup (v.adicCompletion K)ˣ :=
  (v.adicCompletionIntegers K).unitGroup

/- The following local bridge uses the standard algebra maps, while the principal ideles themselves
are the canonical Chapter 9 construction. -/

def chapter13PrincipalFiniteIdeleValue (K : Type*) [Field K] [NumberField K] (a : Kˣ) :
    ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ :=
  fun v => Units.map (algebraMap K (v.adicCompletion K)) a

abbrev chapter13PrincipalFiniteIdele (K : Type*) [Field K] [NumberField K] :
    Kˣ →* Chapter13FiniteIdele K :=
  LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FinitePrincipalIdele K

abbrev chapter13PrincipalIdele (K : Type*) [Field K] [NumberField K] :
    Kˣ →* Chapter13Idele K :=
  LastLib.Book04AdelesAndIdeles.Chapter11.chapter11PrincipalIdeleHom (K := K)

def chapter13FiniteIdeleCoordinate
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter13FiniteIdele K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ :=
  (RestrictedProduct.unitsEquiv
    (fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => w.adicCompletion K) x) v

theorem chapter13PrincipalIdele_infinite_coordinate
    (K : Type*) [Field K] [NumberField K] (a : Kˣ)
    (v : NumberField.InfinitePlace K) :
    (MulEquiv.piUnits
      ((MulEquiv.prodUnits (chapter13PrincipalIdele K a)).1)) v =
      Units.map (algebraMap K v.Completion) a := by
  rfl

theorem chapter13PrincipalIdele_finite_coordinate
    (K : Type*) [Field K] [NumberField K]
    (a : Kˣ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter13FiniteIdeleCoordinate K
        ((MulEquiv.prodUnits (chapter13PrincipalIdele K a)).2) v =
      chapter13PrincipalFiniteIdeleValue K a v := by
  rfl

theorem chapter13FiniteIdeleCoordinate_principal
    (K : Type*) [Field K] [NumberField K] (a : Kˣ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter13FiniteIdeleCoordinate K (chapter13PrincipalFiniteIdele K a) v =
      chapter13PrincipalFiniteIdeleValue K a v := by
  rfl

theorem chapter13FiniteIdeleCoordinate_continuous
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Continuous (fun x : Chapter13FiniteIdele K =>
      chapter13FiniteIdeleCoordinate K x v) := by
  change Continuous (fun x : Chapter13FiniteIdele K =>
    (LastLib.Book04AdelesAndIdeles.Chapter07.chapter07FiniteIdeleEquiv (𝓞 K) K x) v)
  let tRP : TopologicalSpace
      (LastLib.Book04AdelesAndIdeles.Chapter07.chapter07FiniteIdeleRestrictedProduct
        (𝓞 K) K) :=
    @RestrictedProduct.topologicalSpace
      (IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => (w.adicCompletion K)ˣ)
      (fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
        ((Submonoid.ofClass (w.adicCompletionIntegers K)).units :
          Set ((w.adicCompletion K)ˣ)))
      Filter.cofinite
      (fun w => inferInstance)
  have hEval :
      @Continuous
        (LastLib.Book04AdelesAndIdeles.Chapter07.chapter07FiniteIdeleRestrictedProduct
          (𝓞 K) K)
        ((v.adicCompletion K)ˣ)
        tRP
        (inferInstance : TopologicalSpace ((v.adicCompletion K)ˣ))
        (fun y => y v) := by
    simpa [tRP] using
      (@RestrictedProduct.continuous_eval
        (ι := IsDedekindDomain.HeightOneSpectrum (𝓞 K))
        (R := fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
          (w.adicCompletion K)ˣ)
        (A := fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
          ((Submonoid.ofClass (w.adicCompletionIntegers K)).units :
            Set ((w.adicCompletion K)ˣ)))
        (𝓕 := Filter.cofinite)
        (fun w => inferInstance) v)
  change @Continuous (Chapter13FiniteIdele K)
    ((v.adicCompletion K)ˣ)
    (TopologicalSpace.induced
      (LastLib.Book04AdelesAndIdeles.Chapter07.chapter07FiniteIdeleEquiv (𝓞 K) K)
      tRP)
    (inferInstance : TopologicalSpace ((v.adicCompletion K)ˣ))
    (fun x : Chapter13FiniteIdele K =>
      (LastLib.Book04AdelesAndIdeles.Chapter07.chapter07FiniteIdeleEquiv (𝓞 K) K x) v)
  exact hEval.comp
    (@continuous_induced_dom
      (Chapter13FiniteIdele K)
      (LastLib.Book04AdelesAndIdeles.Chapter07.chapter07FiniteIdeleRestrictedProduct
        (𝓞 K) K)
      (LastLib.Book04AdelesAndIdeles.Chapter07.chapter07FiniteIdeleEquiv (𝓞 K) K)
      tRP)

/- The following local embeddings are the canonical single-place maps after transporting local
units through the unit equivalences of the infinite and finite adele factors. -/

def chapter13InfiniteLocalIdele
    (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (x : (v.Completion)ˣ) : Chapter13Idele K := by
  classical
  exact (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).symm
    ((MulEquiv.piUnits (M := fun w : NumberField.InfinitePlace K => w.Completion)).symm
      (Pi.mulSingle v x), 1)

open scoped Classical in
private theorem chapter13InfiniteLocalIdele_product
    (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (x : (v.Completion)ˣ) :
    (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K)
        (chapter13InfiniteLocalIdele K v x) =
      ((MulEquiv.piUnits
          (M := fun w : NumberField.InfinitePlace K => w.Completion)).symm
        (Pi.mulSingle v x),
        (1 : (Chapter13FiniteAdele K)ˣ)) := by
  classical
  unfold chapter13InfiniteLocalIdele
  exact (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).apply_symm_apply _

def chapter13FiniteLocalIdele
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : Chapter13Idele K := by
  classical
  let localUnit : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K)ˣ :=
    fun w => dite (w = v) (fun h => h ▸ x) (fun _ => 1)
  have hunit : ∀ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      localUnit w ∈ (Submonoid.ofClass (w.adicCompletionIntegers K)).units := by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw
    have hw' : w ≠ v := by simpa using hw
    simp [localUnit, hw']
  let finite : Chapter13FiniteIdele K := RestrictedProduct.mkUnit localUnit hunit
  exact (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).symm (1, finite)

theorem chapter13InfiniteLocalIdele_coordinate
    (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (x : (v.Completion)ˣ) :
    (MulEquiv.piUnits
      ((MulEquiv.prodUnits (chapter13InfiniteLocalIdele K v x)).1)) v = x := by
  classical
  have hdecomp := chapter13InfiniteLocalIdele_product K v x
  change (MulEquiv.piUnits
      ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K
        (chapter13InfiniteLocalIdele K v x)).1)) v = x
  rw [hdecomp]
  change (MulEquiv.piUnits
      ((MulEquiv.piUnits
        (M := fun z : NumberField.InfinitePlace K => z.Completion)).symm
        (Pi.mulSingle v x))) v = x
  rw [(MulEquiv.piUnits (M := fun z : NumberField.InfinitePlace K => z.Completion)).apply_symm_apply]
  exact Pi.mulSingle_eq_same (M := fun z : NumberField.InfinitePlace K => (z.Completion)ˣ) v x

theorem chapter13InfiniteLocalIdele_coordinate_off
    (K : Type*) [Field K] [NumberField K]
    (v w : NumberField.InfinitePlace K) (x : (v.Completion)ˣ) (hvw : w ≠ v) :
    (MulEquiv.piUnits
      ((MulEquiv.prodUnits (chapter13InfiniteLocalIdele K v x)).1)) w = 1 := by
  classical
  have hdecomp := chapter13InfiniteLocalIdele_product K v x
  change (MulEquiv.piUnits
      ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K
        (chapter13InfiniteLocalIdele K v x)).1)) w = 1
  rw [hdecomp]
  change (MulEquiv.piUnits
      ((MulEquiv.piUnits
        (M := fun z : NumberField.InfinitePlace K => z.Completion)).symm
        (Pi.mulSingle v x))) w = 1
  rw [(MulEquiv.piUnits (M := fun z : NumberField.InfinitePlace K => z.Completion)).apply_symm_apply]
  exact Pi.mulSingle_eq_of_ne
    (M := fun z : NumberField.InfinitePlace K => (z.Completion)ˣ) hvw x

theorem chapter13InfiniteLocalIdele_finite_coordinate
    (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (x : (v.Completion)ˣ)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter13FiniteIdeleCoordinate K
        ((MulEquiv.prodUnits (chapter13InfiniteLocalIdele K v x)).2) w = 1 := by
  classical
  have hdecomp := chapter13InfiniteLocalIdele_product K v x
  change chapter13FiniteIdeleCoordinate K
      ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K
        (chapter13InfiniteLocalIdele K v x)).2) w = 1
  rw [hdecomp]
  change chapter13FiniteIdeleCoordinate K (1 : (Chapter13FiniteAdele K)ˣ) w = 1
  unfold chapter13FiniteIdeleCoordinate
  rfl

theorem chapter13InfiniteLocalIdele_one
    (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) :
    chapter13InfiniteLocalIdele K v 1 = 1 := by
  classical
  apply (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).injective
  have hdecomp := chapter13InfiniteLocalIdele_product K v (1 : (v.Completion)ˣ)
  rw [hdecomp]
  change ((MulEquiv.piUnits
      (M := fun z : NumberField.InfinitePlace K => z.Completion)).symm
      (Pi.mulSingle v 1), 1) = 1
  rw [Pi.mulSingle_one]
  rw [(MulEquiv.piUnits
      (M := fun z : NumberField.InfinitePlace K => z.Completion)).symm.map_one]
  exact Prod.ext rfl (by simp)

theorem chapter13InfiniteLocalIdele_mul
    (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (x y : (v.Completion)ˣ) :
    chapter13InfiniteLocalIdele K v (x * y) =
      chapter13InfiniteLocalIdele K v x * chapter13InfiniteLocalIdele K v y := by
  classical
  apply (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).injective
  have hxy := chapter13InfiniteLocalIdele_product K v (x * y)
  have hx := chapter13InfiniteLocalIdele_product K v x
  have hy := chapter13InfiniteLocalIdele_product K v y
  rw [hxy, (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).map_mul, hx, hy]
  change ((MulEquiv.piUnits
      (M := fun z : NumberField.InfinitePlace K => z.Completion)).symm
      (Pi.mulSingle v (x * y)), 1) =
    ((MulEquiv.piUnits
      (M := fun z : NumberField.InfinitePlace K => z.Completion)).symm
      (Pi.mulSingle v x), 1) *
      ((MulEquiv.piUnits
        (M := fun z : NumberField.InfinitePlace K => z.Completion)).symm
        (Pi.mulSingle v y), 1)
  rw [Pi.mulSingle_mul]
  rw [(MulEquiv.piUnits
      (M := fun z : NumberField.InfinitePlace K => z.Completion)).symm.map_mul]
  apply Prod.ext
  · rfl
  · change (1 : (Chapter13FiniteAdele K)ˣ) = 1 * 1
    simp

theorem chapter13InfiniteLocalIdele_continuous
    (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) :
    Continuous (chapter13InfiniteLocalIdele K v) := by
  classical
  let e := LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K
  let tprod : TopologicalSpace
      ((LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ ×
        Chapter13FiniteIdele K) :=
    @instTopologicalSpaceProd
      ((LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ)
      (Chapter13FiniteIdele K) inferInstance
      (LastLib.Book04AdelesAndIdeles.Chapter11.chapter11FiniteIdeleGraphTopology K)
  change @Continuous
    ((v.Completion)ˣ) (Chapter13Idele K)
    (inferInstance : TopologicalSpace ((v.Completion)ˣ))
    (TopologicalSpace.induced e tprod)
    (fun x => e.symm
      (((MulEquiv.piUnits).symm (Pi.mulSingle v x)), 1))
  rw [continuous_induced_rng]
  have hprod : @Continuous
      ((v.Completion)ˣ)
      ((LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ ×
        Chapter13FiniteIdele K)
      (inferInstance : TopologicalSpace ((v.Completion)ˣ)) tprod
      (fun x => ((MulEquiv.piUnits).symm (Pi.mulSingle v x), 1)) := by
    exact (((ContinuousMulEquiv.piUnits
        (M := fun w : NumberField.InfinitePlace K => w.Completion)).symm.continuous.comp
      (continuous_mulSingle v)).prodMk continuous_const)
  have heq : (fun x => e (e.symm
      (((MulEquiv.piUnits).symm (Pi.mulSingle v x)), 1))) =
      (fun x => ((MulEquiv.piUnits).symm (Pi.mulSingle v x), 1)) := by
    funext x
    exact e.apply_symm_apply _
  change Continuous (fun x => e (e.symm
      (((MulEquiv.piUnits).symm (Pi.mulSingle v x)), 1)))
  rw [heq]
  exact hprod

def chapter13InfiniteLocalIdeleHom
    (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) :
    (v.Completion)ˣ →ₜ* Chapter13Idele K :=
  { toMonoidHom :=
      { toFun := chapter13InfiniteLocalIdele K v
        map_one' := chapter13InfiniteLocalIdele_one K v
        map_mul' := chapter13InfiniteLocalIdele_mul K v }
    continuous_toFun := chapter13InfiniteLocalIdele_continuous K v }

theorem chapter13FiniteLocalIdele_coordinate
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    chapter13FiniteIdeleCoordinate K
        ((MulEquiv.prodUnits (chapter13FiniteLocalIdele K v x)).2) v = x := by
  classical
  unfold chapter13FiniteIdeleCoordinate
  change (RestrictedProduct.unitsEquiv
      (fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K
        (chapter13FiniteLocalIdele K v x)).2)) v = x
  unfold chapter13FiniteLocalIdele
  simp
  apply Units.ext
  rw [RestrictedProduct.unitsEquiv_apply]
  simp [RestrictedProduct.mkUnit]

theorem chapter13FiniteLocalIdele_coordinate_off
    (K : Type*) [Field K] [NumberField K]
    (v w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ)
    (hvw : w ≠ v) :
    chapter13FiniteIdeleCoordinate K
        ((MulEquiv.prodUnits (chapter13FiniteLocalIdele K v x)).2) w = 1 := by
  classical
  unfold chapter13FiniteIdeleCoordinate
  change (RestrictedProduct.unitsEquiv
      (fun z : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => z.adicCompletion K)
      ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K
        (chapter13FiniteLocalIdele K v x)).2)) w = 1
  unfold chapter13FiniteLocalIdele
  simp
  apply Units.ext
  rw [RestrictedProduct.unitsEquiv_apply]
  simp [RestrictedProduct.mkUnit, hvw]

theorem chapter13FiniteLocalIdele_infinite_coordinate
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ)
    (w : NumberField.InfinitePlace K) :
    (MulEquiv.piUnits
      ((MulEquiv.prodUnits (chapter13FiniteLocalIdele K v x)).1)) w = 1 := by
  classical
  change (MulEquiv.piUnits
      ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K
        (chapter13FiniteLocalIdele K v x)).1)) w = 1
  unfold chapter13FiniteLocalIdele
  simp
  change (1 : ∀ z : NumberField.InfinitePlace K, (z.Completion)ˣ) w = 1
  rfl

theorem chapter13FiniteLocalIdele_one
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter13FiniteLocalIdele K v 1 = 1 := by
  classical
  apply (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).injective
  let localUnit : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K)ˣ :=
    fun w => dite (w = v) (fun h => h ▸ (1 : (v.adicCompletion K)ˣ)) (fun _ => 1)
  have hlocal : localUnit = (fun _ => 1) := by
    funext w
    by_cases hw : w = v
    · subst w
      simp [localUnit]
    · simp [localUnit, hw]
  change (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K)
      ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).symm
        (1, RestrictedProduct.mkUnit localUnit _)) =
    (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K) 1
  simp [hlocal, RestrictedProduct.mkUnit]
  apply Prod.ext
  · rfl
  · apply Units.ext
    ext i
    rfl

theorem chapter13FiniteLocalIdele_mul
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x y : (v.adicCompletion K)ˣ) :
    chapter13FiniteLocalIdele K v (x * y) =
      chapter13FiniteLocalIdele K v x * chapter13FiniteLocalIdele K v y := by
  classical
  apply (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).injective
  let localUnitXY : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K)ˣ :=
    fun w => dite (w = v) (fun h => h ▸ (x * y)) (fun _ => 1)
  let localUnitX : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K)ˣ :=
    fun w => dite (w = v) (fun h => h ▸ x) (fun _ => 1)
  let localUnitY : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K)ˣ :=
    fun w => dite (w = v) (fun h => h ▸ y) (fun _ => 1)
  have hunitXY : ∀ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      localUnitXY w ∈ (Submonoid.ofClass (w.adicCompletionIntegers K)).units := by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw
    have hw' : w ≠ v := by simpa using hw
    simp [localUnitXY, hw']
  have hunitX : ∀ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      localUnitX w ∈ (Submonoid.ofClass (w.adicCompletionIntegers K)).units := by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw
    have hw' : w ≠ v := by simpa using hw
    simp [localUnitX, hw']
  have hunitY : ∀ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      localUnitY w ∈ (Submonoid.ofClass (w.adicCompletionIntegers K)).units := by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw
    have hw' : w ≠ v := by simpa using hw
    simp [localUnitY, hw']
  let finiteXY : Chapter13FiniteIdele K := RestrictedProduct.mkUnit localUnitXY hunitXY
  let finiteX : Chapter13FiniteIdele K := RestrictedProduct.mkUnit localUnitX hunitX
  let finiteY : Chapter13FiniteIdele K := RestrictedProduct.mkUnit localUnitY hunitY
  change (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K)
      ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).symm
        (1, finiteXY)) =
    (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K)
      ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).symm
        (1, finiteX)) *
      (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K)
        ((LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K).symm
          (1, finiteY))
  simp
  let e : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ ≃*
      (Πʳ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        [(w.adicCompletion K)ˣ,
          (Submonoid.ofClass (w.adicCompletionIntegers K)).units]_[Filter.cofinite] ) :=
    RestrictedProduct.unitsEquiv
      (fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
  apply e.injective
  rw [e.map_mul]
  apply RestrictedProduct.ext
  intro i
  apply Units.ext
  change (chapter13FiniteIdeleCoordinate K finiteXY i).val =
    (chapter13FiniteIdeleCoordinate K finiteX i *
      chapter13FiniteIdeleCoordinate K finiteY i).val
  simp [chapter13FiniteIdeleCoordinate, finiteXY, finiteX, finiteY,
    RestrictedProduct.unitsEquiv, RestrictedProduct.mkUnit,
    localUnitXY, localUnitX, localUnitY]
  change (localUnitXY i : i.adicCompletion K) =
    (localUnitX i : i.adicCompletion K) * (localUnitY i : i.adicCompletion K)
  by_cases hi : i = v
  · subst i
    simp [localUnitXY, localUnitX, localUnitY]
  · simp [localUnitXY, localUnitX, localUnitY, hi]

theorem chapter13FiniteLocalIdele_continuous
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Continuous (chapter13FiniteLocalIdele K v) := by
  classical
  let e := LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K
  let tprod : TopologicalSpace
      ((LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ ×
        Chapter13FiniteIdele K) :=
    @instTopologicalSpaceProd
      ((LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ)
      (Chapter13FiniteIdele K) inferInstance
      (LastLib.Book04AdelesAndIdeles.Chapter11.chapter11FiniteIdeleGraphTopology K)
  let tRP : TopologicalSpace
      (LastLib.Book04AdelesAndIdeles.Chapter07.chapter07FiniteIdeleRestrictedProduct
        (𝓞 K) K) :=
    @RestrictedProduct.topologicalSpace
      (IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => (w.adicCompletion K)ˣ)
      (fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
        ((Submonoid.ofClass (w.adicCompletionIntegers K)).units :
          Set ((w.adicCompletion K)ˣ)))
      Filter.cofinite
      (fun w => inferInstance)
  let finiteMap : (v.adicCompletion K)ˣ → Chapter13FiniteIdele K := fun x =>
    (MulEquiv.prodUnits (chapter13FiniteLocalIdele K v x)).2
  let S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := {v}ᶜ
  have hS : Filter.cofinite ≤ Filter.principal S := by
    apply Filter.le_principal_iff.mpr
    apply Filter.mem_cofinite.mpr
    simp [S]
  let g : (v.adicCompletion K)ˣ →
      (Πʳ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        [(w.adicCompletion K)ˣ,
          (Submonoid.ofClass (w.adicCompletionIntegers K)).units]_[Filter.principal S]) :=
    fun x => ⟨Pi.mulSingle v x, by
      apply Filter.mem_principal.mpr
      intro w hw
      have hw' : w ≠ v := by simpa [S] using hw
      simp [Pi.mulSingle_eq_of_ne hw']⟩
  have hg : Continuous g := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro w
    change Continuous (fun x : (v.adicCompletion K)ˣ =>
      Pi.mulSingle (M := fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
        (w.adicCompletion K)ˣ) v x w)
    by_cases hw : w = v
    · subst w
      have hfun : (fun x : (v.adicCompletion K)ˣ =>
          Pi.mulSingle (M := fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
            (w.adicCompletion K)ˣ) v x v) =
          (id : (v.adicCompletion K)ˣ → (v.adicCompletion K)ˣ) := by
        funext x
        exact Pi.mulSingle_eq_same
          (M := fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
            (w.adicCompletion K)ˣ) v x
      rw [hfun]
      exact continuous_id
    · simpa [g, Pi.mulSingle_eq_of_ne hw] using
        (continuous_const : Continuous
          (fun _ : (v.adicCompletion K)ˣ => (1 : (w.adicCompletion K)ˣ)))
  have hfactor :
      (fun x =>
        LastLib.Book04AdelesAndIdeles.Chapter07.chapter07FiniteIdeleEquiv
          (𝓞 K) K (finiteMap x)) =
        RestrictedProduct.inclusion
          (fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
            (w.adicCompletion K)ˣ)
          (fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
            ((Submonoid.ofClass (w.adicCompletionIntegers K)).units :
              Set ((w.adicCompletion K)ˣ))) hS ∘ g := by
    funext x
    apply RestrictedProduct.ext
    intro w
    apply Units.ext
    by_cases hw : w = v
    · subst w
      change (chapter13FiniteIdeleCoordinate K (finiteMap x) v).val =
        (g x v).val
      have hcoord : chapter13FiniteIdeleCoordinate K (finiteMap x) v = x := by
        simpa [finiteMap] using (chapter13FiniteLocalIdele_coordinate K v x)
      rw [hcoord]
      change (x : v.adicCompletion K) =
        Pi.mulSingle (M := fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
          (w.adicCompletion K)ˣ) v x v
      simp
    · change (chapter13FiniteIdeleCoordinate K (finiteMap x) w).val =
        (g x w).val
      have hcoord : chapter13FiniteIdeleCoordinate K (finiteMap x) w = 1 := by
        simpa [finiteMap] using
          (chapter13FiniteLocalIdele_coordinate_off K v w x hw)
      rw [hcoord]
      change (1 : w.adicCompletion K) =
        Pi.mulSingle (M := fun z : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
          (z.adicCompletion K)ˣ) v x w
      simp [hw]
  have hfinite : @Continuous
      ((v.adicCompletion K)ˣ) (Chapter13FiniteIdele K)
      (inferInstance : TopologicalSpace ((v.adicCompletion K)ˣ))
      (LastLib.Book04AdelesAndIdeles.Chapter11.chapter11FiniteIdeleGraphTopology K)
      finiteMap := by
    change @Continuous
      ((v.adicCompletion K)ˣ) (Chapter13FiniteIdele K)
      (inferInstance : TopologicalSpace ((v.adicCompletion K)ˣ))
      (TopologicalSpace.induced
        (LastLib.Book04AdelesAndIdeles.Chapter07.chapter07FiniteIdeleEquiv
          (𝓞 K) K) tRP)
      finiteMap
    rw [continuous_induced_rng]
    change Continuous (fun x =>
      LastLib.Book04AdelesAndIdeles.Chapter07.chapter07FiniteIdeleEquiv
        (𝓞 K) K (finiteMap x))
    rw [hfactor]
    exact (RestrictedProduct.continuous_inclusion hS).comp hg
  change @Continuous
    ((v.adicCompletion K)ˣ) (Chapter13Idele K)
    (inferInstance : TopologicalSpace ((v.adicCompletion K)ˣ))
    (TopologicalSpace.induced e tprod)
    (fun x => e.symm (1, finiteMap x))
  rw [continuous_induced_rng]
  have hprod : @Continuous
      ((v.adicCompletion K)ˣ)
      ((LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ ×
        Chapter13FiniteIdele K)
      (inferInstance : TopologicalSpace ((v.adicCompletion K)ˣ)) tprod
      (fun x => (1, finiteMap x)) := by
    exact continuous_const.prodMk hfinite
  have heq : (fun x => e (e.symm (1, finiteMap x))) =
      (fun x => (1, finiteMap x)) := by
    funext x
    exact e.apply_symm_apply _
  change Continuous (fun x => e (e.symm (1, finiteMap x)))
  rw [heq]
  exact hprod

def chapter13FiniteLocalIdeleHom
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →ₜ* Chapter13Idele K :=
  { toMonoidHom :=
      { toFun := chapter13FiniteLocalIdele K v
        map_one' := chapter13FiniteLocalIdele_one K v
        map_mul' := chapter13FiniteLocalIdele_mul K v }
    continuous_toFun := chapter13FiniteLocalIdele_continuous K v }

abbrev chapter13PrincipalIdeleSubgroup (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter13Idele K) :=
  LastLib.Book04AdelesAndIdeles.Chapter11.chapter11PrincipalIdeleSubgroup (K := K)

abbrev Chapter13IdeleClass (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter11.Chapter11IdeleClassGroup K

instance chapter13IdeleClassCommGroup
    (K : Type*) [Field K] [NumberField K] :
    CommGroup (Chapter13IdeleClass K) := by
  change CommGroup
    (LastLib.Book04AdelesAndIdeles.Chapter11.Chapter11IdeleClassGroup K)
  infer_instance

abbrev Chapter13ClassCharacter (K : Type*) [Field K] [NumberField K] :=
  Chapter13IdeleClass K →ₜ* ℂˣ

/-! A restricted product of local multiplicative characters is called unramified when its local
character is trivial on the distinguished local unit group. -/

abbrev Chapter13ContinuousComplexCharacter (G : Type*) [Monoid G] [TopologicalSpace G] :=
  G →ₜ* ℂˣ

def chapter13TrivialOnSubgroup {G : Type*} [Group G] (H : Subgroup G)
    (χ : G →* ℂˣ) : Prop :=
  ∀ x : H, χ x = 1

def chapter13AdditiveAnnihilator {A : Type*} [NonUnitalNonAssocRing A]
    (ψ : AddChar A Circle) (H : AddSubgroup A) : AddSubgroup A := by
  refine
    { carrier := {y | ∀ x : H, ψ ((x : A) * y) = 1}
      zero_mem' := by
        intro x
        simp
      add_mem' := by
        intro a b ha hb x
        rw [mul_add, ψ.map_add_eq_mul, ha x, hb x]
        exact mul_one 1
      neg_mem' := by
        intro x hx y
        rw [mul_neg, ψ.map_neg_eq_inv, hx y]
        exact inv_one }

theorem chapter13_mem_additiveAnnihilator_iff
    {A : Type*} [NonUnitalNonAssocRing A]
    (ψ : AddChar A Circle) (H : AddSubgroup A) (y : A) :
    y ∈ chapter13AdditiveAnnihilator ψ H ↔
      ∀ x : H, ψ ((x : A) * y) = 1 :=
  Iff.rfl

abbrev Chapter13AdditiveDual (A : Type*) [AddCommGroup A] [TopologicalSpace A] :=
  Additive (PontryaginDual (Multiplicative A))

abbrev Chapter13QModZ := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

abbrev Chapter13Padic (p : {p : ℕ // Nat.Prime p}) :=
  @Padic p.1 ⟨p.2⟩

abbrev Chapter13PadicInteger (p : {p : ℕ // Nat.Prime p}) :=
  @PadicInt p.1 ⟨p.2⟩

def chapter13RationalModIntegerCharacter : AddChar Chapter13QModZ Circle :=
  (AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ))
      (Real.fourierChar.compAddMonoidHom (Rat.castHom ℝ).toAddMonoidHom).toAddMonoidHom
      (by
        rw [AddSubgroup.zmultiples_le]
        simp [Real.fourierChar_apply', mul_one, Circle.exp_two_pi])))⁻¹

/- The ray levels are the canonical Chapter 11 moduli and quotients.  Keeping these aliases here
lets the character statements use chapter-13 names without replacing the established ray-class
API by a generic system of unrelated open subgroups. -/

abbrev Chapter13RayModulus (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter11.RayModulus K

abbrev Chapter13RayClassGroup {K : Type*} [Field K] [NumberField K]
    (m : Chapter13RayModulus K) :=
  LastLib.Book04AdelesAndIdeles.Chapter11.chapter11RayClassGroup m

abbrev Chapter13RayClassCharacter {K : Type*} [Field K] [NumberField K]
    (m : Chapter13RayModulus K) :=
  Chapter13RayClassGroup m →* ℂˣ

/-!
The following two structures are intentionally hypotheses rather than disguised conclusions.  They
record the missing earlier interfaces used by the additive half of the chapter: a global standard
character and its local trace pairing. -/

/- DEPENDENCY_GUESS: the standard p-adic principal-part maps, the adelic trace, and the associated
continuity/finite-support proofs are expected from the earlier local and trace chapters. -/

structure Chapter13RationalPrincipalPartData (p : {p : ℕ // Nat.Prime p}) where
  principalPart : Chapter13Padic p →+ Chapter13QModZ
  principalPart_eq_zero_on_integers :
    ∀ x : Chapter13PadicInteger p, principalPart x = 0
  principalPart_nontrivial : ∃ x, principalPart x ≠ 0
  principalCharacter : AddChar (Chapter13Padic p) Circle
  principalCharacter_continuous : Continuous principalCharacter
  principalCharacter_trivial_on_integers :
    ∀ x : Chapter13PadicInteger p, principalCharacter x = 1
  principalCharacter_nontrivial_on_inverse_p :
    principalCharacter ((p.1 : Chapter13Padic p)⁻¹) ≠ 1
  principalCharacter_formula :
    ∀ x, principalCharacter x = chapter13RationalModIntegerCharacter (principalPart x)

structure Chapter13RationalStandardCharacterData where
  psiInfinity : AddChar ℝ Circle
  psiInfinity_eq_fourier : psiInfinity = Real.fourierChar
  finiteCoordinate : ∀ p : {p : ℕ // Nat.Prime p}, Chapter13Adele ℚ → Chapter13Padic p
  finiteCoordinate_integral :
    ∀ x : Chapter13Adele ℚ,
      ∀ᶠ p in Filter.cofinite,
        ∃ z : Chapter13PadicInteger p, (z : Chapter13Padic p) = finiteCoordinate p x
  finiteCoordinate_continuous :
    ∀ p, Continuous (finiteCoordinate p)
  finiteCoordinate_additive :
    ∀ p x y, finiteCoordinate p (x + y) =
      finiteCoordinate p x + finiteCoordinate p y
  infinityCoordinate : Chapter13Adele ℚ → ℝ
  infinityCoordinate_continuous : Continuous infinityCoordinate
  infinityCoordinate_additive :
    ∀ x y, infinityCoordinate (x + y) = infinityCoordinate x + infinityCoordinate y
  infinityCoordinate_principal :
    ∀ a : ℚ,
      infinityCoordinate (algebraMap ℚ (Chapter13Adele ℚ) a) = (a : ℝ)
  finiteCoordinate_principal :
    ∀ (p : {p : ℕ // Nat.Prime p}) (a : ℚ),
      finiteCoordinate p (algebraMap ℚ (Chapter13Adele ℚ) a) =
        (a : Chapter13Padic p)
  padic : ∀ p : {p : ℕ // Nat.Prime p}, Chapter13RationalPrincipalPartData p
  principalPart_balance :
    ∀ a : ℚ,
      QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) a =
        ∑ᶠ p,
          (padic p).principalPart
            (finiteCoordinate p (algebraMap ℚ (Chapter13Adele ℚ) a))

structure Chapter13AdelicTraceData (K : Type*) [Field K] [NumberField K] where
  localTraceData :
    LastLib.Book04AdelesAndIdeles.Chapter04.Chapter04AdelicTraceData ℚ K
  trace : Chapter13Adele K →+ Chapter13Adele ℚ
  trace_continuous : Continuous trace
  trace_eq_localTraceData :
    trace =
      LastLib.Book04AdelesAndIdeles.Chapter04.chapter04AdelicTrace localTraceData
  trace_principal :
    ∀ a : K, trace (algebraMap K (Chapter13Adele K) a) =
      algebraMap ℚ (Chapter13Adele ℚ) (Algebra.trace ℚ K a)
  rationalCharacter : Chapter13RationalStandardCharacterData

structure Chapter13LocalSelfDualityData (F : Type*) [Field F] [TopologicalSpace F]
    [AddCommGroup F] where
  pairing : F → F → Circle
  pairing_add_left : ∀ x y z, pairing (x + y) z = pairing x z * pairing y z
  pairing_add_right : ∀ x y z, pairing x (y + z) = pairing x y * pairing x z
  pairing_continuous : Continuous (Function.uncurry pairing)
  pairing_left_nondegenerate : ∀ x, (∀ y, pairing x y = 1) → x = 0
  pairing_right_nondegenerate : ∀ y, (∀ x, pairing x y = 1) → y = 0
  /- The pairing map is the local character parametrization.  Nondegeneracy only gives
  injectivity; surjectivity and openness are the genuinely additional local-duality inputs. -/
  pairingMap : F →ₜ+ Chapter13AdditiveDual F
  pairingMap_apply : ∀ y x, pairingMap y x = pairing x y
  pairingMap_surjective : Function.Surjective pairingMap
  pairingMap_isOpenMap : IsOpenMap pairingMap

end
end LastLib.Book04AdelesAndIdeles.Chapter13
