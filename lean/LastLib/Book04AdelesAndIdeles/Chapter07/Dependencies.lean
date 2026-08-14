import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.DiscreteSubset

namespace LastLib.Book04AdelesAndIdeles.Chapter07

noncomputable section

open Set Filter Topology WithZeroTopology
open scoped BigOperators DirectSum RestrictedProduct WithZero

/-!
Shared interfaces for Book 4, Chapter 7.

The pinned Mathlib already supplies the finite and full adele rings and the
topology on restricted products.  This file keeps the chapter's notation
close to those canonical definitions, and records the few book-facing
bridges which are not bundled into a single Mathlib declaration.
-/

abbrev chapter07AdeleRing
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  NumberField.AdeleRing R K

abbrev chapter07FiniteAdeleRing
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  IsDedekindDomain.FiniteAdeleRing R K

abbrev chapter07IdeleGroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  (chapter07AdeleRing R K)ˣ

/-- The topology inherited by the units from the additive adele ring. -/
@[instance_reducible]
def chapter07NaiveIdeleTopology
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    TopologicalSpace (chapter07IdeleGroup R K) :=
  TopologicalSpace.induced (fun x : chapter07IdeleGroup R K => (x : chapter07AdeleRing R K))
    inferInstance

abbrev chapter07FiniteIdeleGroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  (chapter07FiniteAdeleRing R K)ˣ

abbrev chapter07FinitePlace
    (R : Type*) [CommRing R] [IsDedekindDomain R] :=
  IsDedekindDomain.HeightOneSpectrum R

abbrev chapter07LocalField
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :=
  v.adicCompletion K

abbrev chapter07LocalIntegerRing
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :=
  v.adicCompletionIntegers K

/-- The unit subgroup of the local integer ring, viewed inside the local field's unit group. -/
abbrev chapter07LocalIntegralUnitSubgroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) : Subgroup (chapter07LocalField R K v)ˣ :=
  (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units

@[simp]
theorem chapter07_mem_localIntegralUnitSubgroup_iff
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) (u : (chapter07LocalField R K v)ˣ) :
    u ∈ chapter07LocalIntegralUnitSubgroup R K v ↔
      u ∈ (Submonoid.ofClass (chapter07LocalIntegerRing R K v)).units :=
  Iff.rfl

theorem chapter07_finite_local_residueField_finite
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    (v : chapter07FinitePlace R) :
    Finite (IsLocalRing.ResidueField (chapter07LocalIntegerRing R K v)) := by
  let hfiniteQuotient : Finite (R ⧸ v.asIdeal) :=
    v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  let f : R →+* IsLocalRing.ResidueField (chapter07LocalIntegerRing R K v) :=
    (IsLocalRing.residue (chapter07LocalIntegerRing R K v)).comp
      (algebraMap R (chapter07LocalIntegerRing R K v))
  have hf : ∀ r : R, r ∈ v.asIdeal → f r = 0 := by
    intro r hr
    apply (IsLocalRing.residue_eq_zero_iff
      (R := ↥(chapter07LocalIntegerRing R K v))
      (algebraMap R (chapter07LocalIntegerRing R K v) r)).2
    rw [IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit (algebraMap R (chapter07LocalIntegerRing R K v) r)
    intro hunit
    have hval :=
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
        (K := K) (v := v)).1 hunit
    have hlt : Valued.v
        ((algebraMap R (chapter07LocalIntegerRing R K v) r :
          chapter07LocalIntegerRing R K v) : chapter07LocalField R K v) < 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
      rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
        (K := K) (v := v) (algebraMap R K r)]
      exact (v.valuation_lt_one_iff_mem (K := K) r).2 hr
    exact (ne_of_lt hlt) hval
  let g : R ⧸ v.asIdeal →+* IsLocalRing.ResidueField
      (chapter07LocalIntegerRing R K v) :=
    Ideal.Quotient.lift v.asIdeal f hf
  have hrep : ∀ x : chapter07LocalIntegerRing R K v, ∃ r : R,
      IsLocalRing.residue (chapter07LocalIntegerRing R K v)
          (algebraMap R (chapter07LocalIntegerRing R K v) r) =
        IsLocalRing.residue (chapter07LocalIntegerRing R K v) x := by
    intro x
    have hxval : Valued.v (x : chapter07LocalField R K v) ≤ 1 := x.property
    let U : Set (chapter07LocalField R K v) :=
      {z | Valued.v (z - (x : chapter07LocalField R K v)) < 1}
    have hUopen : IsOpen U := by
      change IsOpen ((fun z : chapter07LocalField R K v =>
        Valued.v (z - (x : chapter07LocalField R K v))) ⁻¹' Set.Iio 1)
      apply (WithZeroTopology.isOpen_Iio : IsOpen (Set.Iio (1 : ℤᵐ⁰))).preimage
      exact (Valued.continuous_valuation_of_surjective
        (v.valuedAdicCompletion_surjective K)).comp
        (continuous_id.sub continuous_const)
    have hxU : (x : chapter07LocalField R K v) ∈ U := by
      simp [U]
    obtain ⟨y, hy⟩ :=
      (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap
        (v := v) (K := K)).exists_mem_open hUopen ⟨x, hxU⟩
    have hyclose : Valued.v
        ((algebraMap K (chapter07LocalField R K v) y) -
          (x : chapter07LocalField R K v)) < 1 := hy
    have hmapK : algebraMap K (chapter07LocalField R K v) y =
        (y : chapter07LocalField R K v) := by
      rfl
    have hyval' : Valued.v (algebraMap K (chapter07LocalField R K v) y) ≤ 1 := by
      have hsum := (Valued.v : Valuation (chapter07LocalField R K v) ℤᵐ⁰).map_add
        ((algebraMap K (chapter07LocalField R K v) y) -
          (x : chapter07LocalField R K v)) (x : chapter07LocalField R K v)
      rw [sub_add_cancel] at hsum
      exact (hsum.trans (max_le (le_of_lt hyclose) hxval))
    have hyval : v.valuation K y ≤ 1 := by
      rw [← IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe
        (K := K) (v := v) y]
      rw [hmapK] at hyval'
      exact hyval'
    obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer (K := K) hyval
      (1 : (ℤᵐ⁰)ˣ)
    have hmapR : algebraMap R (chapter07LocalField R K v) r =
        (algebraMap R K r : chapter07LocalField R K v) := by
      rfl
    have hsub : ((algebraMap R K r - y : K) : chapter07LocalField R K v) =
        (algebraMap R K r : chapter07LocalField R K v) -
          (y : chapter07LocalField R K v) := by
      apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
      change
        ((WithVal.toVal (v.valuation K) (algebraMap R K r - y) :
          WithVal (v.valuation K)) :
          UniformSpace.Completion (WithVal (v.valuation K))) =
          ((WithVal.toVal (v.valuation K) (algebraMap R K r) :
            WithVal (v.valuation K)) :
            UniformSpace.Completion (WithVal (v.valuation K))) -
            ((WithVal.toVal (v.valuation K) y : WithVal (v.valuation K)) :
              UniformSpace.Completion (WithVal (v.valuation K)))
      exact (UniformSpace.Completion.coeRingHom
        (α := WithVal (v.valuation K))).map_sub _ _
    have hrclose : Valued.v
        ((algebraMap R (chapter07LocalField R K v) r) -
          (algebraMap K (chapter07LocalField R K v) y)) < 1 := by
      have hr' : Valued.v
          (((algebraMap R K r - y : K) : chapter07LocalField R K v)) < 1 := by
        rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe
          (K := K) (v := v)]
        simpa using hr
      rw [hmapR, hmapK]
      rw [← hsub]
      exact hr'
    have harclose : Valued.v
        ((algebraMap R (chapter07LocalField R K v) r) -
          (x : chapter07LocalField R K v)) < 1 := by
      have hsum := (Valued.v : Valuation (chapter07LocalField R K v) ℤᵐ⁰).map_add
        ((algebraMap R (chapter07LocalField R K v) r) -
          (algebraMap K (chapter07LocalField R K v) y))
        ((algebraMap K (chapter07LocalField R K v) y) -
          (x : chapter07LocalField R K v))
      rw [sub_add_sub_cancel] at hsum
      exact (hsum.trans_lt (max_lt hrclose hyclose))
    have hmax : (algebraMap R (chapter07LocalIntegerRing R K v) r :
        chapter07LocalIntegerRing R K v) - x ∈
        IsLocalRing.maximalIdeal (chapter07LocalIntegerRing R K v) := by
      rw [IsLocalRing.mem_maximalIdeal]
      change ¬ IsUnit ((algebraMap R (chapter07LocalIntegerRing R K v) r :
        chapter07LocalIntegerRing R K v) - x)
      intro hunit
      have hval :=
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
          (K := K) (v := v)).1 hunit
      have hlt : Valued.v
          (((algebraMap R (chapter07LocalIntegerRing R K v) r :
            chapter07LocalIntegerRing R K v) - x) :
            chapter07LocalField R K v) < 1 := by
        simpa [hmapR] using harclose
      exact (ne_of_lt hlt) hval
    have hzero : IsLocalRing.residue (chapter07LocalIntegerRing R K v)
        ((algebraMap R (chapter07LocalIntegerRing R K v) r :
          chapter07LocalIntegerRing R K v) - x) = 0 :=
      (IsLocalRing.residue_eq_zero_iff
        (R := ↥(chapter07LocalIntegerRing R K v))
        ((algebraMap R (chapter07LocalIntegerRing R K v) r :
          chapter07LocalIntegerRing R K v) - x)).2 hmax
    refine ⟨r, ?_⟩
    exact sub_eq_zero.mp (by simpa using hzero)
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨x, rfl⟩ :=
      IsLocalRing.residue_surjective
        (R := ↥(chapter07LocalIntegerRing R K v)) z
    obtain ⟨r, hr⟩ := hrep x
    refine ⟨Ideal.Quotient.mk v.asIdeal r, ?_⟩
    simpa [g, f, IsLocalRing.residue_def] using hr
  exact Finite.of_surjective g hg

theorem chapter07_finite_local_integer_isCompact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    (v : chapter07FinitePlace R) :
    IsCompact (chapter07LocalIntegerRing R K v : Set (chapter07LocalField R K v)) := by
  let e : chapter07LocalIntegerRing R K v ≃+*
      Valued.integer (chapter07LocalField R K v) :=
    { toFun := fun x =>
        ⟨x, (Valuation.mem_valuationSubring_iff (Valued.v)
          (x : chapter07LocalField R K v)).1 x.property⟩
      invFun := fun x =>
        ⟨x, (Valuation.mem_valuationSubring_iff (Valued.v)
          (x : chapter07LocalField R K v)).2 x.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_mul' := by intro x y; rfl }
  let hcomplete : CompleteSpace (Valued.integer (chapter07LocalField R K v)) := by
    apply completeSpace_of_isComplete_univ
    rw [Subtype.isComplete_iff]
    convert (Valued.isClosed_valuationSubring (chapter07LocalField R K v)).isComplete using 1
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact (Valuation.mem_valuationSubring_iff (Valued.v)
        (y : chapter07LocalField R K v)).2 y.property
    · intro hx
      exact ⟨⟨x, (Valuation.mem_valuationSubring_iff (Valued.v)
          (x : chapter07LocalField R K v)).1 hx⟩, Set.mem_univ _, rfl⟩
  let hdvr : IsDiscreteValuationRing (Valued.integer (chapter07LocalField R K v)) :=
    { principal := (isPrincipalIdealRing_iff _).1 (.of_surjective _ e.surjective)
      __ := e.isLocalRing
      not_a_field' := by
        obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt
          (bot_lt_iff_ne_bot.mpr <| IsDiscreteValuationRing.not_a_field
            (chapter07LocalIntegerRing R K v))
        rw [Submodule.ne_bot_iff]
        refine ⟨e a, ⟨?_, by simp only [ne_eq, EmbeddingLike.map_eq_zero_iff,
          ZeroMemClass.coe_eq_zero, ha, not_false_eq_true]⟩⟩
        rw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff e,
          ← IsLocalRing.mem_maximalIdeal]
        exact a.2 }
  let hfiniteO : Finite (IsLocalRing.ResidueField (chapter07LocalIntegerRing R K v)) :=
    chapter07_finite_local_residueField_finite R K v
  let hfiniteI : Finite (Valued.ResidueField (chapter07LocalField R K v)) := by
    exact @Finite.of_equiv _ _ hfiniteO (IsLocalRing.ResidueField.mapEquiv e).toEquiv
  let hcompactSpaceI : CompactSpace (Valued.integer (chapter07LocalField R K v)) :=
    (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
      (K := chapter07LocalField R K v) (Γ₀ := ℤᵐ⁰)).2
      ⟨hcomplete, hdvr, hfiniteI⟩
  have hcompactI : IsCompact (Valued.integer (chapter07LocalField R K v) :
      Set (chapter07LocalField R K v)) := by
    convert ((isCompact_univ_iff.mpr hcompactSpaceI :
        IsCompact (Set.univ : Set (Valued.integer (chapter07LocalField R K v)))).image
        (continuous_subtype_val : Continuous
          (fun x : Valued.integer (chapter07LocalField R K v) =>
            (x : chapter07LocalField R K v)))) using 1
    ext x
    simp
  convert hcompactI using 1
  ext x
  constructor
  · intro hx
    exact (Valuation.mem_valuationSubring_iff (Valued.v) x).2 hx
  · intro hx
    exact (Valuation.mem_valuationSubring_iff (Valued.v) x).1 hx

/-- The finite idele group, with its canonical restricted-product presentation available through
`chapter07FiniteIdeleEquiv`.  The primary definition is the unit group of the finite adele ring,
so it inherits the graph topology supplied by Mathlib. -/
abbrev chapter07FiniteIdeleRestrictedProduct
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] : Type _ :=
  Πʳ v : chapter07FinitePlace R,
    [(chapter07LocalField R K v)ˣ,
      chapter07LocalIntegralUnitSubgroup R K v]

/-- The canonical restricted-product description of the finite ideles. -/
def chapter07FiniteIdeleEquiv
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    chapter07FiniteIdeleGroup R K ≃*
      chapter07FiniteIdeleRestrictedProduct R K :=
  RestrictedProduct.unitsEquiv
    (𝓕 := Filter.cofinite)
    (B := fun v : chapter07FinitePlace R => chapter07LocalIntegerRing R K v)
    (fun v : chapter07FinitePlace R => chapter07LocalField R K v)

/-! ### Basic neighborhoods for classical restricted products -/

def chapter07RestrictedProductBasicOpenShared
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    (S : Set ι) (U : (i : ι) → Set (R i)) :
    Set (Πʳ i, [R i, A i]) :=
  {x | (∀ i ∈ S, x i ∈ U i) ∧ ∀ i ∉ S, x i ∈ A i}

theorem chapter07_restrictedProduct_basicOpen_isOpen_shared
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    [∀ i, TopologicalSpace (R i)]
    (S : Set ι) (hS : S.Finite) (U : (i : ι) → Set (R i))
    (hU : ∀ i, IsOpen (U i)) (hA : ∀ i, IsOpen (A i)) :
    IsOpen (chapter07RestrictedProductBasicOpenShared R A S U) := by
  have hU' : IsOpen (⋂ i ∈ S, (fun x : Πʳ i, [R i, A i] => x i) ⁻¹' U i) :=
    hS.isOpen_biInter fun i hi =>
      (hU i).preimage (RestrictedProduct.continuous_eval (R := R) (A := A) i)
  have hA' : IsOpen {x : Πʳ i, [R i, A i] | ∀ i, i ∉ S → x i ∈ A i} :=
    RestrictedProduct.isOpen_forall_imp_mem hA
  have hopen := hU'.inter hA'
  rw [show chapter07RestrictedProductBasicOpenShared R A S U =
      (⋂ i ∈ S, (fun x : Πʳ i, [R i, A i] => x i) ⁻¹' U i) ∩
        {x : Πʳ i, [R i, A i] | ∀ i, i ∉ S → x i ∈ A i} by
    ext x
    simp [chapter07RestrictedProductBasicOpenShared]]
  exact hopen

theorem chapter07_restrictedProduct_basicOpen_basis_shared
    {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))
    [∀ i, TopologicalSpace (R i)] (hA : ∀ i, IsOpen (A i)) :
    ∀ x : Πʳ i, [R i, A i], ∀ U ∈ 𝓝 x,
      ∃ S : Set ι, S.Finite ∧ ∃ V : (i : ι) → Set (R i),
        (∀ i, IsOpen (V i)) ∧ x ∈ chapter07RestrictedProductBasicOpenShared R A S V ∧
      chapter07RestrictedProductBasicOpenShared R A S V ⊆ U := by
  classical
  intro x U hUx
  rcases mem_nhds_iff.mp hUx with ⟨W, hWU, hWopen, hxW⟩
  let T : Set ι := {i | x i ∈ A i}
  have hT : cofinite ≤ 𝓟 T := by
    apply le_principal_iff.mpr
    change ∀ᶠ i in cofinite, x i ∈ A i
    exact x.2
  have hxT : ∀ᶠ i in 𝓟 T, x i ∈ A i := by
    exact Filter.mem_principal.mpr subset_rfl
  rcases RestrictedProduct.exists_inclusion_eq_of_eventually R A hT hxT with ⟨x', hxx⟩
  have hle :
      TopologicalSpace.coinduced (RestrictedProduct.inclusion R A hT)
          (RestrictedProduct.topologicalSpace R A (𝓟 T)) ≤
        (inferInstance : TopologicalSpace (Πʳ i, [R i, A i])) := by
    change TopologicalSpace.coinduced (RestrictedProduct.inclusion R A hT)
          (RestrictedProduct.topologicalSpace R A (𝓟 T)) ≤
        RestrictedProduct.topologicalSpace R A cofinite
    rw [RestrictedProduct.topologicalSpace_eq_iSup cofinite]
    exact le_iSup_of_le T (le_iSup_of_le hT le_rfl)
  have hWcomp : IsOpen[
      TopologicalSpace.coinduced (RestrictedProduct.inclusion R A hT)
        (RestrictedProduct.topologicalSpace R A (𝓟 T))] W :=
    hle W hWopen
  have hpre : IsOpen[RestrictedProduct.topologicalSpace R A (𝓟 T)]
      (RestrictedProduct.inclusion R A hT ⁻¹' W) :=
    isOpen_coinduced.mp hWcomp
  rw [RestrictedProduct.topologicalSpace_eq_of_principal] at hpre
  rcases isOpen_induced_iff.mp hpre with ⟨O, hO, hOeq⟩
  have hxpre : x' ∈ RestrictedProduct.inclusion R A hT ⁻¹' W := by
    change RestrictedProduct.inclusion R A hT x' ∈ W
    rw [hxx]
    exact hxW
  have hxO : (x' : ∀ i, R i) ∈ O := by
    have hxpre' := hxpre
    rw [← hOeq] at hxpre'
    exact hxpre'
  rcases isOpen_pi_iff.mp hO (x' : ∀ i, R i) hxO with ⟨J, q, hq, hqO⟩
  let S : Set ι := (J : Set ι) ∪ Tᶜ
  let V : (i : ι) → Set (R i) := fun i =>
    if i ∈ J then if i ∈ T then q i ∩ A i else q i else univ
  have hTcomp : Tᶜ.Finite := by
    change {i | x i ∉ A i}.Finite
    exact Filter.eventually_cofinite.mp x.2
  have hS : S.Finite := by
    exact J.finite_toSet.union hTcomp
  have hV : ∀ i, IsOpen (V i) := by
    intro i
    by_cases hiJ : i ∈ J
    · by_cases hiT : i ∈ T
      · simpa [V, hiJ, hiT] using (hq i hiJ).1.inter (hA i)
      · simpa [V, hiJ, hiT] using (hq i hiJ).1
    · simp [V, hiJ]
  have hxB : x ∈ chapter07RestrictedProductBasicOpenShared R A S V := by
    constructor
    · intro i hiS
      by_cases hiJ : i ∈ J
      · have hxu : (x' : ∀ i, R i) i ∈ q i := (hq i hiJ).2
        have hxcoord : (x' : ∀ i, R i) i = x i := by
          simpa using congrArg (fun z : Πʳ i, [R i, A i] => z i) hxx
        rw [hxcoord] at hxu
        by_cases hiT : i ∈ T
        · have hxa : x i ∈ A i := hiT
          simpa [V, hiJ, hiT] using And.intro hxu hxa
        · simpa [V, hiJ, hiT] using hxu
      · simp [S] at hiS
        simp [V, hiJ]
    · intro i hiS
      have hiT : i ∈ T := by
        by_contra hiT
        exact hiS (by simp [S, hiT])
      exact hiT
  refine ⟨S, hS, V, hV, hxB, ?_⟩
  intro z hz
  have hzT : ∀ᶠ i in 𝓟 T, z i ∈ A i := by
    apply Filter.mem_principal.mpr
    intro i hiT
    by_cases hiJ : i ∈ J
    · have hzV : z i ∈ V i := hz.1 i (by simp [S, hiJ])
      have hzVA : z i ∈ q i ∩ A i := by
        simpa [V, hiJ, hiT] using hzV
      exact hzVA.2
    · exact hz.2 i (by simp [S, hiJ, hiT])
  rcases RestrictedProduct.exists_inclusion_eq_of_eventually R A hT hzT with ⟨z', hzz⟩
  have hzO : (z' : ∀ i, R i) ∈ O := by
    apply hqO
    intro i hiJ
    have hiJ' : i ∈ J := by simpa using hiJ
    have hiS : i ∈ S := by
      change i ∈ (J : Set ι) ∪ Tᶜ
      exact Or.inl hiJ
    have hzV : z i ∈ V i := hz.1 i hiS
    have hzq : z i ∈ q i := by
      by_cases hiT : i ∈ T
      · exact (show z i ∈ q i ∩ A i by simpa [V, hiJ', hiT] using hzV).1
      · simpa [V, hiJ', hiT] using hzV
    have hzcoord : (z' : ∀ i, R i) i = z i := by
      simpa using congrArg (fun w : Πʳ i, [R i, A i] => w i) hzz
    rw [hzcoord]
    exact hzq
  have hzpre : z' ∈ RestrictedProduct.inclusion R A hT ⁻¹' W := by
    rw [← hOeq]
    exact hzO
  apply hWU
  change RestrictedProduct.inclusion R A hT z' ∈ W at hzpre
  simpa [hzz] using hzpre

theorem chapter07_finiteIdele_restrictedProduct_topology
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    (inferInstance : TopologicalSpace (chapter07FiniteIdeleGroup R K)) =
      TopologicalSpace.induced (chapter07FiniteIdeleEquiv R K) inferInstance := by
  let φ : ∀ v : chapter07FinitePlace R,
      (chapter07LocalField R K v)ˣ → chapter07LocalField R K v :=
    fun _ u => u
  have hφ : ∀ᶠ v : chapter07FinitePlace R in cofinite,
      MapsTo (φ v)
        (chapter07LocalIntegralUnitSubgroup R K v)
        (chapter07LocalIntegerRing R K v) := by
    exact Filter.Eventually.of_forall (fun v u hu => hu.1)
  let fval : chapter07FiniteIdeleRestrictedProduct R K →
      chapter07FiniteAdeleRing R K :=
    RestrictedProduct.map φ hφ
  have hfval : Continuous fval := by
    exact RestrictedProduct.mapAlong_continuous
      (R₁ := fun v => (chapter07LocalField R K v)ˣ)
      (R₂ := fun v => chapter07LocalField R K v)
      (f := id) (hf := Filter.tendsto_id)
      (φ := φ)
      (hφ := hφ) (fun v => Units.continuous_val)
  have hval : Continuous (fun y : chapter07FiniteIdeleRestrictedProduct R K =>
      ((chapter07FiniteIdeleEquiv R K).symm y :
        chapter07FiniteAdeleRing R K)) := by
    change Continuous fval
    exact hfval
  let ginv : chapter07FiniteIdeleRestrictedProduct R K →
      chapter07FiniteAdeleRing R K :=
    fun y => (↑((chapter07FiniteIdeleEquiv R K).symm y)⁻¹ :
      chapter07FiniteAdeleRing R K)
  have hinvval : Continuous ginv := by
    change Continuous (fval ∘ fun a => a⁻¹)
    exact hfval.comp continuous_inv
  have hinv : Continuous (chapter07FiniteIdeleEquiv R K).symm := by
    rw [Units.continuous_iff]
    exact ⟨hval, by simpa only [ginv] using hinvval⟩
  have hBopen : ∀ v : chapter07FinitePlace R,
      IsOpen (chapter07LocalIntegerRing R K v : Set (chapter07LocalField R K v)) := by
    intro v
    exact Valued.isOpen_valuationSubring _
  have hAopen : ∀ v : chapter07FinitePlace R,
      IsOpen (chapter07LocalIntegralUnitSubgroup R K v :
        Set ((chapter07LocalField R K v)ˣ)) := by
    intro v
    exact Submonoid.isOpen_units (hBopen v)
  have hcoord (v : chapter07FinitePlace R) :
      Continuous (fun z : chapter07FiniteIdeleGroup R K =>
        chapter07FiniteIdeleEquiv R K z v) := by
    rw [Units.continuous_iff]
    constructor
    · change Continuous (fun z : chapter07FiniteIdeleGroup R K => z.1 v)
      exact (RestrictedProduct.continuous_eval v).comp Units.continuous_val
    · change Continuous (fun z : chapter07FiniteIdeleGroup R K =>
        (z⁻¹ : chapter07FiniteIdeleGroup R K).1 v)
      exact (RestrictedProduct.continuous_eval v).comp Units.continuous_coe_inv
  have hE_val (z : chapter07FiniteIdeleGroup R K) (v : chapter07FinitePlace R) :
      (↑(chapter07FiniteIdeleEquiv R K z v) : chapter07LocalField R K v) =
        (z : chapter07FiniteAdeleRing R K) v := by
    rfl
  have hE_inv_val (z : chapter07FiniteIdeleGroup R K) (v : chapter07FinitePlace R) :
      (↑((chapter07FiniteIdeleEquiv R K z v)⁻¹) : chapter07LocalField R K v) =
        ((z⁻¹ : chapter07FiniteIdeleGroup R K) : chapter07FiniteAdeleRing R K) v := by
    rfl
  have he : Continuous (chapter07FiniteIdeleEquiv R K) := by
    rw [continuous_def]
    intro W hW
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    rcases chapter07_restrictedProduct_basicOpen_basis_shared
        (fun v : chapter07FinitePlace R => (chapter07LocalField R K v)ˣ)
        (fun v : chapter07FinitePlace R =>
          chapter07LocalIntegralUnitSubgroup R K v) hAopen
        (chapter07FiniteIdeleEquiv R K x) W
        (mem_nhds_iff.mpr ⟨W, subset_rfl, hW, hx⟩) with
      ⟨S, hS, U, hU, hxU, hUW⟩
    have hfinite : IsOpen {z : chapter07FiniteIdeleGroup R K |
        ∀ v ∈ S, chapter07FiniteIdeleEquiv R K z v ∈ U v} := by
      rw [show {z : chapter07FiniteIdeleGroup R K |
          ∀ v ∈ S, chapter07FiniteIdeleEquiv R K z v ∈ U v} =
          ⋂ v ∈ S, (fun z : chapter07FiniteIdeleGroup R K =>
            chapter07FiniteIdeleEquiv R K z v) ⁻¹' U v by
        ext z
        simp]
      exact hS.isOpen_biInter (fun v hv => (hU v).preimage (hcoord v))
    have hbase : IsOpen {z : chapter07FiniteIdeleGroup R K |
        ∀ v, v ∉ S → (z : chapter07FiniteAdeleRing R K) v ∈
          chapter07LocalIntegerRing R K v} := by
      exact (RestrictedProduct.isOpen_forall_imp_mem hBopen).preimage
        Units.continuous_val
    have hbase_inv : IsOpen {z : chapter07FiniteIdeleGroup R K |
        ∀ v, v ∉ S → ((z⁻¹ : chapter07FiniteIdeleGroup R K) :
          chapter07FiniteAdeleRing R K) v ∈ chapter07LocalIntegerRing R K v} := by
      exact (RestrictedProduct.isOpen_forall_imp_mem hBopen).preimage
        Units.continuous_coe_inv
    have hpre : (chapter07FiniteIdeleEquiv R K) ⁻¹'
        (chapter07RestrictedProductBasicOpenShared
          (fun v : chapter07FinitePlace R => (chapter07LocalField R K v)ˣ)
          (fun v : chapter07FinitePlace R =>
            chapter07LocalIntegralUnitSubgroup R K v) S U) =
        {z : chapter07FiniteIdeleGroup R K |
          ∀ v ∈ S, chapter07FiniteIdeleEquiv R K z v ∈ U v} ∩
          {z : chapter07FiniteIdeleGroup R K |
            ∀ v, v ∉ S → (z : chapter07FiniteAdeleRing R K) v ∈
              chapter07LocalIntegerRing R K v} ∩
          {z : chapter07FiniteIdeleGroup R K |
            ∀ v, v ∉ S → ((z⁻¹ : chapter07FiniteIdeleGroup R K) :
              chapter07FiniteAdeleRing R K) v ∈ chapter07LocalIntegerRing R K v} := by
      ext z
      simp only [chapter07RestrictedProductBasicOpenShared, mem_preimage, mem_ofPred_eq,
        mem_inter_iff]
      change
        ((∀ i ∈ S, chapter07FiniteIdeleEquiv R K z i ∈ U i) ∧
          ∀ i ∉ S, chapter07FiniteIdeleEquiv R K z i ∈
            chapter07LocalIntegralUnitSubgroup R K i) ↔
        (((∀ i ∈ S, chapter07FiniteIdeleEquiv R K z i ∈ U i) ∧
            (∀ i ∉ S, (z : chapter07FiniteAdeleRing R K) i ∈
              chapter07LocalIntegerRing R K i)) ∧
          (∀ i ∉ S, ((z⁻¹ : chapter07FiniteIdeleGroup R K) :
            chapter07FiniteAdeleRing R K) i ∈ chapter07LocalIntegerRing R K i))
      constructor
      · rintro ⟨hS', hA'⟩
        refine ⟨⟨hS', ?_⟩, ?_⟩
        · intro v hv
          have hv' := Submonoid.val_mem_of_mem_units
            (Submonoid.ofClass (chapter07LocalIntegerRing R K v)) (hA' v hv)
          rw [hE_val] at hv'
          exact hv'
        · intro v hv
          have hv' := Submonoid.inv_val_mem_of_mem_units
            (Submonoid.ofClass (chapter07LocalIntegerRing R K v)) (hA' v hv)
          rw [hE_inv_val] at hv'
          exact hv'
      · rintro ⟨⟨hS', hA'⟩, hAinv'⟩
        refine ⟨hS', ?_⟩
        intro v hv
        have hv' := hA' v hv
        have hv'' := hAinv' v hv
        rw [← hE_val] at hv'
        rw [← hE_inv_val] at hv''
        exact Submonoid.mem_units_of_val_mem_inv_val_mem
          (Submonoid.ofClass (chapter07LocalIntegerRing R K v)) hv' hv''
    apply mem_nhds_iff.mpr
    refine ⟨(chapter07FiniteIdeleEquiv R K) ⁻¹'
        (chapter07RestrictedProductBasicOpenShared
          (fun v : chapter07FinitePlace R => (chapter07LocalField R K v)ˣ)
          (fun v : chapter07FinitePlace R =>
            chapter07LocalIntegralUnitSubgroup R K v) S U), ?_, ?_, ?_⟩
    · exact preimage_mono hUW
    · rw [hpre]
      exact (hfinite.inter hbase).inter hbase_inv
    · rw [hpre]
      refine ⟨⟨hxU.1, ?_⟩, ?_⟩
      · intro v hv
        have hv' := Submonoid.val_mem_of_mem_units
          (Submonoid.ofClass (chapter07LocalIntegerRing R K v)) (hxU.2 v hv)
        rw [hE_val] at hv'
        exact hv'
      · intro v hv
        have hv' := Submonoid.inv_val_mem_of_mem_units
          (Submonoid.ofClass (chapter07LocalIntegerRing R K v)) (hxU.2 v hv)
        rw [hE_inv_val] at hv'
        exact hv'
  let hhomeo :
      Homeomorph (chapter07FiniteIdeleGroup R K)
        (chapter07FiniteIdeleRestrictedProduct R K) :=
    Homeomorph.mk (chapter07FiniteIdeleEquiv R K).toEquiv he hinv
  change Units.instTopologicalSpaceUnits =
    TopologicalSpace.induced (chapter07FiniteIdeleEquiv R K)
      (RestrictedProduct.topologicalSpace
        (fun v : chapter07FinitePlace R => (chapter07LocalField R K v)ˣ)
        (fun v : chapter07FinitePlace R => chapter07LocalIntegralUnitSubgroup R K v)
        cofinite)
  have htop := hhomeo.isInducing.eq_induced
  simpa [hhomeo] using htop

@[simp]
theorem chapter07FiniteIdeleEquiv_apply
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07FiniteIdeleGroup R K) (v : chapter07FinitePlace R) :
    chapter07FiniteIdeleEquiv R K x v = x.1 v :=
  rfl

/-- The finite divisor group in the book's direct-sum notation. -/
abbrev chapter07FiniteDivisorGroup
    (R : Type*) [CommRing R] [IsDedekindDomain R] :=
  chapter07FinitePlace R →₀ ℤ

def chapter07FiniteDivisorGroupToDirectSum
    (R : Type*) [CommRing R] [IsDedekindDomain R] :
    chapter07FiniteDivisorGroup R ≃+
      (⨁ _ : chapter07FinitePlace R, ℤ) :=
  letI : DecidableEq (chapter07FinitePlace R) := Classical.decEq _
  (finsuppLEquivDirectSum ℤ ℤ (chapter07FinitePlace R)).toAddEquiv

@[simp]
theorem chapter07FiniteDivisorGroupToDirectSum_apply
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (d : chapter07FiniteDivisorGroup R) (v : chapter07FinitePlace R) :
    chapter07FiniteDivisorGroupToDirectSum R d v = d v :=
by
  rfl


/-! ### The graph topology of units -/

def chapter07IdeleGraph
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    chapter07IdeleGroup R K → chapter07AdeleRing R K × chapter07AdeleRing R K :=
  fun x => (x.1, (x⁻¹ : chapter07IdeleGroup R K).1)

@[simp]
theorem chapter07IdeleGraph_apply_fst
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (x : chapter07IdeleGroup R K) :
    (chapter07IdeleGraph R K x).1 = x.1 :=
  rfl

@[simp]
theorem chapter07IdeleGraph_apply_snd
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (x : chapter07IdeleGroup R K) :
    (chapter07IdeleGraph R K x).2 = (x⁻¹ : chapter07IdeleGroup R K).1 :=
  rfl

/-! ### Local unit coordinates of a full idele -/

/-- The local unit represented by an infinite coordinate of a full idele.  The inverse coordinate
comes from the inverse adele and supplies the unit laws. -/
def chapter07IdeleInfiniteCoordinate
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07IdeleGroup R K) (v : NumberField.InfinitePlace K) : (v.Completion)ˣ where
  val := x.1.1 v
  inv := (x⁻¹ : chapter07IdeleGroup R K).1.1 v
  val_inv := by
    change x.1.1 v * x.inv.1 v = 1
    exact congrArg (fun a : chapter07AdeleRing R K => a.1 v) x.val_inv
  inv_val := by
    change x.inv.1 v * x.1.1 v = 1
    exact congrArg (fun a : chapter07AdeleRing R K => a.1 v) x.inv_val

@[simp]
theorem chapter07IdeleInfiniteCoordinate_val
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07IdeleGroup R K) (v : NumberField.InfinitePlace K) :
    (chapter07IdeleInfiniteCoordinate R K x v : v.Completion) = x.1.1 v :=
  rfl

/-- The local unit represented by a finite coordinate of a full idele. -/
def chapter07IdeleFiniteCoordinate
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07IdeleGroup R K) (v : chapter07FinitePlace R) :
    (chapter07LocalField R K v)ˣ where
  val := x.1.2 v
  inv := (x⁻¹ : chapter07IdeleGroup R K).1.2 v
  val_inv := by
    change x.1.2 v * x.inv.2 v = 1
    exact congrArg (fun a : chapter07AdeleRing R K => a.2 v) x.val_inv
  inv_val := by
    change x.inv.2 v * x.1.2 v = 1
    exact congrArg (fun a : chapter07AdeleRing R K => a.2 v) x.inv_val

@[simp]
theorem chapter07IdeleFiniteCoordinate_val
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07IdeleGroup R K) (v : chapter07FinitePlace R) :
    (chapter07IdeleFiniteCoordinate R K x v : chapter07LocalField R K v) = x.1.2 v :=
  rfl

/-! ### A restricted-product presentation over all places -/

abbrev chapter07AllPlace
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  Sum (NumberField.InfinitePlace K) (chapter07FinitePlace R)

abbrev chapter07AllLocalUnitGroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (w : chapter07AllPlace R K) : Type _ :=
  match w with
  | Sum.inl v => (v.Completion)ˣ
  | Sum.inr v => (chapter07LocalField R K v)ˣ

instance chapter07AllLocalUnitGroup_group
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (w : chapter07AllPlace R K) :
    Group (chapter07AllLocalUnitGroup R K w) := by
  cases w <;> infer_instance

instance chapter07AllLocalUnitGroup_topologicalSpace
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (w : chapter07AllPlace R K) :
    TopologicalSpace (chapter07AllLocalUnitGroup R K w) := by
  cases w <;> infer_instance

def chapter07AllIntegralUnitSubgroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (w : chapter07AllPlace R K) : Subgroup (chapter07AllLocalUnitGroup R K w) :=
  match w with
  | Sum.inl _ => ⊤
  | Sum.inr v => chapter07LocalIntegralUnitSubgroup R K v

abbrev chapter07AllIntegralUnitSet
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (w : chapter07AllPlace R K) : Set (chapter07AllLocalUnitGroup R K w) :=
  chapter07AllIntegralUnitSubgroup R K w

abbrev chapter07GlobalIdeleRestrictedProduct
  (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  Πʳ w : chapter07AllPlace R K,
    [chapter07AllLocalUnitGroup R K w, chapter07AllIntegralUnitSubgroup R K w]

/-- The full idele group is the restricted product of the local multiplicative groups, with no
restriction at archimedean places and the local integral unit restriction at finite places. -/
noncomputable def chapter07IdeleRestrictedProductEquiv
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    chapter07IdeleGroup R K ≃*
      chapter07GlobalIdeleRestrictedProduct R K where
  toFun x :=
    RestrictedProduct.mk
      (fun w => match w with
        | Sum.inl v => chapter07IdeleInfiniteCoordinate R K x v
        | Sum.inr v => chapter07IdeleFiniteCoordinate R K x v)
      (by
        apply Filter.mem_cofinite.mpr
        let bad : Set (chapter07FinitePlace R) :=
          {v | x.1.2 v ∉ chapter07LocalIntegerRing R K v ∨
            (x⁻¹ : chapter07IdeleGroup R K).1.2 v ∉ chapter07LocalIntegerRing R K v}
        have hbad : bad.Finite := by
          have hbad₁ : {v : chapter07FinitePlace R |
              x.1.2 v ∉ chapter07LocalIntegerRing R K v}.Finite :=
            Filter.eventually_cofinite.mp x.1.2.2
          have hbad₂ : {v : chapter07FinitePlace R |
              (x⁻¹ : chapter07IdeleGroup R K).1.2 v ∉ chapter07LocalIntegerRing R K v}.Finite :=
            Filter.eventually_cofinite.mp (x⁻¹ : chapter07IdeleGroup R K).1.2.2
          rw [show bad = {v : chapter07FinitePlace R |
              x.1.2 v ∉ chapter07LocalIntegerRing R K v} ∪
              {v : chapter07FinitePlace R |
                (x⁻¹ : chapter07IdeleGroup R K).1.2 v ∉ chapter07LocalIntegerRing R K v} by
            ext v
            simp [bad]]
          exact hbad₁.union hbad₂
        apply (hbad.image Sum.inr).subset
        intro w hw
        cases w with
        | inl v => simp [chapter07AllIntegralUnitSubgroup] at hw
        | inr v =>
          refine ⟨v, ?_, rfl⟩
          by_contra hbad'
          have hval : x.1.2 v ∈ chapter07LocalIntegerRing R K v := by
            by_contra hv
            exact hbad' (Or.inl hv)
          have hinv : (x⁻¹ : chapter07IdeleGroup R K).1.2 v ∈
              chapter07LocalIntegerRing R K v := by
            by_contra hv
            exact hbad' (Or.inr hv)
          apply hw
          exact Submonoid.mem_units_of_val_mem_inv_val_mem
            (Submonoid.ofClass (chapter07LocalIntegerRing R K v))
            (by
              change x.1.2 v ∈ chapter07LocalIntegerRing R K v
              exact hval)
            (by
              change (x⁻¹ : chapter07IdeleGroup R K).1.2 v ∈
                chapter07LocalIntegerRing R K v
              exact hinv))
  invFun y :=
    { val :=
        ⟨(fun v : NumberField.InfinitePlace K =>
            (y (Sum.inl v) : v.Completion)),
          RestrictedProduct.mk
            (fun v : chapter07FinitePlace R =>
              (y (Sum.inr v) : chapter07LocalField R K v))
            (by
              apply Filter.mem_cofinite.mpr
              have hy : {w : chapter07AllPlace R K |
                  y w ∉ chapter07AllIntegralUnitSubgroup R K w}.Finite :=
                Filter.eventually_cofinite.mp y.2
              have hy' := hy.preimage
                (Sum.inr_injective : Function.Injective
                  (Sum.inr : chapter07FinitePlace R → chapter07AllPlace R K)).injOn
              apply hy'.subset
              intro v hv hmem
              apply hv
              exact Submonoid.val_mem_of_mem_units
                (Submonoid.ofClass (chapter07LocalIntegerRing R K v)) hmem)⟩
      inv :=
        ⟨(fun v : NumberField.InfinitePlace K =>
            ((y (Sum.inl v))⁻¹ : v.Completion)),
          RestrictedProduct.mk
            (fun v : chapter07FinitePlace R =>
              ((y (Sum.inr v))⁻¹ : chapter07LocalField R K v))
            (by
              have hy : {w : chapter07AllPlace R K |
                  y w ∉ chapter07AllIntegralUnitSubgroup R K w}.Finite :=
                Filter.eventually_cofinite.mp y.2
              have hy' := hy.preimage
                (Sum.inr_injective : Function.Injective
                  (Sum.inr : chapter07FinitePlace R → chapter07AllPlace R K)).injOn
              filter_upwards [hy'.compl_mem_cofinite] with v hv
              have hmem : y (Sum.inr v) ∈
                  chapter07AllIntegralUnitSubgroup R K (Sum.inr v) := by
                by_contra hbad
                exact hv hbad
              rw [← Units.val_inv_eq_inv_val]
              exact Submonoid.val_mem_of_mem_units
                (Submonoid.ofClass (chapter07LocalIntegerRing R K v))
                ((chapter07AllIntegralUnitSubgroup R K (Sum.inr v)).inv_mem hmem))⟩
      val_inv := by
        apply Prod.ext
        · funext v
          change (y (Sum.inl v) : v.Completion) *
              ((y (Sum.inl v))⁻¹ : v.Completion) = 1
          rw [← Units.val_inv_eq_inv_val, ← Units.inv_eq_val_inv]
          exact (y (Sum.inl v)).val_inv
        · apply RestrictedProduct.ext
          intro v
          change (y (Sum.inr v) : chapter07LocalField R K v) *
              ((y (Sum.inr v))⁻¹ : chapter07LocalField R K v) = 1
          rw [← Units.val_inv_eq_inv_val, ← Units.inv_eq_val_inv]
          exact (y (Sum.inr v)).val_inv
      inv_val := by
        apply Prod.ext
        · funext v
          change ((y (Sum.inl v))⁻¹ : v.Completion) *
              (y (Sum.inl v) : v.Completion) = 1
          rw [← Units.val_inv_eq_inv_val, ← Units.inv_eq_val_inv]
          exact (y (Sum.inl v)).inv_val
        · apply RestrictedProduct.ext
          intro v
          change ((y (Sum.inr v))⁻¹ : chapter07LocalField R K v) *
              (y (Sum.inr v) : chapter07LocalField R K v) = 1
          rw [← Units.val_inv_eq_inv_val, ← Units.inv_eq_val_inv]
          exact (y (Sum.inr v)).inv_val }
  left_inv := by
    intro x
    apply Units.ext
    apply Prod.ext
    · funext v
      simp [chapter07IdeleInfiniteCoordinate]
    · apply RestrictedProduct.ext
      intro v
      rfl
  right_inv := by
    intro y
    apply RestrictedProduct.ext
    intro w
    cases w <;> apply Units.ext <;> rfl
  map_mul' := by
    intro x₁ x₂
    apply RestrictedProduct.ext
    intro w
    cases w <;> apply Units.ext <;> rfl

theorem chapter07_idele_restrictedProduct_topology
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
      (inferInstance : TopologicalSpace (chapter07IdeleGroup R K)) =
      TopologicalSpace.induced (chapter07IdeleRestrictedProductEquiv R K) inferInstance := by
  have hAopen : ∀ w : chapter07AllPlace R K,
      IsOpen (chapter07AllIntegralUnitSet R K w :
        Set (chapter07AllLocalUnitGroup R K w)) := by
    intro w
    cases w with
    | inl v => simp [chapter07AllIntegralUnitSet, chapter07AllIntegralUnitSubgroup]
    | inr v =>
      have hlocal : IsOpen (chapter07LocalIntegerRing R K v :
          Set (chapter07LocalField R K v)) := by
        exact Valued.isOpen_valuationSubring _
      exact Submonoid.isOpen_units hlocal
  have hcoord (w : chapter07AllPlace R K) :
      Continuous (fun x : chapter07IdeleGroup R K =>
        chapter07IdeleRestrictedProductEquiv R K x w) := by
    cases w with
    | inl v =>
      rw [Units.continuous_iff]
      constructor
      · change Continuous (fun x : chapter07IdeleGroup R K => x.1.1 v)
        exact (continuous_apply v).comp
          (continuous_fst.comp Units.continuous_val)
      · change Continuous (fun x : chapter07IdeleGroup R K =>
          (x⁻¹ : chapter07IdeleGroup R K).1.1 v)
        exact (continuous_apply v).comp
          (continuous_fst.comp Units.continuous_coe_inv)
    | inr v =>
      rw [Units.continuous_iff]
      constructor
      · change Continuous (fun x : chapter07IdeleGroup R K => x.1.2 v)
        exact (RestrictedProduct.continuous_eval v).comp
          (continuous_snd.comp Units.continuous_val)
      · change Continuous (fun x : chapter07IdeleGroup R K =>
          (x⁻¹ : chapter07IdeleGroup R K).1.2 v)
        exact (RestrictedProduct.continuous_eval v).comp
          (continuous_snd.comp Units.continuous_coe_inv)
  have he : Continuous (chapter07IdeleRestrictedProductEquiv R K) := by
    rw [continuous_def]
    intro W hW
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    rcases chapter07_restrictedProduct_basicOpen_basis_shared
        (chapter07AllLocalUnitGroup R K) (chapter07AllIntegralUnitSet R K) hAopen
        (chapter07IdeleRestrictedProductEquiv R K x) W
        (mem_nhds_iff.mpr ⟨W, subset_rfl, hW, hx⟩) with
      ⟨S, hS, U, hU, hxU, hUW⟩
    have hBopen : ∀ v : chapter07FinitePlace R,
        IsOpen (chapter07LocalIntegerRing R K v :
          Set (chapter07LocalField R K v)) := by
      intro v
      exact Valued.isOpen_valuationSubring _
    have hvalUnits : Continuous (fun z : chapter07IdeleGroup R K =>
        (z : chapter07AdeleRing R K)) := by
      exact Units.continuous_val
    have hinvUnits : Continuous (fun z : chapter07IdeleGroup R K =>
        ((z⁻¹ : chapter07IdeleGroup R K) : chapter07AdeleRing R K)) := by
      exact Units.continuous_coe_inv
    have hfinite : IsOpen {z : chapter07IdeleGroup R K |
        ∀ w ∈ S, chapter07IdeleRestrictedProductEquiv R K z w ∈ U w} := by
      rw [show {z : chapter07IdeleGroup R K |
          ∀ w ∈ S, chapter07IdeleRestrictedProductEquiv R K z w ∈ U w} =
          ⋂ w ∈ S, (fun z : chapter07IdeleGroup R K =>
            chapter07IdeleRestrictedProductEquiv R K z w) ⁻¹' U w by
        ext z
        simp]
      exact hS.isOpen_biInter (fun w hw => (hU w).preimage (hcoord w))
    have hbase : IsOpen {z : chapter07IdeleGroup R K |
        ∀ v : chapter07FinitePlace R, Sum.inr v ∉ S →
          (z : chapter07AdeleRing R K).2 v ∈ chapter07LocalIntegerRing R K v} := by
      change IsOpen ((fun z : chapter07IdeleGroup R K =>
        (z : chapter07AdeleRing R K).2) ⁻¹'
          {a : chapter07FiniteAdeleRing R K | ∀ v : chapter07FinitePlace R,
            Sum.inr v ∉ S → a v ∈ chapter07LocalIntegerRing R K v})
      exact (RestrictedProduct.isOpen_forall_imp_mem hBopen).preimage
        (continuous_snd.comp hvalUnits)
    have hbase_inv : IsOpen {z : chapter07IdeleGroup R K |
        ∀ v : chapter07FinitePlace R, Sum.inr v ∉ S →
          ((z⁻¹ : chapter07IdeleGroup R K) : chapter07AdeleRing R K).2 v ∈
            chapter07LocalIntegerRing R K v} := by
      change IsOpen ((fun z : chapter07IdeleGroup R K =>
        ((z⁻¹ : chapter07IdeleGroup R K) : chapter07AdeleRing R K).2) ⁻¹'
          {a : chapter07FiniteAdeleRing R K | ∀ v : chapter07FinitePlace R,
            Sum.inr v ∉ S → a v ∈ chapter07LocalIntegerRing R K v})
      exact (RestrictedProduct.isOpen_forall_imp_mem hBopen).preimage
        (continuous_snd.comp hinvUnits)
    have hE_val (z : chapter07IdeleGroup R K) (v : chapter07FinitePlace R) :
        (↑(chapter07IdeleRestrictedProductEquiv R K z (Sum.inr v)) :
          chapter07LocalField R K v) = (z : chapter07AdeleRing R K).2 v := by
      rfl
    have hE_inv_val (z : chapter07IdeleGroup R K) (v : chapter07FinitePlace R) :
        (↑((chapter07IdeleRestrictedProductEquiv R K z (Sum.inr v))⁻¹) :
          chapter07LocalField R K v) =
          ((z⁻¹ : chapter07IdeleGroup R K) : chapter07AdeleRing R K).2 v := by
      rfl
    let B := chapter07RestrictedProductBasicOpenShared
      (chapter07AllLocalUnitGroup R K) (chapter07AllIntegralUnitSet R K) S U
    have hpre : (chapter07IdeleRestrictedProductEquiv R K) ⁻¹' B =
        {z : chapter07IdeleGroup R K |
          ∀ w ∈ S, chapter07IdeleRestrictedProductEquiv R K z w ∈ U w} ∩
        {z : chapter07IdeleGroup R K |
          ∀ v : chapter07FinitePlace R, Sum.inr v ∉ S →
            (z : chapter07AdeleRing R K).2 v ∈ chapter07LocalIntegerRing R K v} ∩
        {z : chapter07IdeleGroup R K |
          ∀ v : chapter07FinitePlace R, Sum.inr v ∉ S →
            ((z⁻¹ : chapter07IdeleGroup R K) : chapter07AdeleRing R K).2 v ∈
              chapter07LocalIntegerRing R K v} := by
      ext z
      simp only [B, chapter07RestrictedProductBasicOpenShared, mem_preimage,
        mem_ofPred_eq, mem_inter_iff]
      change
        ((∀ i ∈ S, chapter07IdeleRestrictedProductEquiv R K z i ∈ U i) ∧
          ∀ i ∉ S, chapter07IdeleRestrictedProductEquiv R K z i ∈
            chapter07AllIntegralUnitSubgroup R K i) ↔
        (((∀ i ∈ S, chapter07IdeleRestrictedProductEquiv R K z i ∈ U i) ∧
            (∀ v : chapter07FinitePlace R, Sum.inr v ∉ S →
              (z : chapter07AdeleRing R K).2 v ∈
                chapter07LocalIntegerRing R K v)) ∧
          (∀ v : chapter07FinitePlace R, Sum.inr v ∉ S →
            ((z⁻¹ : chapter07IdeleGroup R K) : chapter07AdeleRing R K).2 v ∈
              chapter07LocalIntegerRing R K v))
      constructor
      · rintro ⟨hS', hA'⟩
        refine ⟨⟨hS', ?_⟩, ?_⟩
        · intro v hv
          have hv' := Submonoid.val_mem_of_mem_units
            (Submonoid.ofClass (chapter07LocalIntegerRing R K v))
            (hA' (Sum.inr v) hv)
          rw [hE_val] at hv'
          exact hv'
        · intro v hv
          have hv' := Submonoid.inv_val_mem_of_mem_units
            (Submonoid.ofClass (chapter07LocalIntegerRing R K v))
            (hA' (Sum.inr v) hv)
          rw [hE_inv_val] at hv'
          exact hv'
      · rintro ⟨⟨hS', hA'⟩, hAinv'⟩
        refine ⟨hS', ?_⟩
        intro w hw
        cases w with
        | inl v => simp [chapter07AllIntegralUnitSubgroup]
        | inr v =>
          apply Submonoid.mem_units_of_val_mem_inv_val_mem
            (Submonoid.ofClass (chapter07LocalIntegerRing R K v))
          · rw [hE_val]
            exact hA' v hw
          · rw [hE_inv_val]
            exact hAinv' v hw
    apply mem_nhds_iff.mpr
    refine ⟨(chapter07IdeleRestrictedProductEquiv R K) ⁻¹' B, ?_, ?_, ?_⟩
    · exact preimage_mono hUW
    · rw [hpre]
      exact (hfinite.inter hbase).inter hbase_inv
    · rw [hpre]
      refine ⟨⟨hxU.1, ?_⟩, ?_⟩
      · intro v hv
        have hv' := Submonoid.val_mem_of_mem_units
          (Submonoid.ofClass (chapter07LocalIntegerRing R K v)) (hxU.2 (Sum.inr v) hv)
        rw [hE_val] at hv'
        exact hv'
      · intro v hv
        have hv' := Submonoid.inv_val_mem_of_mem_units
          (Submonoid.ofClass (chapter07LocalIntegerRing R K v)) (hxU.2 (Sum.inr v) hv)
        rw [hE_inv_val] at hv'
        exact hv'
  let projFinite : chapter07GlobalIdeleRestrictedProduct R K →
      chapter07FiniteAdeleRing R K :=
    RestrictedProduct.mapAlong
      (chapter07AllLocalUnitGroup R K)
      (fun v : chapter07FinitePlace R => chapter07LocalField R K v)
      (Sum.inr : chapter07FinitePlace R → chapter07AllPlace R K)
      ((Sum.inr_injective : Function.Injective
        (Sum.inr : chapter07FinitePlace R → chapter07AllPlace R K)).tendsto_cofinite)
      (fun v u => (u : chapter07LocalField R K v))
      (Filter.Eventually.of_forall (fun v u hu =>
        Submonoid.val_mem_of_mem_units
          (Submonoid.ofClass (chapter07LocalIntegerRing R K v)) hu))
  have hproj : Continuous projFinite := by
    apply RestrictedProduct.mapAlong_continuous
      (R₁ := chapter07AllLocalUnitGroup R K)
      (R₂ := fun v : chapter07FinitePlace R => chapter07LocalField R K v)
      (f := Sum.inr)
      (hf := (Sum.inr_injective : Function.Injective
        (Sum.inr : chapter07FinitePlace R → chapter07AllPlace R K)).tendsto_cofinite)
      (φ := fun v u => (u : chapter07LocalField R K v))
      (hφ := Filter.Eventually.of_forall (fun v u hu =>
        Submonoid.val_mem_of_mem_units
          (Submonoid.ofClass (chapter07LocalIntegerRing R K v)) hu))
    intro v
    exact Units.continuous_val
  have hinf : Continuous (fun y : chapter07GlobalIdeleRestrictedProduct R K =>
      fun v : NumberField.InfinitePlace K => (y (Sum.inl v) : v.Completion)) := by
    exact continuous_pi (fun v => Units.continuous_val.comp
      (RestrictedProduct.continuous_eval (Sum.inl v)))
  have hval : Continuous (fun y : chapter07GlobalIdeleRestrictedProduct R K =>
      ((chapter07IdeleRestrictedProductEquiv R K).symm y :
        chapter07AdeleRing R K)) := by
    change Continuous (fun y : chapter07GlobalIdeleRestrictedProduct R K =>
      (fun v : NumberField.InfinitePlace K => (y (Sum.inl v) : v.Completion),
        projFinite y))
    exact hinf.prodMk hproj
  have hRP_inv : Continuous (fun y : chapter07GlobalIdeleRestrictedProduct R K => y⁻¹) := by
    have : ∀ w : chapter07AllPlace R K,
        ContinuousInv (chapter07AllLocalUnitGroup R K w) := fun w => by
      cases w <;> infer_instance
    rw [RestrictedProduct.continuous_dom]
    intro T hT
    have hprincipal : ContinuousInv
        (Πʳ w : chapter07AllPlace R K,
          [chapter07AllLocalUnitGroup R K w,
            chapter07AllIntegralUnitSubgroup R K w]_[𝓟 T]) :=
      RestrictedProduct.isEmbedding_coe_of_principal.continuousInv (fun _ => rfl)
    exact (RestrictedProduct.continuous_inclusion hT).comp hprincipal.continuous_inv
  have hinvval : Continuous (fun y : chapter07GlobalIdeleRestrictedProduct R K =>
      (((chapter07IdeleRestrictedProductEquiv R K).symm y)⁻¹ :
        chapter07IdeleGroup R K).1) := by
    have heq : (fun y : chapter07GlobalIdeleRestrictedProduct R K =>
        ((chapter07IdeleRestrictedProductEquiv R K).symm (y⁻¹) :
          chapter07IdeleGroup R K).1) =
        (fun y : chapter07GlobalIdeleRestrictedProduct R K =>
          (((chapter07IdeleRestrictedProductEquiv R K).symm y)⁻¹ :
            chapter07IdeleGroup R K).1) := by
      funext y
      rw [map_inv]
    rw [← heq]
    exact hval.comp hRP_inv
  have hinv : Continuous (chapter07IdeleRestrictedProductEquiv R K).symm := by
    rw [Units.continuous_iff]
    exact ⟨hval, hinvval⟩
  let hhomeo : Homeomorph (chapter07IdeleGroup R K)
      (chapter07GlobalIdeleRestrictedProduct R K) :=
    Homeomorph.mk (chapter07IdeleRestrictedProductEquiv R K).toEquiv he hinv
  change Units.instTopologicalSpaceUnits =
    TopologicalSpace.induced (chapter07IdeleRestrictedProductEquiv R K)
      (RestrictedProduct.topologicalSpace
        (chapter07AllLocalUnitGroup R K) (chapter07AllIntegralUnitSet R K) cofinite)
  have htop := hhomeo.isInducing.eq_induced
  simpa [hhomeo] using htop

theorem chapter07_ideleGraph_isEmbedding
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    IsEmbedding (chapter07IdeleGraph R K) := by
  have hprod : IsEmbedding
      (fun p : chapter07AdeleRing R K × (chapter07AdeleRing R K)ᵐᵒᵖ =>
        (p.1, MulOpposite.unop p.2)) :=
    IsEmbedding.id.prodMap MulOpposite.opHomeomorph.symm.isEmbedding
  have hcomp := hprod.comp (Units.isEmbedding_embedProduct)
  change IsEmbedding (fun x : (chapter07AdeleRing R K)ˣ =>
    (x.1, (x⁻¹ : (chapter07AdeleRing R K)ˣ).1))
  exact hcomp

theorem chapter07_ideleTopology_is_graphTopology
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    (inferInstance : TopologicalSpace (chapter07IdeleGroup R K)) =
      TopologicalSpace.induced (chapter07IdeleGraph R K) inferInstance := by
  exact (chapter07_ideleGraph_isEmbedding R K).eq_induced

/-! ### A reusable maximal-compactness predicate -/

/-- A subgroup which contains every compact subgroup.  This packages the uniqueness assertion
used for the local and global maximal compact subgroups. -/
def chapter07UniqueMaximalCompactSubgroup
    (G : Type*) [Group G] [TopologicalSpace G] (H : Subgroup G) : Prop :=
  IsCompact (H : Set G) ∧
    ∀ L : Subgroup G, IsCompact (L : Set G) → L ≤ H

theorem chapter07UniqueMaximalCompactSubgroup.is_compact
    (G : Type*) [Group G] [TopologicalSpace G] (H : Subgroup G)
    (hH : chapter07UniqueMaximalCompactSubgroup G H) :
    IsCompact (H : Set G) :=
  hH.1

theorem chapter07UniqueMaximalCompactSubgroup.contains_compact
    (G : Type*) [Group G] [TopologicalSpace G] (H : Subgroup G)
    (hH : chapter07UniqueMaximalCompactSubgroup G H)
    (L : Subgroup G) (hL : IsCompact (L : Set G)) :
    L ≤ H :=
  hH.2 L hL

/-! ### Local orders -/

/- LOCAL_DEPENDENCY_GUESS: Mathlib exposes the normalized valuation on each finite completion, but
does not package its integer-valued order map on the local unit group.  The following map is the
canonical `-log` normalization; its two homomorphism laws are deferred to the proof pass. -/
noncomputable def chapter07LocalOrder
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :
    (chapter07LocalField R K v)ˣ → ℤ :=
  fun u => -WithZero.log (Valued.v u.1)

@[simp]
theorem chapter07LocalOrder_apply_one
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :
    chapter07LocalOrder R K v 1 = 0 := by
  simp [chapter07LocalOrder]

theorem chapter07LocalOrder_mul
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) (u w : (chapter07LocalField R K v)ˣ) :
    chapter07LocalOrder R K v (u * w) =
      chapter07LocalOrder R K v u + chapter07LocalOrder R K v w := by
  simp only [chapter07LocalOrder, Units.val_mul, map_mul]
  rw [WithZero.log_mul]
  · ring
  · exact (Valuation.ne_zero_iff _).2 (by simp [Units.ne_zero u])
  · exact (Valuation.ne_zero_iff _).2 (by simp [Units.ne_zero w])

theorem chapter07LocalOrder_inv
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) (u : (chapter07LocalField R K v)ˣ) :
    chapter07LocalOrder R K v u⁻¹ = -chapter07LocalOrder R K v u := by
  simp [chapter07LocalOrder]

/- The local order is surjective already at the dependency layer.  Section 7.3 needs this
   fact for the global finite order map, while the more book-facing wrapper in Section 7.4
   necessarily comes later in the import DAG. -/
theorem chapter07LocalOrder_surjective
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) :
    Function.Surjective (chapter07LocalOrder R K v) := by
  intro n
  obtain ⟨a, ha⟩ := v.valuedAdicCompletion_surjective K (WithZero.exp (-n))
  have hval : Valued.v a ≠ 0 := by
    rw [ha]
    exact WithZero.exp_ne_zero
  have ha0 : a ≠ 0 := (Valuation.ne_zero_iff Valued.v).1 hval
  refine ⟨Units.mk0 a ha0, ?_⟩
  simp [chapter07LocalOrder, ha]

theorem chapter07LocalOrder_eq_zero_on_integral_units
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) (u : (chapter07LocalField R K v)ˣ)
    (hu : u ∈ chapter07LocalIntegralUnitSubgroup R K v) :
    chapter07LocalOrder R K v u = 0 := by
  rw [chapter07LocalOrder]
  have huv : Valued.v (u : chapter07LocalField R K v) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).1 hu
  simp [huv]

theorem chapter07LocalOrder_eq_zero_iff_mem_localIntegralUnitSubgroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : chapter07FinitePlace R) (u : (chapter07LocalField R K v)ˣ) :
    chapter07LocalOrder R K v u = 0 ↔
      u ∈ chapter07LocalIntegralUnitSubgroup R K v := by
  constructor
  · intro hu
    apply (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).2
    have huv : Valued.v (u : chapter07LocalField R K v) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (by simp [Units.ne_zero u])
    have hlog : WithZero.log (Valued.v (u : chapter07LocalField R K v)) = 0 :=
      neg_eq_zero.mp (by simpa [chapter07LocalOrder] using hu)
    have hexp := congrArg WithZero.exp hlog
    simpa [WithZero.exp_log huv] using hexp
  · exact chapter07LocalOrder_eq_zero_on_integral_units R K v u

end

end LastLib.Book04AdelesAndIdeles.Chapter07
