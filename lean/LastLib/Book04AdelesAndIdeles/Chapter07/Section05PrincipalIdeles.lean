import LastLib.Book04AdelesAndIdeles.Chapter07.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter07.Section02TheIdeleGroup
import LastLib.Book04AdelesAndIdeles.Chapter07.Section04OpenAndMaximalCompactSubgroups
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.Section02ContinuityOfAlgebraicOperations
import LastLib.Book04AdelesAndIdeles.Chapter01.Section03ArchimedeanEmbeddings
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Algebra.Ring.Compact

namespace LastLib.Book04AdelesAndIdeles.Chapter07

noncomputable section

open Set Filter Topology
open scoped BigOperators DirectSum RestrictedProduct NNReal NumberField

/-! # 7.5 Principal ideles -/

/-- The diagonal embedding of the global multiplicative group into the full idele group. -/
def chapter07PrincipalIdeleEmbedding
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Kˣ →* chapter07IdeleGroup R K :=
  Units.map (algebraMap K (chapter07AdeleRing R K))

/-- The finite diagonal embedding, useful for recording the obstruction to finite density. -/
def chapter07FinitePrincipalIdeleEmbedding
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Kˣ →* chapter07FiniteIdeleGroup R K :=
  IsDedekindDomain.FiniteAdeleRing.unitEmbedding R K

@[simp]
theorem chapter07PrincipalIdeleEmbedding_apply_infinite
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (a : Kˣ) (v : NumberField.InfinitePlace K) :
    (chapter07PrincipalIdeleEmbedding R K a).1.1 v = algebraMap K (v.Completion) a := by
  rfl

@[simp]
theorem chapter07PrincipalIdeleEmbedding_apply_finite
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (a : Kˣ) (v : chapter07FinitePlace R) :
    (chapter07PrincipalIdeleEmbedding R K a).1.2 v =
      algebraMap K (chapter07LocalField R K v) a := by
  rfl

@[simp]
theorem chapter07FinitePrincipalIdeleEmbedding_apply
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (a : Kˣ) :
    chapter07FinitePrincipalIdeleEmbedding R K a =
      IsDedekindDomain.FiniteAdeleRing.unitEmbedding R K a :=
  rfl

def chapter07PrincipalIdeleSubgroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Subgroup (chapter07IdeleGroup R K) :=
  (chapter07PrincipalIdeleEmbedding R K).range

theorem chapter07_principal_idele_embedding_injective
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    Function.Injective (chapter07PrincipalIdeleEmbedding R K) := by
  intro a b h
  obtain ⟨v⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace K))
  apply Units.ext
  apply (FaithfulSMul.algebraMap_injective K (v.Completion))
  simpa using congrArg (fun z : chapter07IdeleGroup R K => z.1.1 v) h

theorem chapter07_principal_ideles_are_discrete
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    IsDiscrete (chapter07PrincipalIdeleSubgroup R K :
      Set (chapter07IdeleGroup R K)) := by
  classical
  have hL : IsDiscrete
      (NumberField.mixedEmbedding.integerLattice K :
        Set (NumberField.mixedEmbedding.mixedSpace K)) := by
    rw [isDiscrete_iff_discreteTopology]
    exact LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_integer_lattice_is_discrete K
  obtain ⟨Uinf, hUinfOpen, hUinfInter⟩ :=
    isDiscrete_iff_forall_mem_exists_isOpen.mp hL 0 (by simp)
  have hUinfZero : (0 : NumberField.mixedEmbedding.mixedSpace K) ∈ Uinf := by
    have hmem : (0 : NumberField.mixedEmbedding.mixedSpace K) ∈
        Uinf ∩ (NumberField.mixedEmbedding.integerLattice K :
          Set (NumberField.mixedEmbedding.mixedSpace K)) := by
      rw [hUinfInter]
      simp
    exact hmem.1
  let UinfA : Set (NumberField.InfiniteAdeleRing K) :=
    (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K) ⁻¹' Uinf
  have hUinfAOpen : IsOpen UinfA := by
    have hcont : Continuous
        (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
      let e : NumberField.InfiniteAdeleRing K ≃ₜ
          NumberField.mixedEmbedding.mixedSpace K :=
        (Homeomorph.piEquivPiSubtypeProd
          (fun (v : NumberField.InfinitePlace K) =>
            NumberField.InfinitePlace.IsReal v)
          (fun (v : NumberField.InfinitePlace K) => v.Completion)).trans
          (Homeomorph.prodCongr
            (Homeomorph.piCongrRight
              (fun w : {w : NumberField.InfinitePlace K //
                  NumberField.InfinitePlace.IsReal w} =>
                (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal
                  w.2).toHomeomorph))
            ((Homeomorph.piCongrRight
              (fun w : {w : NumberField.InfinitePlace K //
                  ¬ NumberField.InfinitePlace.IsReal w} =>
                (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex
                  (NumberField.InfinitePlace.not_isReal_iff_isComplex.1 w.2)).toHomeomorph)).trans
              (Homeomorph.piCongrLeft
                (Y := fun _ : {w : NumberField.InfinitePlace K //
                    NumberField.InfinitePlace.IsComplex w} => ℂ)
                (Equiv.subtypeEquivRight
                  (fun _ => NumberField.InfinitePlace.not_isReal_iff_isComplex)))))
      exact e.continuous
    exact hUinfOpen.preimage hcont
  have hUinfAZero : (0 : NumberField.InfiniteAdeleRing K) ∈ UinfA := by
    change NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K 0 ∈ Uinf
    simpa only [map_zero] using hUinfZero
  let Ufin : Set (chapter07FiniteAdeleRing R K) :=
    {x | ∀ v : chapter07FinitePlace R,
      x v ∈ (chapter07LocalIntegerRing R K v :
        Set (chapter07LocalField R K v))}
  have hUfinOpen : IsOpen Ufin := by
    change IsOpen {x : Πʳ v : chapter07FinitePlace R,
        [chapter07LocalField R K v, chapter07LocalIntegerRing R K v] |
      ∀ v : chapter07FinitePlace R,
        x v ∈ (chapter07LocalIntegerRing R K v :
          Set (chapter07LocalField R K v))}
    exact RestrictedProduct.isOpen_forall_mem (fun v =>
      Valued.isOpen_valuationSubring _)
  let Ufull : Set (chapter07AdeleRing R K) := UinfA ×ˢ Ufin
  have hUfullOpen : IsOpen Ufull := hUinfAOpen.prod hUfinOpen
  have hUfullZero : (0 : chapter07AdeleRing R K) ∈ Ufull := by
    refine ⟨hUinfAZero, ?_⟩
    intro v
    change (0 : chapter07LocalField R K v) ∈
      (chapter07LocalIntegerRing R K v : Set (chapter07LocalField R K v))
    exact (chapter07LocalIntegerRing R K v).zero_mem
  let V : Set (chapter07AdeleRing R K) :=
    (fun x : chapter07AdeleRing R K => x - 1) ⁻¹' Ufull
  have hVOpen : IsOpen V := by
    exact hUfullOpen.preimage (continuous_id.sub continuous_const)
  have hVOne : (1 : chapter07AdeleRing R K) ∈ V := by
    change (1 : chapter07AdeleRing R K) - 1 ∈ Ufull
    simpa using hUfullZero
  let W : Set (chapter07IdeleGroup R K) :=
    (fun x : chapter07IdeleGroup R K => (x : chapter07AdeleRing R K)) ⁻¹' V
  have hWOpen : IsOpen W := hVOpen.preimage Units.continuous_val
  have hWOne : (1 : chapter07IdeleGroup R K) ∈ W := by
    change (1 : chapter07AdeleRing R K) ∈ V
    exact hVOne
  have hUinfA_iff (x : NumberField.InfiniteAdeleRing K) :
      x ∈ UinfA ↔
        NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x ∈ Uinf := by
    rfl
  have hWInter :
      W ∩ (chapter07PrincipalIdeleSubgroup R K :
        Set (chapter07IdeleGroup R K)) = {1} := by
    ext x
    constructor
    · intro hx
      rcases (show x ∈ Set.range (chapter07PrincipalIdeleEmbedding R K) from hx.2) with
        ⟨a, rfl⟩
      let z : K := (a : K) - 1
      have hxV :
          (((chapter07PrincipalIdeleEmbedding R K a : chapter07IdeleGroup R K) :
            chapter07AdeleRing R K) - 1) ∈ Ufull := by
        simpa [W, V] using hx.1
      have hxV' :
          (((chapter07PrincipalIdeleEmbedding R K a : chapter07IdeleGroup R K) :
            chapter07AdeleRing R K) - 1) ∈ UinfA ×ˢ Ufin := by
        change
          (((chapter07PrincipalIdeleEmbedding R K a : chapter07IdeleGroup R K) :
              chapter07AdeleRing R K) - 1).1 ∈ UinfA ∧
            (((chapter07PrincipalIdeleEmbedding R K a : chapter07IdeleGroup R K) :
              chapter07AdeleRing R K) - 1).2 ∈ Ufin at hxV
        exact hxV
      have hxArch :
          (((chapter07PrincipalIdeleEmbedding R K a : chapter07IdeleGroup R K) :
            chapter07AdeleRing R K) - 1).1 ∈ UinfA := hxV'.1
      have hmix :
          NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K
              (((chapter07PrincipalIdeleEmbedding R K a : chapter07IdeleGroup R K) :
                chapter07AdeleRing R K) - 1).1 ∈ Uinf :=
        (hUinfA_iff _).1 hxArch
      have hprincipalInf :
          ((chapter07PrincipalIdeleEmbedding R K a : chapter07IdeleGroup R K) :
              chapter07AdeleRing R K).1 =
            algebraMap K (NumberField.InfiniteAdeleRing K) (a : K) := by
        rfl
      have hmix' : NumberField.mixedEmbedding K z ∈ Uinf := by
        have heq :
            NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K
                (((chapter07PrincipalIdeleEmbedding R K a : chapter07IdeleGroup R K) :
                  chapter07AdeleRing R K) - 1).1 =
                NumberField.mixedEmbedding K z := by
          have harch_sub :
              (((chapter07PrincipalIdeleEmbedding R K a : chapter07IdeleGroup R K) :
                chapter07AdeleRing R K) - 1).1 =
                algebraMap K (NumberField.InfiniteAdeleRing K) (a : K) - 1 := by
            change
              ((chapter07PrincipalIdeleEmbedding R K a : chapter07IdeleGroup R K) :
                chapter07AdeleRing R K).1 - 1 =
                algebraMap K (NumberField.InfiniteAdeleRing K) (a : K) - 1
            rw [hprincipalInf]
          rw [harch_sub]
          rw [NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
          simp [z]
        rw [← heq]
        exact hmix
      have hxFin : ∀ v : chapter07FinitePlace R,
          (((chapter07PrincipalIdeleEmbedding R K a : chapter07IdeleGroup R K) :
            chapter07AdeleRing R K) - 1).2 v ∈
            (chapter07LocalIntegerRing R K v :
              Set (chapter07LocalField R K v)) := by
        intro v
        have hv :
            (((chapter07PrincipalIdeleEmbedding R K a : chapter07IdeleGroup R K) :
              chapter07AdeleRing R K) - 1).2 ∈ Ufin := hxV'.2
        simpa [Ufin] using hv v
      have hzval : ∀ v : chapter07FinitePlace R, v.valuation K z ≤ 1 := by
        intro v
        have hvint :
            (algebraMap K (chapter07LocalField R K v) z) ∈
              (chapter07LocalIntegerRing R K v :
                Set (chapter07LocalField R K v)) := by
          have hv := hxFin v
          change ((chapter07PrincipalIdeleEmbedding R K a).1.2 v - 1) ∈
            (chapter07LocalIntegerRing R K v :
              Set (chapter07LocalField R K v)) at hv
          rw [chapter07PrincipalIdeleEmbedding_apply_finite R K a v] at hv
          simpa [z] using hv
        have hvval :=
          (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
            R K v).1 hvint
        have hvval' : Valued.v
            (z : chapter07LocalField R K v) ≤ 1 := by
          exact hvval
        simpa only [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
          (K := K) (v := v) z] using hvval'
      obtain ⟨r, hr⟩ :=
        IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
          (R := R) (K := K) z hzval
      have hzint : IsIntegral ℤ z := by
        rw [← hr]
        exact (IsIntegral.of_finite ℤ r).algebraMap
      obtain ⟨b, hb⟩ :=
        (IsIntegralClosure.isIntegral_iff
          (A := NumberField.RingOfIntegers K) (R := ℤ) (B := K)).1 hzint
      have hzlat : NumberField.mixedEmbedding K z ∈
          (NumberField.mixedEmbedding.integerLattice K :
            Set (NumberField.mixedEmbedding.mixedSpace K)) := by
        change ∃ c : NumberField.RingOfIntegers K,
          NumberField.mixedEmbedding K
              (algebraMap (NumberField.RingOfIntegers K) K c) =
            NumberField.mixedEmbedding K z
        exact ⟨b, by rw [hb]⟩
      have hzzero : NumberField.mixedEmbedding K z = 0 := by
        have hmem : NumberField.mixedEmbedding K z ∈ Uinf ∩
            (NumberField.mixedEmbedding.integerLattice K :
              Set (NumberField.mixedEmbedding.mixedSpace K)) :=
          ⟨hmix', hzlat⟩
        rw [hUinfInter] at hmem
        exact hmem
      have hz : z = 0 := NumberField.mixedEmbedding_injective K (by
        simpa only [map_zero] using hzzero)
      have ha : a = 1 := by
        apply Units.ext
        simpa [z] using sub_eq_zero.mp hz
      simp [ha]
    · intro hx
      have hx1 : x = 1 := Set.mem_singleton_iff.mp hx
      subst x
      refine ⟨hWOne, ?_⟩
      exact ⟨1, by simp [chapter07PrincipalIdeleEmbedding]⟩
  refine isDiscrete_iff_forall_mem_exists_isOpen.mpr ?_
  intro x hx
  rcases (show x ∈ Set.range (chapter07PrincipalIdeleEmbedding R K) from hx) with
    ⟨a, rfl⟩
  let h : chapter07IdeleGroup R K := chapter07PrincipalIdeleEmbedding R K a
  refine ⟨(fun y : chapter07IdeleGroup R K => y * h⁻¹) ⁻¹' W, ?_, ?_⟩
  · exact hWOpen.preimage (continuous_mul_const _)
  · ext y
    constructor
    · rintro ⟨hyW, hyH⟩
      change y * h⁻¹ ∈ W at hyW
      have hyH' : y * h⁻¹ ∈
          (chapter07PrincipalIdeleSubgroup R K :
            Set (chapter07IdeleGroup R K)) := by
        exact (chapter07PrincipalIdeleSubgroup R K).mul_mem hyH
          ((chapter07PrincipalIdeleSubgroup R K).inv_mem ⟨a, rfl⟩)
      have hyone : y * h⁻¹ = 1 := by
        apply Set.mem_singleton_iff.mp
        rw [← hWInter]
        exact ⟨hyW, hyH'⟩
      have hy : y = h := by
        have := congrArg (fun z => z * h) hyone
        simpa [mul_assoc] using this
      change y = chapter07PrincipalIdeleEmbedding R K a
      rw [hy]
    · intro hy
      have hy' : y = h := Set.mem_singleton_iff.mp hy
      subst y
      refine ⟨?_, ⟨a, rfl⟩⟩
      change h * h⁻¹ ∈ W
      simpa using hWOne

theorem chapter07_principal_ideles_are_closed
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    IsClosed (chapter07PrincipalIdeleSubgroup R K :
      Set (chapter07IdeleGroup R K)) := by
  let _ : DiscreteTopology (chapter07PrincipalIdeleSubgroup R K) :=
    isDiscrete_iff_discreteTopology.mp
      (chapter07_principal_ideles_are_discrete R K)
  let _ : ∀ v : NumberField.InfinitePlace K, T2Space v.Completion :=
    fun v => inferInstance
  let _ : ∀ v : chapter07FinitePlace R, T2Space (chapter07LocalField R K v) :=
    fun v => inferInstance
  let _ : T2Space (NumberField.InfiniteAdeleRing K) :=
    @Pi.t2Space (NumberField.InfinitePlace K) (fun v => v.Completion)
      (fun _ => inferInstance) (fun _ => inferInstance)
  let _ : T2Space (chapter07FiniteAdeleRing R K) :=
    T2Space.of_injective_continuous DFunLike.coe_injective RestrictedProduct.continuous_coe
  let _ : T2Space (chapter07AdeleRing R K) :=
    @Prod.t2Space (NumberField.InfiniteAdeleRing K) (chapter07FiniteAdeleRing R K)
      inferInstance inferInstance inferInstance inferInstance
  let _ : T2Space (chapter07IdeleGroup R K) :=
    (chapter07_ideleGraph_isEmbedding R K).t2Space
  exact Subgroup.isClosed_of_discrete

private theorem chapter07_card_of_involutive_generators
    {G : Type*} [CommGroup G] [Fintype G]
    (d : ℕ) (g : Fin d → G)
    (hg : Subgroup.closure (Set.range g) = ⊤)
    (hinv : ∀ i, g i * g i = 1) :
    Fintype.card G ≤ 2 ^ d := by
  classical
  let F : (Fin d → Bool) → G := fun a =>
    ∏ i, if a i then g i else 1
  have hmul (a b : Fin d → Bool) :
      F a * F b = F (fun i => Bool.xor (a i) (b i)) := by
    simp only [F]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases ha : a i = true <;> by_cases hb : b i = true <;>
      simp [ha, hb, Bool.xor, hinv i]
  have hone : F (fun _ => false) = 1 := by
    simp [F]
  have hsq (a : Fin d → Bool) : F a * F a = 1 := by
    simp only [F]
    rw [← Finset.prod_mul_distrib]
    have hcoord : ∀ i : Fin d,
        (if a i then g i else 1) * (if a i then g i else 1) = 1 := by
      intro i
      by_cases h : a i = true <;> simp [h, hinv i]
    simp_rw [hcoord]
    simp
  let H : Subgroup G :=
    { carrier := Set.range F
      one_mem' := ⟨fun _ => false, hone⟩
      mul_mem' := by
        intro x y hx hy
        rcases hx with ⟨a, rfl⟩
        rcases hy with ⟨b, rfl⟩
        exact ⟨fun i => Bool.xor (a i) (b i), (hmul a b).symm⟩
      inv_mem' := by
        intro x hx
        rcases hx with ⟨a, rfl⟩
        refine ⟨a, ?_⟩
        exact eq_inv_of_mul_eq_one_left (hsq a) }
  have hgen : Set.range g ⊆ H := by
    rintro x ⟨i, rfl⟩
    refine ⟨fun j => j = i, ?_⟩
    simp only [F]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j hj hji
      simp [hji]
    · simp
  have hH : H = ⊤ := by
    apply top_unique
    rw [← hg]
    exact (Subgroup.closure_le H).2 hgen
  have hsurj : Function.Surjective F := by
    intro x
    have hx : x ∈ H := by rw [hH]; trivial
    change x ∈ Set.range F at hx
    exact hx
  simpa using Fintype.card_le_of_surjective F hsurj

private theorem chapter07_global_units_fg
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    Group.FG Rˣ := by
  let : IsIntegrallyClosed R := IsDedekindRing.toIsIntegralClosure
  let : IsIntegralClosure R ℤ K :=
    IsIntegralClosure.of_isIntegrallyClosed R ℤ K
  let e : (𝓞 K) ≃+* R := NumberField.RingOfIntegers.equiv R
  have : Group.FG (𝓞 K)ˣ := by
    exact Group.fg_iff_monoid_fg.mpr (inferInstance : Monoid.FG (𝓞 K)ˣ)
  apply Group.fg_of_surjective (f := Units.map e.toMonoidHom)
  intro y
  refine ⟨Units.map e.symm.toMonoidHom y, ?_⟩
  apply Units.ext
  simp [e]

private noncomputable def chapter07OddPrimeOver
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Module.Finite ℤ R] [Module.Free ℤ R] (p : Nat.Primes) :
    Ideal.primesOver (Ideal.span {(p.1 : ℤ)}) R := by
  let P : Ideal ℤ := Ideal.span {(p.1 : ℤ)}
  letI : P.IsPrime := by
    exact Ideal.isPrime_span_singleton_of_prime
      (Nat.prime_iff_prime_int.1 p.2)
  exact Classical.choice (inferInstance : Nonempty (Ideal.primesOver P R))

private noncomputable def chapter07OddFinitePlace
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Module.Finite ℤ R] [Module.Free ℤ R] (p : Nat.Primes) :
    chapter07FinitePlace R := by
  let Q := chapter07OddPrimeOver R p
  exact ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver
    (by simpa using (show (p.1 : ℤ) ≠ 0 from Int.ofNat_ne_zero.mpr p.2.ne_zero)) Q.2⟩

private theorem chapter07OddFinitePlace_residue_char
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] (p : Nat.Primes) :
    ringChar (IsLocalRing.ResidueField
      (chapter07LocalIntegerRing R K (chapter07OddFinitePlace R p))) = p.1 := by
  apply CharP.ringChar_of_prime_eq_zero p.2
  apply (IsLocalRing.residue_eq_zero_iff
    (R := chapter07LocalIntegerRing R K (chapter07OddFinitePlace R p))
    (algebraMap ℤ (chapter07LocalIntegerRing R K
      (chapter07OddFinitePlace R p)) (p.1 : ℤ))).2
  rw [IsLocalRing.mem_maximalIdeal]
  change ¬ IsUnit (algebraMap ℤ (chapter07LocalIntegerRing R K
    (chapter07OddFinitePlace R p)) (p.1 : ℤ))
  intro hunit
  have hval :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (K := K) (v := chapter07OddFinitePlace R p)).1 hunit
  have hmem : (p.1 : ℤ) ∈ Ideal.span {(p.1 : ℤ)} := by simp
  have hmem' : algebraMap ℤ R (p.1 : ℤ) ∈
      (chapter07OddPrimeOver R p).1 := by
    let hLiesOver : (chapter07OddPrimeOver R p).1.LiesOver
        (Ideal.span {(p.1 : ℤ)}) := (chapter07OddPrimeOver R p).2.2
    exact (@Ideal.mem_of_liesOver (A := ℤ) (B := R)
      (inferInstance : CommSemiring ℤ) (inferInstance : Semiring R)
      (inferInstance : Algebra ℤ R) (chapter07OddPrimeOver R p).1
      (Ideal.span {(p.1 : ℤ)}) hLiesOver (p.1 : ℤ)).1 hmem
  have hlt : Valued.v
      (((algebraMap ℤ (chapter07LocalIntegerRing R K
        (chapter07OddFinitePlace R p)) (p.1 : ℤ) :
        chapter07LocalIntegerRing R K (chapter07OddFinitePlace R p)) :
        chapter07LocalField R K (chapter07OddFinitePlace R p))) < 1 := by
    have hcoemap :
        ((algebraMap ℤ (chapter07LocalIntegerRing R K
          (chapter07OddFinitePlace R p)) (p.1 : ℤ) :
          chapter07LocalIntegerRing R K (chapter07OddFinitePlace R p)) :
          chapter07LocalField R K (chapter07OddFinitePlace R p)) =
          algebraMap ℤ (chapter07LocalField R K (chapter07OddFinitePlace R p))
            (p.1 : ℤ) := by
      calc
        ((algebraMap ℤ (chapter07LocalIntegerRing R K
          (chapter07OddFinitePlace R p)) (p.1 : ℤ) :
          chapter07LocalIntegerRing R K (chapter07OddFinitePlace R p)) :
          chapter07LocalField R K (chapter07OddFinitePlace R p)) =
            ((p.1 : ℤ) : chapter07LocalField R K
              (chapter07OddFinitePlace R p)) := by
                exact congrArg (fun z : chapter07LocalIntegerRing R K
                  (chapter07OddFinitePlace R p) =>
                  (z : chapter07LocalField R K (chapter07OddFinitePlace R p)))
                  (map_intCast (algebraMap ℤ
                    (chapter07LocalIntegerRing R K
                      (chapter07OddFinitePlace R p))) (p.1 : ℤ))
        _ = algebraMap ℤ (chapter07LocalField R K
          (chapter07OddFinitePlace R p)) (p.1 : ℤ) := by
            symm
            exact map_intCast (algebraMap ℤ
              (chapter07LocalField R K (chapter07OddFinitePlace R p)))
              (p.1 : ℤ)
    rw [hcoemap]
    have hcoemapK :
        algebraMap ℤ (chapter07LocalField R K (chapter07OddFinitePlace R p))
            (p.1 : ℤ) =
          algebraMap K (chapter07LocalField R K (chapter07OddFinitePlace R p))
            (algebraMap ℤ K (p.1 : ℤ)) := by
      calc
        algebraMap ℤ (chapter07LocalField R K (chapter07OddFinitePlace R p))
            (p.1 : ℤ) = ((p.1 : ℤ) : chapter07LocalField R K
              (chapter07OddFinitePlace R p)) :=
          map_intCast (algebraMap ℤ
            (chapter07LocalField R K (chapter07OddFinitePlace R p))) (p.1 : ℤ)
        _ = algebraMap K (chapter07LocalField R K (chapter07OddFinitePlace R p))
            (algebraMap ℤ K (p.1 : ℤ)) := by
          symm
          simp
    rw [hcoemapK]
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, Algebra.algebraMap_self_apply]
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
      (K := K) (v := chapter07OddFinitePlace R p)
      (algebraMap ℤ K (p.1 : ℤ))]
    have hmap : algebraMap ℤ K (p.1 : ℤ) =
        algebraMap R K (algebraMap ℤ R (p.1 : ℤ)) := by
      simp
    rw [hmap]
    exact (chapter07OddFinitePlace R p).valuation_lt_one_iff_mem (K := K)
      (algebraMap ℤ R (p.1 : ℤ)) |>.2 hmem'
  exact (ne_of_lt hlt) hval

private theorem chapter07OddFinitePlace_injective
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    Function.Injective (chapter07OddFinitePlace R) := by
  intro p q hpq
  apply Subtype.ext
  calc
    p.1 = ringChar (IsLocalRing.ResidueField
      (chapter07LocalIntegerRing R K (chapter07OddFinitePlace R p))) :=
        (chapter07OddFinitePlace_residue_char R K p).symm
    _ = ringChar (IsLocalRing.ResidueField
      (chapter07LocalIntegerRing R K (chapter07OddFinitePlace R q))) := by
        rw [hpq]
    _ = q.1 := chapter07OddFinitePlace_residue_char R K q

private theorem chapter07_local_residue_continuous
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] (v : chapter07FinitePlace R) :
    @Continuous (chapter07LocalIntegerRing R K v)
      (IsLocalRing.ResidueField (chapter07LocalIntegerRing R K v)) inferInstance
      (⊥ : TopologicalSpace (IsLocalRing.ResidueField (chapter07LocalIntegerRing R K v)))
      (IsLocalRing.residue (chapter07LocalIntegerRing R K v)) := by
  let : TopologicalSpace (IsLocalRing.ResidueField (chapter07LocalIntegerRing R K v)) := ⊥
  let : DiscreteTopology
      (IsLocalRing.ResidueField (chapter07LocalIntegerRing R K v)) := ⟨rfl⟩
  let : CompactSpace (chapter07LocalIntegerRing R K v) := by
    constructor
    rw [Subtype.isCompact_iff]
    convert chapter07_finite_local_integer_isCompact R K v using 1
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  apply LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.chapter06_reduction_continuous
  exact IsLocalRing.isOpen_maximalIdeal _

private noncomputable def chapter07LocalResidueQuadraticHom
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] (v : chapter07FinitePlace R) :
    chapter07LocalIntegralUnitSubgroup R K v →* ℤˣ := by
  classical
  let F := IsLocalRing.ResidueField (chapter07LocalIntegerRing R K v)
  letI : Finite F := chapter07_finite_local_residueField_finite R K v
  letI : Fintype F := Fintype.ofFinite F
  exact (quadraticChar F).toUnitHom.comp
    ((Units.map (IsLocalRing.residue (chapter07LocalIntegerRing R K v)).toMonoidHom).comp
      (Submonoid.unitsEquivUnitsType
      (Submonoid.ofClass (chapter07LocalIntegerRing R K v))).toMonoidHom)

private theorem chapter07LocalResidueQuadraticHom_surjective
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] (p : Nat.Primes) (hp : p.1 ≠ 2) :
    Function.Surjective
      (chapter07LocalResidueQuadraticHom R K (chapter07OddFinitePlace R p)) := by
  classical
  let A := chapter07LocalIntegerRing R K (chapter07OddFinitePlace R p)
  let F := IsLocalRing.ResidueField A
  let : Finite F := chapter07_finite_local_residueField_finite R K _
  let : Fintype F := Fintype.ofFinite F
  intro z
  rcases Int.units_eq_one_or z with rfl | rfl
  · exact ⟨1, by simp [chapter07LocalResidueQuadraticHom]⟩
  · obtain ⟨b, hb⟩ := quadraticChar_exists_neg_one'
      (show ringChar F ≠ 2 by
        rw [chapter07OddFinitePlace_residue_char R K p]
        exact hp)
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (b : F)
    have hua : IsUnit a := by
      by_contra hna
      apply Units.ne_zero b
      rw [← ha]
      exact (IsLocalRing.residue_eq_zero_iff a).2 (by
        rw [IsLocalRing.mem_maximalIdeal]
        exact hna)
    let uA : Aˣ := hua.unit
    let u : chapter07LocalIntegralUnitSubgroup R K (chapter07OddFinitePlace R p) :=
      (Submonoid.unitsEquivUnitsType (Submonoid.ofClass A)).symm uA
    refine ⟨u, ?_⟩
    apply Units.ext
    change quadraticChar F (IsLocalRing.residue A (uA : A)) = -1
    rw [hua.unit_spec, ha]
    exact hb

private theorem chapter07LocalResidueQuadraticHom_continuous
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] (v : chapter07FinitePlace R) :
    Continuous (chapter07LocalResidueQuadraticHom R K v) := by
  classical
  let A := chapter07LocalIntegerRing R K v
  let F := IsLocalRing.ResidueField A
  let S := Submonoid.ofClass A
  let : TopologicalSpace F := ⊥
  let : DiscreteTopology F := ⟨rfl⟩
  let : Finite F := chapter07_finite_local_residueField_finite R K v
  let : Fintype F := Fintype.ofFinite F
  let q := chapter07LocalResidueQuadraticHom R K v
  have hA : Continuous (fun x : S.units =>
      (⟨(x.1 : chapter07LocalField R K v), x.property.1⟩ : A)) := by
    exact (Units.continuous_val.comp continuous_subtype_val).subtype_mk _
  have hres : Continuous (fun x : S.units =>
      IsLocalRing.residue A
        (⟨(x.1 : chapter07LocalField R K v), x.property.1⟩ : A)) :=
    (chapter07_local_residue_continuous R K v).comp hA
  have hqval : Continuous (fun x : S.units => ((q x : ℤˣ) : ℤ)) := by
    have hquad : Continuous (fun y : F => (quadraticChar F y : ℤ)) :=
      continuous_of_discreteTopology
    change Continuous (fun x : S.units =>
      (quadraticChar F
        (IsLocalRing.residue A
          (⟨(x.1 : chapter07LocalField R K v), x.property.1⟩ : A)) : ℤ))
    exact hquad.comp hres
  rw [Units.continuous_iff]
  refine ⟨hqval, ?_⟩
  have hqval' := hqval.comp (continuous_inv :
      Continuous (fun x : S.units => x⁻¹))
  exact hqval'.congr (by
    intro x
    change ((q (x⁻¹) : ℤˣ) : ℤ) = ((q x)⁻¹ : ℤˣ)
    rw [map_inv])

private noncomputable def chapter07FiniteResidueQuadraticHom
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    {n : ℕ} (v : Fin n → chapter07FinitePlace R) :
    chapter07FiniteIntegralUnitSubgroup R K →* (Fin n → ℤˣ) := by
  classical
  exact
    { toFun := fun x i =>
        chapter07LocalResidueQuadraticHom R K (v i)
          ⟨chapter07FiniteIdeleEquiv R K (x : chapter07FiniteIdeleGroup R K) (v i),
            x.property (v i)⟩
      map_one' := by
        funext i
        change chapter07LocalResidueQuadraticHom R K (v i) 1 = 1
        exact map_one _
      map_mul' := by
        intro x y
        funext i
        let xi : chapter07LocalIntegralUnitSubgroup R K (v i) :=
          ⟨chapter07FiniteIdeleEquiv R K (x : chapter07FiniteIdeleGroup R K) (v i),
            x.property (v i)⟩
        let yi : chapter07LocalIntegralUnitSubgroup R K (v i) :=
          ⟨chapter07FiniteIdeleEquiv R K (y : chapter07FiniteIdeleGroup R K) (v i),
            y.property (v i)⟩
        have hxy :
            (⟨chapter07FiniteIdeleEquiv R K (x * y : chapter07FiniteIdeleGroup R K)
                (v i), (x * y).property (v i)⟩ :
              chapter07LocalIntegralUnitSubgroup R K (v i)) = xi * yi := by
          apply Subtype.ext
          rfl
        change chapter07LocalResidueQuadraticHom R K (v i)
            (⟨chapter07FiniteIdeleEquiv R K (x * y : chapter07FiniteIdeleGroup R K)
                (v i), (x * y).property (v i)⟩ :
              chapter07LocalIntegralUnitSubgroup R K (v i)) =
          chapter07LocalResidueQuadraticHom R K (v i) xi *
            chapter07LocalResidueQuadraticHom R K (v i) yi
        rw [hxy, map_mul] }

private noncomputable def chapter07LocalResidueQuadraticFiber
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    (v : chapter07FinitePlace R) (c : ℤˣ) :
    Set ((chapter07LocalField R K v)ˣ) :=
  (fun x : chapter07LocalIntegralUnitSubgroup R K v =>
      (x : (chapter07LocalField R K v)ˣ)) ''
    ((chapter07LocalResidueQuadraticHom R K v) ⁻¹' ({c} : Set ℤˣ))

private theorem chapter07LocalResidueQuadraticFiber_isOpen
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    (v : chapter07FinitePlace R) (c : ℤˣ) :
    IsOpen (chapter07LocalResidueQuadraticFiber R K v c) := by
  have hlocal : IsOpen (chapter07LocalIntegerRing R K v :
      Set (chapter07LocalField R K v)) := Valued.isOpen_valuationSubring _
  have hsub : IsOpen (chapter07LocalIntegralUnitSubgroup R K v :
      Set ((chapter07LocalField R K v)ˣ)) :=
    Submonoid.isOpen_units hlocal
  exact hsub.isOpenEmbedding_subtypeVal.isOpenMap _
    ((chapter07LocalResidueQuadraticHom_continuous R K v).isOpen_preimage _
      (isOpen_discrete _))

private noncomputable def chapter07SelectedResidueValue
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    {n : ℕ} (v : Fin n → chapter07FinitePlace R)
    (z : Fin n → ℤˣ) (w : chapter07FinitePlace R) : ℤˣ :=
  by
    classical
    exact if h : ∃ i, v i = w then z (Classical.choose h) else 1

private theorem chapter07SelectedResidueValue_at
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    {n : ℕ} (v : Fin n → chapter07FinitePlace R)
    (z : Fin n → ℤˣ) (hv : Function.Injective v) (i : Fin n) :
    chapter07SelectedResidueValue R v z (v i) = z i := by
  classical
  simp only [chapter07SelectedResidueValue]
  split <;> rename_i h
  · have hci : Classical.choose h = i := hv (Classical.choose_spec h)
    simp [hci]
  · exact (h ⟨i, rfl⟩).elim

private theorem chapter07FiniteResidueBasicOpen_isOpen
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    {n : ℕ} (v : Fin n → chapter07FinitePlace R) (z : Fin n → ℤˣ) :
    IsOpen (chapter07RestrictedProductBasicOpen
      (fun w : chapter07FinitePlace R => (chapter07LocalField R K w)ˣ)
      (fun w : chapter07FinitePlace R =>
        chapter07LocalIntegralUnitSubgroup R K w)
      (Set.range v)
      (fun w => chapter07LocalResidueQuadraticFiber R K w
        (chapter07SelectedResidueValue R v z w))) := by
  apply chapter07_restrictedProduct_basicOpen_isOpen
    (fun w : chapter07FinitePlace R => (chapter07LocalField R K w)ˣ)
    (fun w : chapter07FinitePlace R =>
      chapter07LocalIntegralUnitSubgroup R K w)
    (Set.range v) (Set.finite_range v)
    (fun w => chapter07LocalResidueQuadraticFiber R K w
      (chapter07SelectedResidueValue R v z w))
  · intro w
    exact chapter07LocalResidueQuadraticFiber_isOpen R K w _
  · intro w
    have hlocal : IsOpen (chapter07LocalIntegerRing R K w :
        Set (chapter07LocalField R K w)) := Valued.isOpen_valuationSubring _
    exact Submonoid.isOpen_units hlocal

private theorem chapter07_finite_principal_in_integral_units_is_global_unit
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (a : Kˣ)
    (ha : chapter07FinitePrincipalIdeleEmbedding R K a ∈
      chapter07FiniteIntegralUnitSubgroup R K) :
    ∃ b : Rˣ, Units.map (algebraMap R K).toMonoidHom b = a := by
  have hval : ∀ v : chapter07FinitePlace R, v.valuation K (a : K) = 1 := by
    intro v
    have hv := (chapter07_finiteIntegralUnits_valued_iff R K
      (chapter07FinitePrincipalIdeleEmbedding R K a)).1 ha v
    change Valued.v (algebraMap K (chapter07LocalField R K v) (a : K)) = 1 at hv
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion] at hv
    simp only [Function.comp_apply] at hv
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    exact hv
  have haR : (a : K) ∈ (algebraMap R K).range := by
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K
    intro v
    exact (hval v).le
  have hainv : (a⁻¹ : K) ∈ (algebraMap R K).range := by
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K
    intro v
    rw [map_inv₀, hval v, inv_one]
  rcases haR with ⟨r, hr⟩
  rcases hainv with ⟨s, hs⟩
  have hrs : r * s = 1 := by
    apply IsFractionRing.injective R K
    rw [map_mul, hr, hs]
    simp
  let b : Rˣ :=
    { val := r
      inv := s
      val_inv := hrs
      inv_val := by rw [mul_comm, hrs] }
  refine ⟨b, ?_⟩
  apply Units.ext
  change algebraMap R K r = (a : K)
  exact hr

theorem chapter07_finite_principal_ideles_are_not_dense
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    ¬ DenseRange (chapter07FinitePrincipalIdeleEmbedding R K) := by
  classical
  intro hden
  rcases (Group.fg_iff').1 (chapter07_global_units_fg R K) with
    ⟨d, S, hScard, hSgen⟩
  let eS : S ≃ Fin d := S.equivFinOfCardEq hScard
  let g : Fin d → Rˣ := fun i => eS.symm i
  have hgrange : Set.range g = (S : Set Rˣ) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (eS.symm i).property
    · intro hx
      exact ⟨eS ⟨x, hx⟩, by simp [g]⟩
  have hggen : Subgroup.closure (Set.range g) = (⊤ : Subgroup Rˣ) := by
    rw [hgrange]
    exact hSgen
  let P : Set Nat.Primes := Set.univ \ {⟨2, Nat.prime_two⟩}
  have hP : P.Infinite := by
    have h := Set.Infinite.sdiff (Set.infinite_univ :
        (Set.univ : Set Nat.Primes).Infinite)
      (Set.finite_singleton (⟨2, Nat.prime_two⟩ : Nat.Primes))
    exact h
  let ep : ℕ ↪ P := hP.natEmbedding
  let n := d + 1
  let v : Fin n → chapter07FinitePlace R := fun i =>
    chapter07OddFinitePlace R (ep i).1
  have hv_inj : Function.Injective v := by
    intro i j hij
    have hpq : (ep i) = (ep j) := by
      apply Subtype.ext
      exact chapter07OddFinitePlace_injective R K hij
    exact Fin.ext (ep.injective hpq)
  have hv_odd (i : Fin n) : ((ep i).1).1 ≠ 2 := by
    have hpq : (ep i).1 ≠ (⟨2, Nat.prime_two⟩ : Nat.Primes) := by
      intro heq
      exact (ep i).2.2 heq
    intro h
    apply hpq
    apply Subtype.ext
    exact h
  let Q := chapter07FiniteResidueQuadraticHom R K v
  have hQsurj : Function.Surjective Q := by
    intro z
    have hlocal : ∀ i : Fin n, ∃ u :
        chapter07LocalIntegralUnitSubgroup R K (v i),
        chapter07LocalResidueQuadraticHom R K (v i) u = z i := by
      intro i
      simpa [v] using
        (chapter07LocalResidueQuadraticHom_surjective R K (ep i).1
          (hv_odd i) (z i))
    choose u hu using hlocal
    let r : chapter07FiniteIdeleRestrictedProduct R K :=
      ∏ i : Fin n,
        RestrictedProduct.mulSingle
          (fun w : chapter07FinitePlace R =>
            chapter07LocalIntegralUnitSubgroup R K w)
          (v i) (u i : (chapter07LocalField R K (v i))ˣ)
    have hri (i : Fin n) (w : chapter07FinitePlace R) :
        (RestrictedProduct.mulSingle
          (fun w : chapter07FinitePlace R =>
            chapter07LocalIntegralUnitSubgroup R K w)
          (v i) (u i : (chapter07LocalField R K (v i))ˣ)) w ∈
          chapter07LocalIntegralUnitSubgroup R K w := by
      by_cases hwi : w = v i
      · subst w
        simpa only [RestrictedProduct.mulSingle_eq_same] using (u i).property
      · simp [RestrictedProduct.coe_mulSingle_apply, Pi.mulSingle_eq_of_ne hwi]
    have hrmem (w : chapter07FinitePlace R) : r w ∈
        chapter07LocalIntegralUnitSubgroup R K w := by
      dsimp [r]
      have hprod (s : Finset (Fin n)) :
          (s.prod (fun i => RestrictedProduct.mulSingle
              (fun w : chapter07FinitePlace R =>
                chapter07LocalIntegralUnitSubgroup R K w)
              (v i) (u i : (chapter07LocalField R K (v i))ˣ))) w =
            s.prod (fun i => (RestrictedProduct.mulSingle
                (fun w : chapter07FinitePlace R =>
                  chapter07LocalIntegralUnitSubgroup R K w)
                (v i) (u i : (chapter07LocalField R K (v i))ˣ)) w) := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih =>
            rw [Finset.prod_insert ha, Finset.prod_insert ha,
              RestrictedProduct.mul_apply, ih]
      rw [hprod Finset.univ]
      exact (chapter07LocalIntegralUnitSubgroup R K w).prod_mem
        (fun i hi => hri i w)
    let x : chapter07FiniteIdeleGroup R K :=
      (chapter07FiniteIdeleEquiv R K).symm r
    have hxmem : x ∈ chapter07FiniteIntegralUnitSubgroup R K := by
      rw [chapter07_mem_finiteIntegralUnitSubgroup_iff]
      intro w
      change chapter07FiniteIdeleEquiv R K x w ∈
        chapter07LocalIntegralUnitSubgroup R K w
      rw [show chapter07FiniteIdeleEquiv R K x = r by
        exact (chapter07FiniteIdeleEquiv R K).apply_symm_apply r]
      exact hrmem w
    refine ⟨⟨x, hxmem⟩, ?_⟩
    funext i
    have hri_coord : r (v i) = (u i : (chapter07LocalField R K (v i))ˣ) := by
      dsimp [r]
      have hprod (s : Finset (Fin n)) :
          (s.prod (fun j => RestrictedProduct.mulSingle
              (fun w : chapter07FinitePlace R =>
                chapter07LocalIntegralUnitSubgroup R K w)
              (v j) (u j : (chapter07LocalField R K (v j))ˣ))) (v i) =
            s.prod (fun j => (RestrictedProduct.mulSingle
                (fun w : chapter07FinitePlace R =>
                  chapter07LocalIntegralUnitSubgroup R K w)
                (v j) (u j : (chapter07LocalField R K (v j))ˣ)) (v i)) := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih =>
            rw [Finset.prod_insert ha, Finset.prod_insert ha,
              RestrictedProduct.mul_apply, ih]
      rw [hprod Finset.univ]
      rw [Finset.prod_eq_single i]
      · simp [RestrictedProduct.coe_mulSingle_apply]
      · intro j hj hji
        simp [RestrictedProduct.coe_mulSingle_apply,
          Pi.mulSingle_eq_of_ne (hv_inj.ne hji).symm]
      · simp
    let xH : chapter07FiniteIntegralUnitSubgroup R K := ⟨x, hxmem⟩
    have hxi :
        (⟨chapter07FiniteIdeleEquiv R K x (v i), xH.property (v i)⟩ :
          chapter07LocalIntegralUnitSubgroup R K (v i)) = u i := by
      apply Subtype.ext
      calc
        (chapter07FiniteIdeleEquiv R K x) (v i) = r (v i) := by
          exact congrArg (fun y : chapter07FiniteIdeleRestrictedProduct R K => y (v i))
            ((chapter07FiniteIdeleEquiv R K).apply_symm_apply r)
        _ = u i := hri_coord
    change chapter07LocalResidueQuadraticHom R K (v i)
        (⟨chapter07FiniteIdeleEquiv R K x (v i), xH.property (v i)⟩ :
          chapter07LocalIntegralUnitSubgroup R K (v i)) = z i
    rw [hxi]
    exact hu i
  have hglobal_mem (a : Rˣ) :
      chapter07FinitePrincipalIdeleEmbedding R K
          (Units.map (algebraMap R K).toMonoidHom a) ∈
        chapter07FiniteIntegralUnitSubgroup R K := by
    apply (chapter07_finiteIntegralUnits_valued_iff R K _).2
    intro w
    let au : (chapter07LocalIntegerRing R K w)ˣ :=
      Units.map (algebraMap R (chapter07LocalIntegerRing R K w)).toMonoidHom a
    let auF : (chapter07LocalField R K w)ˣ :=
      Units.map (algebraMap (chapter07LocalIntegerRing R K w)
        (chapter07LocalField R K w)).toMonoidHom au
    have hav : Valued.v (auF : chapter07LocalField R K w) = 1 := by
      change Valued.v ((au : chapter07LocalIntegerRing R K w) :
        chapter07LocalField R K w) = 1
      exact
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).1
          au.isUnit
    have hcoord :
        chapter07FiniteIdeleEquiv R K
            (chapter07FinitePrincipalIdeleEmbedding R K
              (Units.map (algebraMap R K).toMonoidHom a)) w = auF := by
      apply Units.ext
      change algebraMap K (chapter07LocalField R K w)
          (algebraMap R K (a : R)) =
        (algebraMap (chapter07LocalIntegerRing R K w)
          (chapter07LocalField R K w)
          (algebraMap R (chapter07LocalIntegerRing R K w) (a : R)))
      rw [← IsScalarTower.algebraMap_apply R K (chapter07LocalField R K w)]
      rw [IsScalarTower.algebraMap_apply R (chapter07LocalIntegerRing R K w)
        (chapter07LocalField R K w)]
    rw [hcoord]
    exact hav
  let pR : Rˣ →* chapter07FiniteIdeleGroup R K :=
    (chapter07FinitePrincipalIdeleEmbedding R K).comp
      (Units.map (algebraMap R K).toMonoidHom)
  let Punit : Rˣ →* chapter07FiniteIntegralUnitSubgroup R K :=
    { toFun := fun a => ⟨pR a, hglobal_mem a⟩
      map_one' := by
        apply Subtype.ext
        exact map_one pR
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact map_mul pR a b }
  let G : Rˣ →* (Fin n → ℤˣ) := Q.comp Punit
  have hGnot : ¬ Function.Surjective G := by
    intro hG
    have himage : G '' Set.range g = Set.range (fun i => G (g i)) := by
      ext y
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨g i, ⟨i, rfl⟩, rfl⟩
    have hclosure :
        Subgroup.closure (Set.range (fun i : Fin d => G (g i))) =
          (⊤ : Subgroup (Fin n → ℤˣ)) := by
      rw [← himage, ← MonoidHom.map_closure G (Set.range g), hggen]
      exact Subgroup.map_top_of_surjective G hG
    have hinv : ∀ i : Fin d,
        (fun j : Fin n => G (g i) j) * (fun j : Fin n => G (g i) j) = 1 := by
      intro i
      funext j
      rw [← pow_two]
      exact Int.units_sq (G (g i) j)
    have hcard := chapter07_card_of_involutive_generators d
      (fun i => G (g i)) hclosure hinv
    have hcard' : 2 ^ n ≤ 2 ^ d := by
      calc
        2 ^ n = Fintype.card (Fin n → ℤˣ) := by
          rw [Fintype.card_pi_const, Fintype.card_units_int]
        _ ≤ 2 ^ d := hcard
    have hpow : 2 ^ (d + 1) ≤ 2 ^ d := by
      simpa [n] using hcard'
    have hlt : 2 ^ d < 2 ^ (d + 1) := by
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℕ) < 2) d]
    exact (Nat.not_lt_of_ge hpow) hlt
  obtain ⟨z0, hz0⟩ : ∃ z0 : Fin n → ℤˣ, z0 ∉ Set.range G := by
    by_contra h
    apply hGnot
    intro z
    have hz : z ∈ Set.range G := by
      by_contra hz
      exact h ⟨z, hz⟩
    exact hz
  obtain ⟨y, hy⟩ := hQsurj z0
  let B : Set (chapter07FiniteIdeleRestrictedProduct R K) :=
    chapter07RestrictedProductBasicOpen
      (fun w : chapter07FinitePlace R => (chapter07LocalField R K w)ˣ)
      (fun w : chapter07FinitePlace R =>
        chapter07LocalIntegralUnitSubgroup R K w)
      (Set.range v)
      (fun w => chapter07LocalResidueQuadraticFiber R K w
        (chapter07SelectedResidueValue R v z0 w))
  have hBopen : IsOpen B := by
    dsimp [B]
    exact chapter07FiniteResidueBasicOpen_isOpen R K v z0
  have he_inducing : IsInducing (chapter07FiniteIdeleEquiv R K) :=
    ⟨chapter07_finiteIdele_restrictedProduct_topology R K⟩
  have he : Continuous (chapter07FiniteIdeleEquiv R K) :=
    he_inducing.continuous
  let O : Set (chapter07FiniteIdeleGroup R K) :=
    (chapter07FiniteIdeleEquiv R K) ⁻¹' B
  have hOopen : IsOpen O := by
    dsimp [O]
    exact hBopen.preimage he
  have hyB : chapter07FiniteIdeleEquiv R K (y : chapter07FiniteIdeleGroup R K) ∈ B := by
    change
      (∀ w ∈ Set.range v,
        chapter07FiniteIdeleEquiv R K (y : chapter07FiniteIdeleGroup R K) w ∈
          chapter07LocalResidueQuadraticFiber R K w
            (chapter07SelectedResidueValue R v z0 w)) ∧
      ∀ w ∉ Set.range v,
        chapter07FiniteIdeleEquiv R K (y : chapter07FiniteIdeleGroup R K) w ∈
          chapter07LocalIntegralUnitSubgroup R K w
    constructor
    · intro w hw
      rcases hw with ⟨i, rfl⟩
      let yi : chapter07LocalIntegralUnitSubgroup R K (v i) :=
        ⟨chapter07FiniteIdeleEquiv R K (y : chapter07FiniteIdeleGroup R K) (v i),
          y.property (v i)⟩
      refine ⟨yi, ?_, rfl⟩
      change chapter07LocalResidueQuadraticHom R K (v i) yi =
        chapter07SelectedResidueValue R v z0 (v i)
      rw [chapter07SelectedResidueValue_at R v z0 hv_inj i]
      exact congrFun hy i
    · intro w hw
      exact y.property w
  have hyO : (y : chapter07FiniteIdeleGroup R K) ∈ O := hyB
  obtain ⟨a, haO⟩ := hden.exists_mem_open hOopen ⟨y, hyO⟩
  change chapter07FiniteIdeleEquiv R K
      (chapter07FinitePrincipalIdeleEmbedding R K a) ∈ B at haO
  have haH : chapter07FinitePrincipalIdeleEmbedding R K a ∈
      chapter07FiniteIntegralUnitSubgroup R K := by
    apply (chapter07_mem_finiteIntegralUnitSubgroup_iff R K _).2
    intro w
    by_cases hw : w ∈ Set.range v
    · rcases hw with ⟨i, rfl⟩
      have hi := haO.1 (v i) ⟨i, rfl⟩
      rcases hi with ⟨u, hu, hcoord⟩
      rw [← hcoord]
      exact u.property
    · exact haO.2 w hw
  let xA : chapter07FiniteIntegralUnitSubgroup R K :=
    ⟨chapter07FinitePrincipalIdeleEmbedding R K a, haH⟩
  have hQa : Q xA = z0 := by
    funext i
    have hi := haO.1 (v i) ⟨i, rfl⟩
    rcases hi with ⟨u, hu, hcoord⟩
    let xi : chapter07LocalIntegralUnitSubgroup R K (v i) :=
      ⟨chapter07FiniteIdeleEquiv R K
          (chapter07FinitePrincipalIdeleEmbedding R K a) (v i),
        haH (v i)⟩
    have hxi : xi = u := by
      apply Subtype.ext
      exact hcoord.symm
    have hu' : chapter07LocalResidueQuadraticHom R K (v i) u =
        chapter07SelectedResidueValue R v z0 (v i) := by
      change chapter07LocalResidueQuadraticHom R K (v i) u ∈
        ({chapter07SelectedResidueValue R v z0 (v i)} : Set ℤˣ) at hu
      simpa using hu
    change chapter07LocalResidueQuadraticHom R K (v i) xi = z0 i
    rw [hxi, hu', chapter07SelectedResidueValue_at R v z0 hv_inj i]
  obtain ⟨b, hba⟩ :=
    chapter07_finite_principal_in_integral_units_is_global_unit R K a haH
  have hPunit : Punit b = xA := by
    apply Subtype.ext
    change pR b = chapter07FinitePrincipalIdeleEmbedding R K a
    dsimp [pR]
    exact congrArg (chapter07FinitePrincipalIdeleEmbedding R K) hba
  have hGb : G b = z0 := by
    change Q (Punit b) = z0
    rw [hPunit]
    exact hQa
  exact hz0 ⟨b, hGb⟩

theorem chapter07_finite_principal_ideles_have_finite_order_restrictions
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (a : Kˣ) :
    ∀ᶠ v : chapter07FinitePlace R in cofinite,
      Valued.v ((chapter07FinitePrincipalIdeleEmbedding R K a).1 v) = 1 := by
  have ha : IsUnit ((chapter07FinitePrincipalIdeleEmbedding R K a :
      chapter07FiniteAdeleRing R K)) :=
    (chapter07FinitePrincipalIdeleEmbedding R K a).isUnit
  exact (IsDedekindDomain.FiniteAdeleRing.isUnit_iff.mp ha).2

/-- The idele class group `C_K = A_K^× / K^×`. -/
abbrev chapter07IdeleClassGroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  chapter07IdeleGroup R K ⧸ chapter07PrincipalIdeleSubgroup R K

def chapter07IdeleClassProjection
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    chapter07IdeleGroup R K →* chapter07IdeleClassGroup R K :=
  QuotientGroup.mk' (chapter07PrincipalIdeleSubgroup R K)

instance chapter07_idele_class_group_is_comm_group
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    CommGroup (chapter07IdeleClassGroup R K) := by
  infer_instance

theorem chapter07_idele_class_group_is_topological_group
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    IsTopologicalGroup (chapter07IdeleClassGroup R K) := by
  infer_instance

theorem chapter07_idele_class_projection_kernel
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    (chapter07IdeleClassProjection R K).ker =
      chapter07PrincipalIdeleSubgroup R K := by
  exact QuotientGroup.ker_mk' _

theorem chapter07_idele_class_group_is_locally_compact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    LocallyCompactSpace (chapter07IdeleClassGroup R K) := by
  exact @QuotientGroup.instLocallyCompactSpace
    (chapter07IdeleGroup R K) inferInstance inferInstance inferInstance
    (chapter07_idele_group_is_locally_compact R K)
    (chapter07PrincipalIdeleSubgroup R K)

theorem chapter07_idele_class_group_is_hausdorff
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    T2Space (chapter07IdeleClassGroup R K) := by
  exact @QuotientGroup.instT2Space
    (chapter07IdeleGroup R K) inferInstance inferInstance inferInstance
    (chapter07PrincipalIdeleSubgroup R K)
    (chapter07_principal_ideles_are_closed R K)

/-- The quotient's positive-size witness.  The usual construction is the product of normalized
local absolute values; the product formula makes it trivial on principal ideles. -/
structure Chapter07IdeleClassSizeWitness
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] where
  size : chapter07IdeleClassGroup R K →* ℝ≥0ˣ
  continuous_size : Continuous size
  nontrivial : ∃ c : chapter07IdeleClassGroup R K, size c ≠ 1

private noncomputable def chapter07NormUnit
    {F : Type*} [NormedField F] (u : Fˣ) : ℝ≥0ˣ :=
  Units.mk0 ‖(u : F)‖₊ (by simp [Units.ne_zero u])

private theorem chapter07NormUnit_mul
    {F : Type*} [NormedField F] (u w : Fˣ) :
    chapter07NormUnit (u * w) = chapter07NormUnit u * chapter07NormUnit w := by
  ext
  simp [chapter07NormUnit]

private theorem chapter07NormUnit_one
    {F : Type*} [NormedField F] :
    chapter07NormUnit (1 : Fˣ) = 1 := by
  ext
  simp [chapter07NormUnit]

private noncomputable def chapter07InfiniteNormModuleHom
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    chapter07IdeleGroup R K →* ℝ≥0ˣ where
  toFun x := ∏ v : NumberField.InfinitePlace K,
    chapter07NormUnit (chapter07IdeleInfiniteCoordinate R K x v) ^ v.mult
  map_one' := by
    have hone : ∀ v : NumberField.InfinitePlace K,
        chapter07IdeleInfiniteCoordinate R K 1 v = 1 := by
      intro v
      apply Units.ext
      change (1 : v.Completion) = 1
      rfl
    simp_rw [hone]
    simp [chapter07NormUnit_one]
  map_mul' := by
    intro x y
    have hcoord : ∀ v : NumberField.InfinitePlace K,
        chapter07NormUnit (chapter07IdeleInfiniteCoordinate R K (x * y) v) ^ v.mult =
          (chapter07NormUnit (chapter07IdeleInfiniteCoordinate R K x v) ^ v.mult) *
            (chapter07NormUnit (chapter07IdeleInfiniteCoordinate R K y v) ^ v.mult) := by
      intro v
      have hxy : chapter07IdeleInfiniteCoordinate R K (x * y) v =
          chapter07IdeleInfiniteCoordinate R K x v *
            chapter07IdeleInfiniteCoordinate R K y v := by
        apply Units.ext
        change x.1.1 v * y.1.1 v = x.1.1 v * y.1.1 v
        rfl
      rw [hxy, chapter07NormUnit_mul, mul_pow]
    calc
      (∏ v : NumberField.InfinitePlace K,
          chapter07NormUnit (chapter07IdeleInfiniteCoordinate R K (x * y) v) ^ v.mult) =
        ∏ v : NumberField.InfinitePlace K,
          (chapter07NormUnit (chapter07IdeleInfiniteCoordinate R K x v) ^ v.mult) *
            (chapter07NormUnit (chapter07IdeleInfiniteCoordinate R K y v) ^ v.mult) := by
          apply Finset.prod_congr rfl
          intro v hv
          exact hcoord v
      _ = _ := Finset.prod_mul_distrib

private theorem chapter07NormUnit_eq_one_of_mem_localIntegralUnit
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    (v : chapter07FinitePlace R) (u : (chapter07LocalField R K v)ˣ)
    (hu : u ∈ chapter07LocalIntegralUnitSubgroup R K v) :
    chapter07NormUnit u = 1 := by
  ext
  simp only [chapter07NormUnit, Units.val_mk0]
  have hv : Valued.v (u : chapter07LocalField R K v) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).1 hu
  rw [coe_nnnorm]
  rw [NumberField.FinitePlace.norm_def]
  simp [hv]

private theorem chapter07FiniteNormUnit_hasFiniteMulSupport
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    (x : chapter07FiniteIdeleGroup R K) :
    Function.HasFiniteMulSupport (fun v : chapter07FinitePlace R =>
      chapter07NormUnit (chapter07FiniteIdeleEquiv R K x v)) := by
  have hbad : {v : chapter07FinitePlace R |
      chapter07FiniteIdeleEquiv R K x v ∉
        chapter07LocalIntegralUnitSubgroup R K v}.Finite :=
    Filter.eventually_cofinite.mp (chapter07FiniteIdeleEquiv R K x).2
  apply hbad.subset
  intro v hv
  by_contra hmem
  apply hv
  have hmem' : chapter07FiniteIdeleEquiv R K x v ∈
      chapter07LocalIntegralUnitSubgroup R K v := by
    simpa using hmem
  exact chapter07NormUnit_eq_one_of_mem_localIntegralUnit R K v
    (chapter07FiniteIdeleEquiv R K x v) hmem'

private noncomputable def chapter07FiniteNormModuleHom
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    chapter07FiniteIdeleGroup R K →* ℝ≥0ˣ where
  toFun x := ∏ᶠ v : chapter07FinitePlace R,
    chapter07NormUnit (chapter07FiniteIdeleEquiv R K x v)
  map_one' := by
    simp [chapter07NormUnit_one]
  map_mul' := by
    intro x y
    have hcoord : ∀ v : chapter07FinitePlace R,
        chapter07NormUnit (chapter07FiniteIdeleEquiv R K (x * y) v) =
          chapter07NormUnit (chapter07FiniteIdeleEquiv R K x v) *
            chapter07NormUnit (chapter07FiniteIdeleEquiv R K y v) := by
      intro v
      rw [(chapter07FiniteIdeleEquiv R K).map_mul]
      change chapter07NormUnit
          (chapter07FiniteIdeleEquiv R K x v * chapter07FiniteIdeleEquiv R K y v) = _
      rw [chapter07NormUnit_mul]
    calc
      (∏ᶠ v : chapter07FinitePlace R,
          chapter07NormUnit (chapter07FiniteIdeleEquiv R K (x * y) v)) =
        ∏ᶠ v : chapter07FinitePlace R,
          chapter07NormUnit (chapter07FiniteIdeleEquiv R K x v) *
            chapter07NormUnit (chapter07FiniteIdeleEquiv R K y v) :=
        finprod_congr hcoord
      _ = _ := finprod_mul_distrib
        (chapter07FiniteNormUnit_hasFiniteMulSupport R K x)
        (chapter07FiniteNormUnit_hasFiniteMulSupport R K y)

private noncomputable def chapter07IdeleFiniteProjection
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    chapter07IdeleGroup R K →* chapter07FiniteIdeleGroup R K :=
  Units.map (RingHom.snd (NumberField.InfiniteAdeleRing K)
    (chapter07FiniteAdeleRing R K)).toMonoidHom

private noncomputable def chapter07IdeleModuleHom
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    chapter07IdeleGroup R K →* ℝ≥0ˣ :=
  chapter07InfiniteNormModuleHom R K *
    (chapter07FiniteNormModuleHom R K).comp (chapter07IdeleFiniteProjection R K)

private theorem chapter07FiniteNorm_principal_eq_embedding_norm
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    (v : chapter07FinitePlace R) (a : K) :
    ‖algebraMap K (chapter07LocalField R K v) a‖ =
    ‖NumberField.FinitePlace.embedding v a‖ := by
  rfl

private theorem chapter07FinitePrincipalNormProduct_integral
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    {r : R} (hr : r ≠ 0) :
    (∏ᶠ v : chapter07FinitePlace R,
      ‖NumberField.FinitePlace.embedding v (algebraMap R K r)‖) =
      (Ideal.absNorm (Ideal.span ({r} : Set R)) : ℝ)⁻¹ := by
  have h_span_nezero : Ideal.span ({r} : Set R) ≠ 0 := by
    simp [hr]
  let t₀ := {v : chapter07FinitePlace R | r ∈ v.asIdeal}
  have h_fin₀ : t₀.Finite := by
    simp only [← Ideal.dvd_span_singleton, Ideal.finite_factors h_span_nezero, t₀]
  let t₁ :=
    (fun v : chapter07FinitePlace R ↦
      ‖NumberField.FinitePlace.embedding v (algebraMap R K r)‖).mulSupport
  have h_fin₁ : t₁.Finite := h_fin₀.subset <| by
    simp [NumberField.FinitePlace.norm_eq_one_iff_notMem, t₁, t₀]
  let t₂ :=
    (fun v : chapter07FinitePlace R ↦
      (Ideal.absNorm (v.maxPowDividing (Ideal.span {r})) : ℝ)).mulSupport
  have h_fin₂ : t₂.Finite := by
    refine h_fin₀.subset ?_
    simp only [Function.mulSupport_subset_iff, Set.mem_ofPred_eq, t₂, t₀,
      IsDedekindDomain.HeightOneSpectrum.maxPowDividing, ← Ideal.dvd_span_singleton]
    intro v hv
    simp only [map_pow, Nat.cast_pow, ← pow_zero (Ideal.absNorm v.asIdeal : ℝ)] at hv
    refine (Associates.count_ne_zero_iff_dvd h_span_nezero
      v.irreducible).1 <| fun h ↦ hv ?_
    congr
  have h_prod :
      (Ideal.absNorm
          (∏ᶠ (v : chapter07FinitePlace R),
            v.maxPowDividing (Ideal.span {r})) : ℝ) =
        ∏ᶠ (v : chapter07FinitePlace R),
          (Ideal.absNorm (v.maxPowDividing (Ideal.span {r})) : ℝ) :=
    ((Nat.castRingHom ℝ).toMonoidHom.comp Ideal.absNorm.toMonoidHom).map_finprod_of_preimage_one
      (by simp) _
  refine (inv_eq_of_mul_eq_one_left ?_).symm
  rw [← Ideal.finprod_heightOneSpectrum_factorization h_span_nezero, h_prod,
    ← finprod_mul_distrib h_fin₁ h_fin₂]
  exact finprod_eq_one_of_forall_eq_one fun v ↦
    NumberField.HeightOneSpectrum.embedding_mul_absNorm K v hr

private theorem chapter07IdealNorm_span_eq_abs_globalNorm
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    {r : R} (hr : r ≠ 0) :
    (Ideal.absNorm (Ideal.span ({r} : Set R)) : ℝ) =
      |Algebra.norm ℚ (algebraMap R K r)| := by
  let : IsIntegrallyClosed R :=
    IsDedekindRing.toIsIntegralClosure
  let : IsIntegralClosure R ℤ K :=
    IsIntegralClosure.of_isIntegrallyClosed R ℤ K
  have hnorm :
      algebraMap ℤ ℚ (Algebra.norm ℤ r) =
        Algebra.norm ℚ (algebraMap R K r) := by
    symm
    exact Algebra.norm_localization ℤ (nonZeroDivisors ℤ) r
  rw [Ideal.absNorm_span_singleton]
  rw [Nat.cast_natAbs]
  have hnorm_ne : Algebra.norm ℚ (algebraMap R K r) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr
      ((map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).2 hr)
  rcases eq_or_ne (Algebra.norm ℚ (algebraMap R K r)) 0 with hzero | _
  · exact (hnorm_ne hzero).elim
  · simpa using congrArg (fun z : ℚ => |(z : ℝ)|) hnorm

private theorem chapter07FiniteEmbeddingNorm_hasFiniteMulSupport
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    {r : R} (hr : r ≠ 0) :
    Function.HasFiniteMulSupport (fun v : chapter07FinitePlace R ↦
      ‖NumberField.FinitePlace.embedding v (algebraMap R K r)‖) := by
  let t₀ := {v : chapter07FinitePlace R | r ∈ v.asIdeal}
  have h_span_nezero : Ideal.span ({r} : Set R) ≠ 0 := by
    simp [hr]
  have h_fin₀ : t₀.Finite := by
    simp only [← Ideal.dvd_span_singleton, Ideal.finite_factors h_span_nezero, t₀]
  apply h_fin₀.subset
  simp [Function.mulSupport_subset_iff,
    NumberField.FinitePlace.norm_eq_one_iff_notMem, t₀]

private theorem chapter07FinitePrincipalNormProduct
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    {x : K} (hx : x ≠ 0) :
    (∏ᶠ v : chapter07FinitePlace R,
      ‖NumberField.FinitePlace.embedding v x‖) =
      |Algebra.norm ℚ x|⁻¹ := by
  rcases IsFractionRing.div_surjective R x with ⟨a, b, hb, rfl⟩
  apply nonZeroDivisors.ne_zero at hb
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hx
  simp_rw [map_div₀, norm_div,
    finprod_div_distrib
      (chapter07FiniteEmbeddingNorm_hasFiniteMulSupport R K ha)
      (chapter07FiniteEmbeddingNorm_hasFiniteMulSupport R K hb),
    chapter07FinitePrincipalNormProduct_integral R K ha,
    chapter07FinitePrincipalNormProduct_integral R K hb,
    chapter07IdealNorm_span_eq_abs_globalNorm R K ha,
    chapter07IdealNorm_span_eq_abs_globalNorm R K hb]
  have hnormdiv :
      Algebra.norm ℚ ((algebraMap R K a) / (algebraMap R K b)) =
        Algebra.norm ℚ (algebraMap R K a) /
          Algebra.norm ℚ (algebraMap R K b) := by
    simp only [div_eq_mul_inv, map_mul, Algebra.norm_inv]
  rw [hnormdiv]
  simp [Rat.cast_inv, abs_inv, div_eq_mul_inv]
  ac_rfl

private theorem chapter07InfiniteNormUnit_principal
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    (v : NumberField.InfinitePlace K) (a : Kˣ) :
    ((chapter07NormUnit
        (chapter07IdeleInfiniteCoordinate R K
          (chapter07PrincipalIdeleEmbedding R K a) v) : ℝ≥0ˣ) : ℝ≥0) =
      ‖v (a : K)‖₊ := by
  apply NNReal.eq
  simp only [chapter07NormUnit, Units.val_mk0, coe_nnnorm,
    chapter07IdeleInfiniteCoordinate_val,
    chapter07PrincipalIdeleEmbedding_apply_infinite]
  change ‖((a : K) : v.Completion)‖ = ‖v (a : K)‖
  rw [← (WithAbs.equiv v.1).apply_symm_apply (a : K),
    NumberField.InfinitePlace.Completion.norm_coe]
  change v (a : K) = ‖v (a : K)‖
  rw [Real.norm_eq_abs, abs_of_pos (NumberField.InfinitePlace.pos_iff.mpr a.ne_zero)]

private theorem chapter07FiniteNormUnit_principal
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    (v : chapter07FinitePlace R) (a : Kˣ) :
    ((chapter07NormUnit
        (chapter07FiniteIdeleEquiv R K
          (chapter07FinitePrincipalIdeleEmbedding R K a) v) : ℝ≥0ˣ) : ℝ≥0) =
      ‖NumberField.FinitePlace.embedding v (a : K)‖₊ := by
  apply NNReal.eq
  simp only [chapter07NormUnit, Units.val_mk0, coe_nnnorm]
  change ‖algebraMap K (chapter07LocalField R K v) (a : K)‖ =
    ‖NumberField.FinitePlace.embedding v (a : K)‖
  exact chapter07FiniteNorm_principal_eq_embedding_norm R K v (a : K)

private theorem chapter07IdeleFiniteProjection_principal
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (a : Kˣ) :
    chapter07IdeleFiniteProjection R K
        (chapter07PrincipalIdeleEmbedding R K a) =
      chapter07FinitePrincipalIdeleEmbedding R K a := by
  apply Units.ext
  rfl

private theorem chapter07NormUnit_continuous
    {F : Type*} [NormedField F] :
    Continuous (chapter07NormUnit : Fˣ → ℝ≥0ˣ) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun u : Fˣ => ‖(u : F)‖₊)
    exact continuous_nnnorm.comp Units.continuous_val
  · have h : Continuous (fun u : Fˣ => ‖(↑(u⁻¹) : F)‖₊) :=
      continuous_nnnorm.comp Units.continuous_coe_inv
    simpa [chapter07NormUnit, nnnorm_inv] using h

private theorem chapter07FiniteNormModule_factor_continuous
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    (v : chapter07FinitePlace R) :
    Continuous (fun x : chapter07FiniteIdeleGroup R K =>
      chapter07NormUnit (chapter07FiniteIdeleEquiv R K x v)) := by
  let U := RestrictedProduct.unitsEquiv
    (𝓕 := Filter.cofinite)
    (B := fun v : chapter07FinitePlace R => chapter07LocalIntegerRing R K v)
    (fun v : chapter07FinitePlace R => chapter07LocalField R K v)
  have hU : Continuous (fun x : chapter07FiniteIdeleGroup R K => U x v) := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun x : chapter07FiniteIdeleGroup R K =>
        ((x : chapter07FiniteAdeleRing R K) v))
      exact RestrictedProduct.continuous_eval v |>.comp Units.continuous_val
    · change Continuous (fun x : chapter07FiniteIdeleGroup R K =>
        ((↑(x⁻¹) : chapter07FiniteAdeleRing R K) v))
      exact RestrictedProduct.continuous_eval v |>.comp Units.continuous_coe_inv
  exact (chapter07NormUnit_continuous.comp hU)

private theorem chapter07FiniteNormModule_locallyFinite
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    LocallyFinite (fun v : chapter07FinitePlace R =>
      Function.mulSupport (fun x : chapter07FiniteIdeleGroup R K =>
        chapter07NormUnit (chapter07FiniteIdeleEquiv R K x v))) := by
  classical
  intro x
  let S : Set (chapter07FinitePlace R) :=
    {v | (x : chapter07FiniteAdeleRing R K) v ∈
        chapter07LocalIntegerRing R K v ∧
      ((↑(x⁻¹) : chapter07FiniteAdeleRing R K) v ∈
        chapter07LocalIntegerRing R K v)}
  have hS_mem : S ∈ Filter.cofinite := by
    filter_upwards [x.1.2, (x⁻¹).1.2] with v hv hv'
    exact ⟨hv, hv'⟩
  have hopen : ∀ v : chapter07FinitePlace R,
      IsOpen (chapter07LocalIntegerRing R K v :
        Set (chapter07LocalField R K v)) := by
    intro v
    exact Valued.isOpen_valuationSubring (chapter07LocalField R K v)
  have hval_open : IsOpen {z : chapter07FiniteAdeleRing R K |
      ∀ v, v ∈ S → z v ∈ chapter07LocalIntegerRing R K v} := by
    exact RestrictedProduct.isOpen_forall_imp_mem hopen
  have hval_mem : (x : chapter07FiniteAdeleRing R K) ∈
      {z : chapter07FiniteAdeleRing R K |
        ∀ v, v ∈ S → z v ∈ chapter07LocalIntegerRing R K v} := by
    intro v hv
    exact hv.1
  have hinv_mem : (↑(x⁻¹) : chapter07FiniteAdeleRing R K) ∈
      {z : chapter07FiniteAdeleRing R K |
        ∀ v, v ∈ S → z v ∈ chapter07LocalIntegerRing R K v} := by
    intro v hv
    exact hv.2
  have hval_nhds : {y : chapter07FiniteIdeleGroup R K |
      ∀ v, v ∈ S →
        (y : chapter07FiniteAdeleRing R K) v ∈
          chapter07LocalIntegerRing R K v} ∈ 𝓝 x := by
    exact Units.continuous_val.continuousAt.preimage_mem_nhds
      (hval_open.mem_nhds hval_mem)
  have hinv_nhds : {y : chapter07FiniteIdeleGroup R K |
      ∀ v, v ∈ S →
        ((↑(y⁻¹) : chapter07FiniteAdeleRing R K) v ∈
          chapter07LocalIntegerRing R K v)} ∈ 𝓝 x := by
    exact Units.continuous_coe_inv.continuousAt.preimage_mem_nhds
      (hval_open.mem_nhds hinv_mem)
  refine ⟨{y : chapter07FiniteIdeleGroup R K |
      ∀ v, v ∈ S →
        ((y : chapter07FiniteAdeleRing R K) v ∈
            chapter07LocalIntegerRing R K v ∧
          ((↑(y⁻¹) : chapter07FiniteAdeleRing R K) v ∈
            chapter07LocalIntegerRing R K v))}, ?_, ?_⟩
  · filter_upwards [hval_nhds, hinv_nhds] with y hy hy'
    intro v hv
    exact ⟨hy v hv, hy' v hv⟩
  have hSc : Sᶜ.Finite := Filter.eventually_cofinite.mp hS_mem
  apply hSc.subset
  intro v hv
  by_contra hvScompl
  have hvS : v ∈ S := by
    simpa only [Set.mem_compl_iff, not_not] using hvScompl
  rcases hv with ⟨y, hy_support, hy_neighborhood⟩
  change chapter07NormUnit (chapter07FiniteIdeleEquiv R K y v) ≠ 1 at hy_support
  apply hy_support
  apply chapter07NormUnit_eq_one_of_mem_localIntegralUnit R K v
  apply Submonoid.mem_units_of_val_mem_inv_val_mem
  · change ((y : chapter07FiniteAdeleRing R K) v) ∈
      chapter07LocalIntegerRing R K v
    exact (hy_neighborhood v hvS).1
  · change ((↑(y⁻¹) : chapter07FiniteAdeleRing R K) v) ∈
      chapter07LocalIntegerRing R K v
    exact (hy_neighborhood v hvS).2

private theorem chapter07FiniteNormModule_continuous
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    Continuous (chapter07FiniteNormModuleHom R K) := by
  change Continuous (fun x : chapter07FiniteIdeleGroup R K =>
    ∏ᶠ v : chapter07FinitePlace R,
      chapter07NormUnit (chapter07FiniteIdeleEquiv R K x v))
  exact continuous_finprod
    (fun v => chapter07FiniteNormModule_factor_continuous R K v)
    (chapter07FiniteNormModule_locallyFinite R K)

private theorem chapter07InfiniteNormModule_continuous
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :
    Continuous (chapter07InfiniteNormModuleHom R K) := by
  change Continuous (fun x : chapter07IdeleGroup R K =>
    ∏ v : NumberField.InfinitePlace K,
      chapter07NormUnit (chapter07IdeleInfiniteCoordinate R K
        x v) ^ v.mult)
  apply continuous_finsetProd Finset.univ
  intro v hv
  have hcoord : Continuous (fun x : chapter07IdeleGroup R K =>
      chapter07IdeleInfiniteCoordinate R K x v) := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun x : chapter07IdeleGroup R K =>
        ((x : chapter07AdeleRing R K).1 v))
      exact continuous_apply v |>.comp
        (continuous_fst.comp Units.continuous_val)
    · change Continuous (fun x : chapter07IdeleGroup R K =>
        ((↑(x⁻¹) : chapter07AdeleRing R K).1 v))
      exact continuous_apply v |>.comp
        (continuous_fst.comp Units.continuous_coe_inv)
  exact (chapter07NormUnit_continuous.comp hcoord).pow v.mult

private theorem chapter07IdeleModule_continuous
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    Continuous (chapter07IdeleModuleHom R K) := by
  change Continuous (fun x : chapter07IdeleGroup R K =>
    chapter07InfiniteNormModuleHom R K x *
      chapter07FiniteNormModuleHom R K
        (chapter07IdeleFiniteProjection R K x))
  have hproj : Continuous (chapter07IdeleFiniteProjection R K) := by
    change Continuous (Units.map (RingHom.snd
      (NumberField.InfiniteAdeleRing K) (chapter07FiniteAdeleRing R K)).toMonoidHom)
    exact continuous_snd.units_map _
  exact (chapter07InfiniteNormModule_continuous R K).mul <|
    (chapter07FiniteNormModule_continuous R K).comp hproj

private theorem chapter07IdeleModule_exists_ne_one
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    ∃ x : chapter07IdeleGroup R K,
      chapter07IdeleModuleHom R K x ≠ 1 := by
  classical
  let v : NumberField.InfinitePlace K :=
    Classical.choice (inferInstance : Nonempty (NumberField.InfinitePlace K))
  let u : v.Completionˣ := Units.mk0
    (algebraMap K v.Completion (2 : K)) (by
      exact (map_ne_zero_iff (algebraMap K v.Completion)
        (FaithfulSMul.algebraMap_injective K v.Completion)).2 (by norm_num))
  let y : ∀ w : NumberField.InfinitePlace K, w.Completionˣ := fun w =>
    dite (w = v) (fun h => h ▸ u) (fun _ => 1)
  let xinf : (NumberField.InfiniteAdeleRing K)ˣ :=
    (MulEquiv.piUnits).symm y
  let x : chapter07IdeleGroup R K :=
    (MulEquiv.prodUnits).symm (xinf, 1)
  have hpi : MulEquiv.piUnits xinf = y := by
    exact (MulEquiv.piUnits).apply_symm_apply y
  have hcoord : ∀ w : NumberField.InfinitePlace K,
      chapter07IdeleInfiniteCoordinate R K x w = y w := by
    intro w
    apply Units.ext
    change x.1.1 w = y w
    change xinf.1 w = y w
    exact congrArg (fun z : w.Completionˣ => (z : w.Completion))
      (congrArg (fun z => z w) hpi)
  have hinf :
      chapter07InfiniteNormModuleHom R K x =
        chapter07NormUnit u ^ v.mult := by
    change ∏ w : NumberField.InfinitePlace K,
        chapter07NormUnit (chapter07IdeleInfiniteCoordinate R K x w) ^ w.mult = _
    simp_rw [hcoord]
    rw [Fintype.prod_eq_single v]
    · simp [y]
    · intro w hw
      simp [y, hw, chapter07NormUnit_one]
  have hnormu :
      ((chapter07NormUnit u : ℝ≥0ˣ) : ℝ≥0) = 2 := by
    apply NNReal.eq
    simp only [u, chapter07NormUnit, Units.val_mk0, coe_nnnorm]
    change ‖((2 : K) : v.Completion)‖ = 2
    rw [← (WithAbs.equiv v.1).apply_symm_apply (2 : K),
      NumberField.InfinitePlace.Completion.norm_coe]
    exact v.map_natCast 2
  have hpow_ne :
      ((chapter07NormUnit u ^ v.mult : ℝ≥0ˣ) : ℝ≥0) ≠ 1 := by
    change ((chapter07NormUnit u : ℝ≥0ˣ) : ℝ≥0) ^ v.mult ≠ 1
    rw [hnormu]
    rcases v.isReal_or_isComplex with hv | hv
    · rw [NumberField.InfinitePlace.IsReal.mult_eq_one hv]
      norm_num
    · rw [NumberField.InfinitePlace.IsComplex.mult_eq_two hv]
      norm_num
  have hfin :
      chapter07IdeleFiniteProjection R K x = 1 := by
    apply Units.ext
    rfl
  refine ⟨x, ?_⟩
  intro hx
  have hx' := congrArg (fun z : ℝ≥0ˣ => (z : ℝ≥0)) hx
  change
      ((chapter07InfiniteNormModuleHom R K x : ℝ≥0ˣ) : ℝ≥0) *
        ((chapter07FiniteNormModuleHom R K
          (chapter07IdeleFiniteProjection R K x) : ℝ≥0ˣ) : ℝ≥0) = 1 at hx'
  rw [hinf, hfin] at hx'
  exact hpow_ne (by
    simpa only [map_one, Units.val_one, mul_one] using hx')

private theorem chapter07IdeleModule_principal
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R]
    (a : Kˣ) :
    chapter07IdeleModuleHom R K
        (chapter07PrincipalIdeleEmbedding R K a) = 1 := by
  have hinf :
      ((chapter07InfiniteNormModuleHom R K
          (chapter07PrincipalIdeleEmbedding R K a) : ℝ≥0ˣ) : ℝ≥0) =
        ∏ v : NumberField.InfinitePlace K,
          ‖v (a : K)‖₊ ^ v.mult := by
    change (Units.coeHom ℝ≥0)
        (∏ v : NumberField.InfinitePlace K,
          chapter07NormUnit
            (chapter07IdeleInfiniteCoordinate R K
              (chapter07PrincipalIdeleEmbedding R K a) v) ^ v.mult) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro v hv
    simp only [map_pow, Units.coeHom_apply]
    rw [chapter07InfiniteNormUnit_principal]
  have hsupportNN :
      Function.HasFiniteMulSupport
        (fun v : chapter07FinitePlace R =>
          ‖NumberField.FinitePlace.embedding v (a : K)‖₊) := by
    apply (chapter07FiniteNormUnit_hasFiniteMulSupport R K
      (chapter07FinitePrincipalIdeleEmbedding R K a)).subset
    intro v hv
    by_contra hnn
    apply hv
    have hunit : chapter07NormUnit
        (chapter07FiniteIdeleEquiv R K
          (chapter07FinitePrincipalIdeleEmbedding R K a) v) = 1 := by
      simpa [Function.mulSupport] using hnn
    have hcoe := congrArg (fun u : ℝ≥0ˣ => (u : ℝ≥0)) hunit
    rw [chapter07FiniteNormUnit_principal] at hcoe
    exact hcoe
  have hfin :
      ((chapter07FiniteNormModuleHom R K
          (chapter07FinitePrincipalIdeleEmbedding R K a) : ℝ≥0ˣ) : ℝ≥0) =
        ∏ᶠ v : chapter07FinitePlace R,
          ‖NumberField.FinitePlace.embedding v (a : K)‖₊ := by
    change (Units.coeHom ℝ≥0)
        (∏ᶠ v : chapter07FinitePlace R,
          chapter07NormUnit
            (chapter07FiniteIdeleEquiv R K
              (chapter07FinitePrincipalIdeleEmbedding R K a) v)) = _
    rw [(Units.coeHom ℝ≥0).map_finprod
      (chapter07FiniteNormUnit_hasFiniteMulSupport R K
        (chapter07FinitePrincipalIdeleEmbedding R K a))]
    apply finprod_congr
    intro v
    change ((chapter07NormUnit
      (chapter07FiniteIdeleEquiv R K
        (chapter07FinitePrincipalIdeleEmbedding R K a) v) : ℝ≥0ˣ) : ℝ≥0) = _
    rw [chapter07FiniteNormUnit_principal]
  have hinfprod :
      (∏ v : NumberField.InfinitePlace K,
        ‖v (a : K)‖₊ ^ v.mult) =
        ‖(Algebra.norm ℚ (a : K) : ℝ)‖₊ := by
    apply NNReal.eq
    simpa only [NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm,
      Real.norm_eq_abs,
      abs_of_pos (NumberField.InfinitePlace.pos_iff.mpr a.ne_zero), Rat.cast_abs] using
      (NumberField.InfinitePlace.prod_eq_abs_norm (a : K))
  have hfinprod :
      (∏ᶠ v : chapter07FinitePlace R,
        ‖NumberField.FinitePlace.embedding v (a : K)‖₊) =
        ‖(Algebra.norm ℚ (a : K) : ℝ)‖₊⁻¹ := by
    apply NNReal.eq
    change (NNReal.toRealHom.toMonoidHom)
        (∏ᶠ v : chapter07FinitePlace R,
          ‖NumberField.FinitePlace.embedding v (a : K)‖₊) = _
    rw [NNReal.toRealHom.toMonoidHom.map_finprod hsupportNN]
    change (∏ᶠ v : chapter07FinitePlace R,
        ‖NumberField.FinitePlace.embedding v (a : K)‖) =
      ‖(Algebra.norm ℚ (a : K) : ℝ)‖⁻¹
    rw [chapter07FinitePrincipalNormProduct R K a.ne_zero]
    simp only [Real.norm_eq_abs]
    rw [Rat.cast_inv, Rat.cast_abs]
  apply Units.ext
  change
      ((chapter07InfiniteNormModuleHom R K
          (chapter07PrincipalIdeleEmbedding R K a) : ℝ≥0ˣ) : ℝ≥0) *
        ((chapter07FiniteNormModuleHom R K
          (chapter07IdeleFiniteProjection R K
            (chapter07PrincipalIdeleEmbedding R K a)) : ℝ≥0ˣ) : ℝ≥0) = 1
  rw [hinf, chapter07IdeleFiniteProjection_principal R K a, hfin,
    hinfprod, hfinprod]
  exact mul_inv_cancel₀ (by
    exact (NNReal.coe_ne_zero).mp (by
      simpa only [NNReal.coe_inv, coe_nnnorm, Real.norm_eq_abs] using
        (abs_ne_zero.mpr (Rat.cast_ne_zero.mpr
          (Algebra.norm_ne_zero_iff.mpr a.ne_zero)))))

theorem chapter07_idele_class_group_has_positive_size
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    Nonempty (Chapter07IdeleClassSizeWitness R K) := by
  have hker :
      chapter07PrincipalIdeleSubgroup R K ≤
        (chapter07IdeleModuleHom R K).ker := by
    intro x hx
    rcases hx with ⟨a, rfl⟩
    exact chapter07IdeleModule_principal R K a
  let size : chapter07IdeleClassGroup R K →* ℝ≥0ˣ :=
    QuotientGroup.lift (chapter07PrincipalIdeleSubgroup R K)
      (chapter07IdeleModuleHom R K) hker
  have hsize_cont : Continuous size := by
    apply (QuotientGroup.isQuotientMap_mk
      (chapter07PrincipalIdeleSubgroup R K)).continuous_iff.mpr
    change Continuous (fun x : chapter07IdeleGroup R K =>
      size (QuotientGroup.mk x))
    have hcomp : (fun x : chapter07IdeleGroup R K =>
        size (QuotientGroup.mk x)) = chapter07IdeleModuleHom R K := by
      funext x
      exact QuotientGroup.lift_mk'
        (chapter07PrincipalIdeleSubgroup R K) hker x
    rw [hcomp]
    exact chapter07IdeleModule_continuous R K
  obtain ⟨x, hx⟩ := chapter07IdeleModule_exists_ne_one R K
  refine ⟨⟨size, hsize_cont, ?_⟩⟩
  refine ⟨QuotientGroup.mk x, ?_⟩
  intro h
  apply hx
  have h' : size (QuotientGroup.mk x) =
      chapter07IdeleModuleHom R K x := by
    exact QuotientGroup.lift_mk'
      (chapter07PrincipalIdeleSubgroup R K) hker x
  rw [h'] at h
  exact h

private theorem chapter07_idele_class_group_not_compact_aux
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (w : Chapter07IdeleClassSizeWitness R K) :
    ¬ CompactSpace (chapter07IdeleClassGroup R K) := by
  intro hcompact
  let f : chapter07IdeleClassGroup R K → ℝ≥0 := fun x => w.size x
  have hf : Continuous f := Units.continuous_val.comp w.continuous_size
  have hfrange : IsCompact (Set.range f) := by
    simpa only [Set.image_univ] using (hcompact.isCompact_univ.image hf)
  obtain ⟨M, hM⟩ := hfrange.bddAbove
  obtain ⟨c, hc⟩ := w.nontrivial
  have hc' : f c ≠ 1 := by
    intro h
    apply hc
    exact Units.ext h
  rcases lt_or_gt_of_ne hc' with hlt | hgt
  · let d := c⁻¹
    have hdgt : 1 < f d := by
      change 1 < (w.size (c⁻¹) : ℝ≥0)
      rw [map_inv, Units.val_inv_eq_inv_val]
      exact (one_lt_inv₀ (pos_iff_ne_zero.2 (Units.ne_zero (w.size c)))).2 hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hdgt
    have hle : f (d ^ n) ≤ M := hM ⟨d ^ n, rfl⟩
    have hpow : f (d ^ n) = (f d) ^ n := by
      simp [f, map_pow]
    rw [hpow] at hle
    exact (not_lt_of_ge hle) hn
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hgt
    have hle : f (c ^ n) ≤ M := hM ⟨c ^ n, rfl⟩
    have hpow : f (c ^ n) = (f c) ^ n := by
      simp [f, map_pow]
    rw [hpow] at hle
    exact (not_lt_of_ge hle) hn

theorem chapter07_idele_class_group_not_compact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K]
    [Module.Finite ℤ R] [Module.Free ℤ R] :
    ¬ CompactSpace (chapter07IdeleClassGroup R K) := by
  obtain ⟨w⟩ := chapter07_idele_class_group_has_positive_size R K
  exact chapter07_idele_class_group_not_compact_aux R K w

theorem chapter07_idele_class_group_not_compact_from_positive_size
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (w : Chapter07IdeleClassSizeWitness R K) :
    ¬ CompactSpace (chapter07IdeleClassGroup R K) := by
  exact chapter07_idele_class_group_not_compact_aux R K w

end

end LastLib.Book04AdelesAndIdeles.Chapter07
