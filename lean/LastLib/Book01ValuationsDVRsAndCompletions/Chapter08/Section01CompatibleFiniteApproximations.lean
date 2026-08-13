import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.AdicCompletion.Topology

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter08

open Filter
open scoped Topology

noncomputable section

/-!
# Chapter 8: Inverse limits and digit expansions

This file is deliberately a statement-generation pass. The declarations use Mathlib's
AdicCompletion, ideal quotients, PadicInt, Padic, PowerSeries, and LaurentSeries
where those interfaces match the book. A few predicates package the adic convergence and
digit notation used in the prose.
-/

/-! # Book 1, Chapter 8, Section 8.1: Compatible Finite Approximations
-/

/-! ### 8.1 Compatible finite approximations -/

/-- The finite precision quotient occurring in Chapter 8. -/
abbrev Chapter08Truncation (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ) : Type _ :=
  A ⧸ I ^ n

/-- The ring of compatible families of residues, indexed from precision 1 onwards. -/
def Chapter08CompatibleSubring (A : Type*) [CommRing A] (I : Ideal A) :
    Subring (∀ n : ℕ, A ⧸ I ^ (n + 1)) where
  carrier := {x | ∀ n : ℕ,
    Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)) (x (n + 1)) = x n}
  zero_mem' := by
    intro n
    simp
  add_mem' := by
    intro x y hx hy n
    simp [hx n, hy n]
  neg_mem' := by
    intro x hx n
    simp [hx n]
  one_mem' := by
    intro n
    simp
  mul_mem' := by
    intro x y hx hy n
    simp [hx n, hy n]

/-- A compatible family is the inverse-limit model used throughout the chapter. -/
abbrev Chapter08CompatibleFamily (A : Type*) [CommRing A] (I : Ideal A) : Type _ :=
  Chapter08CompatibleSubring A I

@[simp]
theorem Chapter08CompatibleFamily.compatible
    {A : Type*} [CommRing A] {I : Ideal A}
    (x : Chapter08CompatibleFamily A I) (n : ℕ) :
    Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)) (x.1 (n + 1)) = x.1 n := by
  exact x.2 n

@[instance_reducible]
def Chapter08FiniteQuotientTopology
    (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ) :
    TopologicalSpace (A ⧸ I ^ (n + 1)) := ⊥

/-- A small interface for the phrase topological-ring isomorphism. -/
structure Chapter08TopologicalRingEquiv (R S : Type*)
    [CommRing R] [CommRing S] (tR : TopologicalSpace R) (tS : TopologicalSpace S) where
  ringEquiv : R ≃+* S
  continuous_toFun : @Continuous R S tR tS ringEquiv
  continuous_invFun : @Continuous S R tS tR ringEquiv.symm

@[instance_reducible]
def Chapter08InverseLimitProductTopology
    (A : Type*) [CommRing A] (I : Ideal A) :
    TopologicalSpace (∀ n : ℕ, A ⧸ I ^ (n + 1)) :=
  @Pi.topologicalSpace ℕ (fun n : ℕ => A ⧸ I ^ (n + 1))
    (fun n => Chapter08FiniteQuotientTopology A I n)

@[instance_reducible]
def Chapter08InverseLimitTopology
    (A : Type*) [CommRing A] (I : Ideal A) :
    TopologicalSpace (Chapter08CompatibleFamily A I) :=
  TopologicalSpace.induced (fun x : Chapter08CompatibleFamily A I => x.1)
    (Chapter08InverseLimitProductTopology A I)

@[instance_reducible]
def Chapter08AdicCompletionTopology
    (A : Type*) [CommRing A] (I : Ideal A) :
    TopologicalSpace (AdicCompletion I A) :=
  (Ideal.map (algebraMap A (AdicCompletion I A)) I).adicTopology

/-- The residue family attached to an element of an adic completion. -/
def Chapter08CompletionResidues
    {A : Type*} [CommRing A] (I : Ideal A) (x : AdicCompletion I A) :
    Chapter08CompatibleFamily A I := by
  refine ⟨fun n => AdicCompletion.evalₐ I (n + 1) x, ?_⟩
  intro n
  have h1 : (I ^ (n + 1) • (⊤ : Ideal A)) = I ^ (n + 1) := by ext; simp
  have h2 : (I ^ (n + 2) • (⊤ : Ideal A)) = I ^ (n + 2) := by ext; simp
  change Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))
      ((Ideal.quotientEquivAlgOfEq A h2) (x.val (n + 2))) =
    (Ideal.quotientEquivAlgOfEq A h1) (x.val (n + 1))
  rw [← x.property (Nat.le_succ (n + 1))]
  let y := x.val (n + 2)
  have hleft :=
    Submodule.factor_comp_apply
      (p := I ^ (n + 2) • (⊤ : Submodule A A))
      (p' := I ^ (n + 2)) (p'' := I ^ (n + 1))
      (le_of_eq h2) (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) y
  have hright :=
    Submodule.factor_comp_apply
      (p := I ^ (n + 2) • (⊤ : Submodule A A))
      (p' := I ^ (n + 1) • (⊤ : Submodule A A))
      (p'' := I ^ (n + 1))
      (Submodule.pow_smul_top_le I A (Nat.le_succ (n + 1)))
      (le_of_eq h1) y
  change Submodule.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
      (Submodule.factor (le_of_eq h2) y) =
    Submodule.factor (le_of_eq h1)
      (Submodule.factorPow I A (Nat.le_succ (n + 1)) y)
  calc
    _ = Submodule.factor
        ((le_of_eq h2).trans (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) y := hleft
    _ = Submodule.factor
        ((Submodule.pow_smul_top_le I A (Nat.le_succ (n + 1))).trans
          (le_of_eq h1)) y := by
      congr 1
    _ = _ := hright.symm

theorem chapter08_inverse_limit_ring_equiv
    {A : Type*} [CommRing A] (I : Ideal A)
    :
    ∃ e : AdicCompletion I A ≃+* Chapter08CompatibleFamily A I,
      ∀ x, e x = Chapter08CompletionResidues I x := by
  classical
  let coordinate (n : ℕ) :
      Chapter08CompatibleFamily A I →+* A ⧸ I ^ (n + 1) :=
    { toFun := fun x => x.1 n
      map_one' := rfl
      map_mul' := by intro x y; rfl
      map_zero' := rfl
      map_add' := by intro x y; rfl }
  let f : ∀ n : ℕ,
      Chapter08CompatibleFamily A I →+* A ⧸ I ^ n :=
    fun n => (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp (coordinate n)
  have hf : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow I hmn).comp (f n) = f m := by
    intro m n hmn
    ext z
    change Ideal.Quotient.factorPow I hmn
        (Ideal.Quotient.factorPow I (Nat.le_succ n) (z.1 n)) =
      Ideal.Quotient.factorPow I (Nat.le_succ m) (z.1 m)
    have hlong : z.1 m =
        Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn) (z.1 n) := by
      have hlong' :=
        Ideal.Quotient.eq_factor_of_eq_factor_succ
          (I := fun i : ℕ => I ^ (i + 1))
          (fun i j hij => Ideal.pow_le_pow_right (Nat.succ_le_succ hij))
          (fun i => z.1 i)
          (fun i => by
            simp)
          hmn
      simpa [Ideal.Quotient.factorPow] using hlong'
    calc
      Ideal.Quotient.factorPow I hmn
          (Ideal.Quotient.factorPow I (Nat.le_succ n) (z.1 n)) =
          Ideal.Quotient.factorPow I (Nat.le_trans hmn (Nat.le_succ n))
            (z.1 n) := by
        simp [Ideal.Quotient.factorPow]
      _ = Ideal.Quotient.factorPow I (Nat.le_succ m)
          (Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn) (z.1 n)) := by
        simp [Ideal.Quotient.factorPow]
      _ = Ideal.Quotient.factorPow I (Nat.le_succ m) (z.1 m) := by
        exact congrArg (Ideal.Quotient.factorPow I (Nat.le_succ m)) hlong.symm
  let e : AdicCompletion I A →+* Chapter08CompatibleFamily A I :=
    { toFun := Chapter08CompletionResidues I
      map_one' := by
        ext n
        simp [Chapter08CompletionResidues]
      map_mul' := by
        intro x y
        ext n
        simp [Chapter08CompletionResidues]
      map_zero' := by
        ext n
        simp [Chapter08CompletionResidues]
      map_add' := by
        intro x y
        ext n
        simp [Chapter08CompletionResidues] }
  let g : Chapter08CompatibleFamily A I →+* AdicCompletion I A :=
    AdicCompletion.liftRingHom I f hf
  have hge : ∀ y, e (g y) = y := by
    intro y
    apply Subtype.ext
    funext n
    change AdicCompletion.evalₐ I (n + 1) (g y) = y.1 n
    change AdicCompletion.evalₐ I (n + 1)
        (AdicCompletion.liftRingHom I f hf y) = y.1 n
    rw [AdicCompletion.evalₐ_liftRingHom]
    change Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)) (y.1 (n + 1)) = y.1 n
    exact y.2 n
  have heg : ∀ x, g (e x) = x := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    cases n with
    | zero =>
      have hsub : Subsingleton (A ⧸ I ^ 0) := by
        rw [show I ^ 0 = (⊤ : Ideal A) by simp]
        infer_instance
      exact hsub.elim _ _
    | succ n =>
      change AdicCompletion.evalₐ I (n + 1)
          (AdicCompletion.liftRingHom I f hf (e x)) =
        AdicCompletion.evalₐ I (n + 1) x
      rw [AdicCompletion.evalₐ_liftRingHom]
      change Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))
          ((Chapter08CompletionResidues I x).1 (n + 1)) =
        AdicCompletion.evalₐ I (n + 1) x
      exact (Chapter08CompletionResidues I x).2 n
  have heinj : Function.Injective e := by
    intro x y hxy
    rw [← heg x, ← heg y, hxy]
  have hesurj : Function.Surjective e := by
    intro y
    exact ⟨g y, hge y⟩
  let er : AdicCompletion I A ≃+* Chapter08CompatibleFamily A I :=
    RingEquiv.ofBijective e ⟨heinj, hesurj⟩
  exact ⟨er, by intro x; rfl⟩

/-! Theorem 8.1: the completion is canonically the inverse limit of its finite quotients,
including the adic and inverse-limit topologies. The finite-generation hypothesis identifies
the adic powers with the kernels of the finite evaluation maps. -/
theorem chapter08_theorem_8_1_inverse_limit_description
    {A : Type*} [CommRing A] (I : Ideal A) (hI : I.FG) :
      ∃ e : Chapter08TopologicalRingEquiv (AdicCompletion I A)
        (Chapter08CompatibleFamily A I)
        (Chapter08AdicCompletionTopology A I)
        (Chapter08InverseLimitTopology A I),
      ∀ x, e.ringEquiv x = Chapter08CompletionResidues I x := by
  classical
  let : TopologicalSpace (AdicCompletion I A) :=
    Chapter08AdicCompletionTopology A I
  let : ∀ n : ℕ, TopologicalSpace (A ⧸ I ^ (n + 1)) :=
    fun n => Chapter08FiniteQuotientTopology A I n
  let : ∀ n : ℕ, DiscreteTopology (A ⧸ I ^ (n + 1)) :=
    fun n => discreteTopology_bot _
  let : ∀ n : ℕ, IsTopologicalAddGroup (A ⧸ I ^ (n + 1)) :=
    fun n => by infer_instance
  let : ∀ n : ℕ, IsTopologicalRing (A ⧸ I ^ (n + 1)) :=
    fun n => by infer_instance
  let : TopologicalSpace (∀ n : ℕ, A ⧸ I ^ (n + 1)) :=
    Chapter08InverseLimitProductTopology A I
  let : IsTopologicalRing (∀ n : ℕ, A ⧸ I ^ (n + 1)) :=
    Pi.instIsTopologicalRing
  let : IsTopologicalAddGroup (∀ n : ℕ, A ⧸ I ^ (n + 1)) :=
    IsTopologicalRing.to_topologicalAddGroup
  let : TopologicalSpace (Chapter08CompatibleFamily A I) :=
    Chapter08InverseLimitTopology A I
  let : IsTopologicalAddGroup (AdicCompletion I A) :=
    (RingSubgroupsBasis.toRingFilterBasis (Ideal.adic_basis
      (Ideal.map (algebraMap A (AdicCompletion I A)) I)).toRing_subgroups_basis).toAddGroupFilterBasis.isTopologicalAddGroup
  obtain ⟨er, her⟩ := chapter08_inverse_limit_ring_equiv I
  let J : Ideal (AdicCompletion I A) :=
    Ideal.map (algebraMap A (AdicCompletion I A)) I
  have hcoord_cont (n : ℕ) :
      Continuous (fun x : AdicCompletion I A =>
        AdicCompletion.evalₐ I (n + 1) x) := by
    let f : AdicCompletion I A →+* A ⧸ I ^ (n + 1) :=
      (AdicCompletion.evalₐ I (n + 1)).toRingHom
    have hker : J ^ (n + 1) ≤ RingHom.ker f := by
      rw [show J ^ (n + 1) =
        Ideal.map (algebraMap A (AdicCompletion I A)) (I ^ (n + 1)) by
          simp [J, Ideal.map_pow]]
      refine Ideal.map_le_iff_le_comap.mpr ?_
      intro a ha
      change f (algebraMap A (AdicCompletion I A) a) = 0
      rw [show f (algebraMap A (AdicCompletion I A) a) =
          Ideal.Quotient.mk (I ^ (n + 1)) a by
            simp [f, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    have hnhds : ((J ^ (n + 1) : Ideal (AdicCompletion I A)) :
        Set (AdicCompletion I A)) ∈
        𝓝 (0 : AdicCompletion I A) := by
      exact (Ideal.openAddSubgroup J (n + 1)).isOpen'.mem_nhds
        (Ideal.zero_mem (J ^ (n + 1)))
    have hzero : ContinuousAt f 0 := by
      rw [ContinuousAt, map_zero, nhds_discrete (A ⧸ I ^ (n + 1)), tendsto_pure]
      filter_upwards [hnhds] with x hx
      exact RingHom.mem_ker.mp (hker hx)
    exact continuous_of_continuousAt_zero f hzero
  have htoProd : Continuous (fun x : AdicCompletion I A => (er x).1) := by
    apply continuous_pi
    intro n
    have heq : (fun x : AdicCompletion I A => (er x).1 n) =
        (fun x => AdicCompletion.evalₐ I (n + 1) x) := by
      funext x
      rw [her x]
      rfl
    rw [heq]
    exact hcoord_cont n
  have her_cont : Continuous er := by
    apply continuous_induced_rng.mpr
    simpa [Function.comp_def] using htoProd
  let : IsTopologicalAddGroup (Chapter08CompatibleFamily A I) := by
    exact topologicalAddGroup_induced
      (Chapter08CompatibleSubring A I).subtype.toAddMonoidHom
  have hker_eval (n : ℕ) :
      J ^ n = RingHom.ker ((AdicCompletion.evalₐ I n).toRingHom) := by
    ext x
    trans x ∈ (AdicCompletion.eval I A n).ker
    · rw [show J ^ n =
        Ideal.map (algebraMap A (AdicCompletion I A)) (I ^ n) by
          simp [J, Ideal.map_pow]]
      change x ∈ ((Ideal.map (algebraMap A (AdicCompletion I A)) (I ^ n)).restrictScalars A :
        Set (AdicCompletion I A)) ↔ x ∈ (AdicCompletion.eval I A n).ker
      rw [← Ideal.smul_top_eq_map]
      simp [AdicCompletion.pow_smul_top_eq_ker_eval hI]
    · change (AdicCompletion.eval I A n) x = 0 ↔
        AdicCompletion.evalₐ I n x = 0
      have heq : I ^ n * (⊤ : Ideal A) = I ^ n := by
        ext a
        simp
      have hinj : Function.Injective
          (Ideal.Quotient.factor (le_of_eq heq)) := by
        simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
          using Ideal.map_mk_eq_bot_of_le (le_of_eq heq.symm)
      simpa [← AdicCompletion.factor_eval_eq_evalₐ] using
        (map_eq_zero_iff _ hinj).symm
  have her_symm_cont : Continuous er.symm := by
    apply continuous_of_continuousAt_zero
    rw [ContinuousAt, map_zero]
    refine J.hasBasis_nhds_zero_adic.tendsto_right_iff.mpr ?_
    intro n _
    let U : Set (Chapter08CompatibleFamily A I) := {y | y.1 n = 0}
    have hUopen : IsOpen U := by
      change IsOpen ((fun y : Chapter08CompatibleFamily A I => y.1 n) ⁻¹'
        ({0} : Set (A ⧸ I ^ (n + 1))))
      exact (isOpen_discrete ({0} : Set (A ⧸ I ^ (n + 1)))).preimage
        ((continuous_apply n).comp continuous_induced_dom)
    have hUmem : U ∈ 𝓝 (0 : Chapter08CompatibleFamily A I) := by
      exact hUopen.mem_nhds (by simp [U])
    filter_upwards [hUmem] with y hy
    apply (Ideal.pow_le_pow_right (Nat.le_succ n))
    rw [hker_eval (n + 1)]
    apply RingHom.mem_ker.mpr
    have heq : (er (er.symm y)).1 n = 0 := by
      simpa [hy]
    rw [her (er.symm y)] at heq
    simpa [Chapter08CompletionResidues] using heq
  refine ⟨{
    ringEquiv := er
    continuous_toFun := her_cont
    continuous_invFun := her_symm_cont }, her⟩

/-- Coordinatewise operations preserve compatibility, so there is no extra consistency datum. -/
theorem chapter08_inverse_limit_coordinatewise_operations
    {A : Type*} [CommRing A] {I : Ideal A}
    (x y : Chapter08CompatibleFamily A I) (n : ℕ) :
    (x + y).1 n = x.1 n + y.1 n ∧
      (x * y).1 n = x.1 n * y.1 n ∧
      (-x).1 n = -(x.1 n) := by
  simp

/-- A compatible collection of maps on truncations. -/
structure Chapter08CompatibleTruncationMaps
    (A B : Type*) [CommRing A] [CommRing B]
    (I : Ideal A) (J : Ideal B) where
  map : ∀ n : ℕ, A ⧸ I ^ (n + 1) →+* B ⧸ J ^ (n + 1)
  compatible : ∀ n : ℕ,
    (map n).comp (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))) =
      (Ideal.Quotient.factorPow J (Nat.le_succ (n + 1))).comp (map (n + 1))

/-- The map on inverse limits induced by compatible maps on all truncations. -/
def Chapter08InducedMapOnCompatibleFamilies
    {A B : Type*} [CommRing A] [CommRing B]
    {I : Ideal A} {J : Ideal B}
    (φ : Chapter08CompatibleTruncationMaps A B I J) :
    Chapter08CompatibleFamily A I →+* Chapter08CompatibleFamily B J := by
  refine
    { toFun := fun x => ⟨fun n => φ.map n (x.1 n), ?_⟩
      map_one' := by ext n; simp
      map_mul' := by intro x y; ext n; simp
      map_zero' := by ext n; simp
      map_add' := by intro x y; ext n; simp }
  intro n
  change Ideal.Quotient.factorPow J (Nat.le_succ (n + 1))
      (φ.map (n + 1) (x.1 (n + 1))) = φ.map n (x.1 n)
  calc
    Ideal.Quotient.factorPow J (Nat.le_succ (n + 1))
        (φ.map (n + 1) (x.1 (n + 1))) =
        φ.map n
          (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)) (x.1 (n + 1))) := by
            exact RingHom.congr_fun (φ.compatible n).symm (x.1 (n + 1))
    _ = φ.map n (x.1 n) := by rw [Chapter08CompatibleFamily.compatible x n]

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter08
