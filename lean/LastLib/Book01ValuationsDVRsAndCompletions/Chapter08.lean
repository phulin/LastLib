import Mathlib

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter08

open Polynomial IsLocalRing
open Filter
open scoped BigOperators LaurentSeries Topology PowerSeries.WithPiTopology

noncomputable section

/-!
# Chapter 8: Inverse limits and digit expansions

This file is deliberately a statement-generation pass. The declarations use Mathlib's
AdicCompletion, ideal quotients, PadicInt, Padic, PowerSeries, and LaurentSeries
where those interfaces match the book. A few predicates package the adic convergence and
digit notation used in the prose.
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

def Chapter08FiniteQuotientTopology
    (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ) :
    TopologicalSpace (A ⧸ I ^ (n + 1)) := ⊥

/-- A small interface for the phrase topological-ring isomorphism. -/
structure Chapter08TopologicalRingEquiv (R S : Type*)
    [CommRing R] [CommRing S] (tR : TopologicalSpace R) (tS : TopologicalSpace S) where
  ringEquiv : R ≃+* S
  continuous_toFun : @Continuous R S tR tS ringEquiv
  continuous_invFun : @Continuous S R tS tR ringEquiv.symm

def Chapter08InverseLimitProductTopology
    (A : Type*) [CommRing A] (I : Ideal A) :
    TopologicalSpace (∀ n : ℕ, A ⧸ I ^ (n + 1)) :=
  @Pi.topologicalSpace ℕ (fun n : ℕ => A ⧸ I ^ (n + 1))
    (fun n => Chapter08FiniteQuotientTopology A I n)

def Chapter08InverseLimitTopology
    (A : Type*) [CommRing A] (I : Ideal A) :
    TopologicalSpace (Chapter08CompatibleFamily A I) :=
  TopologicalSpace.induced (fun x : Chapter08CompatibleFamily A I => x.1)
    (Chapter08InverseLimitProductTopology A I)

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

private theorem chapter08_inverse_limit_ring_equiv
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
            simpa [Ideal.Quotient.factorPow] using (z.2 i).symm)
          hmn
      simpa [Ideal.Quotient.factorPow] using hlong'
    calc
      Ideal.Quotient.factorPow I hmn
          (Ideal.Quotient.factorPow I (Nat.le_succ n) (z.1 n)) =
          Ideal.Quotient.factorPow I (Nat.le_trans hmn (Nat.le_succ n))
            (z.1 n) := by
        simpa [Ideal.Quotient.factorPow] using
          (Ideal.Quotient.factor_comp_apply
            (S := I ^ (n + 1)) (T := I ^ n) (U := I ^ m)
            (Ideal.pow_le_pow_right (Nat.le_succ n))
            (Ideal.pow_le_pow_right hmn) (z.1 n))
      _ = Ideal.Quotient.factorPow I (Nat.le_succ m)
          (Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn) (z.1 n)) := by
        simpa [Ideal.Quotient.factorPow] using
          (Ideal.Quotient.factor_comp_apply
            (S := I ^ (n + 1)) (T := I ^ (m + 1)) (U := I ^ m)
            (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn))
            (Ideal.pow_le_pow_right (Nat.le_succ m)) (z.1 n))
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
      change AdicCompletion.evalₐ I (n + 1) (g (e x)) =
        AdicCompletion.evalₐ I (n + 1) x
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
  letI : TopologicalSpace (AdicCompletion I A) :=
    Chapter08AdicCompletionTopology A I
  letI : ∀ n : ℕ, TopologicalSpace (A ⧸ I ^ (n + 1)) :=
    fun n => Chapter08FiniteQuotientTopology A I n
  letI : ∀ n : ℕ, DiscreteTopology (A ⧸ I ^ (n + 1)) :=
    fun n => discreteTopology_bot _
  letI : ∀ n : ℕ, IsTopologicalAddGroup (A ⧸ I ^ (n + 1)) :=
    fun n => by infer_instance
  letI : ∀ n : ℕ, IsTopologicalRing (A ⧸ I ^ (n + 1)) :=
    fun n => by infer_instance
  letI : TopologicalSpace (∀ n : ℕ, A ⧸ I ^ (n + 1)) :=
    Chapter08InverseLimitProductTopology A I
  letI : IsTopologicalRing (∀ n : ℕ, A ⧸ I ^ (n + 1)) :=
    Pi.instIsTopologicalRing
  letI : IsTopologicalAddGroup (∀ n : ℕ, A ⧸ I ^ (n + 1)) :=
    IsTopologicalRing.to_topologicalAddGroup
  letI : TopologicalSpace (Chapter08CompatibleFamily A I) :=
    Chapter08InverseLimitTopology A I
  letI : IsTopologicalAddGroup (AdicCompletion I A) :=
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
  letI : IsTopologicalAddGroup (Chapter08CompatibleFamily A I) := by
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
      simpa [AdicCompletion.pow_smul_top_eq_ker_eval hI]
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

/-! ### 8.2 Infinite digits -/

/-- A set of representatives for the residue classes modulo an ideal. -/
def Chapter08IsResidueRepresentativeSet
    (A : Type*) [CommRing A] (I : Ideal A) (S : Set A) : Prop :=
  ∀ a : A, ∃! s : A, s ∈ S ∧ a - s ∈ I

/-- Adic convergence written only in terms of eventual stabilization in every quotient. -/
def Chapter08AdicConverges
    {A : Type*} [CommRing A] (I : Ideal A)
    (u : ℕ → AdicCompletion I A) (x : AdicCompletion I A) : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
    AdicCompletion.evalₐ I n (u m) = AdicCompletion.evalₐ I n x

/-- The adic meaning of a sequence of terms tending to zero. -/
def Chapter08AdicTendsToZero
    {A : Type*} [CommRing A] (I : Ideal A) (a : ℕ → A) : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ i : ℕ, N ≤ i → a i ∈ I ^ n

/-- The n-th partial sum of a digit series in the adic completion. -/
def Chapter08DigitPartialSum
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (d : ℕ → A) (n : ℕ) :
    AdicCompletion I A :=
  ∑ i ∈ Finset.range n,
    algebraMap A (AdicCompletion I A) (d i) *
      (algebraMap A (AdicCompletion I A) π) ^ i

/-- The finite-residue and convergence conditions for an infinite digit expansion. -/
def Chapter08DigitExpansion
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (S : Set A)
    (x : AdicCompletion I A) (d : ℕ → A) : Prop :=
  (∀ i : ℕ, d i ∈ S) ∧
    (∀ n : ℕ,
      AdicCompletion.evalₐ I n x =
        Ideal.Quotient.mk (I ^ n)
          (∑ i ∈ Finset.range n, d i * π ^ i)) ∧
    Chapter08AdicConverges I (Chapter08DigitPartialSum I π d) x

/-- The first n digits matching a residue class modulo pi^n. -/
def Chapter08MatchesTruncation
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (S : Set A)
    (x : AdicCompletion I A) (n : ℕ) (pref : Fin n → A) : Prop :=
  (∀ i : Fin n, pref i ∈ S) ∧
    AdicCompletion.evalₐ I n x =
      Ideal.Quotient.mk (I ^ n)
        (∑ i : Fin n, pref i * π ^ (i : ℕ))

/-! The truncated digit lemma and compatibility of the chosen prefixes. -/
theorem chapter08_truncated_digit_lemma
    {A : Type*} [CommRing A] [IsDomain A] (I : Ideal A) (π : A) (S : Set A)
    (hI : I = Ideal.span {π})
    (hS : Chapter08IsResidueRepresentativeSet A I S)
    (hπ : π ≠ 0)
    (x : AdicCompletion I A) (n : ℕ) :
    ∃! pref : Fin n → A, Chapter08MatchesTruncation I π S x n pref := by
  classical
  have hπmem : π ∈ I := by
    rw [hI]
    exact Ideal.subset_span (by simp)
  have hsum_succ : ∀ (r : ℕ) (w : Fin (r + 1) → A),
      (∑ i : Fin (r + 1), w i * π ^ (i : ℕ)) =
        w 0 + π * ∑ i : Fin r, w i.succ * π ^ (i : ℕ) := by
    intro r w
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, pow_zero, mul_one]
    congr 1
    calc
      (∑ i : Fin r, w i.succ * π ^ (i.succ : ℕ)) =
          ∑ i : Fin r, π * (w i.succ * π ^ (i : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Fin.val_succ, pow_succ]
        ring
      _ = π * ∑ i : Fin r, w i.succ * π ^ (i : ℕ) := by
        rw [Finset.mul_sum]
  have hcancel : ∀ {r : ℕ} {z : A},
      π * z ∈ I ^ (r + 1) → z ∈ I ^ r := by
    intro r z hz
    have hz' : π * z ∈ (Ideal.span {π}) ^ (r + 1) := by
      simpa [hI] using hz
    rw [Ideal.span_singleton_pow] at hz'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hz'
    rw [hI, Ideal.span_singleton_pow]
    apply Ideal.mem_span_singleton'.2
    refine ⟨c, ?_⟩
    apply mul_left_cancel₀ hπ
    calc
      π * (c * π ^ r) = c * π ^ (r + 1) := by
        rw [pow_succ]
        ring
      _ = π * z := hc
  have hrepresent : ∀ (r : ℕ) (a : A),
      ∃ w : Fin r → A,
        (∀ i, w i ∈ S) ∧
          Ideal.Quotient.mk (I ^ r)
              (∑ i : Fin r, w i * π ^ (i : ℕ)) =
            Ideal.Quotient.mk (I ^ r) a := by
    intro r
    induction r with
    | zero =>
        intro a
        refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
        · intro i
          exact Fin.elim0 i
        · rw [show I ^ 0 = (⊤ : Ideal A) by simp]
          exact Subsingleton.elim _ _
    | succ r ihr =>
        intro a
        obtain ⟨s, hs, hsu⟩ := hS a
        have hsa : a - s ∈ Ideal.span {π} := by
          simpa [hI] using hs.2
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hsa
        obtain ⟨t, ht, htq⟩ := ihr c
        let w : Fin (r + 1) → A := Fin.cases s (fun i => t i)
        refine ⟨w, ?_, ?_⟩
        · intro i
          refine Fin.cases hs.1 (fun j => ht j) i
        · have htail :
              ∑ i : Fin r, t i * π ^ (i : ℕ) - c ∈ I ^ r :=
            (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 htq
          have hprod :
              π * (∑ i : Fin r, t i * π ^ (i : ℕ) - c) ∈ I ^ (r + 1) := by
            rw [Ideal.IsTwoSided.pow_succ]
            exact Ideal.mul_mem_mul hπmem htail
          apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
          have hsw := hsum_succ r w
          rw [hsw]
          convert hprod using 1
          dsimp [w]
          calc
            s + π * (∑ i : Fin r, t i * π ^ (i : ℕ)) - a =
                π * (∑ i : Fin r, t i * π ^ (i : ℕ)) - (a - s) := by ring
            _ = π * (∑ i : Fin r, t i * π ^ (i : ℕ)) - c * π := by
              rw [← hc]
            _ = π * (∑ i : Fin r, t i * π ^ (i : ℕ) - c) := by ring
  have hunique : ∀ (r : ℕ) {u v : Fin r → A},
      (∀ i, u i ∈ S) → (∀ i, v i ∈ S) →
      Ideal.Quotient.mk (I ^ r) (∑ i : Fin r, u i * π ^ (i : ℕ)) =
        Ideal.Quotient.mk (I ^ r) (∑ i : Fin r, v i * π ^ (i : ℕ)) →
      u = v := by
    intro r
    induction r with
    | zero =>
        intro u v hu hv huv
        funext i
        exact Fin.elim0 i
    | succ r ihr =>
        intro u v hu hv huv
        have htotal :
            (∑ i : Fin (r + 1), u i * π ^ (i : ℕ)) -
                ∑ i : Fin (r + 1), v i * π ^ (i : ℕ) ∈ I ^ (r + 1) :=
          (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 huv
        have htotalI :
            (∑ i : Fin (r + 1), u i * π ^ (i : ℕ)) -
                ∑ i : Fin (r + 1), v i * π ^ (i : ℕ) ∈ I := by
          have hpow : I ^ (r + 1) ≤ I := by
            simpa [pow_one] using
              (Ideal.pow_le_pow_right (I := I)
                (show 1 ≤ r + 1 by omega))
          exact hpow htotal
        let U : A := ∑ i : Fin r, u i.succ * π ^ (i : ℕ)
        let V : A := ∑ i : Fin r, v i.succ * π ^ (i : ℕ)
        have htailI : π * (U - V) ∈ I := by
          rw [mul_comm]
          exact I.mul_mem_left _ hπmem
        have hsumI : u 0 - v 0 + π * (U - V) ∈ I := by
          convert htotalI using 1
          rw [hsum_succ r u, hsum_succ r v]
          dsimp [U, V]
          ring
        have hzero : u 0 - v 0 ∈ I := by
          have := I.sub_mem hsumI htailI
          convert this using 1 <;> ring
        have hzero' : v 0 - u 0 ∈ I := by
          simpa [sub_eq_add_neg, add_comm] using I.neg_mem hzero
        have heq0 : u 0 = v 0 := by
          exact (hS (v 0)).unique ⟨hu 0, hzero'⟩
            ⟨hv 0, by simpa using I.zero_mem⟩
        have htail : π * (U - V) ∈ I ^ (r + 1) := by
          convert htotal using 1
          rw [hsum_succ r u, hsum_succ r v, heq0]
          dsimp [U, V]
          ring
        have htail' : U - V ∈ I ^ r := hcancel htail
        have htailq :
            Ideal.Quotient.mk (I ^ r) U = Ideal.Quotient.mk (I ^ r) V :=
          (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 htail'
        have htail_eq :
            (fun i : Fin r => u i.succ) = (fun i : Fin r => v i.succ) := by
          apply ihr
          · intro i
            exact hu i.succ
          · intro i
            exact hv i.succ
          · simpa [U, V] using htailq
        funext i
        refine Fin.cases heq0 (fun j => ?_) i
        exact congr_fun htail_eq j
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  obtain ⟨w, hwS, hwq⟩ := hrepresent n a
  have hwx : Chapter08MatchesTruncation I π S x n w := by
    refine ⟨hwS, ?_⟩
    calc
      AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) a := ha.symm
      _ = Ideal.Quotient.mk (I ^ n)
          (∑ i : Fin n, w i * π ^ (i : ℕ)) := hwq.symm
  refine ⟨w, hwx, ?_⟩
  intro v hv
  have hq : Ideal.Quotient.mk (I ^ n)
        (∑ i : Fin n, w i * π ^ (i : ℕ)) =
      Ideal.Quotient.mk (I ^ n) (∑ i : Fin n, v i * π ^ (i : ℕ)) := by
    calc
      Ideal.Quotient.mk (I ^ n)
          (∑ i : Fin n, w i * π ^ (i : ℕ)) =
          AdicCompletion.evalₐ I n x := hwx.2.symm
      _ = Ideal.Quotient.mk (I ^ n) (∑ i : Fin n, v i * π ^ (i : ℕ)) := hv.2
  exact (hunique n hwS hv.1 hq).symm

theorem chapter08_truncated_digits_are_compatible
    {A : Type*} [CommRing A] [IsDomain A] (I : Ideal A) (π : A) (S : Set A)
    (hI : I = Ideal.span {π})
    (hS : Chapter08IsResidueRepresentativeSet A I S)
    (hπ : π ≠ 0)
    {x : AdicCompletion I A} {m n : ℕ} (hmn : m ≤ n)
    {u : Fin m → A} {v : Fin n → A}
    (hu : Chapter08MatchesTruncation I π S x m u)
    (hv : Chapter08MatchesTruncation I π S x n v) :
    ∀ i : Fin m, u i = v ⟨i, lt_of_lt_of_le i.isLt hmn⟩ := by
  classical
  have hfactor : ∀ {r s : ℕ} (hrs : r ≤ s),
      Ideal.Quotient.factorPow I hrs (AdicCompletion.evalₐ I s x) =
        AdicCompletion.evalₐ I r x := by
    intro r s hrs
    let hr : (I ^ r • (⊤ : Ideal A)) = I ^ r := by ext; simp
    let hs : (I ^ s • (⊤ : Ideal A)) = I ^ s := by ext; simp
    change Ideal.Quotient.factorPow I hrs
        ((Ideal.quotientEquivAlgOfEq A hs) (x.val s)) =
      (Ideal.quotientEquivAlgOfEq A hr) (x.val r)
    rw [← x.property hrs]
    induction x.val s using Quotient.inductionOn' with
    | _ a =>
        change Ideal.Quotient.factorPow I hrs
            (Ideal.Quotient.mk (I ^ s) a) = Ideal.Quotient.mk (I ^ r) a
        rfl
  have htail : ∀ {r s : ℕ} (hrs : r ≤ s) (w : Fin s → A),
      (∑ i : Fin s, w i * π ^ (i : ℕ)) -
          ∑ i : Fin r, w ⟨i, lt_of_lt_of_le i.isLt hrs⟩ * π ^ (i : ℕ) ∈ I ^ r := by
    intro r s hrs w
    let f : ℕ → A := fun i =>
      if hi : i < s then w ⟨i, hi⟩ * π ^ i else 0
    have hsum_s : (∑ i : Fin s, w i * π ^ (i : ℕ)) =
        ∑ i ∈ Finset.range s, f i := by
      calc
        (∑ i : Fin s, w i * π ^ (i : ℕ)) =
            ∑ i : Fin s, f (i : ℕ) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [f, i.isLt]
        _ = ∑ i ∈ Finset.range s, f i := by
          rw [Fin.sum_univ_eq_sum_range f]
    have hsum_r :
        (∑ i : Fin r, w ⟨i, lt_of_lt_of_le i.isLt hrs⟩ * π ^ (i : ℕ)) =
          ∑ i ∈ Finset.range r, f i := by
      calc
        (∑ i : Fin r, w ⟨i, lt_of_lt_of_le i.isLt hrs⟩ * π ^ (i : ℕ)) =
            ∑ i : Fin r, f (i : ℕ) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [f, i.isLt, lt_of_lt_of_le i.isLt hrs]
        _ = ∑ i ∈ Finset.range r, f i := by
          rw [Fin.sum_univ_eq_sum_range f]
    rw [hsum_s, hsum_r, Finset.sum_range_sub_sum_range hrs]
    apply (I ^ r).sum_mem
    intro i hi
    rw [Finset.mem_filter] at hi
    have hi_lt : i < s := Finset.mem_range.1 hi.1
    have hir : r ≤ i := hi.2
    dsimp [f]
    rw [dif_pos hi_lt]
    rw [hI, Ideal.span_singleton_pow]
    apply Ideal.mem_span_singleton'.2
    refine ⟨w ⟨i, hi_lt⟩ * π ^ (i - r), ?_⟩
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hir]
  let v' : Fin m → A := fun i => v ⟨i, lt_of_lt_of_le i.isLt hmn⟩
  have hv' : Chapter08MatchesTruncation I π S x m v' := by
    refine ⟨?_, ?_⟩
    · intro i
      exact hv.1 ⟨i, lt_of_lt_of_le i.isLt hmn⟩
    · calc
        AdicCompletion.evalₐ I m x =
            Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) :=
          (hfactor hmn).symm
        _ = Ideal.Quotient.factorPow I hmn
            (Ideal.Quotient.mk (I ^ n)
              (∑ i : Fin n, v i * π ^ (i : ℕ))) := by rw [hv.2]
        _ = Ideal.Quotient.mk (I ^ m)
            (∑ i : Fin m, v' i * π ^ (i : ℕ)) := by
          calc
            Ideal.Quotient.factorPow I hmn
                (Ideal.Quotient.mk (I ^ n)
                  (∑ i : Fin n, v i * π ^ (i : ℕ))) =
                Ideal.Quotient.mk (I ^ m)
                  (∑ i : Fin n, v i * π ^ (i : ℕ)) := by rfl
            _ = Ideal.Quotient.mk (I ^ m)
                (∑ i : Fin m, v' i * π ^ (i : ℕ)) :=
              (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 (htail hmn v)
  have heq : u = v' :=
    (chapter08_truncated_digit_lemma I π S hI hS hπ x m).unique hu hv'
  intro i
  exact congr_fun heq i

-- The partial sums differ from the represented element by an element of I^n. -/
theorem chapter08_digit_partial_sum_error
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (S : Set A)
    {x : AdicCompletion I A} {d : ℕ → A}
    (hd : Chapter08DigitExpansion I π S x d) (n : ℕ) :
    AdicCompletion.evalₐ I n
        (x - Chapter08DigitPartialSum I π d n) = 0 := by
  rw [map_sub, hd.2.1 n]
  simp [Chapter08DigitPartialSum]

theorem chapter08_digit_terms_tend_to_zero
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (d : ℕ → A)
    (hI : I = Ideal.span {π}) :
    Chapter08AdicTendsToZero I (fun i => d i * π ^ i) := by
  intro n
  refine ⟨n, fun i hi => ?_⟩
  rw [hI, Ideal.span_singleton_pow]
  apply Ideal.mem_span_singleton'.2
  refine ⟨d i * π ^ (i - n), ?_⟩
  change d i * π ^ (i - n) * π ^ n = d i * π ^ i
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi]

-- Conversely, every digit series converges in the complete adic model. -/
theorem chapter08_every_digit_series_converges
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (d : ℕ → A)
    (hI : I = Ideal.span {π}) :
    ∃ x : AdicCompletion I A,
      Chapter08AdicConverges I (Chapter08DigitPartialSum I π d) x := by
  classical
  let s : ℕ → A := fun n => ∑ i ∈ Finset.range n, d i * π ^ i
  have hs : ∀ n : ℕ,
      s n ≡ s (n + 1) [SMOD (I ^ n • (⊤ : Submodule A A))] := by
    intro n
    rw [SModEq.sub_mem]
    dsimp [s]
    rw [Finset.sum_range_succ]
    have hterm : d n * π ^ n ∈ I ^ n := by
      rw [hI, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton'.2 ⟨d n, rfl⟩
    simpa [sub_eq_add_neg] using ((I ^ n).neg_mem hterm)
  let c : AdicCompletion.AdicCauchySequence I A :=
    AdicCompletion.AdicCauchySequence.mk I A s hs
  let x : AdicCompletion I A := AdicCompletion.mk I A c
  refine ⟨x, ?_⟩
  intro n
  refine ⟨n, fun m hnm => ?_⟩
  have hc :
      Ideal.Quotient.mk (I ^ n) (s m) = Ideal.Quotient.mk (I ^ n) (s n) := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    simpa [c, s, sub_eq_add_neg, add_comm, Ideal.smul_eq_mul, Ideal.mul_top] using
      (SModEq.sub_mem.1 (c.property hnm).neg)
  calc
    AdicCompletion.evalₐ I n (Chapter08DigitPartialSum I π d m) =
        Ideal.Quotient.mk (I ^ n) (s m) := by
          simp [Chapter08DigitPartialSum, s]
    _ = Ideal.Quotient.mk (I ^ n) (s n) := hc
    _ = AdicCompletion.evalₐ I n x := by
      simp [x, c, s]

/-- Digit sequences with values in the chosen representative set. -/
abbrev Chapter08DigitSequences (A : Type*) (S : Set A) : Type _ :=
  {d : ℕ → A // ∀ n : ℕ, d n ∈ S}

/-! The digit expansion is a bijection of sets, not in general a coefficientwise ring map. -/
theorem chapter08_digit_expansion_set_bijection
    {A : Type*} [CommRing A] [IsDomain A] (I : Ideal A) (π : A) (S : Set A)
    (hI : I = Ideal.span {π})
    (hS : Chapter08IsResidueRepresentativeSet A I S) (hπ : π ≠ 0) :
    ∃ e : AdicCompletion I A ≃ Chapter08DigitSequences A S,
      ∀ x, Chapter08DigitExpansion I π S x (e x).1 ∧
        ∀ d : ℕ → A,
          Chapter08DigitExpansion I π S x d → d = (e x).1 := by
  classical
  have htail : ∀ {r s : ℕ} (hrs : r ≤ s) (w : ℕ → A),
      (∑ i ∈ Finset.range s, w i * π ^ i) -
          ∑ i ∈ Finset.range r, w i * π ^ i ∈ I ^ r := by
    intro r s hrs w
    rw [Finset.sum_range_sub_sum_range hrs]
    apply (I ^ r).sum_mem
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [hI, Ideal.span_singleton_pow]
    apply Ideal.mem_span_singleton'.2
    refine ⟨w i * π ^ (i - r), ?_⟩
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi.2]
  let pref : AdicCompletion I A → ∀ n : ℕ, Fin n → A := fun x n =>
    (chapter08_truncated_digit_lemma I π S hI hS hπ x n).choose
  have hpref : ∀ (x : AdicCompletion I A) (n : ℕ),
      Chapter08MatchesTruncation I π S x n (pref x n) := by
    intro x n
    exact (chapter08_truncated_digit_lemma I π S hI hS hπ x n).choose_spec.1
  let digits : AdicCompletion I A → ℕ → A := fun x i =>
    pref x (i + 1) ⟨i, Nat.lt_succ_self i⟩
  have hdigit_mem : ∀ (x : AdicCompletion I A) (i : ℕ), digits x i ∈ S := by
    intro x i
    exact (hpref x (i + 1)).1 ⟨i, Nat.lt_succ_self i⟩
  have hpref_eq : ∀ (x : AdicCompletion I A) (n : ℕ) (i : Fin n),
      pref x n i = digits x i := by
    intro x n i
    have hcompat := chapter08_truncated_digits_are_compatible
      I π S hI hS hπ (Nat.succ_le_iff.2 i.isLt)
      (hpref x (i + 1)) (hpref x n)
    simpa [digits] using (hcompat ⟨i, Nat.lt_succ_self i⟩).symm
  have hEval : ∀ (x : AdicCompletion I A) (n : ℕ),
      AdicCompletion.evalₐ I n x =
        Ideal.Quotient.mk (I ^ n)
          (∑ i ∈ Finset.range n, digits x i * π ^ i) := by
    intro x n
    have hsum :
        (∑ i : Fin n, pref x n i * π ^ (i : ℕ)) =
          ∑ i ∈ Finset.range n, digits x i * π ^ i := by
      let q : ℕ → A := fun i =>
        if hi : i < n then pref x n ⟨i, hi⟩ * π ^ i else 0
      calc
        (∑ i : Fin n, pref x n i * π ^ (i : ℕ)) =
            ∑ i : Fin n, q (i : ℕ) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [q, i.isLt]
        _ = ∑ i ∈ Finset.range n, q i := by
              rw [Fin.sum_univ_eq_sum_range q]
        _ = ∑ i ∈ Finset.range n, digits x i * π ^ i := by
              apply Finset.sum_congr rfl
              intro i hi
              have he := hpref_eq x n ⟨i, Finset.mem_range.1 hi⟩
              simp [q, Finset.mem_range.1 hi, digits, he]
    rw [(hpref x n).2, hsum]
  have hconv_of_expansion : ∀ (x : AdicCompletion I A),
      Chapter08AdicConverges I (Chapter08DigitPartialSum I π (digits x)) x := by
    intro x n
    refine ⟨n, fun m hnm => ?_⟩
    calc
      AdicCompletion.evalₐ I n
          (Chapter08DigitPartialSum I π (digits x) m) =
          Ideal.Quotient.mk (I ^ n)
            (∑ i ∈ Finset.range m, digits x i * π ^ i) := by
              simp [Chapter08DigitPartialSum]
      _ = Ideal.Quotient.mk (I ^ n)
            (∑ i ∈ Finset.range n, digits x i * π ^ i) :=
          (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 (htail hnm (digits x))
      _ = AdicCompletion.evalₐ I n x := (hEval x n).symm
  let toDigits : AdicCompletion I A → Chapter08DigitSequences A S := fun x =>
    ⟨digits x, hdigit_mem x⟩
  have hfinite_of_converges : ∀ (d : Chapter08DigitSequences A S)
      (x : AdicCompletion I A),
      Chapter08AdicConverges I (Chapter08DigitPartialSum I π d.1) x →
      ∀ n : ℕ,
        AdicCompletion.evalₐ I n x =
          Ideal.Quotient.mk (I ^ n)
            (∑ i ∈ Finset.range n, d.1 i * π ^ i) := by
    intro d x hconv n
    obtain ⟨N, hN⟩ := hconv n
    let m := max N n
    have hmN : N ≤ m := le_max_left _ _
    have hmn : n ≤ m := le_max_right _ _
    calc
      AdicCompletion.evalₐ I n x =
          AdicCompletion.evalₐ I n (Chapter08DigitPartialSum I π d.1 m) :=
        (hN m hmN).symm
      _ = Ideal.Quotient.mk (I ^ n)
          (∑ i ∈ Finset.range m, d.1 i * π ^ i) := by
            simp [Chapter08DigitPartialSum]
      _ = Ideal.Quotient.mk (I ^ n)
          (∑ i ∈ Finset.range n, d.1 i * π ^ i) :=
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 (htail hmn d.1)
  let fromDigits : Chapter08DigitSequences A S → AdicCompletion I A := fun d =>
    Classical.choose (chapter08_every_digit_series_converges I π d.1 hI)
  have hfrom_conv : ∀ d : Chapter08DigitSequences A S,
      Chapter08AdicConverges I (Chapter08DigitPartialSum I π d.1) (fromDigits d) := by
    intro d
    exact Classical.choose_spec (chapter08_every_digit_series_converges I π d.1 hI)
  have hfrom_expansion : ∀ d : Chapter08DigitSequences A S,
      Chapter08DigitExpansion I π S (fromDigits d) d.1 := by
    intro d
    refine ⟨d.2, hfinite_of_converges d (fromDigits d) (hfrom_conv d), hfrom_conv d⟩
  have hdigit_expansion : ∀ x : AdicCompletion I A,
      Chapter08DigitExpansion I π S x (digits x) := by
    intro x
    exact ⟨hdigit_mem x, hEval x, hconv_of_expansion x⟩
  have hexp_unique : ∀ {x : AdicCompletion I A} {d e : ℕ → A},
      Chapter08DigitExpansion I π S x d →
        Chapter08DigitExpansion I π S x e → d = e := by
    intro x d e hd he
    funext i
    let n := i + 1
    let u : Fin n → A := fun j => d j
    let v : Fin n → A := fun j => e j
    have hu : Chapter08MatchesTruncation I π S x n u := by
      refine ⟨fun j => hd.1 j, ?_⟩
      calc
        AdicCompletion.evalₐ I n x =
            Ideal.Quotient.mk (I ^ n)
              (∑ j ∈ Finset.range n, d j * π ^ j) := hd.2.1 n
        _ = Ideal.Quotient.mk (I ^ n)
            (∑ j : Fin n, u j * π ^ (j : ℕ)) := by
          change Ideal.Quotient.mk (I ^ n)
              (∑ j ∈ Finset.range n, d j * π ^ j) =
            Ideal.Quotient.mk (I ^ n)
              (∑ j : Fin n, d j * π ^ (j : ℕ))
          rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => d j * π ^ j)]
    have hv : Chapter08MatchesTruncation I π S x n v := by
      refine ⟨fun j => he.1 j, ?_⟩
      calc
        AdicCompletion.evalₐ I n x =
            Ideal.Quotient.mk (I ^ n)
              (∑ j ∈ Finset.range n, e j * π ^ j) := he.2.1 n
        _ = Ideal.Quotient.mk (I ^ n)
            (∑ j : Fin n, v j * π ^ (j : ℕ)) := by
          change Ideal.Quotient.mk (I ^ n)
              (∑ j ∈ Finset.range n, e j * π ^ j) =
            Ideal.Quotient.mk (I ^ n)
              (∑ j : Fin n, e j * π ^ (j : ℕ))
          rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => e j * π ^ j)]
    have huv := (chapter08_truncated_digit_lemma I π S hI hS hπ x n).unique hu hv
    exact congr_fun huv ⟨i, Nat.lt_succ_self i⟩
  let e : AdicCompletion I A ≃ Chapter08DigitSequences A S :=
    { toFun := toDigits
      invFun := fromDigits
      left_inv := by
        intro x
        apply AdicCompletion.ext_evalₐ
        intro n
        calc
          AdicCompletion.evalₐ I n (fromDigits (toDigits x)) =
              Ideal.Quotient.mk (I ^ n)
                (∑ i ∈ Finset.range n, digits x i * π ^ i) :=
            (hfrom_expansion (toDigits x)).2.1 n
          _ = AdicCompletion.evalₐ I n x := (hEval x n).symm
      right_inv := by
        intro d
        apply Subtype.ext
        funext i
        have h := hexp_unique (x := fromDigits d) (d := d.1)
          (e := (digits (fromDigits d)))
          (hfrom_expansion d) (hdigit_expansion (fromDigits d))
        change digits (fromDigits d) i = d.1 i
        exact (congr_fun h i).symm }
  refine ⟨e, ?_⟩
  intro x
  refine ⟨hdigit_expansion x, ?_⟩
  intro d hd
  exact hexp_unique hd (hdigit_expansion x)

/-- The raw coefficientwise addition suggested by a digit sequence. -/
def Chapter08CoefficientwiseAdd {A : Type*} [Add A]
    (d e : ℕ → A) : ℕ → A := fun n => d n + e n

/-- The raw coefficientwise multiplication suggested by a digit sequence. -/
def Chapter08CoefficientwiseMul {A : Type*} [Mul A]
    (d e : ℕ → A) : ℕ → A := fun n => d n * e n

/-- A predicate saying that a digit coding respects addition coefficient by coefficient. -/
def Chapter08CoefficientwiseAdditiveCoding
    {A : Type*} [CommRing A] (I : Ideal A) (S : Set A)
    (e : AdicCompletion I A ≃ Chapter08DigitSequences A S) : Prop :=
  ∀ x y : AdicCompletion I A, ∀ n : ℕ,
    (e (x + y)).1 n = Chapter08CoefficientwiseAdd (e x).1 (e y).1 n

private theorem chapter08_mixed_characteristic_no_additive_residue_section
    {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A] [CharZero A]
    (I : Ideal A) (p : ℕ) [Fact p.Prime]
    (hI : I = Ideal.span {(p : A)})
    (hImax : I = IsLocalRing.maximalIdeal A) :
    ¬ ∃ f : (A ⧸ I) →+ A, Function.Injective f := by
  classical
  rintro ⟨f, hf⟩
  have hp : (p : A) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
  have hzero : ∀ q : A ⧸ I, f q = 0 := by
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hq : p • (Ideal.Quotient.mk I a) = 0 := by
      rw [← map_nsmul]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [hI]
      have hpI : (p : A) ∈ Ideal.span {(p : A)} :=
        Ideal.mem_span_singleton_self (p : A)
      simpa [nsmul_eq_mul, mul_comm] using
        (Ideal.span {(p : A)}).mul_mem_left a hpI
    have hpq' : p • f (Ideal.Quotient.mk I a) = 0 := by
      calc
        p • f (Ideal.Quotient.mk I a) =
            f (p • Ideal.Quotient.mk I a) := (map_nsmul f p _).symm
        _ = 0 := by rw [hq, map_zero]
    have hpq : (p : A) * f (Ideal.Quotient.mk I a) = 0 := by
      simpa [nsmul_eq_mul] using hpq'
    exact (mul_eq_zero.mp hpq).resolve_left hp
  have hItop : I ≠ (⊤ : Ideal A) := by
    rw [hImax]
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  exact (Ideal.Quotient.zero_ne_one_iff.mpr hItop) (hf (by simp [hzero]))

/-! In mixed characteristic, the absence of a coefficient-field embedding is the carry
obstruction behind the preceding set-theoretic, rather than coefficientwise-ring, model. -/
private theorem chapter08_mixed_characteristic_additive_section_obstruction
    {A : Type*} [CommRing A] [CharZero A] (I : Ideal A) (S : Set A)
    (p : ℕ) [Fact p.Prime]
    (hI : I = Ideal.span {(p : A)})
    (hS : Chapter08IsResidueRepresentativeSet A I S)
    (hnoembed : ¬ ∃ f : (A ⧸ I) →+ A, Function.Injective f)
    (e : AdicCompletion I A ≃ Chapter08DigitSequences A S)
    (hdigits : ∀ x, Chapter08DigitExpansion I (p : A) S x (e x).1) :
    ¬ Chapter08CoefficientwiseAdditiveCoding I S e := by
  classical
  intro hadd
  let d0 : A → A := fun a => (e (algebraMap A (AdicCompletion I A) a)).1 0
  have hadd0 : ∀ a b : A, d0 (a + b) = d0 a + d0 b := by
    intro a b
    have h := hadd (algebraMap A (AdicCompletion I A) a)
      (algebraMap A (AdicCompletion I A) b) 0
    simpa [d0, Chapter08CoefficientwiseAdd] using h
  have hzero : d0 0 = 0 := by
    have h := hadd0 0 0
    apply Eq.symm
    apply add_left_cancel (a := d0 0)
    simpa using h
  have hdigit_mem : ∀ a : A, d0 a ∈ S := by
    intro a
    simpa [d0] using (hdigits (algebraMap A (AdicCompletion I A) a)).1 0
  have hmk : ∀ a : A,
      Ideal.Quotient.mk I a = Ideal.Quotient.mk I (d0 a) := by
    intro a
    have h := (hdigits (algebraMap A (AdicCompletion I A) a)).2.1 1
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of] at h
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    have h' : Ideal.Quotient.mk (I ^ 1) a =
        Ideal.Quotient.mk (I ^ 1) (d0 a) := by
      simpa [d0, AdicCompletion.algebraMap_apply] using h
    simpa using (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 h'
  have h0S : (0 : A) ∈ S := by
    simpa [hzero] using hdigit_mem 0
  have hzero_of_mem : ∀ {a : A}, a ∈ I → d0 a = 0 := by
    intro a ha
    have hda : d0 a ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← hmk a]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    exact (hS 0).unique ⟨hdigit_mem a, by simpa using I.neg_mem hda⟩
      ⟨h0S, by simpa using I.zero_mem⟩
  let f0 : A →+ A :=
    { toFun := d0
      map_zero' := hzero
      map_add' := hadd0 }
  have hker : f0.ker = I.toAddSubgroup := by
    ext a
    constructor
    · intro ha
      change d0 a = 0 at ha
      have hqa : Ideal.Quotient.mk I a = 0 := by
        rw [hmk a, ha]
        exact map_zero (Ideal.Quotient.mk I)
      exact Ideal.Quotient.eq_zero_iff_mem.mp hqa
    · intro ha
      change d0 a = 0
      exact hzero_of_mem ha
  have hfactor : I.toAddSubgroup ≤ f0.ker := by
    rw [hker]
  let f : (A ⧸ I) →+ A :=
    QuotientAddGroup.lift I.toAddSubgroup f0 hfactor
  have hf_mk : ∀ a : A,
      f (Ideal.Quotient.mk I a) = d0 a := by
    intro a
    rfl
  have hf_inj : Function.Injective f := by
    intro q r hqr
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective r
    have hab : d0 a = d0 b := by
      simpa [hf_mk] using hqr
    have hab0 : f0 (a - b) = 0 := by
      rw [map_sub]
      change d0 a - d0 b = 0
      rw [hab, sub_self]
    have habI : a - b ∈ I := by
      have : a - b ∈ f0.ker := hab0
      rw [hker] at this
      exact this
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 habI
  exact hnoembed ⟨f, hf_inj⟩

theorem chapter08_mixed_characteristic_digit_carries_obstruct_coefficientwise_addition
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A]
    (I : Ideal A) (S : Set A)
    (p : ℕ) [Fact p.Prime]
    (hI : I = Ideal.span {(p : A)})
    (hS : Chapter08IsResidueRepresentativeSet A I S)
    (hImax : I = IsLocalRing.maximalIdeal A)
    (e : AdicCompletion I A ≃ Chapter08DigitSequences A S)
    (hdigits : ∀ x, Chapter08DigitExpansion I (p : A) S x (e x).1) :
    ¬ Chapter08CoefficientwiseAdditiveCoding I S e := by
  have hnoembed :=
    chapter08_mixed_characteristic_no_additive_residue_section I p hI hImax
  exact chapter08_mixed_characteristic_additive_section_obstruction
    I S p hI hS hnoembed e hdigits

/-! Equal characteristic: a coefficient field gives literal formal-series coefficients. -/
structure Chapter08CoefficientFieldSection
    (A k : Type*) [CommRing A] [Field k] (I : Ideal A) where
  lift : k →+* A
  residue : A →+* k
  residue_lift : residue.comp lift = RingHom.id k
  kernel_residue : RingHom.ker residue = I

/-- The coefficient sequence represented by a formal power series. -/
def Chapter08CoefficientSequenceEquiv (k : Type*) [Field k] :
    (ℕ → k) ≃ PowerSeries k where
  toFun := PowerSeries.mk
  invFun := fun f n => PowerSeries.coeff n f
  left_inv := by
    intro f
    funext n
    simp
  right_inv := by
    intro f
    apply PowerSeries.ext
    intro n
    simp

/-- The Cauchy product of two coefficient sequences. -/
def Chapter08CauchyProduct {k : Type*} [Semiring k]
    (a b : ℕ → k) (n : ℕ) : k :=
  ∑ i ∈ Finset.range (n + 1), a i * b (n - i)

theorem chapter08_power_series_multiplication_is_cauchy_product
    {k : Type*} [Field k] (a b : ℕ → k) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b) =
      Chapter08CauchyProduct a b n := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Chapter08CauchyProduct]

structure Chapter08FormalSeriesModel
    (A k : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field k] (I : Ideal A) (π : A)
    (sectionData : Chapter08CoefficientFieldSection A k I) where
  equiv : AdicCompletion I A ≃+* PowerSeries k
  maps_section : ∀ c : k,
    equiv (algebraMap A (AdicCompletion I A) (sectionData.lift c)) = PowerSeries.C c
  maps_uniformizer :
    equiv (algebraMap A (AdicCompletion I A) π) = PowerSeries.X

/-! A complete equal-characteristic DVR with a coefficient field has the formal-series model. -/
theorem chapter08_equal_characteristic_formal_series_model
    {A k : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field k] (I : Ideal A) (π : A)
    (hI : I = Ideal.span {π})
    (hcomplete : IsAdicComplete I A)
    (sectionData : Chapter08CoefficientFieldSection A k I) :
    Nonempty (Chapter08FormalSeriesModel A k I π sectionData) := by
  classical
  letI : WithIdeal A := ⟨I⟩
  letI : TopologicalSpace k := ⊥
  letI : UniformSpace k := ⊥
  letI : DiscreteTopology k := discreteTopology_bot k
  have htop := (IsAdic.isAdicComplete_iff (I := I) (by rfl)).mp hcomplete
  letI : CompleteSpace A := htop.1
  letI : T2Space A := htop.2
  have hres_surj : Function.Surjective sectionData.residue := by
    intro c
    refine ⟨sectionData.lift c, ?_⟩
    simpa using congrArg (fun g => g c) sectionData.residue_lift
  have hImax : I.IsMaximal := by
    rw [← sectionData.kernel_residue]
    exact RingHom.ker_isMaximal_of_surjective sectionData.residue hres_surj
  have hInonbot : I ≠ (⊥ : Ideal A) :=
    Ring.ne_bot_of_isMaximal_of_not_isField hImax
      (IsDiscreteValuationRing.not_isField A)
  have hπ : π ≠ 0 := by
    intro hπ0
    apply hInonbot
    calc
      I = Ideal.span {π} := hI
      _ = (⊥ : Ideal A) := Ideal.span_singleton_eq_bot.mpr hπ0
  have hπmem : π ∈ I := by
    rw [hI]
    exact Ideal.mem_span_singleton_self π
  have hπeval : PowerSeries.HasEval π := by
    exact WithIdeal.isTopologicallyNilpotent_of_mem hπmem
  have hlift_cont : Continuous sectionData.lift := continuous_of_discreteTopology
  let f : PowerSeries k →+* A :=
    PowerSeries.eval₂Hom hlift_cont hπeval
  have hfC (c : k) : f (PowerSeries.C c) = sectionData.lift c := by
    dsimp [f]
    rw [PowerSeries.coe_eval₂Hom]
    simp
  have hfX : f PowerSeries.X = π := by
    dsimp [f]
    rw [PowerSeries.coe_eval₂Hom]
    simp
  have hmap :
      (Ideal.span ({PowerSeries.X} : Set (PowerSeries k))).map f = I := by
    rw [Ideal.map_span]
    simpa [hfX, hI]
  have hres : Function.Surjective
      ((Ideal.Quotient.mk ((Ideal.span ({PowerSeries.X} : Set (PowerSeries k))).map f)).comp f) := by
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨PowerSeries.C (sectionData.residue a), ?_⟩
    rw [RingHom.comp_apply, hfC, hmap]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    have hmem : sectionData.lift (sectionData.residue a) - a ∈
        RingHom.ker sectionData.residue := by
      apply RingHom.mem_ker.mpr
      have hleft : sectionData.residue (sectionData.lift (sectionData.residue a)) =
          sectionData.residue a := by
        simpa [RingHom.comp_apply] using
          congrArg (fun g => g (sectionData.residue a)) sectionData.residue_lift
      rw [map_sub, hleft, sub_self]
    simpa only [sectionData.kernel_residue] using hmem
  letI : IsHausdorff
      ((Ideal.span ({PowerSeries.X} : Set (PowerSeries k))).map f) A := by
    rw [hmap]
    exact hcomplete.toIsHausdorff
  letI : IsAdicComplete
      (Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) (PowerSeries k) := inferInstance
  have hf_surj : Function.Surjective f := by
    exact surjective_of_mk_map_comp_surjective f hres
  have hf_inj : Function.Injective f := by
    intro p q hpq
    by_contra hne
    let r : PowerSeries k := p - q
    have hr : r ≠ 0 := by
      intro hr0
      apply hne
      exact sub_eq_zero.mp hr0
    have hunit : IsUnit (PowerSeries.divXPowOrder r) :=
      PowerSeries.isUnit_divided_by_X_pow_order hr
    have hunit_map : IsUnit (f (PowerSeries.divXPowOrder r)) := hunit.map f
    have hpow : f (PowerSeries.X ^ r.order.toNat) ≠ 0 := by
      rw [map_pow, hfX]
      exact pow_ne_zero _ hπ
    have hprod : f (PowerSeries.X ^ r.order.toNat * PowerSeries.divXPowOrder r) ≠ 0 := by
      rw [map_mul]
      exact mul_ne_zero hpow hunit_map.ne_zero
    apply hprod
    rw [PowerSeries.X_pow_order_mul_divXPowOrder]
    dsimp [r]
    rw [map_sub, hpq, sub_self]
  let e₀ : PowerSeries k ≃+* A := RingEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  let eA : A ≃+* AdicCompletion I A := (AdicCompletion.ofAlgEquiv I).toRingEquiv
  let e : AdicCompletion I A ≃+* PowerSeries k := eA.symm.trans e₀.symm
  have heA (a : A) :
      eA.symm (algebraMap A (AdicCompletion I A) a) = a := by
    change (AdicCompletion.ofAlgEquiv I).symm (AdicCompletion.of I A a) = a
    exact AdicCompletion.ofAlgEquiv_symm_of I a
  have he₀C (c : k) : e₀ (PowerSeries.C c) = sectionData.lift c := by
    change f (PowerSeries.C c) = sectionData.lift c
    exact hfC c
  have he₀X : e₀ PowerSeries.X = π := by
    change f PowerSeries.X = π
    exact hfX
  refine ⟨{
    equiv := e
    maps_section := ?_
    maps_uniformizer := ?_ }⟩
  · intro c
    apply e₀.injective
    simpa [e, heA] using (he₀C c).symm
  · apply e₀.injective
    simpa [e, heA] using he₀X.symm

/-! ### 8.3 The p-adic integers and numbers -/

/-- Mathlib's p-adic integers and p-adic numbers, named as in the book. -/
abbrev Chapter08PadicIntegers (p : ℕ) [Fact p.Prime] := PadicInt p
abbrev Chapter08PadicNumbers (p : ℕ) [Fact p.Prime] := Padic p

/-- The inverse-limit presentation of Z_p used in this chapter. -/
abbrev Chapter08PadicIntegerInverseLimit (p : ℕ) [Fact p.Prime] :=
  Chapter08CompatibleFamily ℤ (Ideal.span {(p : ℤ)})

abbrev Chapter08Zp (p : ℕ) [Fact p.Prime] := Chapter08PadicIntegerInverseLimit p
abbrev Chapter08Qp (p : ℕ) [Fact p.Prime] := Chapter08PadicNumbers p

/-- The p-adic numbers are the fraction field of the p-adic integers. -/
theorem chapter08_padic_numbers_are_the_fraction_field_of_integers
    (p : ℕ) [Fact p.Prime] :
    IsFractionRing (Chapter08PadicIntegers p) (Chapter08PadicNumbers p) := by
  infer_instance

-- The inverse-limit ring is canonically the usual Mathlib p-adic integer ring. -/
theorem chapter08_padic_integer_inverse_limit
    (p : ℕ) [Fact p.Prime] :
    Nonempty (Chapter08PadicIntegers p ≃+* Chapter08Zp p) := by
  classical
  let I : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hpow : ∀ n : ℕ, I ^ n = Ideal.span {((p ^ n : ℕ) : ℤ)} := by
    intro n
    simp [I, Ideal.span_singleton_pow, Nat.cast_pow]
  let q (n : ℕ) : (ℤ ⧸ I ^ n) ≃+* ZMod (p ^ n) :=
    (Ideal.quotientEquivAlgOfEq ℤ (hpow n)).toRingEquiv.trans
      (Int.quotientSpanNatEquivZMod (p ^ n))
  have q_mk (n : ℕ) (z : ℤ) :
      q n (Ideal.Quotient.mk (I ^ n) z) = (z : ZMod (p ^ n)) := by
    simp [q, hpow]
  have hfactor_q : ∀ {m n : ℕ} (hmn : m ≤ n) (z : ℤ ⧸ I ^ n),
      (ZMod.cast (q n z) : ZMod (p ^ m)) =
        q m (Ideal.Quotient.factorPow I hmn z) := by
    intro m n hmn z
    refine Submodule.Quotient.induction_on (I ^ n) z ?_
    intro z
    simpa [q, Ideal.Quotient.factorPow] using
      (ZMod.cast_intCast (pow_dvd_pow p hmn) z)
  have hcoord : ∀ {m n : ℕ} (hmn : m ≤ n) (z : Chapter08Zp p),
      Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn) (z.1 n) = z.1 m := by
    intro m n hmn z
    have hlong :=
      Ideal.Quotient.eq_factor_of_eq_factor_succ
        (I := fun i : ℕ => I ^ (i + 1))
        (fun i j hij => Ideal.pow_le_pow_right (Nat.succ_le_succ hij))
        (fun i => z.1 i)
        (fun i => by
          simpa [Ideal.Quotient.factorPow] using (z.2 i).symm)
        hmn
    simpa [Ideal.Quotient.factorPow] using hlong.symm
  let coord (n : ℕ) : Chapter08Zp p →+* ℤ ⧸ I ^ (n + 1) :=
    { toFun := fun z => z.1 n
      map_one' := rfl
      map_mul' := by intro x y; rfl
      map_zero' := rfl
      map_add' := by intro x y; rfl }
  let f0 : Chapter08Zp p →+* ZMod (p ^ 0) :=
    { toFun := fun _ => 0
      map_one' := by
        letI : Subsingleton (ZMod (p ^ 0)) :=
          ZMod.subsingleton_iff.2 (pow_zero p)
        exact Subsingleton.elim _ _
      map_mul' := by
        letI : Subsingleton (ZMod (p ^ 0)) :=
          ZMod.subsingleton_iff.2 (pow_zero p)
        intros
        exact Subsingleton.elim _ _
      map_zero' := rfl
      map_add' := by
        letI : Subsingleton (ZMod (p ^ 0)) :=
          ZMod.subsingleton_iff.2 (pow_zero p)
        intros
        exact Subsingleton.elim _ _ }
  let f : ∀ n : ℕ, Chapter08Zp p →+* ZMod (p ^ n) :=
    fun n => Nat.casesOn n f0 (fun k => (q (k + 1)).toRingHom.comp (coord k))
  have hfcompat : ∀ (m n : ℕ) (hmn : m ≤ n),
      (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))).comp (f n) = f m := by
    intro m n hmn
    cases m with
    | zero =>
        apply RingHom.ext
        intro z
        letI : Subsingleton (ZMod (p ^ 0)) :=
          ZMod.subsingleton_iff.2 (pow_zero p)
        exact Subsingleton.elim _ _
    | succ m =>
        cases n with
        | zero => omega
        | succ n =>
            apply RingHom.ext
            intro z
            change (ZMod.cast (q (n + 1) (z.1 n)) : ZMod (p ^ (m + 1))) =
              q (m + 1) (z.1 m)
            rw [hfactor_q (m := m + 1) (n := n + 1)
              hmn (z.1 n), hcoord (Nat.le_of_succ_le_succ hmn) z]
  let fromFamily : Chapter08Zp p →+* Chapter08PadicIntegers p :=
    PadicInt.lift (f_compat := hfcompat)
  let toFamilyFun : Chapter08PadicIntegers p → Chapter08Zp p := fun x =>
    ⟨fun n => (q (n + 1)).symm (PadicInt.toZModPow (n + 1) x), by
      intro n
      apply (q (n + 1)).injective
      rw [RingEquiv.apply_symm_apply]
      rw [← hfactor_q (m := n + 1) (n := n + 2)
        (Nat.le_succ (n + 1)) ((q (n + 2)).symm (PadicInt.toZModPow (n + 2) x))]
      simp only [RingEquiv.apply_symm_apply]
      exact PadicInt.cast_toZModPow (n + 1) (n + 2) (Nat.le_succ (n + 1)) x⟩
  let toFamily : Chapter08PadicIntegers p →+* Chapter08Zp p :=
    { toFun := toFamilyFun
      map_one' := by
        apply Subtype.ext
        funext n
        simp [toFamilyFun]
      map_mul' := by
        intro x y
        apply Subtype.ext
        funext n
        simp [toFamilyFun]
      map_zero' := by
        apply Subtype.ext
        funext n
        simp [toFamilyFun]
      map_add' := by
        intro x y
        apply Subtype.ext
        funext n
        simp [toFamilyFun] }
  have hfrom : ∀ x : Chapter08PadicIntegers p, fromFamily (toFamily x) = x := by
    intro x
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
        letI : Subsingleton (ZMod (p ^ 0)) :=
          ZMod.subsingleton_iff.2 (pow_zero p)
        exact Subsingleton.elim _ _
    | succ n =>
        have hspec := RingHom.congr_fun
          (PadicInt.lift_spec (f := f) hfcompat (n + 1)) (toFamily x)
        simpa [fromFamily, toFamily, toFamilyFun, f, coord] using hspec
  have hto : ∀ z : Chapter08Zp p, toFamily (fromFamily z) = z := by
    intro z
    apply Subtype.ext
    funext n
    apply (q (n + 1)).injective
    have hspec := RingHom.congr_fun
      (PadicInt.lift_spec (f := f) hfcompat (n + 1)) z
    simpa [toFamily, toFamilyFun, f, coord, fromFamily] using hspec
  let e : Chapter08PadicIntegers p ≃+* Chapter08Zp p :=
    RingEquiv.ofBijective toFamily
      ⟨by
        intro x y hxy
        have h := congrArg fromFamily hxy
        rw [hfrom x, hfrom y] at h
        exact h
       , by
        intro z
        exact ⟨fromFamily z, hto z⟩⟩
  exact ⟨e⟩

-- Z_p is a complete DVR with uniformizer p and residue field F_p. -/
theorem chapter08_padic_integers_are_a_complete_dvr
    (p : ℕ) [Fact p.Prime] :
    IsDiscreteValuationRing (Chapter08PadicIntegers p) ∧
      CompleteSpace (Chapter08PadicIntegers p) ∧
      Irreducible (p : Chapter08PadicIntegers p) ∧
      Nonempty (IsLocalRing.ResidueField (Chapter08PadicIntegers p) ≃+* ZMod p) := by
  exact ⟨inferInstance, inferInstance, PadicInt.irreducible_p, ⟨PadicInt.residueField⟩⟩

/-- The digit alphabet for p-adic integers. -/
abbrev Chapter08PadicDigitSequences (p : ℕ) :=
  {a : ℕ → ℕ // ∀ i : ℕ, a i < p}

/-- The finite partial sum of a p-adic digit sequence. -/
def Chapter08PadicPartialSum (p : ℕ) [Fact p.Prime]
    (a : ℕ → ℕ) (n : ℕ) : Chapter08PadicIntegers p :=
  ∑ i ∈ Finset.range n,
    (a i : Chapter08PadicIntegers p) * (p : Chapter08PadicIntegers p) ^ i

/-- A convergent p-adic digit expansion with digits 0 ≤ a_i < p. -/
def Chapter08PadicExpansion (p : ℕ) [Fact p.Prime]
    (x : Chapter08PadicIntegers p) (a : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, a i < p) ∧ Tendsto (Chapter08PadicPartialSum p a) atTop (𝓝 x)

/-! Every p-adic integer has a unique base-p expansion. -/
theorem chapter08_padic_digit_expansion_unique
    (p : ℕ) [Fact p.Prime] (x : Chapter08PadicIntegers p) :
    ∃! a : ℕ → ℕ, Chapter08PadicExpansion p x a := by
  classical
  let b : ℕ → ℕ := fun n => x.appr n
  let a : ℕ → ℕ := fun n =>
    (b (n + 1) - b n) / p ^ n
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have hmono : ∀ n : ℕ, b n ≤ b (n + 1) := by
    intro n
    simpa [b, Nat.succ_eq_add_one] using
      (PadicInt.appr_mono x (Nat.le_succ n))
  have hdvd : ∀ n : ℕ, p ^ n ∣ b (n + 1) - b n := by
    intro n
    simpa [b, Nat.succ_eq_add_one] using
      (PadicInt.dvd_appr_sub_appr x n (n + 1) (Nat.le_succ n))
  have ha_lt : ∀ n : ℕ, a n < p := by
    intro n
    apply (Nat.mul_lt_mul_right (Nat.pow_pos hp)).mp
    calc
      a n * p ^ n = b (n + 1) - b n := Nat.div_mul_cancel (hdvd n)
      _ < p ^ (n + 1) :=
        lt_of_le_of_lt (Nat.sub_le _ _)
          (by simpa [b] using PadicInt.appr_lt x (n + 1))
      _ = p * p ^ n := by rw [pow_succ, Nat.mul_comm]
  have hsum : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, a i * p ^ i) = b n := by
    intro n
    induction n with
    | zero => simp [b, PadicInt.appr]
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        rw [Nat.div_mul_cancel (hdvd n)]
        have hmn := hmono n
        omega
  let hlim : Tendsto (fun n : ℕ => (b n : Chapter08PadicIntegers p)) atTop (𝓝 x) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt p hε
    refine ⟨N, fun n hn => ?_⟩
    have hle : ‖x - (b n : Chapter08PadicIntegers p)‖ ≤
        (p : ℝ) ^ (-(n : ℤ)) := by
      apply (PadicInt.norm_le_pow_iff_mem_span_pow _ _).2
      simpa [b] using PadicInt.appr_spec n x
    have hpow : (p : ℝ) ^ (-(n : ℤ)) ≤ (p : ℝ) ^ (-(N : ℤ)) := by
      apply zpow_le_zpow_right₀
        (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt.le)
      exact neg_le_neg (by exact_mod_cast hn)
    rw [dist_eq_norm, norm_sub_rev]
    exact hle.trans_lt (hpow.trans_lt hN)
  have hpartial_diff : ∀ (d : ℕ → ℕ) {k m : ℕ}, k ≤ m →
      Chapter08PadicPartialSum p d m - Chapter08PadicPartialSum p d k ∈
        Ideal.span {((p : Chapter08PadicIntegers p) ^ k)} := by
    intro d k m hkm
    rw [Chapter08PadicPartialSum, Chapter08PadicPartialSum]
    rw [Finset.sum_range_sub_sum_range hkm]
    apply (Ideal.span {((p : Chapter08PadicIntegers p) ^ k)}).sum_mem
    intro i hi
    rw [Finset.mem_filter] at hi
    apply Ideal.mem_span_singleton'.2
    refine ⟨(d i : Chapter08PadicIntegers p) *
        (p : Chapter08PadicIntegers p) ^ (i - k), ?_⟩
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi.2]
  have hsum_lt : ∀ (d : ℕ → ℕ), (∀ i, d i < p) → ∀ n,
      (∑ i ∈ Finset.range n, d i * p ^ i) < p ^ n := by
    intro d hd n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        have hsum' :
            (∑ i ∈ Finset.range n, d i * p ^ i) + d n * p ^ n <
              p ^ n + d n * p ^ n := by omega
        have hmul_le : p ^ n + d n * p ^ n ≤ p * p ^ n := by
          calc
            p ^ n + d n * p ^ n = (d n + 1) * p ^ n := by ring
            _ ≤ p * p ^ n := by
              exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (hd n))
        simpa [pow_succ, Nat.mul_comm] using hsum'.trans_le hmul_le
  have hfinite_eq : ∀ (d : ℕ → ℕ), Chapter08PadicExpansion p x d → ∀ n,
      (∑ i ∈ Finset.range n, d i * p ^ i) = b n := by
    intro d hd n
    have hclosed : IsClosed
        (Ideal.span {((p : Chapter08PadicIntegers p) ^ n)} :
          Set (Chapter08PadicIntegers p)) :=
      (Ideal.isCompact_of_fg (IsNoetherian.noetherian _)).isClosed
    have hxd : x - Chapter08PadicPartialSum p d n ∈
        Ideal.span {((p : Chapter08PadicIntegers p) ^ n)} := by
      apply hclosed.mem_of_tendsto
        ((hd.2.sub tendsto_const_nhds))
      refine eventually_atTop.2 ⟨n, fun m hmn => ?_⟩
      exact hpartial_diff d hmn
    have hxb : x - (b n : Chapter08PadicIntegers p) ∈
        Ideal.span {((p : Chapter08PadicIntegers p) ^ n)} := by
      simpa [b] using PadicInt.appr_spec n x
    have hdiff : Chapter08PadicPartialSum p d n - (b n : Chapter08PadicIntegers p) ∈
        Ideal.span {((p : Chapter08PadicIntegers p) ^ n)} := by
      have h := (Ideal.span {((p : Chapter08PadicIntegers p) ^ n)}).sub_mem hxb hxd
      convert h using 1 <;> ring
    have hker : Chapter08PadicPartialSum p d n - (b n : Chapter08PadicIntegers p) ∈
        RingHom.ker (PadicInt.toZModPow n) := by
      rw [PadicInt.ker_toZModPow]
      exact hdiff
    have hto := (RingHom.mem_ker).1 hker
    have hmodZ :
        ((↑(∑ i ∈ Finset.range n, d i * p ^ i) : ZMod (p ^ n))) =
          (b n : ZMod (p ^ n)) := by
      have hto' :
          (∑ i ∈ Finset.range n, (d i : ZMod (p ^ n)) *
              (p : ZMod (p ^ n)) ^ i) - (b n : ZMod (p ^ n)) = 0 := by
        simpa [Chapter08PadicPartialSum, map_sub, map_sum, map_mul, map_pow] using hto
      have htoeq :
          (∑ i ∈ Finset.range n, (d i : ZMod (p ^ n)) *
              (p : ZMod (p ^ n)) ^ i) = (b n : ZMod (p ^ n)) :=
        sub_eq_zero.mp hto'
      simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] using htoeq
    have hmod :
        (∑ i ∈ Finset.range n, d i * p ^ i) ≡ b n [MOD p ^ n] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).1 hmodZ
    rw [Nat.ModEq] at hmod
    rw [Nat.mod_eq_of_lt (hsum_lt d hd.1 n),
      Nat.mod_eq_of_lt (by simpa [b] using PadicInt.appr_lt x n)] at hmod
    exact hmod
  refine ⟨a, ?_, ?_⟩
  · refine ⟨ha_lt, ?_⟩
    have hseq : Chapter08PadicPartialSum p a =
        (fun n => (b n : Chapter08PadicIntegers p)) := by
      funext n
      dsimp [Chapter08PadicPartialSum]
      norm_cast
      exact hsum n
    rw [hseq]
    exact hlim
  · intro d hd
    have hsumd := hfinite_eq d hd
    have hdigits : ∀ n : ℕ, d n = a n := by
      intro n
      have hdnext := hsumd (n + 1)
      have hdnow := hsumd n
      have hanext := hsum (n + 1)
      have hanow := hsum n
      rw [Finset.sum_range_succ] at hdnext hanext
      rw [hdnow] at hdnext
      rw [hanow] at hanext
      have hmul : d n * p ^ n = a n * p ^ n :=
        Nat.add_left_cancel (hdnext.trans hanext.symm)
      exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos hp) hmul
    funext n
    exact hdigits n

/-- The partial sum with all digits equal to p - 1. -/
def Chapter08PadicNegOnePartialSum (p n : ℕ) [Fact p.Prime] :
    Chapter08PadicIntegers p :=
  ∑ i ∈ Finset.range n,
    ((p - 1 : ℕ) : Chapter08PadicIntegers p) * (p : Chapter08PadicIntegers p) ^ i

/-! The displayed expansion -1 = (p-1) + (p-1)p + .... -/
theorem chapter08_padic_negative_one_partial_sum
    (p n : ℕ) [Fact p.Prime] :
    Chapter08PadicNegOnePartialSum p n =
      (p : Chapter08PadicIntegers p) ^ n - 1 := by
  classical
  have hp : 1 ≤ p := (Fact.out : Nat.Prime p).one_lt.le
  induction n with
  | zero => simp [Chapter08PadicNegOnePartialSum]
  | succ n ih =>
    have hstep : Chapter08PadicNegOnePartialSum p (n + 1) =
        Chapter08PadicNegOnePartialSum p n +
          ((p - 1 : ℕ) : Chapter08PadicIntegers p) *
            (p : Chapter08PadicIntegers p) ^ n := by
      simp [Chapter08PadicNegOnePartialSum, Finset.sum_range_succ]
    rw [hstep]
    rw [ih, pow_succ, Nat.cast_sub hp]
    ring

theorem chapter08_padic_negative_one_difference
    (p n : ℕ) [Fact p.Prime] :
    Chapter08PadicNegOnePartialSum p n - (-1) =
      (p : Chapter08PadicIntegers p) ^ n := by
  classical
  rw [chapter08_padic_negative_one_partial_sum]
  ring

theorem chapter08_padic_powers_tend_to_zero
    (p : ℕ) [Fact p.Prime] :
    Tendsto (fun n : ℕ => (p : Chapter08PadicIntegers p) ^ n) atTop (𝓝 0) := by
  classical
  apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
  rw [PadicInt.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt)

theorem chapter08_padic_negative_one_expansion
    (p : ℕ) [Fact p.Prime] :
    Tendsto (fun n => Chapter08PadicNegOnePartialSum p n) atTop (𝓝 (-1)) := by
  classical
  have h := chapter08_padic_powers_tend_to_zero p
  simpa [chapter08_padic_negative_one_partial_sum p] using
    (h.sub tendsto_const_nhds)

/-- A single digit carry moves a unit from the zeroth digit to a higher power of p. -/
theorem chapter08_padic_single_digit_carry
    (p : ℕ) [Fact p.Prime] :
    ((p - 1 : ℕ) : Chapter08PadicIntegers p) + 1 =
      (p : Chapter08PadicIntegers p) := by
  classical
  have hp : 1 ≤ p := (Fact.out : Nat.Prime p).one_lt.le
  rw [Nat.cast_sub hp]
  ring

theorem chapter08_higher_powers_are_smaller_p_adically
    (p n : ℕ) [Fact p.Prime] :
    ‖(p : Chapter08PadicIntegers p) ^ (n + 1)‖ <
      ‖(p : Chapter08PadicIntegers p) ^ n‖ := by
  classical
  rw [PadicInt.norm_p_pow, PadicInt.norm_p_pow]
  have hp : (1 : ℝ) < p := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  exact zpow_lt_zpow_right₀ hp (by omega)

/-- A Laurent expansion in Q_p starts at an arbitrary integral exponent. -/
def Chapter08PadicFieldPartialSum (p : ℕ) [Fact p.Prime]
    (N : ℤ) (a : ℕ → ℕ) (n : ℕ) : Chapter08PadicNumbers p :=
  ∑ i ∈ Finset.range n,
    (a i : Chapter08PadicNumbers p) *
      (p : Chapter08PadicNumbers p) ^ (N + (i : ℤ))

def Chapter08PadicLaurentExpansion (p : ℕ) [Fact p.Prime]
    (x : Chapter08PadicNumbers p) (N : ℤ) (a : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, a i < p) ∧
    Tendsto (Chapter08PadicFieldPartialSum p N a) atTop (𝓝 x)

/-- Every p-adic number admits a Laurent expansion with base-p digits. -/
theorem chapter08_every_padic_number_has_laurent_digit_expansion
    (p : ℕ) [Fact p.Prime] (x : Chapter08PadicNumbers p) :
    ∃ N : ℤ, ∃ a : ℕ → ℕ,
      Chapter08PadicLaurentExpansion p x N a := by
  classical
  by_cases hx : x = 0
  · refine ⟨0, fun _ => 0, ?_⟩
    constructor
    · intro i
      exact (Fact.out : Nat.Prime p).pos
    · have hzero : Chapter08PadicFieldPartialSum p 0 (fun _ => 0) =
          (fun _ => (0 : Chapter08PadicNumbers p)) := by
        funext n
        simp [Chapter08PadicFieldPartialSum]
      rw [hzero]
      simpa [hx] using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (0 : Chapter08PadicNumbers p)) atTop
            (𝓝 (0 : Chapter08PadicNumbers p)))
  · have hp0 : (p : Chapter08PadicNumbers p) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    have hval :
        (x * (p : Chapter08PadicNumbers p) ^ (-x.valuation)).valuation = 0 := by
      rw [Padic.valuation_mul hx (zpow_ne_zero _ hp0),
        Padic.valuation_zpow, Padic.valuation_p]
      ring
    have hy_norm :
        ‖x * (p : Chapter08PadicNumbers p) ^ (-x.valuation)‖ ≤ 1 := by
      apply (Padic.norm_le_one_iff_val_nonneg _).2
      rw [hval]
    let y : Chapter08PadicIntegers p :=
      ⟨x * (p : Chapter08PadicNumbers p) ^ (-x.valuation), hy_norm⟩
    obtain ⟨a, ha, _⟩ := chapter08_padic_digit_expansion_unique p y
    have hxy :
        (y : Chapter08PadicNumbers p) * (p : Chapter08PadicNumbers p) ^ x.valuation = x := by
      change (x * (p : Chapter08PadicNumbers p) ^ (-x.valuation)) *
          (p : Chapter08PadicNumbers p) ^ x.valuation = x
      rw [mul_assoc, ← zpow_add₀ hp0, neg_add_cancel, zpow_zero, mul_one]
    have hpartial (n : ℕ) :
        Chapter08PadicFieldPartialSum p x.valuation a n =
          algebraMap (Chapter08PadicIntegers p) (Chapter08PadicNumbers p)
              (Chapter08PadicPartialSum p a n) *
            (p : Chapter08PadicNumbers p) ^ x.valuation := by
      simp only [Chapter08PadicFieldPartialSum, Chapter08PadicPartialSum,
        map_sum, map_mul, map_pow, PadicInt.algebraMap_apply]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [zpow_add₀ hp0]
      simp only [PadicInt.coe_natCast]
      rw [zpow_natCast]
      ring
    have hcont : Continuous (fun z : Chapter08PadicIntegers p =>
        (z : Chapter08PadicNumbers p) *
          (p : Chapter08PadicNumbers p) ^ x.valuation) := by
      fun_prop
    have hlim := (hcont.tendsto y).comp ha.2
    rw [hxy] at hlim
    refine ⟨x.valuation, a, ?_⟩
    change (∀ i : ℕ, a i < p) ∧
      Tendsto (Chapter08PadicFieldPartialSum p x.valuation a) atTop (𝓝 x)
    refine ⟨ha.1, ?_⟩
    have hseq :
        Chapter08PadicFieldPartialSum p x.valuation a =
          (fun n => algebraMap (Chapter08PadicIntegers p) (Chapter08PadicNumbers p)
              (Chapter08PadicPartialSum p a n) *
            (p : Chapter08PadicNumbers p) ^ x.valuation) := by
      funext n
      exact hpartial n
    rw [hseq]
    exact hlim

/-- The first exponent with a nonzero digit, or top for the zero series. -/
def Chapter08FirstNonzeroExponent (N : ℤ) (a : ℕ → ℕ) : WithTop ℤ := by
  classical
  exact if h : ∃ i : ℕ, a i ≠ 0 then
    (N + (Nat.find h : ℤ) : WithTop ℤ)
  else ⊤

private theorem chapter08_padic_leading_term_valuation
    (p : ℕ) [Fact p.Prime] (x : Chapter08PadicNumbers p)
    (N : ℤ) (a : ℕ → ℕ)
    (ha : Chapter08PadicLaurentExpansion p x N a)
    (hnonzero : ∃ i : ℕ, a i ≠ 0) :
    Padic.addValuation
        ((a (Nat.find hnonzero) : Chapter08PadicNumbers p) *
          (p : Chapter08PadicNumbers p) ^ (N + (Nat.find hnonzero : ℤ))) =
      Chapter08FirstNonzeroExponent N a := by
  classical
  let j := Nat.find hnonzero
  have hj : a j ≠ 0 := Nat.find_spec hnonzero
  have hjp : a j < p := ha.1 j
  have hpndvd : ¬p ∣ a j := Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hj) hjp
  have hval : Padic.valuation (a j : Chapter08PadicNumbers p) = 0 := by
    rw [Padic.valuation_natCast, padicValNat.eq_zero_of_not_dvd hpndvd]
    simp
  have hterm :
      (a j : Chapter08PadicNumbers p) *
          (p : Chapter08PadicNumbers p) ^ (N + (j : ℤ)) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast hj)
      (zpow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero))
  rw [Padic.addValuation.apply hterm,
    Padic.valuation_mul (by exact_mod_cast hj)
      (zpow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)),
    hval, Padic.valuation_zpow, Padic.valuation_p, zero_add,
    Chapter08FirstNonzeroExponent]
  simp [j, hnonzero]

theorem chapter08_padic_valuation_is_first_nonzero_digit
    (p : ℕ) [Fact p.Prime] (x : Chapter08PadicNumbers p)
    (N : ℤ) (a : ℕ → ℕ)
    (ha : Chapter08PadicLaurentExpansion p x N a)
    (hnonzero : ∃ i : ℕ, a i ≠ 0) :
    Padic.addValuation x = Chapter08FirstNonzeroExponent N a := by
  classical
  let j := Nat.find hnonzero
  have hj : a j ≠ 0 := Nat.find_spec hnonzero
  have hzero_before : ∀ i : ℕ, i < j → a i = 0 := by
    intro i hi
    by_contra hne
    exact (Nat.find_min hnonzero hi) hne
  let term : ℕ → Chapter08PadicNumbers p := fun i =>
    (a i : Chapter08PadicNumbers p) *
      (p : Chapter08PadicNumbers p) ^ (N + (i : ℤ))
  let lead := term j
  have hlead_ne : lead ≠ 0 := by
    dsimp [lead, term]
    exact mul_ne_zero (by exact_mod_cast hj)
      (zpow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero))
  have hcop : p.Coprime (a j) := by
    apply (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr
    exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hj) (ha.1 j)
  have hcoef_lead : ‖(a j : Chapter08PadicNumbers p)‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff).2 hcop
  have hlead_norm : ‖lead‖ =
      ‖(p : Chapter08PadicNumbers p) ^ (N + (j : ℤ))‖ := by
    dsimp [lead, term]
    rw [norm_mul, hcoef_lead, one_mul]
  let bound : ℝ := ‖(p : Chapter08PadicNumbers p) ^ (N + (j : ℤ) + 1)‖
  have hterm : ∀ r : ℕ, ‖term (j + 1 + r)‖ ≤ bound := by
    intro r
    have hcoef : ‖(a (j + 1 + r) : Chapter08PadicNumbers p)‖ ≤ 1 := by
      simpa using (Padic.norm_int_le_one (p := p) (a (j + 1 + r) : ℤ))
    have hexp : -(N + ((j + 1 + r : ℕ) : ℤ)) ≤ -(N + (j : ℤ) + 1) := by
      push_cast
      omega
    have hpow :
        ‖(p : Chapter08PadicNumbers p) ^ (N + ((j + 1 + r : ℕ) : ℤ))‖ ≤
          bound := by
      dsimp [bound]
      rw [Padic.norm_p_zpow, Padic.norm_p_zpow]
      apply zpow_le_zpow_right₀
        (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt.le)
      exact hexp
    calc
      ‖term (j + 1 + r)‖ =
          ‖(a (j + 1 + r) : Chapter08PadicNumbers p)‖ *
            ‖(p : Chapter08PadicNumbers p) ^
              (N + ((j + 1 + r : ℕ) : ℤ))‖ := by
        simp [term, norm_mul]
      _ ≤ 1 * ‖(p : Chapter08PadicNumbers p) ^
            (N + ((j + 1 + r : ℕ) : ℤ))‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      _ = ‖(p : Chapter08PadicNumbers p) ^
            (N + ((j + 1 + r : ℕ) : ℤ))‖ := by simp
      _ ≤ bound := hpow
  have hsum_bound : ∀ r : ℕ,
      ‖∑ i ∈ Finset.range r, term (j + 1 + i)‖ ≤ bound := by
    intro r
    induction r with
    | zero =>
        simpa [bound] using
          (norm_nonneg ((p : Chapter08PadicNumbers p) ^ (N + (j : ℤ) + 1)))
    | succ r ihr =>
        rw [Finset.sum_range_succ]
        exact (Padic.nonarchimedean _ _).trans (max_le ihr (hterm r))
  have hbefore : ∑ i ∈ Finset.range j, term i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [term, hzero_before i (Finset.mem_range.mp hi)]
  have hfirst : ∑ i ∈ Finset.range (j + 1), term i = lead := by
    rw [Finset.sum_range_succ, hbefore]
    simp [lead]
  have hbound_lt : bound < ‖lead‖ := by
    rw [hlead_norm]
    dsimp [bound]
    rw [Padic.norm_p_zpow, Padic.norm_p_zpow]
    apply zpow_lt_zpow_right₀ (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt)
    omega
  have hpartial_bound {m : ℕ} (hm : j + 1 ≤ m) :
      ‖Chapter08PadicFieldPartialSum p N a m - lead‖ ≤ bound := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
    calc
      ‖Chapter08PadicFieldPartialSum p N a ((j + 1) + r) - lead‖ =
          ‖∑ i ∈ Finset.range r, term (j + 1 + i)‖ := by
        dsimp [Chapter08PadicFieldPartialSum]
        rw [Finset.sum_range_add, hfirst]
        congr 1
        ring
      _ ≤ bound := hsum_bound r
  have hlead_pos : 0 < ‖lead‖ := norm_pos_iff.mpr hlead_ne
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.1 ha.2) ‖lead‖ hlead_pos
  let m := max M (j + 1)
  have hmM : M ≤ m := le_max_left _ _
  have hmj : j + 1 ≤ m := le_max_right _ _
  have hnear : ‖x - Chapter08PadicFieldPartialSum p N a m‖ < ‖lead‖ := by
    simpa [dist_eq_norm, norm_sub_rev] using hM m hmM
  have htail : ‖Chapter08PadicFieldPartialSum p N a m - lead‖ < ‖lead‖ :=
    (hpartial_bound hmj).trans_lt hbound_lt
  have hxl : ‖x - lead‖ < ‖lead‖ := by
    calc
      ‖x - lead‖ =
          ‖(x - Chapter08PadicFieldPartialSum p N a m) +
            (Chapter08PadicFieldPartialSum p N a m - lead)‖ := by
        congr 1
        ring
      _ ≤ max ‖x - Chapter08PadicFieldPartialSum p N a m‖
          ‖Chapter08PadicFieldPartialSum p N a m - lead‖ :=
        Padic.nonarchimedean _ _
      _ < ‖lead‖ := max_lt hnear htail
  have hnorm : ‖x‖ = ‖lead‖ := Padic.norm_eq_of_norm_sub_lt_right hxl
  have hxne : x ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at hnorm
    exact (ne_of_gt hlead_pos) hnorm.symm
  have hpoweq : (p : ℝ) ^ (-x.valuation) =
      (p : ℝ) ^ (-lead.valuation) := by
    simpa [Padic.norm_eq_zpow_neg_valuation hxne,
      Padic.norm_eq_zpow_neg_valuation hlead_ne] using hnorm
  have hval : x.valuation = lead.valuation := by
    have hneg :=
      (zpow_right_strictMono₀
        (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt)).injective hpoweq
    exact neg_injective hneg
  calc
    Padic.addValuation x = (x.valuation : WithTop ℤ) :=
      Padic.addValuation.apply hxne
    _ = (lead.valuation : WithTop ℤ) := by rw [hval]
    _ = Padic.addValuation lead := (Padic.addValuation.apply hlead_ne).symm
    _ = Chapter08FirstNonzeroExponent N a := by
      simpa [lead, term, j] using
        (chapter08_padic_leading_term_valuation p x N a ha hnonzero)

theorem chapter08_rationals_are_dense_in_Qp
    (p : ℕ) [Fact p.Prime] :
    DenseRange (fun q : ℚ => (q : Chapter08PadicNumbers p)) := by
  exact Padic.denseRange_ratCast p

theorem chapter08_Qp_has_countable_dense_subfield
    (p : ℕ) [Fact p.Prime] :
    DenseRange (fun q : ℚ => (q : Chapter08PadicNumbers p)) ∧ Countable ℚ := by
  exact ⟨chapter08_rationals_are_dense_in_Qp p, inferInstance⟩

theorem chapter08_Zp_is_uncountable
    (p : ℕ) [Fact p.Prime] : ¬ Countable (Chapter08PadicIntegers p) := by
  classical
  let boolEquiv : Set ℕ ≃ (ℕ → Bool) :=
    { toFun := fun s n => if n ∈ s then true else false
      invFun := fun f => {n | f n = true}
      left_inv := by
        intro s
        ext n
        by_cases hn : n ∈ s <;> simp [hn]
      right_inv := by
        intro f
        funext n
        cases h : f n <;> simp [h] }
  have huncBool : Uncountable (ℕ → Bool) := by
    have hcard : Cardinal.aleph0 < Cardinal.mk (ℕ → Bool) := by
      rw [← Cardinal.mk_congr boolEquiv, Cardinal.mk_set_nat]
      exact Cardinal.aleph0_lt_continuum
    constructor
    intro hcount
    exact (not_lt_of_ge (Cardinal.mk_le_aleph0_iff.mpr hcount)) hcard
  have hperfect : Perfect (Set.univ : Set (Chapter08PadicIntegers p)) := by
    refine ⟨isClosed_univ, (preperfect_iff_nhds).2 ?_⟩
    intro z hz U hU
    rcases Metric.mem_nhds_iff.1 hU with ⟨ε, hε, hεU⟩
    obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt p hε
    let y := z + (p : Chapter08PadicIntegers p) ^ N
    refine ⟨y, ⟨hεU ?_, Set.mem_univ _⟩, ?_⟩
    · rw [Metric.mem_ball]
      simpa [y, dist_eq_norm, PadicInt.norm_p_pow, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc] using hN
    · intro hy
      have hpzero : (p : Chapter08PadicIntegers p) ^ N = 0 := by
        have hy' : z + (p : Chapter08PadicIntegers p) ^ N = z := by
          simpa [y] using hy
        exact add_left_cancel (a := z) (by simpa using hy')
      exact (pow_ne_zero N (by exact_mod_cast
        (Fact.out : Nat.Prime p).ne_zero)) hpzero
  letI : Uncountable (ℕ → Bool) := huncBool
  obtain ⟨f, hf_range, hf_cont, hf_inj⟩ :=
    Perfect.exists_nat_bool_injection hperfect ⟨0, Set.mem_univ 0⟩
  exact hf_inj.uncountable.not_countable

theorem chapter08_completion_adds_p_adic_elements
    (p : ℕ) [Fact p.Prime] :
    ¬ Function.Surjective (fun q : ℚ => (q : Chapter08PadicNumbers p)) := by
  classical
  have hZ : Uncountable (Chapter08PadicIntegers p) :=
    ⟨chapter08_Zp_is_uncountable p⟩
  letI : Uncountable (Chapter08PadicIntegers p) := hZ
  letI : Uncountable (Chapter08PadicNumbers p) :=
    (IsFractionRing.injective (Chapter08PadicIntegers p)
      (Chapter08PadicNumbers p)).uncountable
  exact not_surjective_countable_uncountable _

theorem chapter08_Zp_is_compact
    (p : ℕ) [Fact p.Prime] : CompactSpace (Chapter08PadicIntegers p) := by
  infer_instance

/-! ### 8.4 Formal power series -/

abbrev Chapter08FormalPowerSeries (k : Type*) [Semiring k] := PowerSeries k
abbrev Chapter08FormalLaurentSeries (k : Type*) [Field k] := LaurentSeries k

/-- The truncation inverse limit for the polynomial variable X. -/
abbrev Chapter08FormalPowerSeriesInverseLimit (k : Type*) [Field k] :=
  Chapter08CompatibleFamily (MvPolynomial PUnit.{1} k)
    (MvPolynomial.idealOfVars PUnit.{1} k)

theorem chapter08_power_series_inverse_limit
    (k : Type*) [Field k] :
    Nonempty (PowerSeries k ≃+* Chapter08FormalPowerSeriesInverseLimit k) := by
  classical
    obtain ⟨e, he⟩ :=
    chapter08_inverse_limit_ring_equiv
      (MvPolynomial.idealOfVars PUnit.{1} k)
  let c := MvPowerSeries.toAdicCompletionAlgEquiv PUnit.{1} k
  exact ⟨c.toRingEquiv.trans e⟩

/-- Constants give the canonical coefficient-field embedding into formal power series. -/
def Chapter08PowerSeriesConstants (k : Type*) [Semiring k] : k →+* PowerSeries k :=
  PowerSeries.C

theorem chapter08_power_series_constants_injective
    (k : Type*) [Field k] :
    Function.Injective (Chapter08PowerSeriesConstants k) := by
  exact PowerSeries.C_injective

theorem chapter08_power_series_is_fraction_field_of_power_series
    (k : Type*) [Field k] :
    IsFractionRing (PowerSeries k) (Chapter08FormalLaurentSeries k) := by
  infer_instance

theorem chapter08_formal_laurent_series_are_complete
    (k : Type*) [Field k] : CompleteSpace (Chapter08FormalLaurentSeries k) := by
  infer_instance

/-- Coefficientwise Cauchy data for a Laurent-series sequence. -/
def Chapter08LaurentCoefficientwiseCauchy
    {k : Type*} [Field k] (u : ℕ → Chapter08FormalLaurentSeries k) : Prop :=
  ∀ d : ℤ, ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
    (u m).coeff d = (u n).coeff d

/-- A common lower bound on the exponents occurring in a sequence of Laurent series. -/
def Chapter08CommonLaurentLowerBound
    {k : Type*} [Field k] (u : ℕ → Chapter08FormalLaurentSeries k) : Prop :=
  ∃ L : ℤ, ∀ n : ℕ, ∀ d : ℤ, d < L → (u n).coeff d = 0

-- The coefficientwise construction gives a common lower-bounded Laurent series limit. -/
theorem chapter08_laurent_series_cauchy_coefficient_construction
    (k : Type*) [Field k] (u : ℕ → Chapter08FormalLaurentSeries k)
    (hu : Chapter08LaurentCoefficientwiseCauchy u)
    (hL : Chapter08CommonLaurentLowerBound u)
    (hC : CauchySeq u) :
    ∃ x : Chapter08FormalLaurentSeries k,
      (∀ d : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (u n).coeff d = x.coeff d) ∧
        Tendsto u atTop (𝓝 x) := by
  classical
  let hℱ : Cauchy (atTop.map u) := hC
  let x : Chapter08FormalLaurentSeries k := LaurentSeries.Cauchy.limit hℱ
  refine ⟨x, ?_, ?_⟩
  · intro d
    have heq := LaurentSeries.Cauchy.coeff_eventually_equal hℱ (D := d + 1)
    have heq' : ∀ᶠ n in atTop, ∀ d', d' < d + 1 →
        x.coeff d' = (u n).coeff d' := by
      change u ⁻¹' {f : Chapter08FormalLaurentSeries k |
        ∀ d', d' < d + 1 → x.coeff d' = f.coeff d'} ∈ atTop
      exact heq
    rcases (eventually_atTop.1 heq') with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    exact (hN n hn d (by omega)).symm
  · intro U hU
    have h := LaurentSeries.Cauchy.eventually_mem_nhds hℱ hU
    change u ⁻¹' U ∈ atTop
    exact h

/-! The filtration analogy Z_p ↔ k[[t]], Q_p ↔ k((t)), p ↔ t. -/
theorem chapter08_padic_formal_series_filtration_analogy
    (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] :
    IsDiscreteValuationRing (Chapter08PadicIntegers p) ∧
      IsDiscreteValuationRing (PowerSeries k) ∧
      CompleteSpace (Chapter08PadicIntegers p) ∧
      CompleteSpace (Chapter08FormalLaurentSeries k) := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

theorem chapter08_formal_power_series_residue_field_is_constants
    (k : Type*) [Field k] :
    Nonempty (IsLocalRing.ResidueField (PowerSeries k) ≃+* k) := by
  exact ⟨PowerSeries.residueFieldOfPowerSeries⟩

theorem chapter08_power_series_preserves_characteristic
    (k : Type*) [Field k] (q : ℕ) [CharP k q] : CharP (PowerSeries k) q := by
  exact charP_of_injective_ringHom PowerSeries.C_injective q

theorem chapter08_padic_numbers_have_characteristic_zero
    (p : ℕ) [Fact p.Prime] : CharZero (Chapter08PadicNumbers p) := by
  infer_instance

theorem chapter08_no_Fp_embedding_in_characteristic_zero
    {A : Type*} [Ring A] [CharZero A] (p : ℕ) [Fact p.Prime] :
    ¬ ∃ f : ZMod p →+* A, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hp : (p : A) = 0 := by
    calc
      (p : A) = f (p : ZMod p) := by rw [map_natCast]
      _ = f 0 := by rw [ZMod.natCast_self]
      _ = 0 := map_zero f
  exact (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero) hp

/-! ### 8.5 Units and principal units -/

/-- The subgroup 1 + I ^ n inside the unit group. -/
def Chapter08UnitLayer
    (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ) : Subgroup Aˣ where
  carrier := {u | ((u : Aˣ) : A) - 1 ∈ I ^ n}
  one_mem' := by
    simp
  mul_mem' := by
    intro u v hu hv
    change ((u : A) * (v : A) - 1) ∈ I ^ n
    rw [show (u : A) * (v : A) - 1 =
        (u : A) * ((v : A) - 1) + ((u : A) - 1) by ring]
    exact (I ^ n).add_mem ((I ^ n).mul_mem_left _ hv) hu
  inv_mem' := by
    intro u hu
    change ((↑(u⁻¹) : A) - 1) ∈ I ^ n
    have hwu : (↑(u⁻¹) : A) * (u : A) = 1 := by simp
    have hEq : (↑(u⁻¹) : A) - 1 =
        -(↑(u⁻¹) : A) * ((u : A) - 1) := by
      calc
        (↑(u⁻¹) : A) - 1 = (↑(u⁻¹) : A) - (↑(u⁻¹) : A) * (u : A) := by rw [hwu]
        _ = -(↑(u⁻¹) : A) * ((u : A) - 1) := by ring
    rw [hEq]
    simpa [neg_mul] using
      (I ^ n).neg_mem ((I ^ n).mul_mem_left (↑(u⁻¹) : A) hu)

/-- The first principal-unit group in a local ring. -/
abbrev Chapter08PrincipalUnitGroup
    (A : Type*) [CommRing A] [IsLocalRing A] : Subgroup Aˣ :=
  Chapter08UnitLayer A (IsLocalRing.maximalIdeal A) 1

/-- Reduction of units to units in the residue field. -/
def Chapter08UnitReduction
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Aˣ →* (IsLocalRing.ResidueField A)ˣ :=
  Units.map (IsLocalRing.residue A).toMonoidHom

theorem chapter08_unit_reduction_kernel
    (A : Type*) [CommRing A] [IsLocalRing A] :
    (Chapter08UnitReduction A).ker = Chapter08PrincipalUnitGroup A := by
  classical
  ext u
  constructor
  · intro hu
    change Chapter08UnitReduction A u = 1 at hu
    have hval : IsLocalRing.residue A (u : A) = 1 := by
      have h := congrArg Units.val hu
      simpa [Chapter08UnitReduction] using h
    change ((u : Aˣ) : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ 1
    rw [pow_one]
    rw [← IsLocalRing.residue_eq_zero_iff]
    simpa [map_sub] using (sub_eq_zero.mpr hval)
  · intro hu
    change ((u : Aˣ) : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ 1 at hu
    rw [pow_one] at hu
    have hzero : IsLocalRing.residue A (u : A) - 1 = 0 :=
      (show IsLocalRing.residue A ((u : Aˣ) : A) - 1 = 0 from by
        have hz : IsLocalRing.residue A (((u : Aˣ) : A) - 1) = 0 := by
          exact (IsLocalRing.residue_eq_zero_iff _).2 hu
        simpa [map_sub] using hz)
    have hval : IsLocalRing.residue A (u : A) = 1 := sub_eq_zero.mp hzero
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    change IsLocalRing.residue A (u : A) = 1
    exact hval

-- Reduction gives A^× / U^1 ≅ k^×. -/
theorem chapter08_units_mod_principal_units
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Nonempty ((Aˣ ⧸ Chapter08PrincipalUnitGroup A) ≃*
      (IsLocalRing.ResidueField A)ˣ) := by
  classical
  have hsurj : Function.Surjective (Chapter08UnitReduction A) := by
    exact IsLocalRing.surjective_units_map_of_local_ringHom
      (IsLocalRing.residue A) IsLocalRing.residue_surjective
      (inferInstanceAs (IsLocalHom (IsLocalRing.residue A)))
  exact ⟨QuotientGroup.liftEquiv (Chapter08PrincipalUnitGroup A) hsurj
    (chapter08_unit_reduction_kernel A).symm⟩

/-- The additive residue-field layer represented inside the quotient modulo I^(n+1). -/
def Chapter08IdealLayer
    (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ) :
    AddSubgroup (A ⧸ I ^ (n + 1)) :=
  ((I ^ n).map (Ideal.Quotient.mk (I ^ (n + 1)))).toAddSubgroup

/-- The (n+1)-st unit layer viewed as a subgroup of the n-th layer. -/
def Chapter08UnitLayerIn
    (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ) :
    Subgroup (Chapter08UnitLayer A I n) :=
  (Chapter08UnitLayer A I (n + 1)).comap
    (Chapter08UnitLayer A I n).subtype

/-- The map 1+x ↦ x into the additive layer. -/
def Chapter08UnitLayerToIdealLayer
    (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ)
    (u : Chapter08UnitLayer A I n) : Chapter08IdealLayer A I n := by
  refine ⟨Ideal.Quotient.mk (I ^ (n + 1)) (((u : Aˣ) : A) - 1), ?_⟩
  classical
  change Ideal.Quotient.mk (I ^ (n + 1)) (((u : Aˣ) : A) - 1) ∈
    (I ^ n).map (Ideal.Quotient.mk (I ^ (n + 1)))
  exact Ideal.mem_map_of_mem (Ideal.Quotient.mk (I ^ (n + 1))) u.2

/-! Each multiplicative layer is one copy of the additive residue-field layer. -/
private theorem chapter08_principal_unit_layer_equiv_with_formula
    (A : Type*) [CommRing A] [IsLocalRing A] (I : Ideal A)
    (hI : I = IsLocalRing.maximalIdeal A) (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : Additive
          (Chapter08UnitLayer A I n ⧸ Chapter08UnitLayerIn A I n) ≃+
        Chapter08IdealLayer A I n,
      ∀ u : Chapter08UnitLayer A I n,
        e (QuotientGroup.mk' (Chapter08UnitLayerIn A I n) u) =
          Chapter08UnitLayerToIdealLayer A I n u := by
  classical
  let φ : Additive (Chapter08UnitLayer A I n) →+
      Chapter08IdealLayer A I n :=
    { toFun := fun u =>
        Chapter08UnitLayerToIdealLayer A I n (Additive.toMul u)
      map_zero' := by
        apply Subtype.ext
        change Ideal.Quotient.mk (I ^ (n + 1)) (1 - 1) = 0
        simp
      map_add' := by
        intro u v
        apply Subtype.ext
        change
          Ideal.Quotient.mk (I ^ (n + 1))
              ((((Additive.toMul u : Chapter08UnitLayer A I n) : Aˣ) : A) *
                (((Additive.toMul v : Chapter08UnitLayer A I n) : Aˣ) : A) - 1) =
            Ideal.Quotient.mk (I ^ (n + 1))
                ((((Additive.toMul u : Chapter08UnitLayer A I n) : Aˣ) : A) - 1) +
              Ideal.Quotient.mk (I ^ (n + 1))
                ((((Additive.toMul v : Chapter08UnitLayer A I n) : Aˣ) : A) - 1)
        rw [← map_add]
        apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
        have hpow : I ^ n * I ^ n ≤ I ^ (n + 1) := by
          calc
            I ^ n * I ^ n = I ^ (n + n) :=
              (Ideal.IsTwoSided.pow_add (I := I) n n).symm
            _ ≤ I ^ (n + 1) := Ideal.pow_le_pow_right (by omega)
        have hprod :
            ((((Additive.toMul u : Chapter08UnitLayer A I n) : Aˣ) : A) - 1) *
                ((((Additive.toMul v : Chapter08UnitLayer A I n) : Aˣ) : A) - 1) ∈
              I ^ (n + 1) :=
          hpow (Ideal.mul_mem_mul (Additive.toMul u).property
            (Additive.toMul v).property)
        convert hprod using 1 <;> ring }
  let ψ : Chapter08UnitLayer A I n →* Multiplicative (Chapter08IdealLayer A I n) :=
    AddMonoidHom.toMultiplicativeRight φ
  have hker : ψ.ker = Chapter08UnitLayerIn A I n := by
    ext u
    constructor
    · intro hu
      change φ (Additive.ofMul u) = 0 at hu
      have hq :
          Ideal.Quotient.mk (I ^ (n + 1)) (((u : Aˣ) : A) - 1) = 0 := by
        have h := congrArg Subtype.val hu
        simpa [φ, Chapter08UnitLayerToIdealLayer] using h
      change ((u : Aˣ) : A) - 1 ∈ I ^ (n + 1)
      exact Ideal.Quotient.eq_zero_iff_mem.mp hq
    · intro hu
      change ((u : Aˣ) : A) - 1 ∈ I ^ (n + 1) at hu
      apply MonoidHom.mem_ker.mpr
      change φ (Additive.ofMul u) = 0
      apply Subtype.ext
      change Ideal.Quotient.mk (I ^ (n + 1)) (((u : Aˣ) : A) - 1) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hu
  have hsurj : Function.Surjective ψ := by
    intro z
    let q : Chapter08IdealLayer A I n := Multiplicative.toAdd z
    obtain ⟨r, hr, hqr⟩ :=
      (Ideal.mem_map_iff_of_surjective
        (Ideal.Quotient.mk (I ^ (n + 1))) Ideal.Quotient.mk_surjective).1 q.2
    have hrI : r ∈ I := by
      have hp : I ^ n ≤ I := by
        simpa [pow_one] using (Ideal.pow_le_pow_right (I := I) hn)
      exact hp hr
    have hrmax : r ∈ IsLocalRing.maximalIdeal A := by
      rw [← hI]
      exact hrI
    have hnegmax : -r ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.maximalIdeal A).neg_mem hrmax
    have hneg : -r ∈ nonunits A :=
      (IsLocalRing.mem_maximalIdeal (-r)).1 hnegmax
    have hu : IsUnit (1 + r) := by
      have h := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-r) hneg
      convert h using 1 <;> ring
    let w : Aˣ := hu.unit
    have hw : (w : A) - 1 = r := by
      dsimp [w]
      ring
    have hwmem : (w : A) - 1 ∈ I ^ n := by
      rw [hw]
      exact hr
    let u : Chapter08UnitLayer A I n := ⟨w, hwmem⟩
    have hφq : φ (Additive.ofMul u) = q := by
      apply Subtype.ext
      change Ideal.Quotient.mk (I ^ (n + 1)) (((u : Aˣ) : A) - 1) = q.1
      have huw : ((u : Aˣ) : A) - 1 = r := by
        simpa [u] using hw
      rw [huw, hqr]
    refine ⟨u, ?_⟩
    change φ (Additive.ofMul u) = q
    exact hφq
  let eMul := QuotientGroup.liftEquiv (Chapter08UnitLayerIn A I n)
    hsurj hker.symm
  let e : Additive
        (Chapter08UnitLayer A I n ⧸ Chapter08UnitLayerIn A I n) ≃+
      Chapter08IdealLayer A I n := MulEquiv.toAdditiveLeft eMul
  refine ⟨e, ?_⟩
  intro u
  change Multiplicative.toAdd
      (eMul (QuotientGroup.mk' (Chapter08UnitLayerIn A I n) u)) =
    φ (Additive.ofMul u)
  simp [eMul, ψ, φ]

theorem chapter08_principal_unit_layer_quotient
    (A : Type*) [CommRing A] [IsLocalRing A] (I : Ideal A)
    (hI : I = IsLocalRing.maximalIdeal A) (n : ℕ) (hn : 1 ≤ n) :
    Nonempty
      (Additive
      (Chapter08UnitLayer A I n ⧸ Chapter08UnitLayerIn A I n) ≃+
        Chapter08IdealLayer A I n) := by
  classical
  obtain ⟨e, he⟩ :=
    chapter08_principal_unit_layer_equiv_with_formula A I hI n hn
  exact ⟨e⟩

theorem chapter08_principal_unit_layer_formula
    (A : Type*) [CommRing A] [IsLocalRing A] (I : Ideal A)
    (hI : I = IsLocalRing.maximalIdeal A) (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : Additive
          (Chapter08UnitLayer A I n ⧸ Chapter08UnitLayerIn A I n) ≃+
        Chapter08IdealLayer A I n,
      ∀ u : Chapter08UnitLayer A I n,
        e (QuotientGroup.mk' (Chapter08UnitLayerIn A I n) u) =
          Chapter08UnitLayerToIdealLayer A I n u := by
  classical
  exact chapter08_principal_unit_layer_equiv_with_formula A I hI n hn

/-- Partial products of principal units in the adic completion. -/
def Chapter08PrincipalUnitPartialProduct
    {A : Type*} [CommRing A] (I : Ideal A) (a : ℕ → A) (m : ℕ) :
    AdicCompletion I A :=
  ∏ i ∈ Finset.range m, (1 + algebraMap A (AdicCompletion I A) (a i))

def Chapter08PrincipalUnitProductConverges
    {A : Type*} [CommRing A] (I : Ideal A) (a : ℕ → A)
    (x : AdicCompletion I A) : Prop :=
  Chapter08AdicConverges I (Chapter08PrincipalUnitPartialProduct I a) x

-- Infinite products of principal units converge when a_n tends to zero adically. -/
theorem chapter08_infinite_principal_unit_product_converges
    {A : Type*} [CommRing A] [IsLocalRing A]
    (I : Ideal A) (a : ℕ → A)
    (hI : I = IsLocalRing.maximalIdeal A)
    (ha : ∀ n : ℕ, a n ∈ I)
    (htends : Chapter08AdicTendsToZero I a) :
    ∃ x : AdicCompletion I A, Chapter08PrincipalUnitProductConverges I a x := by
  classical
  choose b hb using htends
  let N : ℕ → ℕ := fun n =>
    Nat.rec (b 0) (fun k q => max (q + 1) (max (b (k + 1)) q)) n
  have hN_succ (n : ℕ) :
      N (n + 1) = max (N n + 1) (max (b (n + 1)) (N n)) := by
    rfl
  have hNb : ∀ n : ℕ, b n ≤ N n := by
    intro n
    induction n with
    | zero => simp [N]
    | succ n ih =>
        rw [hN_succ]
        exact (le_max_left _ _).trans (le_max_right _ _)
  have hNinc : ∀ n : ℕ, N n < N (n + 1) := by
    intro n
    rw [hN_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  let P : ℕ → A := fun m =>
    ∏ i ∈ Finset.range m, (1 + a i)
  have hPdiff : ∀ (n l m : ℕ), N n ≤ l → l ≤ m →
      P m - P l ∈ I ^ n := by
    intro n l m hNl hlm
    induction m, hlm using Nat.le_induction with
    | base => simp
    | succ m hlm ih =>
        have ham : a m ∈ I ^ n := hb n m
          ((hNb n).trans (hNl.trans hlm))
        have hident : P (m + 1) - P l =
            (P m - P l) * (1 + a m) + P l * a m := by
          rw [show P (m + 1) = P m * (1 + a m) by
            simp [P, Finset.prod_range_succ]]
          ring
        rw [hident]
        exact (I ^ n).add_mem ((I ^ n).mul_mem_right _ ih)
          ((I ^ n).mul_mem_left _ ham)
  let s : ℕ → A := fun n => P (N n)
  have hs : ∀ n : ℕ,
      s n ≡ s (n + 1) [SMOD (I ^ n • (⊤ : Submodule A A))] := by
    intro n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have h := hPdiff n (N n) (N (n + 1)) (le_rfl) (hNinc n).le
    simpa [s, sub_eq_add_neg] using (I ^ n).neg_mem h
  let c : AdicCompletion.AdicCauchySequence I A :=
    AdicCompletion.AdicCauchySequence.mk I A s hs
  let x : AdicCompletion I A := AdicCompletion.mk I A c
  refine ⟨x, ?_⟩
  intro n
  refine ⟨N n, fun m hm => ?_⟩
  have hquot : Ideal.Quotient.mk (I ^ n) (P m) =
      Ideal.Quotient.mk (I ^ n) (P (N n)) :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
      (hPdiff n (N n) m (le_rfl) hm)
  calc
    AdicCompletion.evalₐ I n
        (Chapter08PrincipalUnitPartialProduct I a m) =
        Ideal.Quotient.mk (I ^ n) (P m) := by
          simp [Chapter08PrincipalUnitPartialProduct, P]
    _ = Ideal.Quotient.mk (I ^ n) (P (N n)) := hquot
    _ = AdicCompletion.evalₐ I n x := by
      simp [x, c, s]

/-- Separating the valuation leaves a unit times a power of a uniformizer. -/
theorem chapter08_dvr_unit_power_separation
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (hπ : Irreducible π) {x : A} (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ u : Aˣ, x = (u : A) * π ^ n := by
  classical
  exact IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ

/-! ### 8.6 Complete does not mean algebraically closed -/

/-- An approximate root modulo I ^ n. -/
def Chapter08ApproximateRoot
    {A : Type*} [CommRing A] (I : Ideal A) (f : A[X]) (a : A) (n : ℕ) : Prop :=
  f.eval a ∈ I ^ n

/-- A unit whose residue is not a square. -/
def Chapter08NonsquareResidueUnit
    (A : Type*) [CommRing A] [IsLocalRing A] (u : A) : Prop :=
  IsUnit u ∧
    ¬ ∃ y : IsLocalRing.ResidueField A,
      y ^ 2 = IsLocalRing.residue A u

/-- A nonsquare residue unit cannot be a square in the local ring. -/
theorem chapter08_nonsquare_residue_unit_not_square
    (A : Type*) [CommRing A] [IsLocalRing A] (u : A)
    (hu : IsUnit u)
    (hns : ¬ ∃ y : IsLocalRing.ResidueField A,
      y ^ 2 = IsLocalRing.residue A u) :
    ¬ ∃ x : A, x ^ 2 = u := by
  classical
  rintro ⟨x, hx⟩
  apply hns
  refine ⟨IsLocalRing.residue A x, ?_⟩
  calc
    IsLocalRing.residue A x ^ 2 = IsLocalRing.residue A (x ^ 2) :=
      (map_pow (IsLocalRing.residue A) x 2).symm
    _ = IsLocalRing.residue A u := by rw [hx]

-- The quadratic X^2-u is an explicit algebraic obstruction. -/
theorem chapter08_quadratic_without_root_from_nonsquare_residue
    (A : Type*) [CommRing A] [IsLocalRing A] (u : A)
    (hu : IsUnit u)
    (hns : ¬ ∃ y : IsLocalRing.ResidueField A,
      y ^ 2 = IsLocalRing.residue A u) :
    ¬ ∃ x : A, (Polynomial.X ^ 2 - Polynomial.C u).eval x = 0 := by
  classical
  rintro ⟨x, hx⟩
  apply chapter08_nonsquare_residue_unit_not_square A u hu hns
  refine ⟨x, ?_⟩
  exact sub_eq_zero.mp (by
    simpa [Polynomial.eval_sub, Polynomial.eval_pow] using hx)

theorem chapter08_complete_padic_field_not_algebraically_closed
    (p : ℕ) [Fact p.Prime] :
      CompleteSpace (Chapter08PadicNumbers p) ∧
      ¬ IsAlgClosed (Chapter08PadicNumbers p) := by
  classical
  refine ⟨inferInstance, ?_⟩
  intro hclosed
  letI : IsAlgClosed (Chapter08PadicNumbers p) := hclosed
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C (p : Chapter08PadicNumbers p)).degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C (by decide)]
    norm_num
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ 2 - Polynomial.C (p : Chapter08PadicNumbers p)) hdeg
  have hz' : z ^ 2 = (p : Chapter08PadicNumbers p) := by
    exact sub_eq_zero.mp (by
      simpa [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow] using hz)
  have hv := congrArg Padic.valuation hz'
  rw [Padic.valuation_pow, Padic.valuation_p] at hv
  omega

/-! Simple roots do lift: this is the Henselian principle deferred to the next chapter. -/
theorem chapter08_simple_root_lifts_in_complete_local_ring
    (A : Type*) [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    ∀ f : A[X], f.Monic →
      ∀ a₀ : IsLocalRing.ResidueField A,
        aeval a₀ f = 0 →
        aeval a₀ f.derivative ≠ 0 →
        ∃ a : A, f.IsRoot a ∧ IsLocalRing.residue A a = a₀ := by
  classical
  letI : HenselianLocalRing A := {
    toIsLocalRing := inferInstance
    is_henselian := by
      intro g hg b hb hunit
      obtain ⟨c, hc, hcmem⟩ :=
        (inferInstance : HenselianRing A (IsLocalRing.maximalIdeal A)).is_henselian
          g hg b hb (hunit.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))
      exact ⟨c, hc, hcmem⟩ }
  intro f hf a₀ hfa₀ hfderiv
  obtain ⟨a₀', ha₀'⟩ := IsLocalRing.residue_surjective a₀
  have hroot : f.eval a₀' ∈ IsLocalRing.maximalIdeal A := by
    apply (IsLocalRing.residue_eq_zero_iff (f.eval a₀')).1
    have hfa₀' : aeval (IsLocalRing.residue A a₀') f = 0 := by
      simpa [ha₀'] using hfa₀
    simpa [aeval_def, IsLocalRing.ResidueField.algebraMap_eq, eval₂_at_apply] using
      hfa₀'
  have hderiv : IsUnit (f.derivative.eval a₀') := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit (f.derivative.eval a₀')).1
    have hfderiv' : aeval (IsLocalRing.residue A a₀') f.derivative ≠ 0 := by
      simpa [ha₀'] using hfderiv
    simpa [aeval_def, IsLocalRing.ResidueField.algebraMap_eq, eval₂_at_apply] using
      hfderiv'
  obtain ⟨a, ha, hmem⟩ := HenselianLocalRing.is_henselian f hf a₀' hroot hderiv
  refine ⟨a, ha, ?_⟩
  rw [← sub_eq_zero]
  calc
    IsLocalRing.residue A a - a₀ =
        IsLocalRing.residue A a - IsLocalRing.residue A a₀' := by rw [ha₀']
    _ = IsLocalRing.residue A (a - a₀') := by rw [map_sub]
    _ = 0 := by
      exact (IsLocalRing.residue_eq_zero_iff (a - a₀')).2 hmem

theorem chapter08_complete_local_ring_is_henselian
    (A : Type*) [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    HenselianLocalRing A := by
  classical
  refine {
    toIsLocalRing := inferInstance
    is_henselian := ?_ }
  intro f hf a₀ h₁ h₂
  obtain ⟨a, ha, hmem⟩ :=
    (inferInstance : HenselianRing A (IsLocalRing.maximalIdeal A)).is_henselian
      f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))
  exact ⟨a, ha, hmem⟩

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter08
