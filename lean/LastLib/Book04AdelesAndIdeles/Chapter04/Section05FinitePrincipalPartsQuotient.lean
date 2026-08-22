import LastLib.Book04AdelesAndIdeles.Chapter04.Section01TheFiniteAdeleRing
import LastLib.Book04AdelesAndIdeles.Chapter04.Section03NeighborhoodsAsLocalSpecifications

namespace LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open Set Filter
open NumberField IsDedekindDomain
open LastLib.Book04AdelesAndIdeles.Chapter01
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ Valued
open scoped BigOperators Topology RestrictedProduct
open scoped WithZero

/-! ### 4.5 The finite principal-parts quotient -/

def chapter04RingOfIntegersEmbedding
    (K : Type*) [Field K] [NumberField K] :
    Chapter04RingOfIntegers K →+* K :=
  algebraMap (Chapter04RingOfIntegers K) K

abbrev Chapter04RingOfIntegersAddSubgroup
    (K : Type*) [Field K] [NumberField K] : AddSubgroup K :=
  (chapter04RingOfIntegersEmbedding K).range.toAddSubgroup

abbrev Chapter04GlobalPrincipalPartsQuotient
    (K : Type*) [Field K] [NumberField K] :=
  K ⧸ Chapter04RingOfIntegersAddSubgroup K

abbrev Chapter04FinitePrincipalPartsQuotient
    (K : Type*) [Field K] [NumberField K] :=
  Chapter04FiniteAdeleRing K ⧸ Chapter04FiniteIntegralAdeleAddSubgroup K

def chapter04FinitePrincipalPartsQuotientMap
    (K : Type*) [Field K] [NumberField K] :
    Chapter04FiniteAdeleRing K →+
      Chapter04FinitePrincipalPartsQuotient K :=
  QuotientAddGroup.mk' (Chapter04FiniteIntegralAdeleAddSubgroup K)

def chapter04GlobalToFiniteAdeleAdditiveMap
    (K : Type*) [Field K] [NumberField K] :
    K →+ Chapter04FiniteAdeleRing K :=
  (IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 K) K).toAddMonoidHom

def chapter04PrincipalPartsMap
    (K : Type*) [Field K] [NumberField K] :
    Chapter04GlobalPrincipalPartsQuotient K →+
      Chapter04FinitePrincipalPartsQuotient K :=
  QuotientAddGroup.lift (Chapter04RingOfIntegersAddSubgroup K)
    ((chapter04FinitePrincipalPartsQuotientMap K).comp
      (chapter04GlobalToFiniteAdeleAdditiveMap K)) (by
        intro x hx
        rcases hx with ⟨a, rfl⟩
        change QuotientAddGroup.mk' (Chapter04FiniteIntegralAdeleAddSubgroup K)
          (chapter04GlobalToFiniteAdeleAdditiveMap K
            (algebraMap (𝓞 K) K a)) = 0
        change (↑(chapter04GlobalToFiniteAdeleAdditiveMap K
            (algebraMap (𝓞 K) K a)) : Chapter04FinitePrincipalPartsQuotient K) =
          ↑(0 : Chapter04FiniteAdeleRing K)
        rw [QuotientAddGroup.eq_iff_sub_mem]
        apply (chapter04_finiteIntegralAdele_mem_iff_all_coordinates_integral K _).2
        intro v
        simp only [sub_zero]
        change algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) ∈
          v.adicCompletionIntegers K
        rw [← IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K) a]
        exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers
          (R := 𝓞 K) (K := K) v a)

@[simp]
theorem chapter04PrincipalPartsMap_apply
    (K : Type*) [Field K] [NumberField K] (a : K) :
    chapter04PrincipalPartsMap K (QuotientAddGroup.mk' _ a) =
      chapter04FinitePrincipalPartsQuotientMap K
        (chapter04GlobalToFiniteAdeleAdditiveMap K a) := by
  rfl

theorem chapter04_principalParts_map_injective
    (K : Type*) [Field K] [NumberField K] :
    Function.Injective (chapter04PrincipalPartsMap K) := by
  intro x y h
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
    (Chapter04RingOfIntegersAddSubgroup K) x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective
    (Chapter04RingOfIntegersAddSubgroup K) y
  rw [chapter04PrincipalPartsMap_apply, chapter04PrincipalPartsMap_apply] at h
  have hzero :
      chapter04FinitePrincipalPartsQuotientMap K
          (chapter04GlobalToFiniteAdeleAdditiveMap K (a - b)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr h
  have hmem :
      chapter04GlobalToFiniteAdeleAdditiveMap K (a - b) ∈
        Chapter04FiniteIntegralAdeleAddSubgroup K := by
    change (↑(chapter04GlobalToFiniteAdeleAdditiveMap K (a - b)) :
      Chapter04FinitePrincipalPartsQuotient K) = ↑(0 : Chapter04FiniteAdeleRing K) at hzero
    simpa only [sub_zero] using (QuotientAddGroup.eq_iff_sub_mem).mp hzero
  have hlocal : ∀ v : Chapter04FinitePlace K,
      ((a - b : K) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    intro v
    exact (chapter04_finiteIntegralAdele_mem_iff_all_coordinates_integral K _).1 hmem v
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  change a - b ∈ (chapter04RingOfIntegersEmbedding K).range
  apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    (R := 𝓞 K) (K := K) (a - b)
  intro v
  rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v]
  exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
    (𝓞 K) K v).1 (hlocal v)

theorem chapter04_principalParts_map_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter04PrincipalPartsMap K) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective
    (Chapter04FiniteIntegralAdeleAddSubgroup K) y
  obtain ⟨a, ha⟩ :=
    LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_principal_parts_approximation K x
  refine ⟨QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K) a, ?_⟩
  rw [chapter04PrincipalPartsMap_apply]
  change (↑(chapter04GlobalToFiniteAdeleAdditiveMap K a) :
      Chapter04FinitePrincipalPartsQuotient K) =
    QuotientAddGroup.mk' (Chapter04FiniteIntegralAdeleAddSubgroup K) x
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  apply (chapter04_finiteIntegralAdele_mem_iff_all_coordinates_integral K _).2
  intro v
  change algebraMap K (v.adicCompletion K) a - x v ∈
    v.adicCompletionIntegers K
  have hneg := (v.adicCompletionIntegers K).neg_mem
    (x v - (a : v.adicCompletion K)) (ha v)
  have hcoe : (a : v.adicCompletion K) = algebraMap K (v.adicCompletion K) a := by
    simp [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  rw [hcoe] at hneg
  simpa [sub_eq_add_neg, add_comm] using hneg

noncomputable def chapter04PrincipalPartsEquiv
    (K : Type*) [Field K] [NumberField K] :
    Chapter04GlobalPrincipalPartsQuotient K ≃+
      Chapter04FinitePrincipalPartsQuotient K :=
  AddEquiv.ofBijective (chapter04PrincipalPartsMap K)
    ⟨chapter04_principalParts_map_injective K,
      chapter04_principalParts_map_surjective K⟩

noncomputable def chapter04_principalParts_quotient_is_an_abstract_additive_group_isomorphism
    (K : Type*) [Field K] [NumberField K] :
    Chapter04GlobalPrincipalPartsQuotient K ≃+
      Chapter04FinitePrincipalPartsQuotient K :=
  chapter04PrincipalPartsEquiv K

def chapter04GlobalPrincipalPartsQuotientIsTorsion
    (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ x : Chapter04GlobalPrincipalPartsQuotient K,
    ∃ n : ℕ, n ≠ 0 ∧ n • x = 0

theorem chapter04_global_principalParts_quotient_is_torsion
    (K : Type*) [Field K] [NumberField K] :
    chapter04GlobalPrincipalPartsQuotientIsTorsion K := by
  intro x
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
    (Chapter04RingOfIntegersAddSubgroup K) x
  obtain ⟨b, hb⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors (𝓞 K)) a
  rcases hb with ⟨d, hd⟩
  let I : Ideal (𝓞 K) := Ideal.span ({(b : 𝓞 K)} : Set (𝓞 K))
  have hI : I ≠ ⊥ := by
    intro h
    have hmem : (b : 𝓞 K) ∈ (⊥ : Ideal (𝓞 K)) := by
      rw [← h]
      exact Ideal.subset_span (by simp)
    simpa [mem_nonZeroDivisors_iff_ne_zero.mp b.property] using hmem
  let n : ℕ := Ideal.absNorm (Ideal.under ℤ I)
  have hn : n ≠ 0 := by
    have hdiv : n ∣ Ideal.absNorm I := by
      exact Int.absNorm_under_dvd_absNorm I
    have hnorm : Ideal.absNorm I ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr hI
    intro hn
    have hzero : (0 : ℕ) ∣ Ideal.absNorm I := by
      simpa [n, hn] using hdiv
    exact hnorm (by simpa using hzero)
  have hnmem : (n : 𝓞 K) ∈ I := by
    exact Int.absNorm_under_mem I
  change (n : 𝓞 K) ∈ Ideal.span ({(b : 𝓞 K)} : Set (𝓞 K)) at hnmem
  rcases Ideal.mem_span_singleton.mp hnmem with ⟨c, hc⟩
  refine ⟨n, hn, ?_⟩
  change QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K) (n • a) = 0
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  simp only [sub_zero]
  change n • a ∈ (chapter04RingOfIntegersEmbedding K).range
  rw [nsmul_eq_mul]
  refine ⟨c * d, ?_⟩
  change algebraMap (𝓞 K) K c * algebraMap (𝓞 K) K d = (n : K) * a
  have hcn : (n : K) = ((b : 𝓞 K) : K) * (c : K) := by
    simpa using congrArg (algebraMap (𝓞 K) K) hc
  rw [hd, hcn]
  simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm]

theorem chapter04_global_principalParts_quotient_is_not_additively_free
    (K : Type*) [Field K] [NumberField K] :
    ¬ IsAddTorsionFree (Chapter04GlobalPrincipalPartsQuotient K) := by
  have hH : Chapter04RingOfIntegersAddSubgroup K ≠ ⊤ := by
    intro h
    have hsurj : Function.Surjective (algebraMap (𝓞 K) K) := by
      intro x
      have hx : x ∈ Chapter04RingOfIntegersAddSubgroup K := by
        rw [h]
        trivial
      change x ∈ (chapter04RingOfIntegersEmbedding K).range at hx
      exact hx
    exact RingOfIntegers.not_isField K
      ((IsFractionRing.surjective_iff_isField (R := 𝓞 K) (K := K)).mp hsurj)
  have hnot : ¬ ∀ x : K, x ∈ Chapter04RingOfIntegersAddSubgroup K := by
    intro hall
    apply hH
    exact top_unique (fun x _ => hall x)
  obtain ⟨a, ha⟩ := not_forall.mp hnot
  have hmk : QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K) a ≠ 0 := by
    intro hzero
    have hmem : a - 0 ∈ Chapter04RingOfIntegersAddSubgroup K :=
      (QuotientAddGroup.eq_iff_sub_mem).mp hzero
    exact ha (by simpa using hmem)
  have hnontriv : Nontrivial (Chapter04GlobalPrincipalPartsQuotient K) :=
    ⟨⟨QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K) a, 0, hmk⟩⟩
  apply @not_isAddTorsionFree_of_isAddTorsion _ inferInstance hnontriv
  intro x
  obtain ⟨n, hn, hnx⟩ := chapter04_global_principalParts_quotient_is_torsion K x
  exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, Nat.pos_of_ne_zero hn, hnx⟩

theorem chapter04_finitePrincipalPartsQuotient_is_discrete
    (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (Chapter04FinitePrincipalPartsQuotient K) := by
  exact QuotientAddGroup.discreteTopology
    (chapter04_finiteIntegralAdele_is_compact_open K).2

abbrev chapter04PrincipalPartsTransportedDiscreteTopology
    (K : Type*) [Field K] [NumberField K] :
    TopologicalSpace (Chapter04GlobalPrincipalPartsQuotient K) :=
  TopologicalSpace.induced (chapter04PrincipalPartsEquiv K) ⊤

theorem chapter04_principalParts_transport_is_discrete
    (K : Type*) [Field K] [NumberField K] :
    @DiscreteTopology (Chapter04GlobalPrincipalPartsQuotient K)
      (chapter04PrincipalPartsTransportedDiscreteTopology K) := by
  sorry

abbrev chapter04GlobalDiagonalSubspaceTopology
    (K : Type*) [Field K] [NumberField K] : TopologicalSpace K :=
  TopologicalSpace.induced
    (IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 K) K)
    inferInstance

theorem chapter04_global_diagonal_is_dense
    (K : Type*) [Field K] [NumberField K] :
    DenseRange (IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 K) K) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro x
  rw [mem_closure_iff_nhds]
  intro U hU
  rcases chapter04_finiteAdele_has_local_specification_basis K x U hU with
    ⟨S, W, hSW, hxW, hsub⟩
  have hxW' := hxW
  rw [chapter04_mem_finiteBasicNeighborhood_iff] at hxW'
  let Sfin : Finset (Chapter04FinitePlace K) := hSW.1.toFinset
  have hSfin (v : Chapter04FinitePlace K) : v ∈ Sfin ↔ v ∈ S := by
    dsimp [Sfin]
    exact hSW.1.mem_toFinset
  have hWlocal : ∀ v : Chapter04FinitePlace K, v ∈ S →
      ∃ n : ℤ, ∀ z : Chapter04FiniteLocalField K v,
        chapter01LocallyClose v (x v) z n → z ∈ W v := by
    intro v hv
    have hmem : W v ∈ 𝓝 (x v) := (hSW.2 v hv).mem_nhds (hxW'.1 v hv)
    rcases Valued.mem_nhds.mp hmem with ⟨γ, hγ⟩
    let γ' : ℤᵐ⁰ := MonoidWithZeroHom.ValueGroup₀.embedding γ.1
    refine ⟨-(WithZero.log γ' - 1), ?_⟩
    intro z hz
    apply hγ
    change Valued.v.restrict (z - x v) < γ.1
    rw [Valued.v.restrict_lt_iff_lt_embedding]
    have hz' : Valued.v (x v - z) ≤
        WithZero.exp (-(-(WithZero.log γ' - 1))) := by
      change Valued.v (x v - z) ≤ WithZero.exp (-(-(WithZero.log γ' - 1))) at hz
      exact hz
    rw [Valuation.map_sub_swap] at hz'
    have hγ'ne : γ' ≠ 0 := by
      exact MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
    change Valued.v (z - x v) < γ'
    rw [← WithZero.exp_log hγ'ne]
    apply lt_of_le_of_lt hz'
    rw [WithZero.exp_lt_exp]
    omega
  let m : ∀ v : Chapter04FinitePlace K, v ∈ Sfin → ℤ := fun v hv =>
    Classical.choose (hWlocal v ((hSfin v).1 hv))
  have hm (v : Chapter04FinitePlace K) (hv : v ∈ Sfin) :
      ∀ z : Chapter04FiniteLocalField K v,
        chapter01LocallyClose v (x v) z (m v hv) → z ∈ W v := by
    exact Classical.choose_spec (hWlocal v ((hSfin v).1 hv))
  obtain ⟨a, haS, haout⟩ :=
    LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_finite_approximation K Sfin
      (fun v _ => x v) m
  refine ⟨chapter04GlobalToFiniteAdeleAdditiveMap K a, ?_, ⟨a, rfl⟩⟩
  apply hsub
  rw [chapter04_mem_finiteBasicNeighborhood_iff]
  constructor
  · intro v hv
    have hvfin : v ∈ Sfin := (hSfin v).2 hv
    have hcoe : (chapter04GlobalToFiniteAdeleAdditiveMap K a) v =
        (a : v.adicCompletion K) := by
      exact IsDedekindDomain.FiniteAdeleRing.algebraMap_apply (𝓞 K) K a v
    rw [hcoe]
    exact hm v hvfin _ (by simpa using haS v hvfin)
  · intro v hv
    have hvfin : v ∉ Sfin := by
      intro hvfin
      exact hv ((hSfin v).1 hvfin)
    change (a : v.adicCompletion K) ∈ v.adicCompletionIntegers K
    apply (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (𝓞 K) K v).2
    rw [chapter01_completion_valuation_agrees_with_global]
    by_cases ha0 : a = 0
    · simp [ha0]
    · have hval : v.valuation K a = WithZero.exp (-(chapter01Order v a)) := by
        simpa [chapter01Order,
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent] using
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
            v ha0)
      rw [hval, ← WithZero.exp_zero, WithZero.exp_le_exp]
      exact neg_nonpos.mpr (haout v hvfin)

abbrev chapter04GlobalPrincipalPartsDenseSubspaceQuotientTopology
    (K : Type*) [Field K] [NumberField K] :
    TopologicalSpace (Chapter04GlobalPrincipalPartsQuotient K) :=
  TopologicalSpace.coinduced
    (QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K))
    (chapter04GlobalDiagonalSubspaceTopology K)

theorem chapter04_global_diagonal_subspace_is_not_discrete
    (K : Type*) [Field K] [NumberField K] :
    ¬ @DiscreteTopology K (chapter04GlobalDiagonalSubspaceTopology K) := by
  let d := IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 K) K
  have hfa_not_discrete :
      ¬ @DiscreteTopology (Chapter04FiniteAdeleRing K) inferInstance := by
    intro hdisc
    letI : DiscreteTopology (Chapter04FiniteAdeleRing K) := hdisc
    let g : 𝓞 K → Chapter04FiniteIntegralAdeleAddSubgroup K := fun r =>
      ⟨d (algebraMap (𝓞 K) K r), by
        apply (chapter04_finiteIntegralAdele_mem_iff_all_coordinates_integral K _).2
        intro v
        change algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r) ∈
          v.adicCompletionIntegers K
        rw [← IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K) r]
        exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers
          (R := 𝓞 K) (K := K) v r⟩
    have hg : Function.Injective g := by
      intro r s hrs
      apply (IsFractionRing.injective (𝓞 K) K)
      have hadele : d (algebraMap (𝓞 K) K r) = d (algebraMap (𝓞 K) K s) :=
        congrArg (fun z : Chapter04FiniteIntegralAdeleAddSubgroup K =>
          (z : Chapter04FiniteAdeleRing K)) hrs
      have hnonempty : Nonempty (Chapter04FinitePlace K) := by
        obtain ⟨I, hI⟩ := Ideal.exists_maximal (𝓞 K)
        exact ⟨(IsDedekindDomain.HeightOneSpectrum.equivMaximalSpectrum
          (RingOfIntegers.not_isField K)).symm ⟨I, hI⟩⟩
      obtain ⟨v⟩ := hnonempty
      apply FaithfulSMul.algebraMap_injective K (v.adicCompletion K)
      have hv := congrArg (fun z : Chapter04FiniteAdeleRing K => z v) hadele
      change algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r) =
        algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K s) at hv
      rw [← IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K) r,
        ← IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K) s] at hv
      exact hv
    letI : Infinite (Chapter04FiniteIntegralAdeleAddSubgroup K) :=
      Infinite.of_injective g hg
    letI : CompactSpace (Chapter04FiniteIntegralAdeleAddSubgroup K) :=
      isCompact_iff_compactSpace.mp (chapter04_finiteIntegralAdele_is_compact_open K).1
    letI : Finite (Chapter04FiniteIntegralAdeleAddSubgroup K) :=
      finite_of_compact_of_discrete
    exact not_finite (Chapter04FiniteIntegralAdeleAddSubgroup K)
  letI : ∀ v : Chapter04FinitePlace K,
      T2Space (Chapter04FiniteLocalField K v) := fun _ => inferInstance
  letI : T2Space (Chapter04FiniteAdeleRing K) := by
    change T2Space
      (Πʳ v : Chapter04FinitePlace K,
        [Chapter04FiniteLocalField K v, chapter04FiniteLocalIntegerSet K v]_[Filter.cofinite])
    exact RestrictedProduct.instT2Space
  letI : ∀ v : Chapter04FinitePlace K,
      T1Space (Chapter04FiniteLocalField K v) := fun _ => inferInstance
  letI : T1Space (Chapter04FiniteAdeleRing K) := T2Space.t1Space
  letI : TopologicalSpace K := chapter04GlobalDiagonalSubspaceTopology K
  intro hdisc
  letI : DiscreteTopology K := hdisc
  have hzero : IsOpen ({0} : Set K) := isOpen_discrete _
  rcases (isOpen_induced_iff.mp hzero) with ⟨U, hU, hpre⟩
  have hzero_mem : (0 : Chapter04FiniteAdeleRing K) ∈ U := by
    have hmem : (0 : K) ∈ d ⁻¹' U := by
      rw [hpre]
      simp
    exact hmem
  by_cases hne : (U \ ({0} : Set (Chapter04FiniteAdeleRing K))).Nonempty
  · have hdiff : IsOpen (U \ ({0} : Set (Chapter04FiniteAdeleRing K))) :=
      hU.sdiff isClosed_singleton
    obtain ⟨a, hz⟩ :=
      (chapter04_global_diagonal_is_dense K).exists_mem_open hdiff hne
    have ha : a ∈ d ⁻¹' U := hz.1
    rw [hpre] at ha
    have ha0 : a = 0 := by simpa using ha
    apply hz.2
    simp [ha0]
  · have hsub : U ⊆ ({0} : Set (Chapter04FiniteAdeleRing K)) := by
      intro z hz
      by_contra hz0
      exact hne ⟨z, hz, hz0⟩
    have hUeq : U = ({0} : Set (Chapter04FiniteAdeleRing K)) :=
      Set.Subset.antisymm hsub (singleton_subset_iff.mpr hzero_mem)
    exact hfa_not_discrete (discreteTopology_of_isOpen_singleton_zero
      (hUeq ▸ hU))

theorem chapter04_global_dense_subspace_quotient_is_discrete
    (K : Type*) [Field K] [NumberField K] :
    @DiscreteTopology (Chapter04GlobalPrincipalPartsQuotient K)
      (chapter04GlobalPrincipalPartsDenseSubspaceQuotientTopology K) := by
  let d := IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 K) K
  have hd_mem (c : K) : d c ∈ Chapter04FiniteIntegralAdeleAddSubgroup K ↔
      c ∈ Chapter04RingOfIntegersAddSubgroup K := by
    constructor
    · intro hc
      apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
        (R := 𝓞 K) (K := K) c
      intro v
      have hcoord :=
        (chapter04_finiteIntegralAdele_mem_iff_all_coordinates_integral K (d c)).1 hc v
      change algebraMap K (v.adicCompletion K) c ∈ v.adicCompletionIntegers K at hcoord
      rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v]
      exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
        (𝓞 K) K v).1 hcoord
    · rintro ⟨r, rfl⟩
      apply (chapter04_finiteIntegralAdele_mem_iff_all_coordinates_integral K _).2
      intro v
      change algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r) ∈
        v.adicCompletionIntegers K
      rw [← IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K) r]
      exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers
        (R := 𝓞 K) (K := K) v r
  letI : TopologicalSpace (Chapter04GlobalPrincipalPartsQuotient K) :=
    chapter04GlobalPrincipalPartsDenseSubspaceQuotientTopology K
  refine ⟨?_⟩
  apply eq_bot_of_singletons_open
  intro y
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
    (Chapter04RingOfIntegersAddSubgroup K) y
  change IsOpen[
    TopologicalSpace.coinduced
      (QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K))
      (chapter04GlobalDiagonalSubspaceTopology K)]
    ({QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K) a} :
      Set (Chapter04GlobalPrincipalPartsQuotient K))
  change IsOpen[chapter04GlobalDiagonalSubspaceTopology K]
    ((QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K)) ⁻¹'
      {QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K) a})
  change IsOpen[TopologicalSpace.induced d inferInstance]
    ((QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K)) ⁻¹'
      {QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K) a})
  change ∃ t : Set (Chapter04FiniteAdeleRing K), IsOpen t ∧ d ⁻¹' t =
    (QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K)) ⁻¹'
      {QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K) a}
  let H : Set (Chapter04FiniteAdeleRing K) :=
    Chapter04FiniteIntegralAdeleAddSubgroup K
  let t : Set (Chapter04FiniteAdeleRing K) :=
    {z | z - d a ∈ H}
  have ht : IsOpen t := by
    change IsOpen ((fun z : Chapter04FiniteAdeleRing K => z - d a) ⁻¹' H)
    exact (continuous_id.sub continuous_const).isOpen_preimage _
      (chapter04_finiteIntegralAdele_is_compact_open K).2
  refine ⟨t, ht, ?_⟩
  ext b
  change d b - d a ∈ H ↔
    QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K) b =
      QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K) a
  rw [← map_sub]
  constructor
  · intro h
    apply (QuotientAddGroup.eq_iff_sub_mem).2
    exact (hd_mem (b - a)).1 (by simpa [H] using h)
  · intro h
    have hmem : b - a ∈ Chapter04RingOfIntegersAddSubgroup K :=
      (QuotientAddGroup.eq_iff_sub_mem).1 h
    exact (by simpa [H] using (hd_mem (b - a)).2 hmem)

theorem chapter04_principalParts_transport_is_the_dense_subspace_quotient_topology
    (K : Type*) [Field K] [NumberField K] :
    chapter04PrincipalPartsTransportedDiscreteTopology K =
      chapter04GlobalPrincipalPartsDenseSubspaceQuotientTopology K := by
  have hleft := chapter04_principalParts_transport_is_discrete K
  have hright := chapter04_global_dense_subspace_quotient_is_discrete K
  exact hleft.eq_bot.trans hright.eq_bot.symm

theorem chapter04_principalParts_quotient_is_a_topological_additive_group_isomorphism
    (K : Type*) [Field K] [NumberField K] :
    @Continuous (Chapter04GlobalPrincipalPartsQuotient K)
        (Chapter04FinitePrincipalPartsQuotient K)
        (chapter04GlobalPrincipalPartsDenseSubspaceQuotientTopology K) inferInstance
        (chapter04PrincipalPartsEquiv K) ∧
      @Continuous (Chapter04FinitePrincipalPartsQuotient K)
        (Chapter04GlobalPrincipalPartsQuotient K)
        inferInstance (chapter04GlobalPrincipalPartsDenseSubspaceQuotientTopology K)
        (chapter04PrincipalPartsEquiv K).symm := by
  constructor
  · letI : TopologicalSpace (Chapter04GlobalPrincipalPartsQuotient K) :=
      chapter04GlobalPrincipalPartsDenseSubspaceQuotientTopology K
    letI : DiscreteTopology (Chapter04GlobalPrincipalPartsQuotient K) :=
      chapter04_global_dense_subspace_quotient_is_discrete K
    exact continuous_of_discreteTopology
  · letI : TopologicalSpace (Chapter04FinitePrincipalPartsQuotient K) := inferInstance
    letI : DiscreteTopology (Chapter04FinitePrincipalPartsQuotient K) :=
      chapter04_finitePrincipalPartsQuotient_is_discrete K
    letI : TopologicalSpace (Chapter04GlobalPrincipalPartsQuotient K) :=
      chapter04GlobalPrincipalPartsDenseSubspaceQuotientTopology K
    exact continuous_of_discreteTopology

def chapter04FiniteAdeleSingleCoordinate
    (K : Type*) [Field K] [NumberField K]
    (v₀ : Chapter04FinitePlace K) (z : Chapter04FiniteLocalField K v₀) :
    Chapter04FiniteAdeleRing K := by
  classical
  exact ⟨fun v => if h : v = v₀ then h ▸ z else 0, by
    filter_upwards [eventually_cofinite_ne v₀] with v hv
    simp only [dif_neg hv]
    exact (v.adicCompletionIntegers K).zero_mem⟩

@[simp]
theorem chapter04FiniteAdeleSingleCoordinate_apply_same
    (K : Type*) [Field K] [NumberField K]
    (v₀ : Chapter04FinitePlace K) (z : Chapter04FiniteLocalField K v₀) :
    chapter04FiniteAdeleSingleCoordinate K v₀ z v₀ = z := by
  sorry

theorem chapter04FiniteAdeleSingleCoordinate_apply_ne
    (K : Type*) [Field K] [NumberField K]
    (v₀ : Chapter04FinitePlace K) (z : Chapter04FiniteLocalField K v₀)
    {v : Chapter04FinitePlace K} (hv : v ≠ v₀) :
    chapter04FiniteAdeleSingleCoordinate K v₀ z v = 0 := by
  sorry

theorem chapter04_finite_principal_parts_are_represented_by_one_global_element
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04FiniteAdeleRing K) :
    ∃ a : K, ∀ v : Chapter04FinitePlace K,
      x v - (a : Chapter04FiniteLocalField K v) ∈
        chapter04FiniteLocalIntegerSet K v := by
  sorry

def chapter04RationalPrincipalPartsCorrectionExample
    (p q : Chapter04FinitePlace ℚ) (_hpq : p ≠ q)
    (r s : ℚ) (_hr : r ≠ 0) (_hs : s ≠ 0) :
    Chapter04FiniteAdeleRing ℚ :=
  chapter04FiniteAdeleSingleCoordinate ℚ p
      (((r : Chapter04FiniteLocalField ℚ p)⁻¹) ^ 2 +
        (r : Chapter04FiniteLocalField ℚ p)⁻¹) +
    chapter04FiniteAdeleSingleCoordinate ℚ q
      (s : Chapter04FiniteLocalField ℚ q)⁻¹

theorem chapter04_rational_principal_parts_correction_example
    (p q : Chapter04FinitePlace ℚ) (hpq : p ≠ q)
    (r s : ℚ) (hr : r ≠ 0) (hs : s ≠ 0) :
    ∃ a : ℚ, ∀ v : Chapter04FinitePlace ℚ,
      chapter04RationalPrincipalPartsCorrectionExample p q hpq r s hr hs v -
          (a : Chapter04FiniteLocalField ℚ v) ∈
      chapter04FiniteLocalIntegerSet ℚ v := by
  sorry

def chapter04RationalDisplayedPrincipalPartsFamily
    (p q : Chapter04RationalPrime) (hpq : p ≠ q) :
    Chapter04RationalFiniteRestrictedProduct := by
  classical
  exact RestrictedProduct.mk (fun r =>
    if h : r = p then
      h ▸ (((p.1 : Chapter04RationalPadic p)⁻¹) ^ 2 +
        (p.1 : Chapter04RationalPadic p)⁻¹)
    else if h : r = q then
      h ▸ (q.1 : Chapter04RationalPadic q)⁻¹
    else 0) (by
      sorry)

def chapter04RationalDisplayedPrincipalPartsRepresentative
    (p q : Chapter04RationalPrime) : ℚ :=
  (p.1 : ℚ)⁻¹ ^ 2 + (p.1 : ℚ)⁻¹ + (q.1 : ℚ)⁻¹

theorem chapter04_rational_displayed_principal_parts_are_represented
    (p q : Chapter04RationalPrime) (hpq : p ≠ q) :
    ∀ r : Chapter04RationalPrime,
      chapter04RationalDisplayedPrincipalPartsFamily p q hpq r -
          (chapter04RationalDisplayedPrincipalPartsRepresentative p q :
            Chapter04RationalPadic r) ∈ Chapter04RationalPadicIntegerSubring r := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter04
