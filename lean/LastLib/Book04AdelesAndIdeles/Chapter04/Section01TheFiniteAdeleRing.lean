import LastLib.Book04AdelesAndIdeles.Chapter04.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open Set Filter
open NumberField IsDedekindDomain
open scoped BigOperators Topology RestrictedProduct

/-! ### 4.1 The finite adele ring -/

theorem chapter04_finiteAdeleRing_is_commutative_topological_ring
    (K : Type*) [Field K] [NumberField K] :
      IsTopologicalRing (Chapter04FiniteAdeleRing K) ∧
      ∀ x y : Chapter04FiniteAdeleRing K, x * y = y * x := by
  refine ⟨(chapter04_finiteAdeleRing_is_locally_compact_topological_ring K).2, ?_⟩
  intro x y
  apply chapter04_finiteAdele_ext K
  intro v
  rw [chapter04_finiteAdele_mul_apply, chapter04_finiteAdele_mul_apply]
  exact mul_comm _ _

theorem chapter04_finiteAdele_integrality_is_cofinite
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04FiniteAdeleRing K) :
    ∀ᶠ v : Chapter04FinitePlace K in Filter.cofinite,
      x v ∈ chapter04FiniteLocalIntegerSet K v :=
  chapter04_finiteAdele_mem_iff_eventually_integral K x

theorem chapter04_finiteAdele_operations_are_coordinatewise
    (K : Type*) [Field K] [NumberField K]
    (x y : Chapter04FiniteAdeleRing K) :
    (∀ v, (x + y) v = x v + y v) ∧
      (∀ v, (x * y) v = x v * y v) := by
  exact ⟨fun v => chapter04_finiteAdele_add_apply K x y v,
    fun v => chapter04_finiteAdele_mul_apply K x y v⟩

theorem chapter04_finiteAdele_multiplication_is_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (fun p : Chapter04FiniteAdeleRing K × Chapter04FiniteAdeleRing K =>
      p.1 * p.2) := by
  exact continuous_mul

theorem chapter04_finiteIntegralAdele_is_the_full_integral_tail
    (K : Type*) [Field K] [NumberField K] :
    (Chapter04FiniteIntegralAdeleSubring K : Set (Chapter04FiniteAdeleRing K)) =
      {x | ∀ v : Chapter04FinitePlace K,
        x v ∈ chapter04FiniteLocalIntegerSet K v} := by
  ext x
  exact chapter04_finiteIntegralAdele_mem_iff_all_coordinates_integral K x

abbrev Chapter04ProfiniteIdealIndex
    (K : Type*) [Field K] [NumberField K] :=
  {I : Ideal (Chapter04RingOfIntegers K) // I ≠ ⊥}

def chapter04ProfiniteCompatibility
    (K : Type*) [Field K] [NumberField K]
    (x : ∀ I : Chapter04ProfiniteIdealIndex K,
      Chapter04RingOfIntegers K ⧸ I.1) : Prop :=
  ∀ (I J : Chapter04ProfiniteIdealIndex K) (hIJ : I.1 ≤ J.1),
    Ideal.Quotient.factor hIJ (x I) = x J

def chapter04ProfiniteCompletionSubring
    (K : Type*) [Field K] [NumberField K] :
    Subring (∀ I : Chapter04ProfiniteIdealIndex K,
      Chapter04RingOfIntegers K ⧸ I.1) where
  carrier := {x | chapter04ProfiniteCompatibility K x}
  zero_mem' := by
    intro I J hIJ
    simp
  one_mem' := by
    intro I J hIJ
    simp
  add_mem' := by
    intro x y hx hy I J hIJ
    simpa [chapter04ProfiniteCompatibility] using congrArg₂ (· + ·) (hx I J hIJ) (hy I J hIJ)
  mul_mem' := by
    intro x y hx hy I J hIJ
    simpa [chapter04ProfiniteCompatibility] using congrArg₂ (· * ·) (hx I J hIJ) (hy I J hIJ)
  neg_mem' := by
    intro x hx I J hIJ
    simpa [chapter04ProfiniteCompatibility] using congrArg Neg.neg (hx I J hIJ)

abbrev Chapter04ProfiniteCompletion
    (K : Type*) [Field K] [NumberField K] :=
  chapter04ProfiniteCompletionSubring K

instance chapter04ProfiniteQuotientTopologicalSpace
    (K : Type*) [Field K] [NumberField K]
    (I : Chapter04ProfiniteIdealIndex K) :
    TopologicalSpace (Chapter04RingOfIntegers K ⧸ I.1) :=
  ⊥

instance chapter04ProfiniteQuotientDiscreteTopology
    (K : Type*) [Field K] [NumberField K]
    (I : Chapter04ProfiniteIdealIndex K) :
    DiscreteTopology (Chapter04RingOfIntegers K ⧸ I.1) :=
  ⟨rfl⟩

theorem chapter04_profiniteCompletion_is_compact_t2_totally_disconnected
    (K : Type*) [Field K] [NumberField K] :
      CompactSpace (Chapter04ProfiniteCompletion K) ∧
      T2Space (Chapter04ProfiniteCompletion K) ∧
      TotallyDisconnectedSpace (Chapter04ProfiniteCompletion K) := by
  let hFinite (I : Chapter04ProfiniteIdealIndex K) :
      Finite (Chapter04RingOfIntegers K ⧸ I.1) :=
    Ring.HasFiniteQuotients.finiteQuotient I.2
  let hCompact (I : Chapter04ProfiniteIdealIndex K) :
      CompactSpace (Chapter04RingOfIntegers K ⧸ I.1) :=
    @Finite.compactSpace _ _ (hFinite I)
  let hT2 (I : Chapter04ProfiniteIdealIndex K) :
      T2Space (Chapter04RingOfIntegers K ⧸ I.1) := by infer_instance
  let hTotallyDisconnected (I : Chapter04ProfiniteIdealIndex K) :
      TotallyDisconnectedSpace (Chapter04RingOfIntegers K ⧸ I.1) := by
    infer_instance
  have hclosed : IsClosed {x : ∀ I : Chapter04ProfiniteIdealIndex K,
      Chapter04RingOfIntegers K ⧸ I.1 | chapter04ProfiniteCompatibility K x} := by
    unfold chapter04ProfiniteCompatibility
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro I
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro J
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro hIJ
    exact isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply I))
      (continuous_apply J)
  let _ : CompactSpace (∀ I : Chapter04ProfiniteIdealIndex K,
      Chapter04RingOfIntegers K ⧸ I.1) :=
    @Pi.compactSpace _ _ (fun _ => inferInstance) hCompact
  let _ : T2Space (∀ I : Chapter04ProfiniteIdealIndex K,
      Chapter04RingOfIntegers K ⧸ I.1) :=
    @Pi.t2Space _ _ (fun _ => inferInstance) hT2
  let _ : TotallyDisconnectedSpace
      (∀ I : Chapter04ProfiniteIdealIndex K, Chapter04RingOfIntegers K ⧸ I.1) :=
    @Pi.totallyDisconnectedSpace _ _ (fun _ => inferInstance) hTotallyDisconnected
  exact ⟨isCompact_iff_compactSpace.mp (hclosed.isCompact), inferInstance, inferInstance⟩

def chapter04ProfiniteCompletionMap
    (K : Type*) [Field K] [NumberField K] :
    Chapter04RingOfIntegers K →+* Chapter04ProfiniteCompletion K where
  toFun x :=
    ⟨fun I => Ideal.Quotient.mk I.1 x, by
      intro I J hIJ
      exact Ideal.Quotient.factor_mk hIJ x⟩
  map_one' := by
    apply Subtype.ext
    funext I
    simp
  map_mul' x y := by
    apply Subtype.ext
    funext I
    simp
  map_zero' := by
    apply Subtype.ext
    funext I
    simp
  map_add' x y := by
    apply Subtype.ext
    funext I
    simp

@[simp]
theorem chapter04_profiniteCompletionMap_apply
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04RingOfIntegers K) (I : Chapter04ProfiniteIdealIndex K) :
    (chapter04ProfiniteCompletionMap K x).val I = Ideal.Quotient.mk I.1 x := by
  rfl

/- LOCAL_DEPENDENCY_GUESS: the explicit profinite ring inverse-limit bridge
below packages the canonical CRT comparison that is not exposed by the
pinned Mathlib finite-adele API as a named ring equivalence. -/
theorem chapter04_finiteIntegralAdele_equiv_profiniteCompletion
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (Chapter04FiniteIntegralAdele K ≃+* Chapter04ProfiniteCompletion K) := by
  sorry

theorem chapter04_finiteIntegralAdele_profiniteCompletion_is_topologically_equivalent
    (K : Type*) [Field K] [NumberField K] :
    ∃ e : Chapter04FiniteIntegralAdele K ≃+* Chapter04ProfiniteCompletion K,
      Continuous e ∧ Continuous e.symm := by
  sorry

def chapter04ProfiniteIdealPrimeSupport
    (K : Type*) [Field K] [NumberField K]
    (I : Chapter04ProfiniteIdealIndex K) : Set (Chapter04FinitePlace K) :=
  {v | I.1 ≤ v.asIdeal}

theorem chapter04_profinite_reduction_uses_finitely_many_prime_divisors
    (K : Type*) [Field K] [NumberField K]
    (I : Chapter04ProfiniteIdealIndex K) :
    (chapter04ProfiniteIdealPrimeSupport K I).Finite := by
  have h := Ideal.finite_factors (R := Chapter04RingOfIntegers K) I.2
  simpa [chapter04ProfiniteIdealPrimeSupport, Ideal.dvd_iff_le] using h

theorem chapter04_profinite_completion_element_is_compatible
    (K : Type*) [Field K] [NumberField K] :
    ∀ (x : Chapter04ProfiniteCompletion K),
      chapter04ProfiniteCompatibility K (x : ∀ I : Chapter04ProfiniteIdealIndex K,
        Chapter04RingOfIntegers K ⧸ I.1) := by
  intro x
  exact x.property

noncomputable def chapter04FiniteIntegralAdeleProfiniteCompletionEquiv
    (K : Type*) [Field K] [NumberField K] :
    Chapter04FiniteIntegralAdele K ≃+* Chapter04ProfiniteCompletion K :=
  Classical.choice (chapter04_finiteIntegralAdele_equiv_profiniteCompletion K)

theorem chapter04_profinite_completion_is_reconstructed_by_CRT
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04ProfiniteCompletion K) :
    ∃! y : Chapter04FiniteIntegralAdele K,
      chapter04FiniteIntegralAdeleProfiniteCompletionEquiv K y = x := by
  let e := chapter04FiniteIntegralAdeleProfiniteCompletionEquiv K
  refine ⟨e.symm x, e.apply_symm_apply x, ?_⟩
  intro y hy
  apply e.injective
  rw [hy, e.apply_symm_apply]

abbrev Chapter04RationalPrime := {p : ℕ // Nat.Prime p}

abbrev Chapter04RationalPadic (p : Chapter04RationalPrime) :=
  @Padic p.1 ⟨p.2⟩

abbrev Chapter04RationalPadicInteger (p : Chapter04RationalPrime) :=
  @PadicInt p.1 ⟨p.2⟩

abbrev Chapter04RationalPadicIntegerSubring (p : Chapter04RationalPrime) :
    Subring (Chapter04RationalPadic p) :=
  @PadicInt.subring p.1 ⟨p.2⟩

abbrev Chapter04RationalFiniteRestrictedProduct :=
  Πʳ p : Chapter04RationalPrime,
    [Chapter04RationalPadic p, Chapter04RationalPadicIntegerSubring p]_[Filter.cofinite]

abbrev Chapter04RationalProfiniteIntegers :=
  ∀ p : Chapter04RationalPrime, Chapter04RationalPadicInteger p

theorem chapter04_rational_finite_adele_ring_is_the_padic_restricted_product :
    Nonempty (Chapter04RationalFiniteRestrictedProduct ≃+*
      Chapter04FiniteAdeleRing ℚ) := by
  let e : Chapter04FinitePlace ℚ ≃ Chapter04RationalPrime :=
    Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
  let f : Chapter04FinitePlace ℚ → Chapter04RationalPrime := fun v => e v
  let φ : ∀ v : Chapter04FinitePlace ℚ,
      Chapter04RationalPadic (f v) →+* Chapter04FiniteLocalField ℚ v :=
    fun v =>
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.toAlgEquiv.toRingEquiv.toRingHom
  have hf : Filter.Tendsto f Filter.cofinite Filter.cofinite := by
    change Filter.Tendsto (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) => e v)
      Filter.cofinite Filter.cofinite
    exact e.injective.tendsto_cofinite
  have hφ : ∀ᶠ v : Chapter04FinitePlace ℚ in Filter.cofinite,
      MapsTo (φ v) (Chapter04RationalPadicIntegerSubring (f v) : Set _)
        (chapter04FiniteLocalIntegerSet ℚ v) := by
    exact Filter.Eventually.of_forall (fun v x hx => by
      let y : Chapter04RationalPadicInteger (f v) := ⟨x, hx⟩
      have hcoe :=
        Rat.HeightOneSpectrum.adicCompletionIntegers.coe_padicIntEquiv_symm_apply v y
      change (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm x ∈
        (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))
      have hcoe' :
          ((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm y :
            v.adicCompletion ℚ) =
          (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm x := by
        simpa [y] using hcoe
      rw [← hcoe']
      exact (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm y |>.property)
  let g : Chapter04RationalPrime → Chapter04FinitePlace ℚ := fun p => e.symm p
  let ψ : ∀ p : Chapter04RationalPrime,
      Chapter04FiniteLocalField ℚ (g p) →+* Chapter04RationalPadic p :=
    fun p =>
      ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv (e.symm p)).trans
        (ContinuousAlgEquiv.cast
          (A := fun q : Chapter04RationalPrime => Chapter04RationalPadic q)
          (e.apply_symm_apply p))).toAlgEquiv.toRingEquiv.toRingHom
  have hg : Filter.Tendsto g Filter.cofinite Filter.cofinite := by
    change Filter.Tendsto (fun p : Chapter04RationalPrime => e.symm p)
      Filter.cofinite Filter.cofinite
    exact e.symm.injective.tendsto_cofinite
  have hψ : ∀ᶠ p : Chapter04RationalPrime in Filter.cofinite,
      MapsTo (ψ p) (chapter04FiniteLocalIntegerSet ℚ (g p))
        (Chapter04RationalPadicIntegerSubring p : Set _) := by
    exact Filter.Eventually.of_forall (fun p x hx => by
      let y : Chapter04FiniteLocalIntegerRing ℚ (g p) := ⟨x, hx⟩
      let z : Chapter04RationalPadicInteger p :=
        (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p).symm y
      have hcoe := PadicInt.coe_adicCompletionIntegersEquiv_symm_apply (𝓞 ℚ) p y
      change (Padic.adicCompletionEquiv (𝓞 ℚ) p).symm x ∈
        (Chapter04RationalPadicIntegerSubring p : Set (Chapter04RationalPadic p))
      have hcoe' :
          (z : Chapter04RationalPadic p) =
          (Padic.adicCompletionEquiv (𝓞 ℚ) p).symm x := by
        simpa [y] using hcoe
      rw [← hcoe']
      exact z.property)
  let F : Chapter04RationalFiniteRestrictedProduct →+*
      Chapter04FiniteAdeleRing ℚ :=
    RestrictedProduct.mapAlongRingHom
      (R₁ := fun p : Chapter04RationalPrime => Chapter04RationalPadic p)
      (R₂ := fun v : Chapter04FinitePlace ℚ => Chapter04FiniteLocalField ℚ v)
      (B₁ := fun p => Chapter04RationalPadicIntegerSubring p)
      (B₂ := fun v => v.adicCompletionIntegers ℚ)
      f hf φ hφ
  let G : Chapter04FiniteAdeleRing ℚ →+*
      Chapter04RationalFiniteRestrictedProduct :=
    RestrictedProduct.mapAlongRingHom
      (R₁ := fun v : Chapter04FinitePlace ℚ => Chapter04FiniteLocalField ℚ v)
      (R₂ := fun p : Chapter04RationalPrime => Chapter04RationalPadic p)
      (B₁ := fun v => v.adicCompletionIntegers ℚ)
      (B₂ := fun p => Chapter04RationalPadicIntegerSubring p)
      g hg ψ hψ
  let E : (∀ v : Chapter04FinitePlace ℚ, Chapter04FiniteLocalField ℚ v) ≃+*
      (∀ p : Chapter04RationalPrime, Chapter04RationalPadic p) :=
    (RingEquiv.piCongrRight
      (fun v => (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv)).trans
      (RingEquiv.piCongrLeft
        (fun p : Chapter04RationalPrime => Chapter04RationalPadic p) e)
  have hF_eq (x : Chapter04RationalFiniteRestrictedProduct) :
      (F x : ∀ v : Chapter04FinitePlace ℚ, Chapter04FiniteLocalField ℚ v) =
        E.symm (x : ∀ p : Chapter04RationalPrime, Chapter04RationalPadic p) := by
    funext v
    rfl
  have hG_eq (y : Chapter04FiniteAdeleRing ℚ) :
      (G y : ∀ p : Chapter04RationalPrime, Chapter04RationalPadic p) =
        E (y : ∀ v : Chapter04FinitePlace ℚ, Chapter04FiniteLocalField ℚ v) := by
    funext p
    change (ψ p) (y (g p)) = _
    simp [E, g, ψ]
    have hcast :
        (ContinuousAlgEquiv.cast (R := ℚ)
          (A := fun q : Chapter04RationalPrime => Chapter04RationalPadic q)
          (e.apply_symm_apply p))
            ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv (e.symm p))
              (y (e.symm p))) =
          Equiv.cast
            (congrArg (fun q : Chapter04RationalPrime => Chapter04RationalPadic q)
              (e.apply_symm_apply p))
            ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv (e.symm p))
              (y (e.symm p))) := by
      exact ContinuousAlgEquiv.cast_apply _ _
    rw [hcast]
    change cast
      (congrArg (fun q : Chapter04RationalPrime => Chapter04RationalPadic q)
        (e.apply_symm_apply p))
      ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv (e.symm p))
      (y (e.symm p))) = _
    simp only [eqRec_eq_cast]
  have hFG : Function.LeftInverse G F := by
    intro x
    apply Subtype.ext
    have h : (G (F x) : ∀ p : Chapter04RationalPrime, Chapter04RationalPadic p) =
        (x : ∀ p : Chapter04RationalPrime, Chapter04RationalPadic p) := by
      rw [hG_eq, hF_eq]
      exact E.apply_symm_apply _
    exact h
  have hGF : Function.RightInverse G F := by
    intro y
    apply Subtype.ext
    have h : (F (G y) : ∀ v : Chapter04FinitePlace ℚ, Chapter04FiniteLocalField ℚ v) =
        (y : ∀ v : Chapter04FinitePlace ℚ, Chapter04FiniteLocalField ℚ v) := by
      rw [hF_eq, hG_eq]
      exact E.symm_apply_apply _
    exact h
  have hbij : Function.Bijective F := by
    refine ⟨?_, ?_⟩
    · intro x₁ x₂ h
      apply hFG.injective
      rw [h]
    · intro y
      exact ⟨G y, hGF y⟩
  exact ⟨RingEquiv.ofBijective F hbij⟩

theorem chapter04_rational_profinite_integers_is_the_product_of_padic_integers :
    Nonempty (Chapter04RationalProfiniteIntegers ≃+*
      Chapter04FiniteIntegralAdele ℚ) := by
  let e : Chapter04FinitePlace ℚ ≃ Chapter04RationalPrime :=
    Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
  let E : (∀ p : Chapter04RationalPrime, Chapter04RationalPadicInteger p) ≃+*
      (∀ v : Chapter04FinitePlace ℚ, Chapter04FiniteLocalIntegerRing ℚ v) :=
    (RingEquiv.piCongrLeft
      (fun p : Chapter04RationalPrime => Chapter04RationalPadicInteger p) e).symm.trans
      (RingEquiv.piCongrRight
      (R := fun v : Chapter04FinitePlace ℚ => Chapter04RationalPadicInteger (e v))
      (S := fun v : Chapter04FinitePlace ℚ => Chapter04FiniteLocalIntegerRing ℚ v)
      (fun v : Chapter04FinitePlace ℚ =>
        (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv
          (R := 𝓞 ℚ) v).symm.toRingEquiv))
  exact ⟨E⟩

def chapter04RationalFamilyIsFiniteAdele
    (x : ∀ p : Chapter04RationalPrime, Chapter04RationalPadic p) : Prop :=
  ∀ᶠ p : Chapter04RationalPrime in Filter.cofinite,
    x p ∈ Chapter04RationalPadicIntegerSubring p

def chapter04RationalInversePrimeFamily :
    ∀ p : Chapter04RationalPrime, Chapter04RationalPadic p :=
  fun p => (p.1 : Chapter04RationalPadic p)⁻¹

theorem chapter04_rational_inverse_prime_family_not_a_finite_adele :
    ¬ chapter04RationalFamilyIsFiniteAdele chapter04RationalInversePrimeFamily := by
  intro h
  have hmem : ∀ᶠ p : Chapter04RationalPrime in Filter.cofinite,
      chapter04RationalInversePrimeFamily p ∈ Chapter04RationalPadicIntegerSubring p := by
    exact h
  let hInfinite : Infinite Chapter04RationalPrime :=
    Infinite.of_injective
      (fun p : Nat.Primes => (⟨p.1, p.2⟩ : Chapter04RationalPrime)) (by
        intro p q hpq
        exact Subtype.ext (congrArg Subtype.val hpq))
  let _ := hInfinite
  obtain ⟨p, hp⟩ := hmem.exists
  have hp_nonzero : (p.1 : Chapter04RationalPadic p) ≠ 0 := by
    exact_mod_cast p.2.ne_zero
  let hp_fact : Fact p.1.Prime := ⟨p.2⟩
  let _ := hp_fact
  have hp_norm : ‖(p.1 : Chapter04RationalPadic p)‖ < 1 := by
    rw [Padic.norm_natCast_lt_one_iff]
  have hp_inv_norm : 1 < ‖(chapter04RationalInversePrimeFamily p)‖ := by
    rw [chapter04RationalInversePrimeFamily, norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hp_nonzero)).2 hp_norm
  change ‖chapter04RationalInversePrimeFamily p‖ ≤ 1 at hp
  exact (not_lt_of_ge hp) hp_inv_norm

def chapter04RationalSingleInversePrimeFamily (p₀ : Chapter04RationalPrime) :
    ∀ p : Chapter04RationalPrime, Chapter04RationalPadic p :=
  fun p => if h : p = p₀ then h ▸ chapter04RationalInversePrimeFamily p₀ else 0

theorem chapter04_rational_single_inverse_prime_family_is_a_finite_adele
    (p₀ : Chapter04RationalPrime) :
    chapter04RationalFamilyIsFiniteAdele
      (chapter04RationalSingleInversePrimeFamily p₀) := by
  classical
  rw [chapter04RationalFamilyIsFiniteAdele]
  filter_upwards [Filter.eventually_cofinite_ne p₀] with p hp
  simp [chapter04RationalSingleInversePrimeFamily, hp]

def chapter04RationalDiagonalFamily (a : ℚ) :
    ∀ p : Chapter04RationalPrime, Chapter04RationalPadic p :=
  fun _ => a

theorem chapter04_rational_diagonal_family_is_a_finite_adele (a : ℚ) :
    chapter04RationalFamilyIsFiniteAdele (chapter04RationalDiagonalFamily a) := by
  let e : Chapter04FinitePlace ℚ ≃ Chapter04RationalPrime :=
    Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
  let x : Chapter04FiniteAdeleRing ℚ :=
    IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 ℚ) ℚ a
  have hx : ∀ᶠ v : Chapter04FinitePlace ℚ in Filter.cofinite,
      x v ∈ chapter04FiniteLocalIntegerSet ℚ v :=
    chapter04_finiteAdele_integrality_is_cofinite ℚ x
  have hx' : ∀ᶠ p : Chapter04RationalPrime in Filter.cofinite,
      x (e.symm p) ∈ chapter04FiniteLocalIntegerSet ℚ (e.symm p) :=
    e.symm.injective.tendsto_cofinite hx
  rw [chapter04RationalFamilyIsFiniteAdele]
  filter_upwards [hx'] with p hp
  have hpadic :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn (e.symm p)).1
      hp
  let q : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv (e.symm p)
  have hqp : q.1 = p.1 := by
    change (Rat.HeightOneSpectrum.primesEquiv (e.symm p)).1 = p.1
    exact congrArg Subtype.val (e.apply_symm_apply p)
  have hxcoord : x (e.symm p) =
      algebraMap ℚ (Chapter04FiniteLocalField ℚ (e.symm p)) a := by
    change
      (algebraMap ℚ (Chapter04FiniteAdeleRing ℚ) a) (e.symm p) = _
    exact IsDedekindDomain.FiniteAdeleRing.algebraMap_apply (𝓞 ℚ) ℚ a (e.symm p)
  have hcoord :
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (e.symm p))
          (x (e.symm p)) =
        algebraMap ℚ (@Padic q.1 ⟨q.2⟩) a := by
    rw [hxcoord]
    simp [q]
  rw [hcoord] at hpadic
  simpa [chapter04RationalDiagonalFamily, q, e, hqp] using hpadic

theorem chapter04_rational_diagonal_family_is_the_canonical_global_diagonal
    (a : ℚ) :
    ∃ x : Chapter04FiniteAdeleRing ℚ,
      x = IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 ℚ) ℚ a ∧
        ∀ v : Chapter04FinitePlace ℚ,
          x v = (a : Chapter04FiniteLocalField ℚ v) := by
  refine ⟨algebraMap ℚ (Chapter04FiniteAdeleRing ℚ) a, rfl, ?_⟩
  intro v
  have hcoe : algebraMap ℚ (Chapter04FiniteLocalField ℚ v) a =
      (a : Chapter04FiniteLocalField ℚ v) := by
    simp
  calc
    (algebraMap ℚ (Chapter04FiniteAdeleRing ℚ) a) v =
        algebraMap ℚ (Chapter04FiniteLocalField ℚ v) a :=
      IsDedekindDomain.FiniteAdeleRing.algebraMap_apply (𝓞 ℚ) ℚ a v
    _ = (a : Chapter04FiniteLocalField ℚ v) := hcoe

end

end LastLib.Book04AdelesAndIdeles.Chapter04
