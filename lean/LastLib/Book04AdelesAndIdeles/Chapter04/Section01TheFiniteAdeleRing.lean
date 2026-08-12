import LastLib.Book04AdelesAndIdeles.Chapter04.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open Set Filter
open NumberField IsDedekindDomain
open scoped BigOperators Topology RestrictedProduct

/-! ### 4.1 The finite adele ring -/

theorem chapter04_finiteAdeleRing_is_commutative_topological_ring
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (CommRing (Chapter04FiniteAdeleRing K)) ∧
      IsTopologicalRing (Chapter04FiniteAdeleRing K) := by
  sorry

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

theorem chapter04_profiniteCompletion_is_compact_t2_totally_disconnected
    (K : Type*) [Field K] [NumberField K] :
    CompactSpace (Chapter04ProfiniteCompletion K) ∧
      T2Space (Chapter04ProfiniteCompletion K) ∧
      TotallyDisconnectedSpace (Chapter04ProfiniteCompletion K) := by
  sorry

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

def chapter04ProfiniteIdealPrimeSupport
    (K : Type*) [Field K] [NumberField K]
    (I : Chapter04ProfiniteIdealIndex K) : Set (Chapter04FinitePlace K) :=
  {v | I.1 ≤ v.asIdeal}

theorem chapter04_profinite_reduction_uses_finitely_many_prime_divisors
    (K : Type*) [Field K] [NumberField K]
    (I : Chapter04ProfiniteIdealIndex K) :
    (chapter04ProfiniteIdealPrimeSupport K I).Finite := by
  sorry

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
  sorry

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
  sorry

theorem chapter04_rational_profinite_integers_is_the_product_of_padic_integers :
    Nonempty (Chapter04RationalProfiniteIntegers ≃+*
      Chapter04FiniteIntegralAdele ℚ) := by
  sorry

def chapter04RationalFamilyIsFiniteAdele
    (x : ∀ p : Chapter04RationalPrime, Chapter04RationalPadic p) : Prop :=
  ∀ᶠ p : Chapter04RationalPrime in Filter.cofinite,
    x p ∈ Chapter04RationalPadicIntegerSubring p

def chapter04RationalInversePrimeFamily :
    ∀ p : Chapter04RationalPrime, Chapter04RationalPadic p :=
  fun p => (p.1 : Chapter04RationalPadic p)⁻¹

theorem chapter04_rational_inverse_prime_family_not_a_finite_adele :
    ¬ chapter04RationalFamilyIsFiniteAdele chapter04RationalInversePrimeFamily := by
  sorry

def chapter04RationalSingleInversePrimeFamily (p₀ : Chapter04RationalPrime) :
    ∀ p : Chapter04RationalPrime, Chapter04RationalPadic p :=
  fun p => if h : p = p₀ then h ▸ chapter04RationalInversePrimeFamily p₀ else 0

theorem chapter04_rational_single_inverse_prime_family_is_a_finite_adele
    (p₀ : Chapter04RationalPrime) :
    chapter04RationalFamilyIsFiniteAdele
      (chapter04RationalSingleInversePrimeFamily p₀) := by
  sorry

def chapter04RationalDiagonalFamily (a : ℚ) :
    ∀ p : Chapter04RationalPrime, Chapter04RationalPadic p :=
  fun _ => a

theorem chapter04_rational_diagonal_family_is_a_finite_adele (a : ℚ) :
    chapter04RationalFamilyIsFiniteAdele (chapter04RationalDiagonalFamily a) := by
  sorry

theorem chapter04_rational_diagonal_family_is_the_canonical_global_diagonal
    (a : ℚ) :
    ∃ x : Chapter04FiniteAdeleRing ℚ,
      x = IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 ℚ) ℚ a ∧
        ∀ v : Chapter04FinitePlace ℚ,
          x v = (a : Chapter04FiniteLocalField ℚ v) := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter04
