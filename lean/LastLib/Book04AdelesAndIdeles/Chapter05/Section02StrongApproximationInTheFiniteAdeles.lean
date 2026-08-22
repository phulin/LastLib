import LastLib.Book04AdelesAndIdeles.Chapter05.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter04.Section03NeighborhoodsAsLocalSpecifications

namespace LastLib.Book04AdelesAndIdeles.Chapter05

open LastLib.Book04AdelesAndIdeles.Chapter01
open LastLib.Book04AdelesAndIdeles.Chapter04
open NumberField IsDedekindDomain

noncomputable section

open scoped Topology WithZero

/-! ## 5.2. Strong approximation in the finite adeles -/

/-! The finite congruence input is the canonical Chapter 1 approximation
statement, expressed through the canonical completion map. -/

theorem chapter05_finite_approximation_hits_congruences
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K))
    (x : ∀ v : Chapter04FinitePlace K, v ∈ S →
      Chapter04FiniteLocalField K v)
    (m : ∀ v : Chapter04FinitePlace K, v ∈ S → ℤ) :
    ∃ a : K,
      (∀ v (hv : v ∈ S),
        LastLib.Book04AdelesAndIdeles.Chapter01.chapter01LocallyClose
          v (x v hv) (chapter05FiniteDiagonal K a v) (m v hv)) ∧
      (∀ q : Chapter04FinitePlace K, q ∉ S →
        0 ≤ LastLib.Book04AdelesAndIdeles.Chapter01.chapter01Order q a) := by
  exact chapter01_finite_approximation K S x m

/-! Every canonical finite-adelic neighborhood contains a principal adele. -/

theorem chapter05_finite_diagonal_hits_nhds
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04FiniteAdeleRing K)
    (U : Set (Chapter04FiniteAdeleRing K)) (hU : U ∈ 𝓝 x) :
    ∃ a : K, chapter05FiniteDiagonal K a ∈ U := by
  classical
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
    chapter05_finite_approximation_hits_congruences K Sfin
      (fun v _ => x v) m
  refine ⟨a, ?_⟩
  apply hsub
  rw [chapter04_mem_finiteBasicNeighborhood_iff]
  constructor
  · intro v hv
    have hvfin : v ∈ Sfin := (hSfin v).2 hv
    exact hm v hvfin (chapter05FiniteDiagonal K a v) (by simpa using haS v hvfin)
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

/-!
**Theorem 5.1 (strong approximation away from infinity).** The canonical
diagonal image of `K` is dense in the finite adele ring.
-/
theorem chapter05_theorem_5_1_strong_approximation_away_from_infinity
    (K : Type*) [Field K] [NumberField K] :
    DenseRange (chapter05FiniteDiagonal K) := by
  sorry

theorem chapter05_strong_approximation_finite_adeles_closure
    (K : Type*) [Field K] [NumberField K] :
    closure (Set.range (chapter05FiniteDiagonal K)) =
      (Set.univ : Set (Chapter04FiniteAdeleRing K)) := by
  sorry

theorem chapter05_strong_approximation_finite_adeles_iff_nhds
    (K : Type*) [Field K] [NumberField K] :
    DenseRange (chapter05FiniteDiagonal K) ↔
      ∀ (x : Chapter04FiniteAdeleRing K)
        (U : Set (Chapter04FiniteAdeleRing K)), U ∈ 𝓝 x →
          ∃ a : K, chapter05FiniteDiagonal K a ∈ U := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter05
