import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14.Section03FactorizationAndFrobeniusCycleType

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14

noncomputable section

open Filter Topology
open Polynomial
open scoped BigOperators NumberField Pointwise

universe u v w

/-! ## 14.4. Weak approximation for coefficients -/

def chapter14FinitePlaceEmbedding
    {F : Type u} [Field F] [NumberField F] (p : Chapter14Prime F) :
    F →+* chapter14BaseCompletion F p :=
  NumberField.FinitePlace.embedding p

def chapter14DiagonalAtFinitePlaces
    {F : Type u} [Field F] [NumberField F]
    (S : Finset (Chapter14Prime F)) :
    F →+* (∀ p : S, chapter14BaseCompletion F p.1) := by
  refine
    { toFun := fun x p => chapter14FinitePlaceEmbedding p.1 x
      map_one' := by
        funext p
        simp [chapter14FinitePlaceEmbedding]
      map_mul' := by
        intro x y
        funext p
        simp [chapter14FinitePlaceEmbedding]
      map_zero' := by
        funext p
        simp [chapter14FinitePlaceEmbedding]
      map_add' := by
        intro x y
        funext p
        simp [chapter14FinitePlaceEmbedding] }

def chapter14WeakApproximationAtFinitePlaces
    {F : Type u} [Field F] [NumberField F]
    (S : Finset (Chapter14Prime F)) : Prop :=
  DenseRange (chapter14DiagonalAtFinitePlaces S)

theorem chapter14_weak_approximation_at_distinct_nonarchimedean_places
    {F : Type u} [Field F] [NumberField F]
    (S : Finset (Chapter14Prime F)) :
    chapter14WeakApproximationAtFinitePlaces S := by
  let v : ∀ p : S, AbsoluteValue F ℝ :=
    fun p => NumberField.HeightOneSpectrum.adicAbv F p.1
  have hv_nontrivial : ∀ p : S, (v p).IsNontrivial := by
    intro p
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot p.1.ne_bot
    refine ⟨algebraMap (𝓞 F) F r, ?_, ?_⟩
    · intro hzero
      apply hr0
      apply NumberField.RingOfIntegers.coe_injective (K := F)
      simpa using hzero
    · have hlt : (v p) (algebraMap (𝓞 F) F r) < 1 := by
        change p.1.adicAbv (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p.1)
          (algebraMap (𝓞 F) F r) < 1
        exact (p.1.adicAbv_coe_lt_one_iff
          (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p.1) r).2 hr
      exact ne_of_lt hlt
  have hv_pairwise : Pairwise (fun p q : S => ¬(v p).IsEquiv (v q)) := by
    intro p q hpq heq
    have hnotle : ¬p.1.asIdeal ≤ q.1.asIdeal := by
      intro hle
      have heqideal : p.1.asIdeal = q.1.asIdeal :=
        p.1.isMaximal.eq_of_le q.1.isMaximal.ne_top hle
      exact hpq (Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext heqideal))
    have hexists : ∃ r, r ∈ p.1.asIdeal ∧ r ∉ q.1.asIdeal := by
      by_contra h
      push Not at h
      exact hnotle h
    obtain ⟨r, hrp, hrq⟩ := hexists
    have hltp : (v p) (algebraMap (𝓞 F) F r) < 1 :=
      (p.1.adicAbv_coe_lt_one_iff
        (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p.1) r).2 hrp
    have hltq : (v q) (algebraMap (𝓞 F) F r) < 1 :=
      (AbsoluteValue.isEquiv_iff_lt_one_iff.mp heq _).mp hltp
    exact hrq ((q.1.adicAbv_coe_lt_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal q.1) r).1 hltq)
  let g : ∀ p : S, WithAbs (v p) → chapter14BaseCompletion F p.1 :=
    fun p x => chapter14FinitePlaceEmbedding p.1 x.ofAbs
  have hg_dense : ∀ p : S, DenseRange (g p) := by
    intro p
    have hbase :=
      IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F p.1
    rw [DenseRange] at hbase ⊢
    have hrange : Set.range (g p) =
        Set.range (algebraMap F (chapter14BaseCompletion F p.1)) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x.ofAbs, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨WithAbs.toAbs _ x, rfl⟩
    rw [hrange]
    exact hbase
  have hg_isometry : ∀ p : S, Isometry (g p) := by
    intro p
    apply Isometry.of_dist_eq
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    change ‖chapter14FinitePlaceEmbedding p.1 x.ofAbs -
        chapter14FinitePlaceEmbedding p.1 y.ofAbs‖ = ‖x - y‖
    rw [← map_sub, chapter14FinitePlaceEmbedding,
      NumberField.FinitePlace.norm_embedding,
      WithAbs.norm_eq_apply_ofAbs]
    rfl
  have hbase : DenseRange (algebraMap F ((p : S) → WithAbs (v p))) :=
    AbsoluteValue.denseRange_algebraMap_pi hv_nontrivial hv_pairwise
  have hg : DenseRange (Pi.map g) := DenseRange.piMap hg_dense
  have hgc : Continuous (Pi.map g) := continuous_pi fun p =>
    (hg_isometry p).continuous.comp (continuous_apply p)
  have hcomp := hg.comp hbase hgc
  change DenseRange (chapter14DiagonalAtFinitePlaces S)
  convert hcomp using 1
  ext x p
  rfl

def chapter14CoefficientDiagonal
    {F : Type u} [Field F] [NumberField F]
    (S : Finset (Chapter14Prime F)) (n : ℕ) :
    (Fin n → F) →+* (∀ p : S, Fin n → chapter14BaseCompletion F p.1) := by
  refine
    { toFun := fun c p i => chapter14FinitePlaceEmbedding p.1 (c i)
      map_one' := by
        funext p i
        simp [chapter14FinitePlaceEmbedding]
      map_mul' := by
        intro c d
        funext p i
        simp [chapter14FinitePlaceEmbedding]
      map_zero' := by
        funext p i
        simp [chapter14FinitePlaceEmbedding]
      map_add' := by
        intro c d
        funext p i
        simp [chapter14FinitePlaceEmbedding] }

theorem chapter14_coefficient_diagonal_apply
    {F : Type u} [Field F] [NumberField F]
    (S : Finset (Chapter14Prime F)) (n : ℕ)
    (c : Fin n → F) (p : S) (i : Fin n) :
    chapter14CoefficientDiagonal S n c p i =
      chapter14FinitePlaceEmbedding p.1 (c i) := by
  rfl

theorem chapter14_coefficient_weak_approximation
    {F : Type u} [Field F] [NumberField F]
    (S : Finset (Chapter14Prime F)) (n : ℕ)
    (a : ∀ p : S, Fin n → chapter14BaseCompletion F p.1)
    (U : ∀ p : S, Set (Fin n → chapter14BaseCompletion F p.1))
    (hU : ∀ p, IsOpen (U p)) (ha : ∀ p, a p ∈ U p) :
    ∃ c : Fin n → F, ∀ p, chapter14CoefficientDiagonal S n c p ∈ U p := by
  have hweak : DenseRange (chapter14DiagonalAtFinitePlaces S) :=
    chapter14_weak_approximation_at_distinct_nonarchimedean_places S
  have hmap : DenseRange
      (Pi.map (fun _ : Fin n => chapter14DiagonalAtFinitePlaces S)) :=
    DenseRange.piMap (fun _ => hweak)
  let transpose :
      (Fin n → (∀ p : S, chapter14BaseCompletion F p.1)) →
        (∀ p : S, Fin n → chapter14BaseCompletion F p.1) :=
    fun b p i => b i p
  have htranspose_surjective : Function.Surjective transpose := by
    intro b
    refine ⟨fun i p => b p i, ?_⟩
    funext p i
    rfl
  have htranspose_continuous : Continuous transpose := by
    apply continuous_pi
    intro p
    apply continuous_pi
    intro i
    exact (continuous_apply p).comp (continuous_apply i)
  have hcoeff : DenseRange (chapter14CoefficientDiagonal S n) := by
    have htranspose_dense : DenseRange transpose :=
      htranspose_surjective.denseRange
    have hcomp := htranspose_dense.comp hmap htranspose_continuous
    convert hcomp using 1
    ext c p i
    rfl
  let A : Set (∀ p : S, Fin n → chapter14BaseCompletion F p.1) :=
    ⋂ p, {b | b p ∈ U p}
  have hA : IsOpen A := by
    apply isOpen_iInter_of_finite
    intro p
    exact (continuous_apply p).isOpen_preimage _ (hU p)
  have haA : a ∈ A := by
    rw [Set.mem_iInter]
    intro p
    exact ha p
  obtain ⟨b, ⟨c, rfl⟩, hb⟩ :=
    (show Dense (Set.range (chapter14CoefficientDiagonal S n)) from hcoeff).exists_mem_open
      hA ⟨a, haA⟩
  rw [Set.mem_iInter] at hb
  exact ⟨c, hb⟩

theorem chapter14_coefficient_polynomial_is_monic
    {R : Type*} [Semiring R] [Nontrivial R] (n : ℕ) (c : Fin n → R) :
    (chapter14CoefficientPolynomial n c).Monic := by
  unfold chapter14CoefficientPolynomial
  exact Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt c)

theorem chapter14_coefficient_polynomial_natDegree
    {R : Type*} [Semiring R] [Nontrivial R] (n : ℕ) (c : Fin n → R) :
    (chapter14CoefficientPolynomial n c).natDegree = n := by
  unfold chapter14CoefficientPolynomial
  rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by
    rw [Polynomial.degree_X_pow]
    exact Polynomial.degree_sum_fin_lt c)]
  exact Polynomial.natDegree_X_pow n

structure Chapter14SimultaneousPolynomialNeighborhood
    {F : Type u} [Field F] [NumberField F]
    (S : Finset (Chapter14Prime F)) (n : ℕ) where
  local_polynomial : ∀ p : S, (chapter14BaseCompletion F p.1)[X]
  monic : ∀ p, (local_polynomial p).Monic
  degree : ∀ p, (local_polynomial p).natDegree = n
  neighborhood : ∀ p : S, Set (Fin n → chapter14BaseCompletion F p.1)
  open_neighborhood : ∀ p, IsOpen (neighborhood p)
  contains : ∀ p,
    (fun i : Fin n => (local_polynomial p).coeff i) ∈ neighborhood p

theorem chapter14_simultaneous_monic_polynomial_approximation
    {F : Type u} [Field F] [NumberField F]
    (S : Finset (Chapter14Prime F)) (n : ℕ)
    (N : Chapter14SimultaneousPolynomialNeighborhood S n) :
    ∃ g : F[X], g.Monic ∧ g.natDegree = n ∧
      ∀ p,
        (fun i : Fin n => (chapter14PolynomialMapAt p.1 g).coeff i) ∈ N.neighborhood p := by
  let a : ∀ p : S, Fin n → chapter14BaseCompletion F p.1 :=
    fun p i => (N.local_polynomial p).coeff i
  obtain ⟨c, hc⟩ :=
    chapter14_coefficient_weak_approximation S n a N.neighborhood
      N.open_neighborhood N.contains
  refine ⟨chapter14CoefficientPolynomial n c,
    chapter14_coefficient_polynomial_is_monic n c,
    chapter14_coefficient_polynomial_natDegree n c, ?_⟩
  intro p
  have hp := hc p
  convert hp using 1
  funext i
  simp [chapter14CoefficientDiagonal, chapter14PolynomialMapAt,
    chapter14CoefficientPolynomial, Polynomial.coeff_map]
  have h_eq (x : Fin n) : ((i : ℕ) = (x : ℕ)) ↔ (i = x) := Fin.ext_iff.symm
  simp_rw [h_eq]
  rw [if_neg (Nat.ne_of_lt i.isLt)]
  rw [← map_sum]
  simp [chapter14FinitePlaceEmbedding]

/- Coefficient congruences are the nonarchimedean neighborhood basis used by
   the proof after denominators have been cleared. -/
def chapter14CoefficientCongruent
    {A : Type*} [CommRing A] (n : ℕ) (m : Ideal A) (N : ℕ)
    (c d : Fin n → A) : Prop :=
  ∀ i, c i - d i ∈ m ^ N

theorem chapter14_coefficient_congruent_comm
    {A : Type*} [CommRing A] (n : ℕ) (m : Ideal A) (N : ℕ)
    (c d : Fin n → A) :
    chapter14CoefficientCongruent n m N c d ↔
      chapter14CoefficientCongruent n m N d c := by
  unfold chapter14CoefficientCongruent
  constructor
  · intro h i
    simpa [sub_eq_add_neg, add_comm] using (m ^ N).neg_mem (h i)
  · intro h i
    simpa [sub_eq_add_neg, add_comm] using (m ^ N).neg_mem (h i)

theorem chapter14_coefficient_congruence_is_open
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (n : ℕ) (m : Ideal A) (N : ℕ)
    (hmN : IsOpen ((m ^ N : Ideal A) : Set A)) (c : Fin n → A) :
    IsOpen {d : Fin n → A | chapter14CoefficientCongruent n m N c d} := by
  rw [show {d : Fin n → A | chapter14CoefficientCongruent n m N c d} =
      ⋂ i : Fin n, {d : Fin n → A | c i - d i ∈ (m ^ N : Ideal A)} by
    ext d
    simp [chapter14CoefficientCongruent]]
  apply isOpen_iInter_of_finite
  intro i
  have hcont : Continuous (fun d : Fin n → A => c i - d i) :=
    continuous_const.sub (continuous_apply i)
  apply Continuous.isOpen_preimage hcont ((m ^ N : Ideal A) : Set A)
  exact hmN

def chapter14DenominatorCleared
    {F : Type u} [Field F] [NumberField F]
    (s : 𝓞 F) (x : F) (y : 𝓞 F) : Prop :=
  algebraMap (𝓞 F) F y = algebraMap (𝓞 F) F s * x

theorem chapter14_coefficients_can_be_denominator_cleared
    {F : Type u} [Field F] [NumberField F]
    (n : ℕ) (c : Fin n → F) :
    ∃ s : 𝓞 F, s ≠ 0 ∧
      ∀ i, ∃ y : 𝓞 F, chapter14DenominatorCleared s (c i) y := by
  choose a b hb hcb using
    fun i : Fin n => IsFractionRing.div_surjective (𝓞 F) (c i)
  let s : 𝓞 F := ∏ i : Fin n, b i
  have hs : s ≠ 0 := by
    dsimp [s]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact nonZeroDivisors.ne_zero (hb i)
  refine ⟨s, hs, ?_⟩
  intro i
  refine ⟨a i * Finset.prod (Finset.univ.erase i) b, ?_⟩
  unfold chapter14DenominatorCleared
  rw [← hcb i]
  have hbi : algebraMap (𝓞 F) F (b i) ≠ 0 := by
    simp [nonZeroDivisors.ne_zero (hb i)]
  have hprod0 :
      Finset.prod (Finset.univ.erase i) b * b i =
        Finset.prod (Finset.univ : Finset (Fin n)) b :=
    Finset.prod_erase_mul (Finset.univ : Finset (Fin n)) b (Finset.mem_univ i)
  have hprod := congrArg (algebraMap (𝓞 F) F) hprod0
  dsimp [s] at ⊢
  simp only [map_mul, map_prod] at hprod ⊢
  field_simp [hbi]
  calc
    _ = algebraMap (𝓞 F) F (a i) *
        ((Finset.prod (Finset.univ.erase i)
          (fun x => algebraMap (𝓞 F) F (b x))) *
          algebraMap (𝓞 F) F (b i)) := by ring
    _ = algebraMap (𝓞 F) F (a i) *
        Finset.prod (Finset.univ : Finset (Fin n))
          (fun x => algebraMap (𝓞 F) F (b x)) := by rw [hprod]

theorem chapter14_simultaneous_prime_power_congruence
    {F : Type u} [Field F] [NumberField F]
    (S : Finset (Chapter14Prime F)) (n : ℕ)
    (N : ∀ p : S, ℕ) (a : ∀ p : S, Fin n → 𝓞 F) :
    ∃ c : Fin n → 𝓞 F, ∀ p : S,
      chapter14CoefficientCongruent n p.1.asIdeal (N p) c (a p) := by
  sorry

theorem chapter14_monic_polynomial_approximation_over_a_dense_field
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (hdense : DenseRange (algebraMap K L)) {f : L[X]} (hf : f.Monic)
    {ε : ℝ} (hε : ε > 0) :
    ∃ g : K[X], g.Monic ∧ f.natDegree = g.natDegree ∧
      ∀ n : ℕ, ‖(g.map (algebraMap K L)).coeff n - f.coeff n‖ < ε := by
  exact Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
    hdense hf hε

/- DEPENDENCY_GUESS: The source's Proposition 12.2/Corollary 12.3 are not
   exposed under those names in the preceding chapter.  The following record
   is the exact open-neighborhood interface needed here. -/
theorem chapter14_separable_polynomial_has_krasner_neighborhood
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [NormedField L]
    [NormedAlgebra K L] [Algebra.IsAlgebraic K L] [IsKrasner K L]
    (g : K[X]) (α : L) (hgmonic : g.Monic) (hroot : aeval α g = 0)
    (hseparable : g.Separable) :
    Nonempty (Chapter14KrasnerNeighborhoodData K L g α) := by
  sorry

def chapter14PolynomialProductDecomposition
    {K : Type*} [Field K] (n : ℕ) (g : K[X]) (factor : Fin n → K[X]) : Prop :=
  Nonempty (AdjoinRoot g ≃+* (∀ i, AdjoinRoot (factor i)))

theorem chapter14_distinct_factor_hensel_stability
    {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K]
    (n : ℕ) (H : Chapter14HenselProductData K n) :
    ∃ U : Set (Fin H.local_polynomial.natDegree → K), IsOpen U ∧
      (fun i : Fin H.local_polynomial.natDegree => H.local_polynomial.coeff i) ∈ U ∧
      ∀ g, g.Monic → g.natDegree = H.local_polynomial.natDegree →
        (fun i : Fin H.local_polynomial.natDegree => g.coeff i) ∈ U →
        ∃ G : Chapter14HenselProductData K n,
        G.local_polynomial = g ∧
          chapter14PolynomialProductDecomposition n g G.factors := by
  sorry

def chapter14EisensteinNeighborhood
    {A : Type*} [CommRing A] (m : Ideal A) (n : ℕ) : Set (Fin n → A) :=
  {c | (chapter14CoefficientPolynomial n c).IsEisensteinAt m}

theorem chapter14_eisenstein_condition_is_open
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (m : Ideal A) (n : ℕ)
    (hm : IsOpen (m : Set A))
    (hm2 : IsOpen ((m ^ 2 : Ideal A) : Set A))
    (hm2_closed : IsClosed ((m ^ 2 : Ideal A) : Set A)) :
    IsOpen (chapter14EisensteinNeighborhood m n) := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14
