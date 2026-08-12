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
  sorry

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
  sorry

theorem chapter14_coefficient_polynomial_is_monic
    {R : Type*} [Semiring R] [Nontrivial R] (n : ℕ) (c : Fin n → R) :
    (chapter14CoefficientPolynomial n c).Monic := by
  sorry

theorem chapter14_coefficient_polynomial_natDegree
    {R : Type*} [Semiring R] [Nontrivial R] (n : ℕ) (c : Fin n → R) :
    (chapter14CoefficientPolynomial n c).natDegree = n := by
  sorry

structure Chapter14SimultaneousPolynomialNeighborhood
    {F : Type u} [Field F] [NumberField F]
    (S : Finset (Chapter14Prime F)) (n : ℕ)
    [∀ p : S, TopologicalSpace ((chapter14BaseCompletion F p.1)[X])] where
  local_polynomial : ∀ p : S, (chapter14BaseCompletion F p.1)[X]
  monic : ∀ p, (local_polynomial p).Monic
  degree : ∀ p, (local_polynomial p).natDegree = n
  neighborhood : ∀ p : S, Set ((chapter14BaseCompletion F p.1)[X])
  open_neighborhood : ∀ p, IsOpen (neighborhood p)
  contains : ∀ p, local_polynomial p ∈ neighborhood p

theorem chapter14_simultaneous_monic_polynomial_approximation
    {F : Type u} [Field F] [NumberField F]
    (S : Finset (Chapter14Prime F)) (n : ℕ)
    [∀ p : S, TopologicalSpace ((chapter14BaseCompletion F p.1)[X])]
    (N : Chapter14SimultaneousPolynomialNeighborhood S n) :
    ∃ g : F[X], g.Monic ∧ g.natDegree = n ∧
      ∀ p, chapter14PolynomialMapAt p.1 g ∈ N.neighborhood p := by
  sorry

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
  sorry

theorem chapter14_coefficient_congruence_is_open
    {A : Type*} [CommRing A] [TopologicalSpace A]
    (n : ℕ) (m : Ideal A) (N : ℕ)
    (hmN : IsOpen ((m ^ N : Ideal A) : Set A)) (c : Fin n → A) :
    IsOpen {d : Fin n → A | chapter14CoefficientCongruent n m N c d} := by
  sorry

def chapter14DenominatorCleared
    {F : Type u} [Field F] [NumberField F]
    (s : 𝓞 F) (x : F) (y : 𝓞 F) : Prop :=
  algebraMap (𝓞 F) F y = algebraMap (𝓞 F) F s * x

theorem chapter14_coefficients_can_be_denominator_cleared
    {F : Type u} [Field F] [NumberField F]
    (n : ℕ) (c : Fin n → F) :
    ∃ s : 𝓞 F, s ≠ 0 ∧
      ∀ i, ∃ y : 𝓞 F, chapter14DenominatorCleared s (c i) y := by
  sorry

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
    [TopologicalSpace K[X]]
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
    [IsUltrametricDist K] [TopologicalSpace K[X]]
    (n : ℕ) (H : Chapter14HenselProductData K n) :
    ∃ U : Set K[X], IsOpen U ∧ H.local_polynomial ∈ U ∧
      ∀ g ∈ U, ∃ G : Chapter14HenselProductData K n,
        G.local_polynomial = g ∧
          chapter14PolynomialProductDecomposition n g G.factors := by
  sorry

def chapter14EisensteinNeighborhood
    {A : Type*} [CommRing A] (m : Ideal A) (n : ℕ) : Set A[X] :=
  {g | g.IsEisensteinAt m ∧ g.natDegree = n}

theorem chapter14_eisenstein_condition_is_open
    {A : Type*} [CommRing A] [TopologicalSpace A] [TopologicalSpace A[X]]
    (m : Ideal A) (n : ℕ)
    (hm : IsOpen (m : Set A))
    (hm2 : IsOpen ((m ^ 2 : Ideal A) : Set A)) :
    IsOpen (chapter14EisensteinNeighborhood m n) := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14
