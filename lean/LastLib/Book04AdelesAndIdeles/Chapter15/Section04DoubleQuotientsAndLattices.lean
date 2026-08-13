import LastLib.Book04AdelesAndIdeles.Chapter15.Section02DiagonalPointsAndDeterminants

namespace LastLib.Book04AdelesAndIdeles.Chapter15

noncomputable section

open Set Filter NumberField
open scoped RestrictedProduct

/-! ## 15.4. Double quotients and local data -/

/-! ### The global quotient and its level embedding -/

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- Embed a finite adelic matrix into the full adelic matrix group by putting `1` at infinity. -/
def chapter15FiniteMatrixInclusion (n : ℕ) :
    Chapter15FiniteMatrixGroup n R K →* Chapter15GLnAdeles n R K where
  toFun g := (fun _ => 1, g)
  map_one' := by sorry
  map_mul' g h := by sorry

theorem chapter15_global_level_subgroup_eq_finite_matrix_inclusion_range
    (n : ℕ) (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K)) :
    chapter15GlobalLevelSubgroup n Kf =
      (chapter15FiniteMatrixInclusion (R := R) (K := K) n).range := by
  sorry

/-- The basic automorphic parameter space at finite level. -/
def chapter15MatrixAutomorphicDoubleQuotient (n : ℕ)
    (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K)) :=
  Chapter15DoubleQuotient
    (chapter15PrincipalMatrix (R := R) (K := K) n).range
    (chapter15GlobalLevelSubgroup n Kf)

instance chapter15MatrixAutomorphicDoubleQuotient_topologicalSpace
    (n : ℕ) (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K)) :
    TopologicalSpace
      (chapter15MatrixAutomorphicDoubleQuotient (R := R) (K := K) n Kf) := by
  change TopologicalSpace
    (Quotient
      (chapter15DoubleCosetSetoid
        (chapter15PrincipalMatrix (R := R) (K := K) n).range
        (chapter15GlobalLevelSubgroup n Kf)))
  infer_instance

theorem chapter15MatrixAutomorphicDoubleQuotient_mk_eq_iff
    (n : ℕ) (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K))
    (x y : Chapter15GLnAdeles n R K) :
    chapter15DoubleQuotientMk
        (chapter15PrincipalMatrix (R := R) (K := K) n).range
        (chapter15GlobalLevelSubgroup n Kf) x =
      chapter15DoubleQuotientMk
        (chapter15PrincipalMatrix (R := R) (K := K) n).range
        (chapter15GlobalLevelSubgroup n Kf) y ↔
      ∃ γ : Matrix.GeneralLinearGroup (Fin n) K,
        ∃ k ∈ chapter15GlobalLevelSubgroup n Kf,
          chapter15PrincipalMatrix n γ * x * k = y := by
  sorry

/-- Enlarging the level induces the expected map of double quotients. -/
def chapter15DoubleQuotientMapOfLevelRefinement
    (n : ℕ) {K₁ K₂ : Subgroup (Chapter15FiniteMatrixGroup n R K)}
    (hK : K₁ ≤ K₂) :
    chapter15MatrixAutomorphicDoubleQuotient (R := R) (K := K) n K₁ →
      chapter15MatrixAutomorphicDoubleQuotient (R := R) (K := K) n K₂ :=
  Quotient.lift
    (fun g => chapter15DoubleQuotientMk
      (chapter15PrincipalMatrix (R := R) (K := K) n).range
      (chapter15GlobalLevelSubgroup n K₂) g)
    (by
      intro x y hxy
      change chapter15DoubleCosetRel
        (chapter15PrincipalMatrix (R := R) (K := K) n).range
        (chapter15GlobalLevelSubgroup n K₁) x y at hxy
      rcases hxy with ⟨γ, hγ, k, hk, heq⟩
      apply (chapter15DoubleQuotient_mk_eq_iff
        (chapter15PrincipalMatrix (R := R) (K := K) n).range
        (chapter15GlobalLevelSubgroup n K₂) x y).2
      refine ⟨γ, hγ, k, ?_, heq⟩
      apply (chapter15_global_level_subgroup_mem_iff n K₂ k).2
      rcases (chapter15_global_level_subgroup_mem_iff n K₁ k).1 hk with ⟨h∞, hk₁⟩
      exact ⟨h∞, hK hk₁⟩)

theorem chapter15DoubleQuotientMapOfLevelRefinement_mk
    (n : ℕ) {K₁ K₂ : Subgroup (Chapter15FiniteMatrixGroup n R K)}
    (hK : K₁ ≤ K₂) (g : Chapter15GLnAdeles n R K) :
    chapter15DoubleQuotientMapOfLevelRefinement n hK
        (chapter15DoubleQuotientMk
          (chapter15PrincipalMatrix (R := R) (K := K) n).range
          (chapter15GlobalLevelSubgroup n K₁) g) =
      chapter15DoubleQuotientMk
        (chapter15PrincipalMatrix (R := R) (K := K) n).range
        (chapter15GlobalLevelSubgroup n K₂) g := by
  rfl

/-! ### The lattice attached to a finite adelic matrix -/

def chapter15LocalizeVector (n : ℕ) (v : Chapter15FinitePlace R)
    (x : Chapter15VectorSpace n K) : Fin n → v.adicCompletion K :=
  fun i => algebraMap K (v.adicCompletion K) (x i)

def chapter15LocalIntegralVectorSet (n : ℕ) (v : Chapter15FinitePlace R) :
    Set (Fin n → v.adicCompletion K) :=
  {y | ∀ i, y i ∈ v.adicCompletionIntegers K}

/-- The local orbit `g_v 𝓞_v^n`. -/
def chapter15LocalMatrixIntegralOrbit (n : ℕ) (g : Chapter15FiniteMatrixGroup n R K)
    (v : Chapter15FinitePlace R) : Set (Fin n → v.adicCompletion K) :=
  {y | ∃ z ∈ chapter15LocalIntegralVectorSet n v,
    Matrix.mulVec (g v : Matrix (Fin n) (Fin n) (v.adicCompletion K)) z = y}

/-- The local definition of `Λ(g_f)`. -/
def chapter15FiniteMatrixLatticeCarrier (n : ℕ) (g : Chapter15FiniteMatrixGroup n R K) :
    Set (Chapter15VectorSpace n K) :=
  {x | ∀ v : Chapter15FinitePlace R,
    ∀ i : Fin n,
      (Matrix.mulVec ((g v)⁻¹) (chapter15LocalizeVector n v x)) i ∈
        v.adicCompletionIntegers K}

/-- `Λ(g_f)` as an `R`-submodule of `K^n`. -/
def chapter15FiniteMatrixLattice (n : ℕ) (g : Chapter15FiniteMatrixGroup n R K) :
    Submodule R (Chapter15VectorSpace n K) where
  carrier := chapter15FiniteMatrixLatticeCarrier n g
  zero_mem' := by
    sorry
  add_mem' := by
    intro x y hx hy
    sorry
  smul_mem' := by
    intro r x hx
    sorry

theorem chapter15FiniteMatrixLattice_mem_iff
    (n : ℕ) (g : Chapter15FiniteMatrixGroup n R K)
    (x : Chapter15VectorSpace n K) :
    x ∈ chapter15FiniteMatrixLattice n g ↔
      ∀ v : Chapter15FinitePlace R, ∀ i : Fin n,
        (Matrix.mulVec
          ((g v)⁻¹ : Matrix (Fin n) (Fin n) (v.adicCompletion K))
          (chapter15LocalizeVector n v x)) i ∈
        v.adicCompletionIntegers K :=
  Iff.rfl

/-- The exact local comparison box `𝔭_v^c 𝓞_v^n`, allowing integer exponents. -/
def chapter15LocalValuationBox (n : ℕ) (v : Chapter15FinitePlace R) (c : ℤ) :
    Set (Fin n → v.adicCompletion K) :=
  {y | ∀ i, Valued.v (y i) ≤ WithZero.exp (-c : ℤ)}

theorem chapter15_finite_matrix_lattice_local_comparison
    (n : ℕ) (g : Chapter15FiniteMatrixGroup n R K) :
    ∃ S : Finset (Chapter15FinitePlace R),
      (∀ v ∉ S,
        g v ∈ chapter15FiniteMatrixIntegralSubgroup n v ∧
          (g⁻¹) v ∈ chapter15FiniteMatrixIntegralSubgroup n v) ∧
      (∀ v ∈ S, ∃ c : ℕ,
        chapter15LocalValuationBox n v (c : ℤ) ⊆
            chapter15LocalMatrixIntegralOrbit n g v ∧
          chapter15LocalMatrixIntegralOrbit n g v ⊆
            chapter15LocalValuationBox n v (-(c : ℤ))) := by
  sorry

/-! ### Global fractional bounds and finiteness -/

/-- Coordinatewise `I^n` inside `K^n`. -/
def chapter15VectorFractionalIdealPower
    (n : ℕ) (I : Chapter15FractionalIdeal R K) :
    Submodule R (Chapter15VectorSpace n K) where
  carrier := {x | ∀ i, x i ∈ (I : Submodule R K)}
  zero_mem' := by
    intro i
    exact (I : Submodule R K).zero_mem
  add_mem' := by
    intro x y hx hy i
    exact (I : Submodule R K).add_mem (hx i) (hy i)
  smul_mem' := by
    intro r x hx i
    exact (I : Submodule R K).smul_mem r (hx i)

omit [IsDedekindDomain R] [IsFractionRing R K] in
theorem chapter15VectorFractionalIdealPower_mem_iff
    (n : ℕ) (I : Chapter15FractionalIdeal R K)
    (x : Chapter15VectorSpace n K) :
    x ∈ chapter15VectorFractionalIdealPower n I ↔
      ∀ i, x i ∈ (I : Submodule R K) :=
  Iff.rfl

structure Chapter15LatticeComparisonBounds
    (n : ℕ) (g : Chapter15FiniteMatrixGroup n R K) where
  lowerIdeal : Chapter15FractionalIdeal R K
  upperIdeal : Chapter15FractionalIdeal R K
  lower_nonzero : lowerIdeal ≠ 0
  lower_le_upper : lowerIdeal ≤ upperIdeal
  lower_bound : chapter15VectorFractionalIdealPower n lowerIdeal ≤
    chapter15FiniteMatrixLattice n g
  upper_bound : chapter15FiniteMatrixLattice n g ≤
    chapter15VectorFractionalIdealPower n upperIdeal

theorem chapter15_finite_matrix_lattice_has_global_fractional_bounds
    (n : ℕ) (g : Chapter15FiniteMatrixGroup n R K) :
    Nonempty (Chapter15LatticeComparisonBounds (R := R) (K := K) n g) := by
  sorry

/-- The finite quotient between two coordinatewise fractional bounds. -/
abbrev Chapter15VectorFractionalIdealQuotient
    (n : ℕ) (I J : Chapter15FractionalIdeal R K) :=
  (chapter15VectorFractionalIdealPower n J) ⧸
    (chapter15VectorFractionalIdealPower n I).comap
      (chapter15VectorFractionalIdealPower n J).subtype

theorem chapter15_vector_fractional_ideal_quotient_finite
    (n : ℕ) {L : Type*} [Field L] [NumberField L]
    (I J : Chapter15FractionalIdeal (𝓞 L) L) (hIJ : I ≤ J) :
    Finite (Chapter15VectorFractionalIdealQuotient n I J) := by
  sorry

theorem chapter15_submodule_between_fractional_bounds_is_finite
    (n : ℕ) (I J : Chapter15FractionalIdeal R K)
    (L : Submodule R (Chapter15VectorSpace n K))
    (hIJ : I ≤ J)
    (hI : chapter15VectorFractionalIdealPower n I ≤ L)
    (hJ : L ≤ chapter15VectorFractionalIdealPower n J) :
    Module.Finite R L := by sorry

theorem chapter15_vector_fractional_ideal_power_spans
    (n : ℕ) (I : Chapter15FractionalIdeal R K) (hI : I ≠ 0) :
    Submodule.span K
        (chapter15VectorFractionalIdealPower n I :
          Set (Chapter15VectorSpace n K)) = ⊤ := by
  sorry

/-- The lattice construction is finite over `𝓞_K` and spans `K^n`. -/
structure Chapter15FullLattice
    (n : ℕ) (L : Submodule R (Chapter15VectorSpace n K)) : Prop where
  finite : Module.Finite R L
  spans : Submodule.span K (L : Set (Chapter15VectorSpace n K)) = ⊤

theorem chapter15_finite_matrix_lattice_is_full
    (n : ℕ) (g : Chapter15FiniteMatrixGroup n R K) :
    Chapter15FullLattice n (chapter15FiniteMatrixLattice n g) := by
  sorry

/-! ### Change of representatives and the rank-one lattice -/

theorem chapter15_finite_matrix_lattice_right_standard_invariant
    (n : ℕ) (g : Chapter15FiniteMatrixGroup n R K)
    (k : Chapter15FiniteMatrixGroup n R K)
    (hk : k ∈ chapter15StandardFiniteMatrixLevel n) :
    chapter15FiniteMatrixLattice (n := n) (g * k) =
      chapter15FiniteMatrixLattice (n := n) g := by
  sorry

theorem chapter15_finite_matrix_lattice_left_rational_change
    (n : ℕ) (γ : Matrix.GeneralLinearGroup (Fin n) K)
    (g : Chapter15FiniteMatrixGroup n R K)
    (x : Chapter15VectorSpace n K) :
    x ∈ chapter15FiniteMatrixLattice n
        ((chapter15FinitePrincipalMatrix (R := R) (K := K) n γ) * g) ↔
      ∃ y ∈ chapter15FiniteMatrixLattice n g,
        Matrix.mulVec (γ : Matrix (Fin n) (Fin n) K) y = x := by
  sorry

/-- The rank-one local lattice condition, prior to identifying it with a fractional ideal. -/
def chapter15FiniteIdeleLatticeCarrier (g : Chapter15FiniteIdeleGroup R K) : Set K :=
  {x | ∀ v : Chapter15FinitePlace R,
    ((g v : (v.adicCompletion K)ˣ) : v.adicCompletion K)⁻¹ *
        algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K}

def chapter15FiniteIdeleLattice (g : Chapter15FiniteIdeleGroup R K) :
    Submodule R K where
  carrier := chapter15FiniteIdeleLatticeCarrier g
  zero_mem' := by
    sorry
  add_mem' := by
    intro x y hx hy
    sorry
  smul_mem' := by
    intro r x hx
    sorry

theorem chapter15FiniteIdeleLattice_mem_iff
    (g : Chapter15FiniteIdeleGroup R K) (x : K) :
    x ∈ chapter15FiniteIdeleLattice g ↔
      ∀ v : Chapter15FinitePlace R,
        ((g v : (v.adicCompletion K)ˣ) : v.adicCompletion K)⁻¹ *
            algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K :=
  Iff.rfl

/- The textbook's order inequality
`ord_v(x) ≥ ord_v(g_v)` is represented canonically by the valuation of the
normalized local quotient being at most one. -/
def chapter15FiniteIdeleLatticeValuationCondition
    (g : Chapter15FiniteIdeleGroup R K) (x : K) : Prop :=
  ∀ v : Chapter15FinitePlace R,
    Valued.v
        (((g v : (v.adicCompletion K)ˣ) : v.adicCompletion K)⁻¹ *
          algebraMap K (v.adicCompletion K) x) ≤ 1

theorem chapter15FiniteIdeleLattice_mem_iff_valuation
    (g : Chapter15FiniteIdeleGroup R K) (x : K) :
    x ∈ chapter15FiniteIdeleLattice g ↔
      chapter15FiniteIdeleLatticeValuationCondition g x := by
  sorry

theorem chapter15_rank_one_idele_lattice_is_fractional_ideal
    (g : Chapter15FiniteIdeleGroup R K) :
    ∃ I : Chapter15FractionalIdeal R K, I ≠ 0 ∧
      (I : Submodule R K) = chapter15FiniteIdeleLattice g := by
  sorry

def chapter15FiniteIdeleClassDoubleQuotient :=
  Chapter15DoubleQuotient
    (chapter15FinitePrincipalIdele (R := R) (K := K)).range
    chapter15StandardFiniteIdeleLevel

/- LOCAL_DEPENDENCY_GUESS: the following is the canonical ideal-class
identification used in the preceding ideles chapter; Mathlib supplies
`ClassGroup R`, but not this idele double-coset presentation. -/
def chapter15_finite_idele_double_quotient_is_class_group :
    chapter15FiniteIdeleClassDoubleQuotient (R := R) (K := K) ≃
      ClassGroup R := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter15
