import LastLib.Book04AdelesAndIdeles.Chapter15.Section02DiagonalPointsAndDeterminants
import LastLib.Book04AdelesAndIdeles.Chapter08.Section81
import LastLib.Book04AdelesAndIdeles.Chapter08.Section84

namespace LastLib.Book04AdelesAndIdeles.Chapter15

noncomputable section

open Set Filter NumberField
open scoped RestrictedProduct WithZero

/-! ## 15.4. Double quotients and local data -/

/-! ### The global quotient and its level embedding -/

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- Embed a finite adelic matrix into the full adelic matrix group by putting `1` at infinity. -/
def chapter15FiniteMatrixInclusion (n : ℕ) :
    Chapter15FiniteMatrixGroup n R K →* Chapter15GLnAdeles n R K where
  toFun g := (fun _ => 1, g)
  map_one' := by
    rfl
  map_mul' g h := by
    apply Prod.ext
    · funext v
      simp
    · rfl

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
  rw [chapter15DoubleQuotient_mk_eq_iff]
  change (∃ h ∈ (chapter15PrincipalMatrix (R := R) (K := K) n).range,
      ∃ k ∈ chapter15GlobalLevelSubgroup n Kf,
        h * x * k = y) ↔ _
  constructor
  · rintro ⟨h, ⟨γ, rfl⟩, k, hk, heq⟩
    exact ⟨γ, k, hk, heq⟩
  · rintro ⟨γ, k, hk, heq⟩
    exact ⟨chapter15PrincipalMatrix n γ, ⟨γ, rfl⟩, k, hk, heq⟩

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
      rcases hxy with ⟨h, hh, k, hk, heq⟩
      have hk₂ : k ∈ chapter15GlobalLevelSubgroup n K₂ := by
        change k.1 = 1 ∧ k.2 ∈ K₂
        change k.1 = 1 ∧ k.2 ∈ K₁ at hk
        exact ⟨hk.1, hK hk.2⟩
      exact chapter15DoubleQuotient_mk_eq_of_left_right
        (chapter15PrincipalMatrix (R := R) (K := K) n).range
        (chapter15GlobalLevelSubgroup n K₂) h hh k hk₂ heq)

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
    intro v i
    rw [show chapter15LocalizeVector n v 0 = 0 by
      ext; simp [chapter15LocalizeVector]]
    simp
  add_mem' := by
    intro x y hx hy v i
    have hloc : chapter15LocalizeVector n v (x + y) =
        chapter15LocalizeVector n v x + chapter15LocalizeVector n v y := by
      ext j
      simp [chapter15LocalizeVector]
    rw [hloc, Matrix.mulVec_add]
    exact (v.adicCompletionIntegers K).add_mem _ _ (hx v i) (hy v i)
  smul_mem' := by
    intro r x hx v i
    have hloc : chapter15LocalizeVector n v (r • x) =
        (algebraMap R (v.adicCompletion K) r) •
          chapter15LocalizeVector n v x := by
      funext j
      simp only [chapter15LocalizeVector, Pi.smul_apply, Algebra.smul_def,
        map_mul]
      exact congrArg
        (fun z => z * algebraMap K (v.adicCompletion K) (x j))
        (IsScalarTower.algebraMap_apply R K (v.adicCompletion K) r).symm
    rw [hloc, Matrix.mulVec_smul]
    change (algebraMap R (v.adicCompletion K) r) *
        (Matrix.mulVec ((g v)⁻¹) (chapter15LocalizeVector n v x)) i ∈
      v.adicCompletionIntegers K
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    exact ValuationSubring.mul_mem (v.adicCompletionIntegers K) _ _
      (IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem _ _ v r)
      (hx v i)

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
  classical
  have hbox (v : Chapter15FinitePlace R) :
      ∃ c : ℕ,
        chapter15LocalValuationBox n v (c : ℤ) ⊆
            chapter15LocalMatrixIntegralOrbit n g v ∧
          chapter15LocalMatrixIntegralOrbit n g v ⊆
            chapter15LocalValuationBox n v (-(c : ℤ)) := by
    let exponent (z : v.adicCompletion K) : ℤ :=
      if hz : (Valued.v z : ℤᵐ⁰) = 0 then
        0
      else
        (WithZero.unzero hz).toAdd
    have hexponent (z : v.adicCompletion K) :
        Valued.v z ≤ WithZero.exp (exponent z) := by
      by_cases hz : (Valued.v z : ℤᵐ⁰) = 0
      · simp [exponent, hz]
      · simp only [exponent, dif_neg hz]
        simpa only [WithZero.toAdd_unzero_eq_log] using
          (WithZero.exp_log hz).symm.le
    have hnatAbs (a : ℤ) : a ≤ (Int.natAbs a : ℤ) := by
      cases a with
      | ofNat a => simp
      | negSucc a => omega
    let c : ℕ :=
      ∑ i : Fin n, ∑ j : Fin n,
        (Int.natAbs (exponent ((g v) i j)) +
          Int.natAbs (exponent ((g⁻¹) v i j)))
    have hnat_g (i j : Fin n) :
        Int.natAbs (exponent ((g v) i j)) ≤ c := by
      dsimp [c]
      calc
        Int.natAbs (exponent ((g v) i j)) ≤
            Int.natAbs (exponent ((g v) i j)) +
              Int.natAbs (exponent ((g⁻¹) v i j)) := Nat.le_add_right _ _
        _ ≤ ∑ k : Fin n,
            (Int.natAbs (exponent ((g v) i k)) +
              Int.natAbs (exponent ((g⁻¹) v i k))) := by
          exact Finset.single_le_sum
            (f := fun k : Fin n =>
              Int.natAbs (exponent ((g v) i k)) +
                Int.natAbs (exponent ((g⁻¹) v i k)))
            (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
        _ ≤ ∑ k : Fin n, ∑ l : Fin n,
            (Int.natAbs (exponent ((g v) k l)) +
              Int.natAbs (exponent ((g⁻¹) v k l))) := by
          exact Finset.single_le_sum
            (f := fun k : Fin n => ∑ l : Fin n,
              (Int.natAbs (exponent ((g v) k l)) +
                Int.natAbs (exponent ((g⁻¹) v k l))))
            (fun k _ => Nat.zero_le _) (Finset.mem_univ i)
    have hnat_inv (i j : Fin n) :
        Int.natAbs (exponent ((g⁻¹) v i j)) ≤ c := by
      dsimp [c]
      calc
        Int.natAbs (exponent ((g⁻¹) v i j)) ≤
            Int.natAbs (exponent ((g v) i j)) +
              Int.natAbs (exponent ((g⁻¹) v i j)) := Nat.le_add_left _ _
        _ ≤ ∑ k : Fin n,
            (Int.natAbs (exponent ((g v) i k)) +
              Int.natAbs (exponent ((g⁻¹) v i k))) := by
          exact Finset.single_le_sum
            (f := fun k : Fin n =>
              Int.natAbs (exponent ((g v) i k)) +
                Int.natAbs (exponent ((g⁻¹) v i k)))
            (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
        _ ≤ ∑ k : Fin n, ∑ l : Fin n,
            (Int.natAbs (exponent ((g v) k l)) +
              Int.natAbs (exponent ((g⁻¹) v k l))) := by
          exact Finset.single_le_sum
            (f := fun k : Fin n => ∑ l : Fin n,
              (Int.natAbs (exponent ((g v) k l)) +
                Int.natAbs (exponent ((g⁻¹) v k l))))
            (fun k _ => Nat.zero_le _) (Finset.mem_univ i)
    have hexp_le_g (i j : Fin n) :
        exponent ((g v) i j) ≤ (c : ℤ) := by
      have hnat := hnat_g i j
      have hcast :
          (Int.natAbs (exponent ((g v) i j)) : ℤ) ≤ (c : ℤ) := by
        exact_mod_cast hnat
      exact (hnatAbs _).trans hcast
    have hexp_le_inv (i j : Fin n) :
        exponent ((g⁻¹) v i j) ≤ (c : ℤ) := by
      have hnat := hnat_inv i j
      have hcast :
          (Int.natAbs (exponent ((g⁻¹) v i j)) : ℤ) ≤ (c : ℤ) := by
        exact_mod_cast hnat
      exact (hnatAbs _).trans hcast
    have hentry_g (i j : Fin n) :
        Valued.v ((g v) i j) ≤ WithZero.exp (c : ℤ) := by
      exact (hexponent _).trans (by
        rw [WithZero.exp_le_exp]
        exact hexp_le_g i j)
    have hentry_inv (i j : Fin n) :
        Valued.v ((g⁻¹) v i j) ≤ WithZero.exp (c : ℤ) := by
      exact (hexponent _).trans (by
        rw [WithZero.exp_le_exp]
        exact hexp_le_inv i j)
    refine ⟨c, ?_, ?_⟩
    · intro y hy
      change ∀ j, Valued.v (y j) ≤ WithZero.exp (-(c : ℤ)) at hy
      refine ⟨Matrix.mulVec
          ((g⁻¹) v : Matrix (Fin n) (Fin n) (v.adicCompletion K)) y, ?_, ?_⟩
      · change ∀ i, Valued.v
          (Matrix.mulVec
            ((g⁻¹) v : Matrix (Fin n) (Fin n) (v.adicCompletion K)) y i) ≤ 1
        intro i
        change Valued.v
            (∑ j : Fin n, ((g⁻¹) v) i j * y j) ≤ 1
        apply (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).map_sum_le
        intro j hj
        rw [Valuation.map_mul]
        calc
          Valued.v (((g⁻¹) v) i j) * Valued.v (y j) ≤
              WithZero.exp (c : ℤ) * WithZero.exp (-(c : ℤ)) :=
            mul_le_mul' (hentry_inv i j) (hy j)
          _ = 1 := by rw [← WithZero.exp_add]; simp
      · rw [Matrix.mulVec_mulVec]
        simp
    · intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      change ∀ i, Valued.v
          (Matrix.mulVec (g v : Matrix (Fin n) (Fin n) (v.adicCompletion K)) z i) ≤
        WithZero.exp (-(-(c : ℤ)))
      simp only [neg_neg]
      change ∀ i, Valued.v
          (∑ j : Fin n, (g v) i j * z j) ≤ WithZero.exp (c : ℤ)
      intro i
      apply (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).map_sum_le
      intro j hj
      have hzj : Valued.v (z j) ≤ 1 := by
        rw [← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
        exact hz j
      rw [Valuation.map_mul]
      exact (mul_le_mul' (hentry_g i j) hzj).trans_eq (by simp)
  have hbad_g : Set.Finite
      {v : Chapter15FinitePlace R |
        ¬ g v ∈ chapter15FiniteMatrixIntegralSubgroup n v} := by
    exact Filter.eventually_cofinite.mp g.2
  have hbad_inv : Set.Finite
      {v : Chapter15FinitePlace R |
        ¬ (g⁻¹) v ∈ chapter15FiniteMatrixIntegralSubgroup n v} := by
    exact Filter.eventually_cofinite.mp (g⁻¹).2
  let S : Finset (Chapter15FinitePlace R) :=
    hbad_g.toFinset ∪ hbad_inv.toFinset
  refine ⟨S, ?_, ?_⟩
  · intro v hv
    constructor
    · by_contra h
      exact hv (by
        change v ∈ hbad_g.toFinset ∪ hbad_inv.toFinset
        exact Finset.mem_union_left _ (hbad_g.mem_toFinset.mpr h))
    · by_contra h
      exact hv (by
        change v ∈ hbad_g.toFinset ∪ hbad_inv.toFinset
        exact Finset.mem_union_right _ (hbad_inv.mem_toFinset.mpr h))
  · intro v hv
    exact hbox v

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
    (_hIJ : I ≤ J)
    (_hI : chapter15VectorFractionalIdealPower n I ≤ L)
    (hJ : L ≤ chapter15VectorFractionalIdealPower n J) :
    Module.Finite R L := by
  have hpower : chapter15VectorFractionalIdealPower n J =
      Submodule.pi Set.univ
        (fun _ : Fin n => (J : Submodule R K)) := by
    ext x
    simp [chapter15VectorFractionalIdealPower]
  rw [Module.Finite.iff_fg]
  apply Submodule.FG.of_le (T := chapter15VectorFractionalIdealPower n J)
  · rw [hpower]
    exact Submodule.fg_pi (fun _ =>
      FractionalIdeal.fg_of_isNoetherianRing
        (S := nonZeroDivisors R) le_rfl J)
  · exact hJ

theorem chapter15_vector_fractional_ideal_power_spans
    (n : ℕ) (I : Chapter15FractionalIdeal R K) (hI : I ≠ 0) :
    Submodule.span K
        (chapter15VectorFractionalIdealPower n I :
          Set (Chapter15VectorSpace n K)) = ⊤ := by
  classical
  obtain ⟨a, ha0, haI⟩ :=
    FractionalIdeal.exists_ne_zero_mem_isInteger (I := I) hI
  let aK : K := algebraMap R K a
  have haK0 : aK ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha0
  have hsingle (i : Fin n) :
      Pi.single i (1 : K) ∈
        Submodule.span K
          (chapter15VectorFractionalIdealPower n I :
            Set (Chapter15VectorSpace n K)) := by
    have hgen : Pi.single i aK ∈
        chapter15VectorFractionalIdealPower n I := by
      rw [chapter15VectorFractionalIdealPower_mem_iff]
      intro j
      by_cases hij : i = j
      · subst j
        simpa [aK] using haI
      · rw [Pi.single_eq_of_ne' hij]
        exact (I : Submodule R K).zero_mem
    have hspan : Pi.single i aK ∈
        Submodule.span K
          (chapter15VectorFractionalIdealPower n I :
            Set (Chapter15VectorSpace n K)) :=
      Submodule.subset_span hgen
    have hsmul := (Submodule.span K
      (chapter15VectorFractionalIdealPower n I :
        Set (Chapter15VectorSpace n K))).smul_mem (aK⁻¹) hspan
    simpa [← Pi.single_smul, haK0] using hsmul
  apply le_antisymm le_top
  intro x hx
  rw [← Finset.univ_sum_single x]
  exact Submodule.sum_mem _ (fun i _ => by
    have hterm := (Submodule.span K
      (chapter15VectorFractionalIdealPower n I :
        Set (Chapter15VectorSpace n K))).smul_mem (x i) (hsingle i)
    have heq : Pi.single i (x i) =
        (x i) • (Pi.single i (1 : K)) := by
      ext j
      by_cases hij : i = j <;> simp [hij]
    rw [heq]
    exact hterm)

/-- The lattice construction is finite over `𝓞_K` and spans `K^n`. -/
structure Chapter15FullLattice
    (n : ℕ) (L : Submodule R (Chapter15VectorSpace n K)) : Prop where
  finite : Module.Finite R L
  spans : Submodule.span K (L : Set (Chapter15VectorSpace n K)) = ⊤

theorem chapter15_finite_matrix_lattice_is_full
    (n : ℕ) (g : Chapter15FiniteMatrixGroup n R K) :
    Chapter15FullLattice n (chapter15FiniteMatrixLattice n g) := by
  rcases chapter15_finite_matrix_lattice_has_global_fractional_bounds n g with ⟨B⟩
  constructor
  · exact chapter15_submodule_between_fractional_bounds_is_finite n
      B.lowerIdeal B.upperIdeal (chapter15FiniteMatrixLattice n g)
      B.lower_le_upper B.lower_bound B.upper_bound
  · have hspan := chapter15_vector_fractional_ideal_power_spans n
      B.lowerIdeal B.lower_nonzero
    apply le_antisymm le_top
    rw [← hspan]
    apply Submodule.span_mono
    intro x hx
    exact B.lower_bound hx

/-! ### Change of representatives and the rank-one lattice -/

theorem chapter15_finite_matrix_lattice_right_standard_invariant
    (n : ℕ) (g : Chapter15FiniteMatrixGroup n R K)
    (k : Chapter15FiniteMatrixGroup n R K)
    (hk : k ∈ chapter15StandardFiniteMatrixLevel n) :
    chapter15FiniteMatrixLattice (n := n) (g * k) =
      chapter15FiniteMatrixLattice (n := n) g := by
  have hmulVec : ∀ (v : Chapter15FinitePlace R)
      (m : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)),
      m ∈ chapter15FiniteMatrixIntegralSubgroup n v →
      ∀ z : Fin n → v.adicCompletion K, (∀ j, z j ∈ v.adicCompletionIntegers K) →
        ∀ i, (Matrix.mulVec (m : Matrix (Fin n) (Fin n) (v.adicCompletion K)) z) i ∈
          v.adicCompletionIntegers K := by
    intro v m hm z hz i
    have hentries :=
      (chapter15_finite_integral_matrix_mem_entries_and_inverse_iff
        (R := R) (K := K) n v m).mp hm
    change (∑ j : Fin n, m i j * z j) ∈ v.adicCompletionIntegers K
    exact (v.adicCompletionIntegers K).toSubring.sum_mem
      (fun j _ => (v.adicCompletionIntegers K).mul_mem _ _
        (hentries i j).1 (hz j))
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    have hx' := (chapter15FiniteMatrixLattice_mem_iff n (g * k) x).mp hx
    apply (chapter15FiniteMatrixLattice_mem_iff n g x).mpr
    intro v i
    have hinv :
        (↑(g v * k v) : Matrix (Fin n) (Fin n) (v.adicCompletion K))⁻¹ =
          (↑(k v) : Matrix (Fin n) (Fin n) (v.adicCompletion K))⁻¹ *
            (↑(g v) : Matrix (Fin n) (Fin n) (v.adicCompletion K))⁻¹ := by
      rw [← Matrix.GeneralLinearGroup.coe_inv (g v * k v), mul_inv_rev,
        Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_inv (k v),
        Matrix.GeneralLinearGroup.coe_inv (g v)]
    have hxv : ∀ j : Fin n,
        (Matrix.mulVec ((k v)⁻¹ : Matrix (Fin n) (Fin n) (v.adicCompletion K))
          (Matrix.mulVec ((g v)⁻¹ : Matrix (Fin n) (Fin n) (v.adicCompletion K))
            (chapter15LocalizeVector n v x))) j ∈
          v.adicCompletionIntegers K := by
      intro j
      simpa only [RestrictedProduct.mul_apply, hinv, Matrix.mulVec_mulVec] using hx' v j
    have hkv : k v ∈ chapter15FiniteMatrixIntegralSubgroup n v := hk v
    have := hmulVec v (k v) hkv _ (fun j => hxv j) i
    simpa [Matrix.mulVec_mulVec] using this
  · intro hx
    have hx' := (chapter15FiniteMatrixLattice_mem_iff n g x).mp hx
    apply (chapter15FiniteMatrixLattice_mem_iff n (g * k) x).mpr
    intro v i
    have hkinv : (k v)⁻¹ ∈ chapter15FiniteMatrixIntegralSubgroup n v :=
      (chapter15FiniteMatrixIntegralSubgroup n v).inv_mem (hk v)
    simp only [RestrictedProduct.mul_apply]
    have hinv :
        (↑(g v * k v) : Matrix (Fin n) (Fin n) (v.adicCompletion K))⁻¹ =
          (↑(k v) : Matrix (Fin n) (Fin n) (v.adicCompletion K))⁻¹ *
            (↑(g v) : Matrix (Fin n) (Fin n) (v.adicCompletion K))⁻¹ := by
      rw [← Matrix.GeneralLinearGroup.coe_inv (g v * k v), mul_inv_rev,
        Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_inv (k v),
        Matrix.GeneralLinearGroup.coe_inv (g v)]
    rw [hinv, ← Matrix.mulVec_mulVec]
    simpa only [Matrix.GeneralLinearGroup.coe_inv] using
      hmulVec v (k v)⁻¹ hkinv _ (hx' v) i

theorem chapter15_finite_matrix_lattice_left_rational_change
    (n : ℕ) (γ : Matrix.GeneralLinearGroup (Fin n) K)
    (g : Chapter15FiniteMatrixGroup n R K)
    (x : Chapter15VectorSpace n K) :
    x ∈ chapter15FiniteMatrixLattice n
        ((chapter15FinitePrincipalMatrix (R := R) (K := K) n γ) * g) ↔
      ∃ y ∈ chapter15FiniteMatrixLattice n g,
        Matrix.mulVec (γ : Matrix (Fin n) (Fin n) K) y = x := by
  let y : Chapter15VectorSpace n K :=
    Matrix.mulVec ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) x
  have hxy : Matrix.mulVec (γ : Matrix (Fin n) (Fin n) K) y = x := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec]
    simp
  have hloc (v : Chapter15FinitePlace R) :
      chapter15LocalizeVector n v y =
        Matrix.mulVec
          ((Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) γ⁻¹) :
            Matrix (Fin n) (Fin n) (v.adicCompletion K))
          (chapter15LocalizeVector n v x) := by
    funext j
    dsimp [y, chapter15LocalizeVector]
    rw [RingHom.map_mulVec]
    rfl
  constructor
  · intro hx
    refine ⟨y, ?_, hxy⟩
    apply (chapter15FiniteMatrixLattice_mem_iff n g y).mpr
    intro v i
    have hxv :=
      (chapter15FiniteMatrixLattice_mem_iff n
        ((chapter15FinitePrincipalMatrix (R := R) (K := K) n γ) * g) x).mp hx v i
    have hmat :
        (↑((Matrix.GeneralLinearGroup.map
          (algebraMap K (v.adicCompletion K)) γ) * g v) :
          Matrix (Fin n) (Fin n) (v.adicCompletion K))⁻¹ =
          (↑(g v) : Matrix (Fin n) (Fin n) (v.adicCompletion K))⁻¹ *
            (↑(Matrix.GeneralLinearGroup.map
              (algebraMap K (v.adicCompletion K)) γ⁻¹) :
              Matrix (Fin n) (Fin n) (v.adicCompletion K)) := by
      rw [← Matrix.GeneralLinearGroup.coe_inv,
        mul_inv_rev, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_inv,
        ← Matrix.GeneralLinearGroup.map_inv]
    rw [hloc]
    rw [Matrix.mulVec_mulVec, ← hmat]
    change (↑((Matrix.GeneralLinearGroup.map
      (algebraMap K (v.adicCompletion K)) γ) * g v) :
        Matrix (Fin n) (Fin n) (v.adicCompletion K))⁻¹.mulVec
      (chapter15LocalizeVector n v x) i ∈ v.adicCompletionIntegers K at hxv
    exact hxv
  · rintro ⟨y, hy, hxy⟩
    apply (chapter15FiniteMatrixLattice_mem_iff n
      ((chapter15FinitePrincipalMatrix (R := R) (K := K) n γ) * g) x).mpr
    intro v i
    have hyv := (chapter15FiniteMatrixLattice_mem_iff n g y).mp hy v i
    let p : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K) :=
      Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) γ
    have hlocx :
        chapter15LocalizeVector n v x =
          Matrix.mulVec (p : Matrix (Fin n) (Fin n) (v.adicCompletion K))
            (chapter15LocalizeVector n v y) := by
      funext j
      change algebraMap K (v.adicCompletion K) (x j) = _
      rw [← hxy, RingHom.map_mulVec]
      rfl
    have hmat :
        (↑(p * g v) : Matrix (Fin n) (Fin n) (v.adicCompletion K))⁻¹ =
          (↑(g v) : Matrix (Fin n) (Fin n) (v.adicCompletion K))⁻¹ *
            (↑p : Matrix (Fin n) (Fin n) (v.adicCompletion K))⁻¹ := by
      rw [← Matrix.GeneralLinearGroup.coe_inv,
        mul_inv_rev, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_inv,
        Matrix.GeneralLinearGroup.coe_inv]
    have hpcancel :
        (↑p : Matrix (Fin n) (Fin n) (v.adicCompletion K))⁻¹ *
            (↑p : Matrix (Fin n) (Fin n) (v.adicCompletion K)) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_inv,
        ← Matrix.GeneralLinearGroup.coe_mul]
      simp
    change (↑(p * g v) : Matrix (Fin n) (Fin n) (v.adicCompletion K))⁻¹.mulVec
        (chapter15LocalizeVector n v x) i ∈ v.adicCompletionIntegers K
    rw [hlocx, hmat, Matrix.mulVec_mulVec, Matrix.mul_assoc, hpcancel, mul_one]
    exact hyv

/-- The rank-one local lattice condition, prior to identifying it with a fractional ideal. -/
def chapter15FiniteIdeleLatticeCarrier (g : Chapter15FiniteIdeleGroup R K) : Set K :=
  {x | ∀ v : Chapter15FinitePlace R,
    ((g v : (v.adicCompletion K)ˣ) : v.adicCompletion K)⁻¹ *
        algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K}

def chapter15FiniteIdeleLattice (g : Chapter15FiniteIdeleGroup R K) :
    Submodule R K where
  carrier := chapter15FiniteIdeleLatticeCarrier g
  zero_mem' := by
    intro v
    simp
  add_mem' := by
    intro x y hx hy v
    rw [map_add, mul_add]
    exact (v.adicCompletionIntegers K).add_mem _ _ (hx v) (hy v)
  smul_mem' := by
    intro r x hx v
    have hcomm :
        ((g v : (v.adicCompletion K)ˣ) : v.adicCompletion K)⁻¹ *
            algebraMap K (v.adicCompletion K) (r • x) =
          (algebraMap R (v.adicCompletion K) r) *
            (((g v : (v.adicCompletion K)ˣ) : v.adicCompletion K)⁻¹ *
              algebraMap K (v.adicCompletion K) x) := by
      simp only [Algebra.smul_def, map_mul]
      rw [← IsScalarTower.algebraMap_apply R K (v.adicCompletion K) r]
      ac_rfl
    rw [hcomm]
    apply (v.adicCompletionIntegers K).mul_mem _ _
    · rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
      exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem _ _ v r
    · exact hx v

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
  change (∀ v : Chapter15FinitePlace R,
      ((g v : (v.adicCompletion K)ˣ) : v.adicCompletion K)⁻¹ *
          algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K) ↔ _
  simp only [chapter15FiniteIdeleLatticeValuationCondition,
    IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]

theorem chapter15_rank_one_idele_lattice_is_fractional_ideal
    (g : Chapter15FiniteIdeleGroup R K) :
    ∃ I : Chapter15FractionalIdeal R K, I ≠ 0 ∧
      (I : Submodule R K) = chapter15FiniteIdeleLattice g := by
  sorry

/- The preceding existence statement is the abstract lattice interface.  For the
number-field specialization, identify the lattice with the canonical ideal map
from Chapter 8, using the same valuation convention as the source chapter. -/
def chapter15FiniteIdeleIdealMap
    (K : Type*) [Field K] [NumberField K] :
    Chapter15FiniteIdeleGroup (𝓞 K) K →*
      LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08IdealGroup K :=
  (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K).comp
    (chapter15_finite_idele_group_equiv_finite_adele_units
      (R := 𝓞 K) (K := K)).toMonoidHom

theorem chapter15_rank_one_idele_lattice_eq_canonical_ideal
    (K : Type*) [Field K] [NumberField K]
    (g : Chapter15FiniteIdeleGroup (𝓞 K) K) :
    chapter15FiniteIdeleLattice g =
      (↑(chapter15FiniteIdeleIdealMap K g :
        LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08FractionalIdeal K) :
        Submodule (𝓞 K) K) := by
  let e := chapter15_finite_idele_group_equiv_finite_adele_units
    (R := 𝓞 K) (K := K)
  let x : LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08FiniteIdeles K := e g
  have hset : ∀ v : Chapter15FinitePlace (𝓞 K),
      (chapter15FiniteUnitIntegralSubgroup (R := 𝓞 K) (K := K) v :
          Set ((v.adicCompletion K)ˣ)) =
        ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
          Set ((v.adicCompletion K)ˣ)) := by
    intro v
    ext u
    constructor
    · rintro ⟨z, rfl⟩
      exact Submonoid.mem_units_of_val_mem_inv_val_mem _ z.1.2 z.2.2
    · intro hu
      rcases hu with ⟨hu, huinv⟩
      let z : (v.adicCompletionIntegers K)ˣ :=
        { val := ⟨(u : v.adicCompletion K), hu⟩
          inv := ⟨((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K), huinv⟩
          val_inv := by apply Subtype.ext; exact u.val_inv
          inv_val := by apply Subtype.ext; exact u.inv_val }
      exact ⟨z, by apply Units.ext; rfl⟩
  let f :
      Chapter15FiniteIdeleGroup (𝓞 K) K ≃*
        (Πʳ v : Chapter15FinitePlace (𝓞 K),
          [(v.adicCompletion K)ˣ,
            (Submonoid.ofClass (v.adicCompletionIntegers K)).units]) :=
    { toFun := fun y =>
        ⟨y.1, by
          filter_upwards [y.2] with v hv
          rw [hset v] at hv
          exact hv⟩
      invFun := fun y =>
        ⟨y.1, by
          filter_upwards [y.2] with v hv
          rw [← hset v] at hv
          exact hv⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun y => Subtype.ext rfl
      map_mul' := fun y z => Subtype.ext rfl }
  let u := RestrictedProduct.unitsEquiv
    (fun v : Chapter15FinitePlace (𝓞 K) => v.adicCompletion K)
    (B := fun v => v.adicCompletionIntegers K) (𝓕 := Filter.cofinite)
  have he : e g = u.symm (f g) := by
    rfl
  have hlocal (v : Chapter15FinitePlace (𝓞 K)) :
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent
          (x⁻¹) v =
        (((g v : (v.adicCompletion K)ˣ) : v.adicCompletion K)⁻¹) := by
    change ((e g)⁻¹).1 v = _
    rw [he]
    have hmap :
        ((u ((u.symm (f g))⁻¹) v : v.adicCompletion K)) =
          (((u (u.symm (f g)))⁻¹ v : v.adicCompletion K)) :=
      congrArg (fun z => (z v : v.adicCompletion K))
        (u.map_inv (u.symm (f g)))
    calc
      (((u.symm (f g))⁻¹ : _) :
          (Πʳ v : Chapter15FinitePlace (𝓞 K),
            [v.adicCompletion K, v.adicCompletionIntegers K])) v =
        ((u ((u.symm (f g))⁻¹) v : v.adicCompletion K)) := by
          exact (RestrictedProduct.unitsEquiv_apply
            (R := fun v : Chapter15FinitePlace (𝓞 K) => v.adicCompletion K)
            (B := fun v => v.adicCompletionIntegers K)
            (𝓕 := Filter.cofinite) v ((u.symm (f g))⁻¹)).symm
      _ = (((u (u.symm (f g)))⁻¹ v : v.adicCompletion K)) := hmap
      _ = (((f g)⁻¹ v : v.adicCompletion K)) := by
        have hu : u (u.symm (f g)) = f g := u.apply_symm_apply (f g)
        rw [hu]
      _ = (↑(g v))⁻¹ := by
        have hf := congrArg (fun z => (z v : v.adicCompletion K))
          (f.map_inv g)
        change ((g⁻¹ v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          ((f g)⁻¹ v : v.adicCompletion K) at hf
        rw [← hf]
        rw [RestrictedProduct.inv_apply]
        exact Units.val_inv_eq_inv_val _
  have hmem (a : K) :
      a ∈ chapter15FiniteIdeleLattice g ↔
        a ∈ LastLib.Book04AdelesAndIdeles.Chapter08.chapter08Lattice (x⁻¹) := by
    rw [chapter15FiniteIdeleLattice_mem_iff,
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_lattice_mem_iff]
    constructor <;> intro h v
    · rw [hlocal v]
      have hacoe : (a : v.adicCompletion K) =
          algebraMap K (v.adicCompletion K) a := by
        rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
        simp
      have hv := h v
      rw [← hacoe] at hv
      simpa [mul_comm] using hv
    · have hv := h v
      rw [hlocal v] at hv
      have hacoe : (a : v.adicCompletion K) =
          algebraMap K (v.adicCompletion K) a := by
        rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
        simp
      rw [hacoe] at hv
      simpa [mul_comm] using hv
  have hideal :
      (↑((LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K
          (x⁻¹) : LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08FractionalIdeal K)⁻¹) :
        Submodule (𝓞 K) K) =
        (↑(chapter15FiniteIdeleIdealMap K g :
          LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08FractionalIdeal K) :
          Submodule (𝓞 K) K) := by
    change (↑((LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K
        ((e g)⁻¹) : LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08FractionalIdeal K)⁻¹) :
      Submodule (𝓞 K) K) =
      (↑(LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K
        (e g) : LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08FractionalIdeal K) :
        Submodule (𝓞 K) K)
    simp
  apply Submodule.ext
  intro a
  rw [hmem, LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_lattice_eq_inverse_ideal_submodule,
    hideal]

/- The source's rank-one lattice statement is about the matrix lattice
`Λ(g_f)`.  This bridge makes its compatibility with the finite idele model
explicit, rather than leaving the two rank-one constructions disconnected. -/
theorem chapter15_rank_one_matrix_lattice_mem_iff_idele_lattice
    (K : Type*) [Field K] [NumberField K]
    (g : Chapter15FiniteMatrixGroup 1 (𝓞 K) K) (x : K) :
    (fun _ : Fin 1 => x) ∈ chapter15FiniteMatrixLattice 1 g ↔
      x ∈ chapter15FiniteIdeleLattice
        (chapter15_rank_one_finite_matrix_group_recovers_finite_ideles K g) := by
  rw [chapter15FiniteMatrixLattice_mem_iff,
    chapter15FiniteIdeleLattice_mem_iff]
  let e : ∀ v : Chapter15FinitePlace (𝓞 K),
      Matrix.GeneralLinearGroup (Fin 1) (v.adicCompletion K) ≃ₜ*
        (v.adicCompletion K)ˣ :=
    fun v =>
      chapter15_rank_one_local_gl_is_topological_multiplicative_group
        (v.adicCompletion K)
  have hcomponent (v : Chapter15FinitePlace (𝓞 K)) :
      (chapter15_rank_one_finite_matrix_group_recovers_finite_ideles K g) v =
        e v (g v) := by
    change e v (g v) = e v (g v)
    rfl
  have hscalar (v : Chapter15FinitePlace (𝓞 K)) :
      g v = Matrix.GeneralLinearGroup.scalar (Fin 1) (e v (g v)) := by
    change g v =
      (chapter15_rank_one_local_gl_is_topological_multiplicative_group
        (v.adicCompletion K)).symm
        ((chapter15_rank_one_local_gl_is_topological_multiplicative_group
          (v.adicCompletion K)) (g v))
    exact ((chapter15_rank_one_local_gl_is_topological_multiplicative_group
      (v.adicCompletion K)).symm_apply_apply (g v)).symm
  constructor
  · intro hx v
    have hxv := hx v (0 : Fin 1)
    rw [hscalar v] at hxv
    rw [hcomponent v]
    simpa [Matrix.GeneralLinearGroup.coe_scalar, chapter15LocalizeVector] using hxv
  · intro hx v i
    have hi : i = (0 : Fin 1) := Unique.eq_default i
    subst i
    rw [hscalar v]
    have hxv := hx v
    rw [hcomponent v] at hxv
    simpa [Matrix.GeneralLinearGroup.coe_scalar, chapter15LocalizeVector] using hxv

def chapter15FiniteIdeleClassDoubleQuotient :=
  Chapter15DoubleQuotient
    (chapter15FinitePrincipalIdele (R := R) (K := K)).range
    chapter15StandardFiniteIdeleLevel

/- LOCAL_DEPENDENCY_GUESS: the following is the canonical ideal-class
identification used in the preceding ideles chapter; Mathlib supplies
`ClassGroup R`, but not this idele double-coset presentation. -/
theorem chapter15_finite_idele_double_quotient_is_class_group_exists :
    Nonempty
      (chapter15FiniteIdeleClassDoubleQuotient (R := R) (K := K) ≃
        ClassGroup R) := by
  sorry

noncomputable def chapter15_finite_idele_double_quotient_is_class_group :
    chapter15FiniteIdeleClassDoubleQuotient (R := R) (K := K) ≃
      ClassGroup R :=
  Classical.choice
    (chapter15_finite_idele_double_quotient_is_class_group_exists
      (R := R) (K := K))

end

end LastLib.Book04AdelesAndIdeles.Chapter15
