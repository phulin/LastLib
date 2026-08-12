import LastLib.Book04AdelesAndIdeles.Chapter05.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter05

noncomputable section

open scoped Topology

universe u v w

/-! ## 5.5. Weak approximation at arbitrary places -/

variable {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
variable {V : Type v} {Kv : V → Type w}
variable [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
variable {P : Chapter05PlaceSystem K V Kv}

def chapter05SelectedFinitePlaces
    (T : Finset V) : Finset V := by
  classical
  exact T.filter (fun v => v ∈ P.finite)

def chapter05SelectedArchimedeanPlaces
    (T : Finset V) : Finset V := by
  classical
  exact T.filter (fun v => v ∈ P.archimedean)

def chapter05FiniteCorrectionSet
    (S : Finset {v // v ∈ P.finite}) (m : S → ℤ) : Set K :=
  chapter05CorrectionSet Kv P.finite P.completionMap P.precision S m

theorem chapter05_finite_correction_set_is_fractional_ideal
    (S : Finset {v // v ∈ P.finite}) (m : S → ℤ) :
    chapter05IsFractionalIdealLike P.integerRing
      (chapter05FiniteCorrectionSet (P := P) S m) := by
  sorry

/-! “An auxiliary rational prime lying below none of the selected finite
    places” is represented by avoiding their residue characteristics. -/

def chapter05AuxiliaryPrimeAvoids
    (S : Finset {v // v ∈ P.finite}) (ell : ℕ) : Prop :=
  Nat.Prime ell ∧ ∀ v : S, ell ≠ P.residueCharacteristic v.1

theorem chapter05_exists_auxiliary_prime
    (S : Finset {v // v ∈ P.finite}) :
    ∃ ell : ℕ, chapter05AuxiliaryPrimeAvoids (P := P) S ell := by
  sorry

def chapter05ScaledCorrectionSet
    (S : Finset {v // v ∈ P.finite}) (m : S → ℤ)
    (ell s : ℕ) : Set K :=
  {c : K |
    ∃ d : K, d ∈ chapter05FiniteCorrectionSet (P := P) S m ∧
      c = ((ell : K)⁻¹) ^ s * d}

theorem chapter05_scaled_correction_preserves_finite_precision
    (S : Finset {v // v ∈ P.finite}) (m : S → ℤ)
    (ell s : ℕ) (hℓ : chapter05AuxiliaryPrimeAvoids (P := P) S ell)
    {c : K} (hc : c ∈ chapter05ScaledCorrectionSet (P := P) S m ell s) :
    c ∈ chapter05FiniteCorrectionSet (P := P) S m := by
  sorry

/-! The following bridge is the lattice-mesh assertion from the proof.  It is
    weaker than the theorem below and is independently reusable for other
    finite-place congruence problems. -/

theorem chapter05_correction_lattice_mesh
    (hmesh : chapter05LatticeMesh P)
    (S : Finset {v // v ∈ P.finite}) (m : S → ℤ)
    (T : Finset {v // v ∈ P.archimedean})
    (x : ∀ v : T, Kv v.1) (W : ∀ v : T, Set (Kv v.1))
    (hW : ∀ v : T, W v ∈ 𝓝 (x v)) :
    ∃ c : K,
      c ∈ chapter05FiniteCorrectionSet (P := P) S m ∧
      ∀ v : T, P.completionMap v.1 c ∈ W v := by
  exact hmesh S m T x W hW

theorem chapter05_place_system_lattice_mesh :
    chapter05LatticeMesh P := by
  exact P.lattice_mesh

/-!
**Theorem 5.3 (weak approximation).** For every finite list of distinct
places, the diagonal map has dense image in the selected local product.
-/
theorem chapter05_theorem_5_3_weak_approximation
    (T : Finset V) :
    chapter05WeakApproximationStatement P T := by
  sorry

theorem chapter05_theorem_5_3_weak_approximation_dense
    (T : Finset V) :
    DenseRange (chapter05DiagonalAtPlaces P T) := by
  sorry

theorem chapter05_weak_approximation_iff_dense_selected_diagonal
    (T : Finset V) :
    chapter05WeakApproximationStatement P T ↔
      DenseRange (chapter05DiagonalAtPlaces P T) := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter05
