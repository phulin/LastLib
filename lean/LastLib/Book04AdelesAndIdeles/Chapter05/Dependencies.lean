import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.Hausdorff

namespace LastLib.Book04AdelesAndIdeles.Chapter05

noncomputable section

open scoped BigOperators Topology

universe u v w z

/-!
Shared interfaces for Chapter 5.

The preceding Book 4 chapters are drafted in parallel with this chapter.  The
two structures below are therefore the smallest book-facing interfaces needed
here.  They retain the local fields, integral subgroups, diagonal maps, and
adelic topology that the approximation arguments use; a later reconciliation
should replace them by the canonical Chapter 1--4 declarations.
-/

/- LOCAL_DEPENDENCY_GUESS: the reconciled Chapters 1--4 should provide a
    number-field place system with these fields and the finite-approximation
    interface.  No Chapter 5 conclusion is included among the fields. -/

/-! A restricted product is first recorded as its canonical carrier.  The
    group and ring structures, together with its final topology, belong to the
    preceding restricted-product chapter and can be installed on this carrier.
-/

def chapter05RestrictedProduct
    (ι : Type u) (K : ι → Type v) (O : ∀ i, Set (K i)) : Type _ :=
  {x : ∀ i, K i // ({i | x i ∉ O i} : Set ι).Finite}

def chapter05RestrictedProduct.support
    {ι : Type u} {K : ι → Type v} {O : ∀ i, Set (K i)}
    (x : chapter05RestrictedProduct ι K O) : Set ι :=
  {i | x.1 i ∉ O i}

@[simp]
theorem chapter05RestrictedProduct.support_finite
    {ι : Type u} {K : ι → Type v} {O : ∀ i, Set (K i)}
    (x : chapter05RestrictedProduct ι K O) :
    (x.support : Set ι).Finite := by
  exact x.2

def chapter05RestrictedProductStage
    {ι : Type u} {K : ι → Type v} {O : ∀ i, Set (K i)}
    (S : Finset ι) : Set (chapter05RestrictedProduct ι K O) :=
  {x | ∀ i, i ∉ S → x.1 i ∈ O i}

theorem chapter05RestrictedProduct_mem_stage_iff
    {ι : Type u} {K : ι → Type v} {O : ∀ i, Set (K i)}
    (S : Finset ι) (x : chapter05RestrictedProduct ι K O) :
    x ∈ chapter05RestrictedProductStage S ↔
      ∀ i, i ∉ S → x.1 i ∈ O i := by
  rfl

/-- The discreteness predicate used for the Minkowski lattice and for the
    diagonal subgroup.  It is written without a topology class on the subset
    so that it remains stable under the book's transport equivalences. -/
def chapter05IsDiscreteSubset
    {X : Type u} [TopologicalSpace X] (s : Set X) : Prop :=
  ∀ x, x ∈ s → ∃ U ∈ 𝓝 x, U ∩ s = {x}

def chapter05NondiscreteAtZero
    {G : Type u} [Zero G] [TopologicalSpace G] : Prop :=
  ({0} : Set G) ∉ 𝓝 (0 : G)

theorem chapter05_discrete_subgroup_not_dense_in_nondiscrete_group
    {G : Type u} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T2Space G]
    (H : AddSubgroup G)
    (hidentity : ∃ U ∈ 𝓝 (0 : G), U ∩ (H : Set G) = {0})
    (hnondiscrete : chapter05NondiscreteAtZero (G := G)) :
    ¬ Dense (H : Set G) := by
  sorry

/-- A full lattice in the form used by the approximation and discreteness
    arguments: discrete, with a compact fundamental set covering the ambient
    additive group by translates. -/
structure Chapter05Lattice
    (X : Type u) [AddCommGroup X] [TopologicalSpace X] where
  carrier : AddSubgroup X
  discrete : chapter05IsDiscreteSubset (carrier : Set X)
  fundamentalDomain : Set X
  fundamental_compact : IsCompact fundamentalDomain
  covers : ∀ x : X, ∃ l : carrier, x - (l : X) ∈ fundamentalDomain

@[ext]
theorem Chapter05Lattice.ext
    {X : Type u} [AddCommGroup X] [TopologicalSpace X]
    {L L' : Chapter05Lattice X}
    (hcarrier : L.carrier = L'.carrier)
    (hfundamental : L.fundamentalDomain = L'.fundamentalDomain) :
    L = L' := by
  sorry

/-! The following predicate is the book-facing fractional-ideal interface.
It is intentionally phrased as an `O`-submodule with a common denominator;
the canonical Mathlib `FractionalIdeal` can be used as an equivalence later. -/

def chapter05IsFractionalIdealLike
    {K : Type u} [Field K] (O : Subring K) (I : Set K) : Prop :=
  0 ∈ I ∧
    (∀ ⦃x y : K⦄, x ∈ I → y ∈ I → x + y ∈ I) ∧
    (∀ ⦃x : K⦄, x ∈ I → -x ∈ I) ∧
    (∀ (r : O) ⦃x : K⦄, x ∈ I → (r : K) * x ∈ I) ∧
    (∃ d : K, d ≠ 0 ∧ ∀ ⦃x : K⦄, x ∈ I → d * x ∈ (O : Set K))

def chapter05FinsetSubtypeCoe
    {V : Type v} {s : Set V} (S : Finset {x // x ∈ s}) : Set V :=
  {x | ∃ hx : x ∈ s, (⟨x, hx⟩ : {x // x ∈ s}) ∈ S}

/-! A number-field place system.  The finite-approximation field is the exact
    algebraic input used in §5.2; the local precision basis is what turns its
    congruence form into arbitrary open neighborhoods. -/

structure Chapter05PlaceSystem
    (K : Type u) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    (V : Type v) (Kv : V → Type w)
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)] where
  finite : Set V
  archimedean : Set V
  finite_archimedean_disjoint : Disjoint finite archimedean
  places_exhaust : finite ∪ archimedean = Set.univ
  archimedean_finite : archimedean.Finite
  archimedean_nonempty : archimedean.Nonempty
  integerRing : Subring K
  completionMap : ∀ v, K →+* Kv v
  completionMap_injective : ∀ v, Function.Injective (completionMap v)
  residueCharacteristic : V → ℕ
  residueCharacteristic_prime :
    ∀ v, v ∈ finite → Nat.Prime (residueCharacteristic v)
  integral : ∀ v, AddSubgroup (Kv v)
  unit : ∀ v, Set (Kv v)
  unit_subset_integral : ∀ v, unit v ⊆ integral v
  rational_scalar_is_unit_away_from_residue_characteristic :
    ∀ (ell : ℕ) (v : V), v ∈ finite →
      ell ≠ residueCharacteristic v →
        completionMap v (ell : K) ∈ unit v
  global_unit_or_zero_tail :
    ∀ a : K, ({v | v ∈ finite ∧ completionMap v a ≠ 0 ∧
      completionMap v a ∉ unit v} : Set V).Finite
  precision : ∀ v, ℤ → AddSubgroup (Kv v)
  precision_le_integral : ∀ v n, 0 ≤ n → precision v n ≤ integral v
  precision_neighborhood_basis :
    ∀ (v : V) (x : Kv v) (U : Set (Kv v)), U ∈ 𝓝 x →
      ∃ n : ℤ, {y | y - x ∈ precision v n} ⊆ U
  global_integrality :
    ∀ a : K, ({v | v ∈ finite ∧ completionMap v a ∉ integral v} : Set V).Finite
  integer_global_iff :
    ∀ a : K, a ∈ integerRing ↔
      ∀ v : V, v ∈ finite → completionMap v a ∈ integral v
  integerRing_infinite : (Set.Infinite (integerRing : Set K))
  finite_approximation :
    ∀ (S : Finset {v // v ∈ finite})
      (x : ∀ v : S, Kv v.1) (m : S → ℤ),
      ∃ a : K,
        (∀ v : S,
          completionMap v.1 a - x v ∈ precision v.1 (m v)) ∧
        (∀ v : V, v ∈ finite → v ∉ chapter05FinsetSubtypeCoe S →
          completionMap v a ∈ integral v)
  correction_set_fractional_ideal :
    ∀ (S : Finset {v // v ∈ finite}) (m : S → ℤ),
      chapter05IsFractionalIdealLike integerRing
        {c : K | ∀ v : S,
          completionMap v.1 c ∈ precision v.1 (m v)}
  /- LOCAL_DEPENDENCY_GUESS: this is the Minkowski lattice-mesh lemma used
       by §5.5.  It is weaker than weak approximation because the finite
       coordinates are required to be zero corrections. -/
  lattice_mesh :
    ∀ (S : Finset {v // v ∈ finite}) (m : S → ℤ)
      (T : Finset {v // v ∈ archimedean})
      (x : ∀ v : T, Kv v.1) (W : ∀ v : T, Set (Kv v.1)),
      (∀ v : T, W v ∈ 𝓝 (x v)) →
        ∃ c : K,
          c ∈ {c : K | ∀ v : S,
            completionMap v.1 c ∈ precision v.1 (m v)} ∧
          ∀ v : T, completionMap v.1 c ∈ W v

abbrev chapter05MinkowskiSpace
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    (P : Chapter05PlaceSystem K V Kv) : Type _ :=
  ∀ v : {v // v ∈ P.archimedean}, Kv v.1

def chapter05ArchimedeanDiagonal
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    (P : Chapter05PlaceSystem K V Kv) :
    K →+ chapter05MinkowskiSpace P where
  toFun a v := P.completionMap v.1 a
  map_zero' := by
    ext v
    simp
  map_add' a b := by
    ext v
    simp

def chapter05CorrectionSet
    {K : Type u} [Field K]
    {V : Type v} (Kv : V → Type w)
    [∀ v, Field (Kv v)]
    (finite : Set V) (completionMap : ∀ v, K →+* Kv v)
    (precision : ∀ v, ℤ → AddSubgroup (Kv v))
    (S : Finset {v // v ∈ finite}) (m : S → ℤ) : Set K :=
  {c : K | ∀ v : S, completionMap v.1 c ∈ precision v.1 (m v)}

@[simp]
theorem chapter05_mem_correctionSet_iff
    {K : Type u} [Field K]
    {V : Type v} (Kv : V → Type w) [∀ v, Field (Kv v)]
    (finite : Set V) (completionMap : ∀ v, K →+* Kv v)
    (precision : ∀ v, ℤ → AddSubgroup (Kv v))
    (S : Finset {v // v ∈ finite}) (m : S → ℤ) (c : K) :
    c ∈ chapter05CorrectionSet Kv finite completionMap precision S m ↔
      ∀ v : S, completionMap v.1 c ∈ precision v.1 (m v) := by
  rfl

/-! A compact-open finite-adele coordinate basis.  This is the only part of
    the finite-adele topology needed to turn the finite approximation lemma
    into density. -/

def chapter05CoordinateNeighborhood
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    (P : Chapter05PlaceSystem K V Kv)
    {A_f : Type z} (coordinate : ∀ v : {v // v ∈ P.finite}, A_f → Kv v.1)
    (x : A_f) (S : Finset {v // v ∈ P.finite}) (m : S → ℤ) : Set A_f :=
  {z | ∀ v : S,
    coordinate v z - coordinate v x ∈ P.precision v.1 (m v)}

@[simp]
theorem chapter05_mem_coordinateNeighborhood_iff
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    (P : Chapter05PlaceSystem K V Kv)
    {A_f : Type z} (coordinate : ∀ v : {v // v ∈ P.finite}, A_f → Kv v.1)
    (x z : A_f) (S : Finset {v // v ∈ P.finite}) (m : S → ℤ) :
    z ∈ chapter05CoordinateNeighborhood P coordinate x S m ↔
      ∀ v : S, coordinate v z - coordinate v x ∈ P.precision v.1 (m v) := by
  rfl

/- LOCAL_DEPENDENCY_GUESS: this is the Chapter 4 adelic package.  The finite
    and full adele types carry their canonical ring and topological structures;
    the coordinate and decomposition fields express the identifications used
    below without assuming any Chapter 5 conclusion. -/

structure Chapter05AdeleModel
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    (P : Chapter05PlaceSystem K V Kv)
    (A_f : Type z) (A : Type (max u z))
    [CommRing A_f] [CommRing A]
    [TopologicalSpace A_f] [TopologicalSpace A]
    [IsTopologicalAddGroup A] where
  finiteIntegral : Subring A_f
  finiteDiagonal : K →+* A_f
  fullDiagonal : K →+* A
  finiteCoordinate : ∀ v : {v // v ∈ P.finite}, A_f → Kv v.1
  finiteDiagonal_coordinate :
    ∀ (a : K) (v : {v // v ∈ P.finite}),
      finiteCoordinate v (finiteDiagonal a) = P.completionMap v.1 a
  decomposition : A ≃+ chapter05MinkowskiSpace P × A_f
  decomposition_diagonal :
    ∀ a : K, decomposition (fullDiagonal a) =
      (chapter05ArchimedeanDiagonal P a, finiteDiagonal a)
  finiteDiagonal_injective : Function.Injective finiteDiagonal
  fullDiagonal_injective : Function.Injective fullDiagonal
  finite_integrality_iff :
    ∀ a : K, finiteDiagonal a ∈ finiteIntegral ↔ a ∈ P.integerRing
  finite_integral_open : IsOpen (finiteIntegral : Set A_f)
  finite_integral_compact : IsCompact (finiteIntegral : Set A_f)
  decomposition_continuous :
    Continuous (decomposition : A → chapter05MinkowskiSpace P × A_f)
  decomposition_inverse_continuous :
    Continuous (decomposition.symm :
      chapter05MinkowskiSpace P × A_f → A)
  integerLattice : Chapter05Lattice (chapter05MinkowskiSpace P)
  integerLattice_global :
    ∀ x : chapter05MinkowskiSpace P,
      x ∈ integerLattice.carrier ↔
        ∃ a : K, a ∈ P.integerRing ∧
          chapter05ArchimedeanDiagonal P a = x
  finite_neighborhood_basis :
    ∀ (x : A_f) (U : Set A_f), U ∈ 𝓝 x →
      ∃ (S : Finset {v // v ∈ P.finite}) (m : S → ℤ),
        chapter05CoordinateNeighborhood P finiteCoordinate x S m ⊆ U

def chapter05FiniteIntegralSubgroup
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    {A_f : Type z} {A : Type (max u z)}
    [CommRing A_f] [CommRing A] [TopologicalSpace A_f] [TopologicalSpace A]
    [IsTopologicalAddGroup A]
    {P : Chapter05PlaceSystem K V Kv}
    (M : Chapter05AdeleModel P A_f A) : AddSubgroup A_f :=
  M.finiteIntegral.toAddSubgroup

def chapter05FullZeroNeighborhood
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    {A_f : Type z} {A : Type (max u z)}
    [CommRing A_f] [CommRing A] [TopologicalSpace A_f] [TopologicalSpace A]
    [IsTopologicalAddGroup A]
    {P : Chapter05PlaceSystem K V Kv}
    (M : Chapter05AdeleModel P A_f A) (Uinf : Set (chapter05MinkowskiSpace P)) : Set A :=
  M.decomposition ⁻¹' (Uinf ×ˢ (M.finiteIntegral : Set A_f))

def chapter05FiniteZeroNeighborhood
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    {A_f : Type z} {A : Type (max u z)}
    [CommRing A_f] [CommRing A] [TopologicalSpace A_f] [TopologicalSpace A]
    [IsTopologicalAddGroup A]
    {P : Chapter05PlaceSystem K V Kv}
    (M : Chapter05AdeleModel P A_f A) : Set A_f :=
  (M.finiteIntegral : Set A_f)

def chapter05FullDiagonalSubgroup
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    {A_f : Type z} {A : Type (max u z)}
    [CommRing A_f] [CommRing A] [TopologicalSpace A_f] [TopologicalSpace A]
    [IsTopologicalAddGroup A]
    {P : Chapter05PlaceSystem K V Kv}
    (M : Chapter05AdeleModel P A_f A) : AddSubgroup A where
  carrier := Set.range M.fullDiagonal
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by simp⟩
  neg_mem' := by
    rintro x ⟨a, rfl⟩
    exact ⟨-a, by simp⟩

def chapter05FiniteDiagonalSubgroup
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    {A_f : Type z} {A : Type (max u z)}
    [CommRing A_f] [CommRing A] [TopologicalSpace A_f] [TopologicalSpace A]
    [IsTopologicalAddGroup A]
    {P : Chapter05PlaceSystem K V Kv}
    (M : Chapter05AdeleModel P A_f A) : AddSubgroup A_f where
  carrier := Set.range M.finiteDiagonal
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by simp⟩
  neg_mem' := by
    rintro x ⟨a, rfl⟩
    exact ⟨-a, by simp⟩

def chapter05FiniteAdeleCarrier
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    (P : Chapter05PlaceSystem K V Kv) : Type _ :=
  chapter05RestrictedProduct
    {v // v ∈ P.finite} (fun v => Kv v.1) (fun v => P.integral v.1)

def chapter05CanonicalFullAdeleCarrier
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    (P : Chapter05PlaceSystem K V Kv) : Type _ :=
  chapter05MinkowskiSpace P × chapter05FiniteAdeleCarrier P

def chapter05AdeleAwayFrom
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    (P : Chapter05PlaceSystem K V Kv) (S : Set V) : Type _ :=
  chapter05RestrictedProduct
    {v // v ∉ S} (fun v => Kv v.1) (fun v => P.integral v.1)

def chapter05AwayDiagonal
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    (P : Chapter05PlaceSystem K V Kv) (S : Set V)
    (hS : P.archimedean ⊆ S) (a : K) : chapter05AdeleAwayFrom P S :=
  ⟨fun v => P.completionMap v.1 a, by
    -- The global denominator set is finite, and its archimedean part is
    -- removed by `hS`; this is the restrictedness of a principal adele.
    sorry⟩

def chapter05FiniteToAwayProjection
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    (P : Chapter05PlaceSystem K V Kv) (S : Set V)
    (hfinite : ∀ v, v ∉ S → v ∈ P.finite)
    (x : chapter05FiniteAdeleCarrier P) : chapter05AdeleAwayFrom P S :=
  ⟨fun v => x.1 ⟨v.1, hfinite v.1 v.2⟩, by
    sorry⟩

/-! The correction-lattice statement used in the weak approximation proof.
It is strictly weaker than weak approximation: it asks only for a correction
inside a prescribed finite-place fractional ideal and at selected infinity
coordinates. -/

def chapter05LatticeMesh
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    (P : Chapter05PlaceSystem K V Kv) : Prop :=
  ∀ (S : Finset {v // v ∈ P.finite}) (m : S → ℤ)
    (T : Finset {v // v ∈ P.archimedean})
    (x : ∀ v : T, Kv v.1) (W : ∀ v : T, Set (Kv v.1)),
    (∀ v : T, W v ∈ 𝓝 (x v)) →
      ∃ c : K,
        c ∈ chapter05CorrectionSet Kv P.finite P.completionMap P.precision S m ∧
        ∀ v : T, P.completionMap v.1 c ∈ W v

def chapter05WeakApproximationStatement
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    (P : Chapter05PlaceSystem K V Kv) (T : Finset V) : Prop :=
  ∀ (x : ∀ v : T, Kv v), ∀ (W : ∀ v : T, Set (Kv v.1)),
    (∀ v : T, W v ∈ 𝓝 (x v)) →
      ∃ a : K, ∀ v : T, P.completionMap v.1 a ∈ W v

def chapter05DiagonalAtPlaces
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    (P : Chapter05PlaceSystem K V Kv) (T : Finset V) :
    K → (∀ v : T, Kv v.1) :=
  fun a v => P.completionMap v.1 a

def chapter05StrongApproximationAwayFrom
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    (P : Chapter05PlaceSystem K V Kv) (S : Set V) : Prop :=
  ∀ (T : Finset {v // v ∉ S})
    (x : ∀ v : T, Kv v.1) (W : ∀ v : T, Set (Kv v.1)),
    (∀ v : T, W v ∈ 𝓝 (0 : Kv v.1)) →
      ∃ a : K,
        (∀ v : T, P.completionMap v.1 a - x v ∈ W v) ∧
        (∀ v : V, v ∉ S → v ∉ chapter05FinsetSubtypeCoe T →
          P.completionMap v a ∈ P.integral v)

def chapter05AwayBasicNeighborhood
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    (P : Chapter05PlaceSystem K V Kv) (S : Set V)
    (x : chapter05AdeleAwayFrom P S)
    (T : Finset {v // v ∉ S}) (W : ∀ v : T, Set (Kv v.1)) :
    Set (chapter05AdeleAwayFrom P S) :=
  {y |
    (∀ v : T, y.1 v - x.1 v ∈ W v) ∧
    (∀ v : {v // v ∉ S}, v ∉ (T : Set {v // v ∉ S}) →
      y.1 v - x.1 v ∈ P.integral v.1)}

@[simp]
theorem chapter05_mem_awayBasicNeighborhood_iff
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    (P : Chapter05PlaceSystem K V Kv) (S : Set V)
    (x y : chapter05AdeleAwayFrom P S)
    (T : Finset {v // v ∉ S}) (W : ∀ v : T, Set (Kv v.1)) :
    y ∈ chapter05AwayBasicNeighborhood P S x T W ↔
      ((∀ v : T, y.1 v - x.1 v ∈ W v) ∧
        (∀ v : {v // v ∉ S}, v ∉ (T : Set {v // v ∉ S}) →
          y.1 v - x.1 v ∈ P.integral v.1)) := by
  rfl

def chapter05RestrictedProductBasis
    {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {V : Type v} {Kv : V → Type w}
    [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
    (P : Chapter05PlaceSystem K V Kv) (S : Set V)
    [TopologicalSpace (chapter05AdeleAwayFrom P S)] : Prop :=
  ∀ (x : chapter05AdeleAwayFrom P S) (U : Set (chapter05AdeleAwayFrom P S)),
    U ∈ 𝓝 x →
      ∃ (T : Finset {v // v ∉ S}) (W : ∀ v : T, Set (Kv v.1)),
        (∀ v : T, W v ∈ 𝓝 (0 : Kv v.1)) ∧
          chapter05AwayBasicNeighborhood P S x T W ⊆ U

end

end LastLib.Book04AdelesAndIdeles.Chapter05
