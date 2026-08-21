import LastLib.Book05LocalClassFieldTheory.Chapter02.Dependencies
import LastLib.Book05LocalClassFieldTheory.Chapter03.Section05TheUnramifiedCyclicComputation
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

namespace LastLib.Book05LocalClassFieldTheory.Chapter04

noncomputable section

open scoped BigOperators
open LastLib.Book05LocalClassFieldTheory.Chapter02

universe u

/-! ## Shared interfaces for Chapter 4

`CSA` and `BrauerGroup` are the canonical pinned Mathlib representations.  The
remaining structures in this file are deliberately small interfaces for the
operations which the pinned Brauer API does not yet expose (tensor products,
scalar restriction, corestriction, reduced norms, and crossed products).
-/

/-- The finite-dimensional central simple algebras used by the chapter. -/
abbrev chapter04CentralSimpleAlgebra (K : Type u) [Field K] := CSA.{u, u} K

/-- The pinned Mathlib quotient of central simple algebras. -/
abbrev chapter04BrauerGroup (K : Type u) [Field K] := BrauerGroup.{u, u} K

/-- The Brauer class represented by a central simple algebra. -/
def chapter04BrauerClass {K : Type u} [Field K]
    (A : chapter04CentralSimpleAlgebra K) : chapter04BrauerGroup K :=
  @Quotient.mk' _ (Brauer.CSA_Setoid K) A

/-- Brauer equivalence, named in the book's namespace. -/
abbrev chapter04BrauerEquivalent {K : Type*} [Field K]
    (A B : chapter04CentralSimpleAlgebra K) : Prop :=
  IsBrauerEquivalent A B

theorem chapter04_brauer_equivalent_refl
    {K : Type*} [Field K] (A : chapter04CentralSimpleAlgebra K) :
    chapter04BrauerEquivalent A A :=
  IsBrauerEquivalent.refl A

theorem chapter04_brauer_equivalent_symm
    {K : Type*} [Field K]
    {A B : chapter04CentralSimpleAlgebra K}
    (h : chapter04BrauerEquivalent A B) :
    chapter04BrauerEquivalent B A :=
  IsBrauerEquivalent.symm h

theorem chapter04_brauer_equivalent_trans
    {K : Type*} [Field K]
    {A B C : chapter04CentralSimpleAlgebra K}
    (hAB : chapter04BrauerEquivalent A B)
    (hBC : chapter04BrauerEquivalent B C) :
    chapter04BrauerEquivalent A C :=
  IsBrauerEquivalent.trans hAB hBC

/- LOCAL_DEPENDENCY_GUESS: Mathlib's quotient currently has no tensor-product
  group structure.  This record is the minimal book-facing abelian-group
  interface; it does not identify arbitrary quotient representatives by fiat. -/
structure Chapter04BrauerGroupLaw (K : Type*) [Field K] where
  tensor : chapter04BrauerGroup K → chapter04BrauerGroup K → chapter04BrauerGroup K
  one : chapter04BrauerGroup K
  opposite : chapter04BrauerGroup K → chapter04BrauerGroup K
  tensor_assoc : ∀ a b c, tensor (tensor a b) c = tensor a (tensor b c)
  tensor_comm : ∀ a b, tensor a b = tensor b a
  one_tensor : ∀ a, tensor one a = a
  tensor_one : ∀ a, tensor a one = a
  tensor_opposite : ∀ a, tensor a (opposite a) = one
  opposite_tensor : ∀ a, tensor (opposite a) a = one

/- The division representative in the Wedderburn decomposition.  The
  two-sided inverse condition is kept as a proposition so this interface does
  not install a second `DivisionRing` instance on a `CSA` carrier. -/
structure Chapter04DivisionAlgebraData (K : Type u) [Field K] where
  carrier : chapter04CentralSimpleAlgebra K
  isDivision : ∀ x : carrier, x ≠ 0 →
    ∃ y : carrier, x * y = 1 ∧ y * x = 1
  degree : ℕ
  degree_pos : 0 < degree
  finrank_eq_degree_sq : Module.finrank K (carrier : Type u) = degree ^ 2

/-- The book's matrix-over-division-algebra decomposition package. -/
structure Chapter04WedderburnDecomposition
    {K : Type u} [Field K]
    (A : chapter04CentralSimpleAlgebra K) where
  matrixSize : ℕ
  matrixSize_pos : 0 < matrixSize
  division : Chapter04DivisionAlgebraData K
  equivalence : Nonempty
    ((A : Type u) ≃ₐ[K]
      Matrix (Fin matrixSize) (Fin matrixSize) (division.carrier : Type u))

/-- Complete discretely valued fields with finite residue field, using the
canonical valuation interface from Book 2. -/
structure Chapter04LocalFieldProfile (K : Type*) [Field K] where
  valuation : AddValuation K (WithTop ℤ)
  localField : Chapter02LocalField valuation
  uniformizer : K
  uniformizer_spec : chapter02IsUniformizer valuation uniformizer

/-- The rational residue group `ℚ/ℤ` used for the local invariant. -/
abbrev chapter04RationalResidue := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

def chapter04RationalResidueMk (q : ℚ) : chapter04RationalResidue :=
  QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) q

def chapter04RationalResidueFraction (r : ℤ) (d : ℕ) : chapter04RationalResidue :=
  chapter04RationalResidueMk ((r : ℚ) / (d : ℚ))

def chapter04RationalResidueOneOver (d : ℕ) : chapter04RationalResidue :=
  chapter04RationalResidueFraction 1 d

/- The finite unramified-extension data used both for the maximal subfield of
  a division algebra and for the algebras `A_{r,d}`. -/
structure Chapter04UnramifiedExtensionData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] where
  valuationK : AddValuation K (WithTop ℤ)
  valuationL : AddValuation L (WithTop ℤ)
  unramified :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnramifiedValuedExtension
      valuationK valuationL
  degree : ℕ
  degree_pos : 0 < degree
  degree_eq : Module.finrank K L = degree
  uniformizer : Kˣ
  uniformizer_value : valuationK (uniformizer : K) = (1 : WithTop ℤ)
  arithmeticFrobenius : Gal(L / K)
  frobenius_generates :
    Subgroup.zpowers arithmeticFrobenius = (⊤ : Subgroup (Gal(L / K)))
  units_are_norms : ∀ u : Kˣ, ∃ x : Lˣ,
    Units.map (Algebra.norm K (S := L)) x = u

/- LOCAL_DEPENDENCY_GUESS: scalar restriction and corestriction are not
  present in the pinned `BrauerGroup` API.  The representative maps below
  make the missing compatibility data explicit instead of leaving it as an
  unconstrained proposition. -/
structure Chapter04SplitBrauerClass (K : Type*) [Field K] where
  representative : chapter04CentralSimpleAlgebra K
  matrixSize : ℕ
  matrixSize_pos : 0 < matrixSize
  split : Nonempty
    (representative ≃ₐ[K]
      Matrix (Fin matrixSize) (Fin matrixSize) K)

structure Chapter04BrauerRestrictionData
    (K L : Type*) [Field K] [Field L] [Algebra K L] where
  restriction : chapter04BrauerGroup K → chapter04BrauerGroup L
  splitClass : Chapter04SplitBrauerClass L
  scalarExtension : chapter04CentralSimpleAlgebra K →
    chapter04CentralSimpleAlgebra L
  representative_compatibility : ∀ A : chapter04CentralSimpleAlgebra K,
    restriction (chapter04BrauerClass A) =
      chapter04BrauerClass (scalarExtension A)

structure Chapter04BrauerCorestrictionData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] where
  corestriction : chapter04BrauerGroup L → chapter04BrauerGroup K
  representativeMap : chapter04CentralSimpleAlgebra L →
    chapter04CentralSimpleAlgebra K
  representative_compatibility : ∀ A : chapter04CentralSimpleAlgebra L,
    corestriction (chapter04BrauerClass A) =
      chapter04BrauerClass (representativeMap A)

def chapter04RestrictionSplitClass
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (R : Chapter04BrauerRestrictionData K L) : chapter04BrauerGroup L :=
  chapter04BrauerClass R.splitClass.representative

/-- The relative Brauer group for an explicit restriction interface. -/
def chapter04RelativeBrauerGroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (R : Chapter04BrauerRestrictionData K L) : Type _ :=
  {a : chapter04BrauerGroup K //
    R.restriction a = chapter04RestrictionSplitClass K L R}

def chapter04RelativeBrauerClass
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (R : Chapter04BrauerRestrictionData K L)
    (a : chapter04BrauerGroup K)
    (ha : R.restriction a = chapter04RestrictionSplitClass K L R) :
    chapter04RelativeBrauerGroup K L R :=
  ⟨a, ha⟩

/- LOCAL_DEPENDENCY_GUESS: reduced norms are not yet exposed by Mathlib for a
  general central division algebra. -/
structure Chapter04ReducedNormData
    (K D : Type u) [Field K] [Ring D] [Algebra K D]
    [FiniteDimensional K D] where
  degree : ℕ
  degree_pos : 0 < degree
  finrank_eq_degree_sq : Module.finrank K D = degree ^ 2
  reducedNorm : Dˣ →* Kˣ
  baseUnitValue : Kˣ → ℚ
  /- LOCAL_DEPENDENCY_GUESS: this is the defining reduced-norm compatibility
    needed by the chapter until a canonical central-simple reduced norm is
    available from earlier LastLib or pinned Mathlib. -/
  reducedNorm_on_commutative_subfields :
    ∀ {E : Type u} [Field E] [Algebra K E] [FiniteDimensional K E]
      (φ : E →ₐ[K] D),
      Module.finrank K E ∣ degree →
      ∀ x : Eˣ,
        (reducedNorm (Units.map φ.toMonoidHom x) : K) =
          (Algebra.norm K (x : E)) ^ (degree / Module.finrank K E)

def chapter04ReducedNormAgreesWithDeterminant
    {K D S : Type*} [Field K] [Ring D] [Field S]
    [Algebra K D] [Algebra K S]
    (N : Dˣ →* Kˣ) (d : ℕ)
    (ρ : D →ₐ[K] Matrix (Fin d) (Fin d) S) : Prop :=
  ∀ x : Dˣ,
    algebraMap K S (N x : K) = Matrix.det (ρ (x : D))

/- The division valuation is explicitly extended from units to all of `D`,
  with the zero value recorded separately. -/
def chapter04DivisionValuation
    {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
    [FiniteDimensional K D]
    (N : Chapter04ReducedNormData K D) :
    (Kˣ → ℚ) → D → WithTop ℚ :=
  fun vK x => by
    classical
    by_cases hx : x = 0
    · exact ⊤
    · exact ((vK (N.reducedNorm (Units.mk0 x hx)) / N.degree : ℚ) : WithTop ℚ)

def chapter04DivisionValuationOnUnits
    {K D : Type u} [Field K] [Ring D] [Algebra K D]
    [FiniteDimensional K D]
    (N : Chapter04ReducedNormData K D) (vK : Kˣ → ℚ) : Dˣ → ℚ :=
  fun x => vK (N.reducedNorm x) / N.degree

def chapter04DivisionValuationRing
    {D : Type*} [Ring D] (w : D → WithTop ℚ) : Set D :=
  {x | w x ≥ 0}

/- Integrality over the valuation subring of a skew field is recorded by a
  monic noncommutative coefficient relation, since Mathlib's `IsIntegral`
  requires a commutative coefficient ring. -/
def chapter04IsIntegralOverSubring
    {D : Type*} [Ring D] (R : Subring D) (x : D) : Prop :=
  ∃ n : ℕ, ∃ p : Fin (n + 1) → R,
    p ⟨n, Nat.lt_succ_self n⟩ = 1 ∧
      ∑ i, (p i : D) * x ^ (i : ℕ) = 0

def chapter04DivisionMaximalIdeal
    {D : Type*} [Ring D] (w : D → WithTop ℚ) : Set D :=
  {x | w x > 0}

def chapter04IdealImage
    {D : Type*} [Ring D] (V : Subring D) (P : Ideal V) : Set D :=
  {x | ∃ y : V, y ∈ P ∧ (y : D) = x}

/- A valuation profile records the valuation ring, its maximal ideal, and the
  finite residue field without pretending that a skew-field valuation is an
  existing Mathlib `Valuation`. -/
structure Chapter04DivisionValuationInterface
    (K D k barD : Type*) [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [TopologicalSpace D] where
  value : D → WithTop ℚ
  unitValue : Dˣ → ℚ
  value_zero : value 0 = ⊤
  value_one : value 1 = 0
  value_unit : ∀ x : Dˣ, value (x : D) = (unitValue x : WithTop ℚ)
  value_add : ∀ x y : D, value (x + y) ≥ min (value x) (value y)
  value_strict_add : ∀ {x y : D}, value x < value y → value (x + y) = value x
  value_mul : ∀ x y : D, value (x * y) = value x + value y
  value_inv : ∀ x : Dˣ,
    value (x : D) + value ((x⁻¹ : Dˣ) : D) = 0
  valuationSubring : Subring D
  valuationSubring_eq : valuationSubring.carrier = {x | value x ≥ 0}
  maximalIdeal : Ideal valuationSubring
  maximalIdeal_eq :
    chapter04IdealImage valuationSubring maximalIdeal = {x | value x > 0}
  residueMap : valuationSubring →+* barD
  residue_surjective : Function.Surjective residueMap
  residue_eq_iff : ∀ x y : valuationSubring,
    residueMap x = residueMap y ↔ x - y ∈ maximalIdeal
  residue_finite : Finite barD
  valuationSubring_compact : IsCompact (valuationSubring.carrier : Set D)
  maximalIdeal_open : IsOpen (chapter04IdealImage valuationSubring maximalIdeal)

def chapter04ValueGroup
    {D : Type*} [Monoid D] (w : Dˣ → ℚ) : AddSubgroup ℚ :=
  AddSubgroup.closure (Set.range w)

def chapter04ValueGroupModInteger
    {D : Type*} [Monoid D] (w : Dˣ → ℚ) :
    AddSubgroup (chapter04ValueGroup w) :=
  AddSubgroup.comap (chapter04ValueGroup w).subtype
    (AddSubgroup.zmultiples (1 : ℚ))

def chapter04RamificationIndex
    {D : Type*} [Monoid D] (w : Dˣ → ℚ) : ℕ :=
  Nat.card (chapter04ValueGroup w ⧸ chapter04ValueGroupModInteger w)

def chapter04ResidueDegree
    (k barD : Type*) [Field k] [Field barD] [Algebra k barD]
    [FiniteDimensional k barD] : ℕ :=
  Module.finrank k barD

def chapter04FractionalValueLattice (d : ℕ) : AddSubgroup ℚ :=
  AddSubgroup.zmultiples ((1 : ℚ) / d)

def chapter04ValueGroupContainedInFractionalLattice
    {D : Type*} [Monoid D] (w : Dˣ → ℚ) (d : ℕ) : Prop :=
  ∀ x : Dˣ, w x ∈ chapter04FractionalValueLattice d

def chapter04IntegerValueLattice : AddSubgroup ℚ :=
  AddSubgroup.zmultiples (1 : ℚ)

/- The quotient-level local invariant interface. -/
structure Chapter04LocalInvariantData (K : Type*) [Field K] where
  brauerLaw : Chapter04BrauerGroupLaw K
  invariant : chapter04BrauerGroup K → chapter04RationalResidue
  invariant_injective : Function.Injective invariant
  invariant_surjective : Function.Surjective invariant
  invariant_tensor : ∀ a b,
    invariant (brauerLaw.tensor a b) = invariant a + invariant b
  invariant_opposite : ∀ a,
    invariant (brauerLaw.opposite a) = -invariant a

def chapter04InvariantOfRelativeClass
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (I : Chapter04LocalInvariantData K)
    (R : Chapter04BrauerRestrictionData K L)
    (a : chapter04RelativeBrauerGroup K L R) : chapter04RationalResidue :=
  I.invariant a.1

abbrev chapter04CoefficientRep
    (K L : Type) [CommRing K] [CommRing L] [Algebra K L] :=
  Rep.ofAlgebraAutOnUnits K L

abbrev chapter04H2
    (K L : Type) [Field K] [Field L] [Algebra K L] : ModuleCat ℤ :=
  groupCohomology (chapter04CoefficientRep K L) 2

/-- Normalized multiplicative two-cocycles for a Galois action. -/
structure Chapter04NormalizedTwoCocycle
    (G L : Type*) [Group G] [Field L] [MulSemiringAction G L]
    [MulAction G Lˣ] where
  value : G → G → Lˣ
  left_normalized : ∀ g, value 1 g = 1
  right_normalized : ∀ g, value g 1 = 1
  action_on_units_compatible : ∀ g x : Lˣ,
    g • (x : L) = (g • x : L)
  cocycle : ∀ g h k,
    value g h * value (g * h) k = (g • value h k) * value g (h * k)

abbrev chapter04CrossedProductCarrier
    (G L : Type*) [Group G] [AddCommGroup L] := G →₀ L

def chapter04CrossedProductScalar
    {G L : Type*} [Group G] [AddCommGroup L] (x : L) :
    chapter04CrossedProductCarrier G L :=
  Finsupp.single 1 x

def chapter04CrossedProductBasis
    {G L : Type*} [Group G] [AddCommGroup L] [One L] (g : G) :
    chapter04CrossedProductCarrier G L :=
  Finsupp.single g 1

def chapter04CrossedProductMul
    {G L : Type*} [Group G] [Field L] [MulSemiringAction G L]
    [MulAction G Lˣ] (c : Chapter04NormalizedTwoCocycle G L) :
    chapter04CrossedProductCarrier G L →
      chapter04CrossedProductCarrier G L →
        chapter04CrossedProductCarrier G L :=
  fun x y => x.sum fun g a => y.sum fun h b =>
    Finsupp.single (g * h) (a * (g • b) * (c.value g h : L))

def chapter04CocycleCohomologous
    {G L : Type*} [Group G] [Field L] [MulSemiringAction G L]
    [MulAction G Lˣ]
    (c₁ c₂ : Chapter04NormalizedTwoCocycle G L) : Prop :=
  ∃ b : G → Lˣ, ∀ g h,
    c₂.value g h = b g * (g • b h) * (b (g * h))⁻¹ * c₁.value g h

/- A two-sided inverse pair is used instead of a second quotient algebra in
  order to keep the cohomology/Brauer comparison independent of presentation. -/
structure Chapter04RelativeBrauerCohomologyData
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (R : Chapter04BrauerRestrictionData K L) where
  toRelative : chapter04H2 K L → chapter04RelativeBrauerGroup K L R
  fromRelative : chapter04RelativeBrauerGroup K L R → chapter04H2 K L
  left_inverse : Function.LeftInverse fromRelative toRelative
  right_inverse : Function.RightInverse fromRelative toRelative

end

end LastLib.Book05LocalClassFieldTheory.Chapter04
