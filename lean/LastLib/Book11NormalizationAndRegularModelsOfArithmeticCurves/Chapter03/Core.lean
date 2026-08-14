import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03.Dependencies

/-!
# Book 11, Chapter 3: Why normalization is finite

This file follows §§3.1–3.5 of the source chapter.  The algebraic predicates are kept explicit:
Japanese and Nagata conditions are not conflated with noetherianity, and excellence records its
three separate ingredients.  Proofs are intentionally postponed in this optimistic statement
pass, but canonical constructions such as `integralClosure`, generic fibers, formal fibers, and
trace-dual lattices use their pinned Mathlib definitions.
-/

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
open scoped AlgebraicGeometry BigOperators TensorProduct

noncomputable section

universe u v

/-! ## 3.1. Japanese and Nagata rings -/

/-
The integral closure used by the chapter is Mathlib's canonical subalgebra.  The source usually
works in a finite extension of a fraction field, while this definition deliberately keeps the
ambient algebra visible so that it also covers the componentwise reduced case.
-/

/-- The integral closure of `A` in an `A`-algebra `L`. -/
def chapter03IntegralClosure (A L : Type u) [CommRing A] [CommRing L] [Algebra A L] :
    Subalgebra A L :=
  integralClosure A L

/-- Finiteness of the normalization, expressed as module-finiteness of the integral closure. -/
def chapter03NormalizationFinite (A L : Type u) [CommRing A] [CommRing L] [Algebra A L] : Prop :=
  Module.Finite A (chapter03IntegralClosure A L)

/- The opening warning is kept separate from the normalization-specific examples in §3.5. -/
/-- An integral algebra can fail to be module-finite over its base. -/
structure Chapter03IntegralNonFiniteExample where
  A : Type u
  B : Type u
  [commRingA : CommRing A]
  [noetherianA : IsNoetherianRing A]
  [commRingB : CommRing B]
  [algebraAB : Algebra A B]
  integral : IsIntegralHom (algebraMap A B)
  not_finite : ¬ Module.Finite A B

def Chapter03IntegralNeedNotBeFinite : Prop :=
  Nonempty Chapter03IntegralNonFiniteExample

theorem chapter03_integral_need_not_be_finite :
    Chapter03IntegralNeedNotBeFinite := by
  sorry

/- The explicit `IsDomain` argument makes this property usable for prime quotients in the Nagata
  definition without manufacturing a global typeclass instance for every quotient. -/
/-- A domain is Japanese when every finite fraction-field extension has finite integral closure. -/
def Chapter03Japanese (A : Type u) [CommRing A] : Prop :=
  ∀ (hA : IsDomain A) (K L : Type u) [Field K] [Field L] [Algebra A K]
    [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L],
    Module.Finite A (chapter03IntegralClosure A L)

/-- The Chapter 1 Japanese class and the Chapter 3 proposition have the same content on domains. -/
theorem chapter03_japanese_iff_chapter11Japanese
    (A : Type u) [CommRing A] [IsDomain A] :
    Chapter03Japanese A ↔ Chapter11Japanese A := by
  sorry

/-- The canonical Chapter 1 Japanese witness gives the Chapter 3 formulation. -/
theorem chapter03_japanese_of_chapter11Japanese
    (A : Type u) [CommRing A] [IsDomain A]
    (hA : Chapter11Japanese A) : Chapter03Japanese A := by
  sorry

/-- A noetherian ring is Nagata when every prime quotient is Japanese. -/
def Chapter03NagataRing (A : Type u) [CommRing A] : Prop :=
  IsNoetherianRing A ∧
    ∀ (p : Ideal A), p.IsPrime → Chapter03Japanese (A ⧸ p)

theorem chapter03_nagataRing_iff_prime_quotients
    (A : Type u) [CommRing A] :
    Chapter03NagataRing A ↔
      IsNoetherianRing A ∧
        ∀ (p : Ideal A), p.IsPrime → Chapter03Japanese (A ⧸ p) := by
  rfl

/-- A scheme is Nagata when all affine coordinate rings are Nagata. -/
def Chapter03NagataScheme (X : Scheme.{u}) : Prop :=
  ∀ (U : X.Opens), IsAffineOpen U → Chapter03NagataRing Γ(X, U)

/-- The hypotheses of the finite normalization criterion, with all scheme predicates visible. -/
def Chapter03ReducedNoetherianNagata (X : Scheme.{u}) : Prop :=
  IsReduced X ∧ IsNoetherian X ∧ Chapter03NagataScheme X

theorem chapter03_reduced_noetherian_nagata_iff
    (X : Scheme.{u}) :
    Chapter03ReducedNoetherianNagata X ↔
      IsReduced X ∧ IsNoetherian X ∧ Chapter03NagataScheme X := by
  rfl

/- LOCAL_DEPENDENCY_GUESS: Chapters 1–2 of Book 11 supply a normalization map whose affine
   charts are the displayed integral-closure presentations.  This local interface is the
   weakest chapter-3 boundary needed to state the finiteness theorem while those files are absent
   from the drafting workspace. -/

/-- An affine chart of a normalization, with the ambient algebra and closure presentation exposed. -/
structure Chapter03AffineIntegralClosurePresentation (A : Type u) [CommRing A] where
  Q : Type u
  B : Type u
  [commRingQ : CommRing Q]
  [commRingB : CommRing B]
  [algebraAQ : Algebra A Q]
  [algebraAB : Algebra A B]
  [algebraBQ : Algebra B Q]
  [tower : IsScalarTower A B Q]
  closure : IsIntegralClosure B A Q

/-- A scheme whose local rings are normal domains. -/
def Chapter03NormalScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X,
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

/-- The affine-local normalization interface used by the scheme-level finiteness statements. -/
structure Chapter03NormalizationMap {X Y : Scheme.{u}} (ν : Y ⟶ X) : Prop where
  integral : IsIntegralHom ν
  normal : Chapter03NormalScheme Y
  affine_chart :
    ∀ (U : X.Opens) (hU : IsAffineOpen U),
      IsAffineOpen (ν ⁻¹ᵁ U) ∧
        ∃ (P : Chapter03AffineIntegralClosurePresentation Γ(X, U)),
          ∃ e : Γ(Y, ν ⁻¹ᵁ U) ≃+* P.B,
            ∀ a, e ((ν.app U).hom a) = algebraMap (Γ(X, U)) P.B a

/-- A finite Japanese normalization chart over a domain. -/
theorem chapter03_japanese_finite_integralClosure
    (A : Type u) [CommRing A] (hA : IsDomain A) (hJ : Chapter03Japanese A)
    (K L : Type u) [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] :
    Module.Finite A (chapter03IntegralClosure A L) := by
  exact hJ hA K L

/-- The domain case of the Japanese criterion in its canonical finite-extension presentation. -/
theorem chapter03_integralClosure_finite_of_nagata_domain
    (A : Type u) [CommRing A] [IsDomain A]
    (hA : Chapter03NagataRing A)
    (K L : Type u) [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] :
    Module.Finite A (chapter03IntegralClosure A L) := by
  sorry

/- The scheme statement is the componentwise form of the preceding ring argument. -/
/-- The normalization of a reduced noetherian Nagata scheme is finite. -/
theorem chapter03_normalization_finite_of_reduced_noetherian_nagata
    {X Y : Scheme.{u}} [IsReduced X] [IsNoetherian X]
    (hX : Chapter03NagataScheme X) (ν : Y ⟶ X)
    (hν : Chapter03NormalizationMap ν) :
    IsFinite ν := by
  sorry

/-- Componentwise normalization in a finite field extension is finite over a Nagata component. -/
theorem chapter03_component_normalization_finite_of_nagata
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hA : Chapter03NagataRing A) (K L : Type u) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] :
    Module.Finite A (chapter03IntegralClosure A L) := by
  sorry

/-! ## 3.2. Excellent rings -/

/- The following chain interface is an explicit book-facing encoding of catenarity.  Pinned
  Mathlib does not expose a catenary-ring predicate in the required form. -/

/-- A saturated finite chain of prime ideals between two specified points. -/
structure Chapter03SaturatedPrimeChain (A : Type u) [CommRing A]
    (p q : PrimeSpectrum A) where
  length : ℕ
  chain : Fin (length + 1) → PrimeSpectrum A
  first : chain 0 = p
  last : chain ⟨length, Nat.lt_succ_self length⟩ = q
  strict : ∀ i : Fin length, chain i.castSucc < chain i.succ
  saturated : ∀ i : Fin length,
    ¬ ∃ r : PrimeSpectrum A, chain i.castSucc < r ∧ r < chain i.succ

/-- A noetherian ring is catenary when saturated prime chains have a unique length. -/
def Chapter03Catenary (A : Type u) [CommRing A] : Prop :=
  ∀ (p q : PrimeSpectrum A), p ≤ q →
    ∀ (c d : Chapter03SaturatedPrimeChain A p q), c.length = d.length

/-- Universal catenarity, tested on finite-type algebras. -/
def Chapter03UniversallyCatenary (A : Type u) [CommRing A] : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    Chapter03Catenary B

/-- The formal fiber of `A` at `p`, namely the completed local ring tensored with its residue field. -/
def chapter03FormalFiber (A : Type u) [CommRing A] (p : PrimeSpectrum A) : Type u :=
  letI : p.asIdeal.IsPrime := p.isPrime
  p.asIdeal.ResidueField ⊗[Localization.AtPrime p.asIdeal]
    AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
      (Localization.AtPrime p.asIdeal)

/-- Geometric regularity of a `k`-algebra, tested after arbitrary field extensions. -/
def Chapter03GeometricallyRegularAlgebra
    (k B : Type u) [Field k] [CommRing B] [Algebra k B] : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K],
    IsRegularRing (B ⊗[k] K)

/-- All formal fibers are geometrically regular. -/
def Chapter03GeometricallyRegularFormalFibers (A : Type u) [CommRing A] : Prop :=
  ∀ p : PrimeSpectrum A,
    letI : p.asIdeal.IsPrime := p.isPrime
    Chapter03GeometricallyRegularAlgebra p.asIdeal.ResidueField
      (chapter03FormalFiber A p)

/-- The regular locus of an affine ring, as a subset of its prime spectrum. -/
def chapter03RegularLocus (B : Type u) [CommRing B] : Set (PrimeSpectrum B) :=
  {p | letI : p.asIdeal.IsPrime := p.isPrime
    IsRegularLocalRing (Localization.AtPrime p.asIdeal)}

/-- The `J₂` condition: regular loci of finite-type algebras are open. -/
def Chapter03JTwo (A : Type u) [CommRing A] : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    IsOpen (chapter03RegularLocus B)

/-- Excellence as universal catenarity, geometrically regular formal fibers, and `J₂`. -/
def Chapter03Excellent (A : Type u) [CommRing A] : Prop :=
  IsNoetherianRing A ∧
    Chapter03UniversallyCatenary A ∧
      Chapter03GeometricallyRegularFormalFibers A ∧ Chapter03JTwo A

/-- The quasi-excellent finiteness input used in the proof of the Nagata theorem. -/
def Chapter03QuasiExcellentDomain (A : Type u) [CommRing A] : Prop :=
  IsNoetherianRing A ∧ IsDomain A ∧
    Chapter03GeometricallyRegularFormalFibers A ∧ Chapter03JTwo A

theorem chapter03_excellent_iff_three_conditions
    (A : Type u) [CommRing A] :
    Chapter03Excellent A ↔
      IsNoetherianRing A ∧
        Chapter03UniversallyCatenary A ∧
          Chapter03GeometricallyRegularFormalFibers A ∧ Chapter03JTwo A := by
  rfl

/-- Excellent rings are Nagata. -/
theorem chapter03_excellent_is_nagata
    (A : Type u) [CommRing A] (hA : Chapter03Excellent A) :
    Chapter03NagataRing A := by
  sorry

/-- Localization preserves excellence. -/
theorem chapter03_localization_of_excellent_is_excellent
    (A : Type u) [CommRing A] (hA : Chapter03Excellent A) (S : Submonoid A) :
    Chapter03Excellent (Localization S) := by
  sorry

/-- Finite-type algebras over excellent rings are excellent. -/
theorem chapter03_finiteType_algebra_of_excellent_is_excellent
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (hA : Chapter03Excellent A) :
    Chapter03Excellent B := by
  sorry

/- A finite-type domain over an excellent ring satisfies the generic finite-normalization
  criterion after the appropriate fraction-field hypotheses are supplied. -/
theorem chapter03_excellent_finiteType_domain_is_nagata
    (A R : Type u) [CommRing A] [CommRing R] [Algebra R A]
    [Algebra.FiniteType R A] (hR : Chapter03Excellent R)
    (hA : IsDomain A) : Chapter03NagataRing A := by
  have h := chapter03_finiteType_algebra_of_excellent_is_excellent R A hR
  exact chapter03_excellent_is_nagata A h

/-- The normalization finiteness criterion used in the proof of excellence implies Nagata. -/
theorem chapter03_quasiExcellent_domain_normalization_finite
    (A : Type u) [CommRing A]
    (hA : Chapter03QuasiExcellentDomain A)
    (K L : Type u) [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] :
    Module.Finite A (chapter03IntegralClosure A L) := by
  sorry

/-- Complete noetherian local rings are excellent. -/
def Chapter03CompleteNoetherianLocalRing (A : Type u) [CommRing A] : Prop :=
  IsNoetherianRing A ∧ IsLocalRing A ∧
    IsAdicComplete (IsLocalRing.maximalIdeal A) A

theorem chapter03_complete_noetherian_local_is_excellent
    (A : Type u) [CommRing A]
    (hA : Chapter03CompleteNoetherianLocalRing A) :
    Chapter03Excellent A := by
  sorry

/-- Fields are excellent. -/
theorem chapter03_field_is_excellent
    (K : Type u) [Field K] : Chapter03Excellent K := by
  sorry

/-- The ring of integers in a number field is finite over the integers. -/
theorem chapter03_ringOfIntegers_finite
    (K : Type u) [Field K] [Algebra ℚ K] [Algebra ℤ K]
    [FiniteDimensional ℚ K] :
    Module.Finite ℤ (integralClosure ℤ K) := by
  sorry

/-- A localization of the ring of integers of a number field, packaged by the canonical closure. -/
structure Chapter03LocalizedRingOfIntegers (A : Type u) [CommRing A] where
  K : Type u
  [fieldK : Field K]
  [algebraQK : Algebra ℚ K]
  [algebraZK : Algebra ℤ K]
  [finiteK : FiniteDimensional ℚ K]
  S : Submonoid (integralClosure ℤ K)
  equivalence : Localization S ≃+* A

/-- Localizations of rings of integers of number fields are excellent. -/
theorem chapter03_localized_numberField_integer_is_excellent
    (A : Type u) [CommRing A]
    (hA : Chapter03LocalizedRingOfIntegers A) :
    Chapter03Excellent A := by
  sorry

/-! ## 3.3. The one-dimensional proof -/

/-- A finite extension of the fraction field of a domain, with all scalar towers explicit. -/
structure Chapter03FiniteFractionFieldExtension
    (A : Type u) [CommRing A] [IsDomain A] where
  K : Type u
  L : Type u
  [fieldK : Field K]
  [fieldL : Field L]
  [algebraAK : Algebra A K]
  [fractionK : IsFractionRing A K]
  [algebraKL : Algebra K L]
  [algebraAL : Algebra A L]
  [tower : IsScalarTower A K L]
  [finite : FiniteDimensional K L]

/-- The finite intermediate algebra obtained by clearing denominators from a field basis. -/
structure Chapter03FiniteIntegralModel {A : Type u} [CommRing A] [IsDomain A]
    (E : Chapter03FiniteFractionFieldExtension A) where
  B₀ : Subalgebra A E.L
  finite : Module.Finite A B₀
  fraction : IsFractionRing B₀ E.L

/-- The normalized ring attached to a finite fraction-field extension. -/
def chapter03NormalizedRing {A : Type u} [CommRing A] [IsDomain A]
    (E : Chapter03FiniteFractionFieldExtension A) : Subalgebra A E.L :=
  integralClosure A E.L

/-- Clearing denominators produces a finite `A`-subalgebra with the prescribed fraction field. -/
theorem chapter03_exists_finite_integral_model
    (A : Type u) [CommRing A] [IsDomain A]
    (E : Chapter03FiniteFractionFieldExtension A) :
    Nonempty (Chapter03FiniteIntegralModel E) := by
  sorry

/-- The ring-theoretic one-dimensional excellent hypothesis. -/
def Chapter03OneDimensionalExcellentDomain (A : Type u) [CommRing A] : Prop :=
  Chapter03Excellent A ∧ IsDomain A ∧ ringKrullDim A = 1

/-- The normalization of an excellent one-dimensional domain in a finite extension is finite. -/
theorem chapter03_oneDimensional_normalization_finite
    (A : Type u) [CommRing A] [IsDomain A]
    (hA : Chapter03OneDimensionalExcellentDomain A)
    (E : Chapter03FiniteFractionFieldExtension A) :
    Module.Finite A (chapter03NormalizedRing E) := by
  sorry

/-- A finite semilocal normal one-dimensional algebra, with finiteness over its base recorded. -/
def Chapter03FiniteSemilocalNormalOneDimensionalAlgebra
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  Module.Finite A B ∧ IsNoetherianRing B ∧ chapter11IsSemilocal B ∧
    IsDomain B ∧ IsIntegrallyClosed B ∧ ringKrullDim B = 1

/-- The localization of a one-dimensional normalization at a nonzero prime is semilocal and normal. -/
theorem chapter03_localized_normalization_is_semilocal_normal_oneDimensional
    (A B L : Type u) [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Field L] [IsDedekindDomain A]
    [Algebra A B] [Algebra A L] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (hfinite : Module.Finite A B) (p : Ideal A) (hp : p.IsPrime) (hp0 : p ≠ ⊥) :
    Chapter03FiniteSemilocalNormalOneDimensionalAlgebra
      (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)) := by
  sorry

/-- Every maximal local factor of a finite semilocal normal one-dimensional algebra is a DVR. -/
theorem chapter03_finite_semilocal_normal_oneDimensional_local_factor_isDVR
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (hB : Chapter03FiniteSemilocalNormalOneDimensionalAlgebra A B)
    (q : Ideal B) [hq : q.IsPrime] (hqmax : q.IsMaximal) :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  sorry

/-- A noetherian normal local domain of dimension one is a discrete valuation ring. -/
theorem chapter03_normal_noetherian_local_dim_one_isDVR
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain R] (hnormal : IsIntegrallyClosed R)
    (hdim : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  exact LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.chapter01_normal_oneDimensional_local_isDVR
    hnormal hdim

/-- A finite separable extension of a Dedekind domain has finite Dedekind normalization. -/
theorem chapter03_excellent_dedekind_separable_normalization_is_dedekind
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (hA : Chapter03Excellent A)
    (K L : Type u) [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsDedekindDomain (integralClosure A L) ∧
      Module.Finite A (integralClosure A L) := by
  sorry

/-- A finite field extension admits a basis whose elements are integral over the base domain. -/
structure Chapter03IntegralBasis
    (A K L : Type u) [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] [IsFractionRing A K]
    [IsScalarTower A K L] [FiniteDimensional K L] where
  ι : Type v
  [finiteIndex : Fintype ι]
  basis : Basis ι K L
  integral_basis : ∀ i, IsIntegral A (basis i)

theorem chapter03_exists_integral_basis
    (A K L : Type u) [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] [IsFractionRing A K]
    [IsScalarTower A K L] [FiniteDimensional K L] :
    Nonempty (Chapter03IntegralBasis A K L) := by
  sorry

/-- The trace-dual fractional lattice generated by a finite trace-dual basis. -/
def chapter03TraceDualLattice
    (A K L : Type u) [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    {ι : Type v} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Submodule A L :=
  Submodule.span A (Set.range <| (Algebra.traceForm K L).dualBasis
    (traceForm_nondegenerate K L) b)

/-- An integral element has integral trace after multiplication by an integral basis element. -/
theorem chapter03_trace_of_integral_is_integral
    (A K L : Type u) [CommRing A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [FiniteDimensional K L]
    (x y : L) (hxy : IsIntegral A (x * y)) :
    IsIntegral A (Algebra.trace K L (x * y)) := by
  sorry

/-- For an integrally closed base, the integral trace actually comes from the base ring. -/
theorem chapter03_trace_of_integral_mem_base
    (A K L : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsFractionRing A K] [IsScalarTower A K L] [FiniteDimensional K L]
    (x y : L) (hxy : IsIntegral A (x * y)) :
    ∃ a : A, algebraMap A K a = Algebra.trace K L (x * y) := by
  sorry

/-- The integral closure is contained in the finite trace-dual lattice. -/
theorem chapter03_integralClosure_le_traceDualLattice
    (A K L : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsFractionRing A K] [IsScalarTower A K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] {ι : Type v} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) (hb : ∀ i, IsIntegral A (b i)) :
    Subalgebra.toSubmodule (integralClosure A L) ≤
      chapter03TraceDualLattice A K L b := by
  exact integralClosure_le_span_dualBasis A K L b hb

/-- The trace-dual lattice is a finite `A`-module. -/
theorem chapter03_traceDualLattice_finite
    (A K L : Type u) [CommRing A] [IsNoetherianRing A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] {ι : Type v} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) :
    Module.Finite A (chapter03TraceDualLattice A K L b) := by
  sorry

/-- The trace-dual lattice is the finite free fractional module used in the trace proof. -/
theorem chapter03_traceDualLattice_free
    (A K L : Type u) [CommRing A] [IsDomain A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsFractionRing A K] [IsScalarTower A K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] {ι : Type v} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) :
    Module.Free A (chapter03TraceDualLattice A K L b) := by
  sorry

/-- The trace-dual proof of finiteness for a separable normalization. -/
theorem chapter03_trace_argument_normalization_finite
    (A K L : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsNoetherianRing A] [Field K] [Field L] [Algebra A K] [Algebra A L]
    [Algebra K L] [IsFractionRing A K] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Module.Finite A (integralClosure A L) := by
  sorry

/-- Every Dedekind domain has finite normalization in a finite separable extension. -/
theorem chapter03_dedekind_is_japanese_for_separable_extensions
    (A K L : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsFractionRing A K] [IsScalarTower A K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] :
    Module.Finite A (integralClosure A L) := by
  sorry

/-- Trace-dual expansion of an element in a separable finite extension. -/
theorem chapter03_trace_dual_expansion
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type v} [Fintype ι] [DecidableEq ι] (b : Basis ι K L) (x : L) :
    x = ∑ i, Algebra.trace K L (x * b i) • b.traceDual i := by
  sorry

/-- The trace form is nondegenerate exactly in the separable case. -/
theorem chapter03_trace_form_nondegenerate_iff_separable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    (Algebra.traceForm K L).Nondegenerate ↔ Algebra.IsSeparable K L := by
  exact (traceForm_nondegenerate_tfae K L).out 2 0

/-- The trace form degenerates in the inseparable case, so the trace-dual proof cannot be used. -/
theorem chapter03_trace_form_degenerate_of_inseparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hsep : ¬ Algebra.IsSeparable K L) :
    ¬ (Algebra.traceForm K L).Nondegenerate := by
  intro h
  exact hsep (chapter03_trace_form_nondegenerate_iff_separable K L).mp h

/-! ## 3.4. The two-dimensional cases used here -/

/-- The generic fiber of a finite-type algebra over a domain. -/
def chapter03GenericFiber
    (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] : Type u :=
  A ⊗[R] FractionRing R

/-- The generic fiber has dimension one. -/
def Chapter03GenericFiberDimensionOne
    (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] : Prop :=
  ringKrullDim (chapter03GenericFiber R A) = 1

/-- Dominance of an affine algebra over its base, in spectrum language. -/
def Chapter03DominatesBase
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : Prop :=
  Function.Surjective (PrimeSpectrum.comap (algebraMap R A))

/-- The dimension bound for a finite-type domain over an excellent Dedekind domain. -/
theorem chapter03_finiteType_domain_over_excellent_dedekind_dim_le_two
    (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.FiniteType R A]
    (hR : Chapter03Excellent R) (hDedekind : IsDedekindDomain R)
    (hgeneric : Chapter03GenericFiberDimensionOne R A) :
    ringKrullDim A ≤ 2 := by
  sorry

/-- Dominance of the affine chart forces dimension exactly two. -/
theorem chapter03_finiteType_domain_over_excellent_dedekind_dim_eq_two_of_dominant
    (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.FiniteType R A]
    (hR : Chapter03Excellent R) (hDedekind : IsDedekindDomain R)
    (hgeneric : Chapter03GenericFiberDimensionOne R A)
    (hdominant : Chapter03DominatesBase R A) :
    ringKrullDim A = 2 := by
  sorry

/-- The finite-type arithmetic-surface chart is excellent and therefore Nagata. -/
theorem chapter03_finiteType_domain_over_excellent_dedekind_is_excellent
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (hR : Chapter03Excellent R)
    (hA : IsDomain A) : Chapter03Excellent A := by
  exact chapter03_finiteType_algebra_of_excellent_is_excellent R A hR

/-- Normalization in every finite extension of the fraction field of an arithmetic-surface chart
is finite. -/
theorem chapter03_arithmetic_surface_chart_normalization_finite
    (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.FiniteType R A]
    (hR : Chapter03Excellent R) (hDedekind : IsDedekindDomain R)
    (E : Chapter03FiniteFractionFieldExtension A) :
    Module.Finite A (chapter03NormalizedRing E) := by
  sorry

/-- An excellent Dedekind scheme is expressed by its affine coordinate rings. -/
def Chapter03ExcellentDedekindScheme (S : Scheme.{u}) : Prop :=
  IsNoetherian S ∧
    ∀ U : S.affineOpens, IsDedekindDomain Γ(S, U) ∧ Chapter03Excellent Γ(S, U)

/-- A finite-type morphism, with the quasi-compactness component made explicit. -/
def Chapter03FiniteTypeMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  QuasiCompact f ∧ LocallyOfFiniteType f

/-- A reduced finite-type scheme over a base. -/
def Chapter03ReducedFiniteTypeMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  IsReduced X ∧ Chapter03FiniteTypeMorphism f

/-- A two-dimensional scheme, using Mathlib's topological Krull dimension. -/
def Chapter03TwoDimensionalScheme (X : Scheme.{u}) : Prop :=
  topologicalKrullDim X = 2

/-- A surface chart with dimension at most two. -/
def Chapter03SurfaceDimensionBound (X : Scheme.{u}) : Prop :=
  topologicalKrullDim X ≤ 2

theorem chapter03_twoDimensionalScheme_implies_surfaceDimensionBound
    (X : Scheme.{u}) (hX : Chapter03TwoDimensionalScheme X) :
    Chapter03SurfaceDimensionBound X := by
  sorry

/-- The normalization of a reduced finite-type scheme over an excellent Dedekind scheme is finite. -/
theorem chapter03_normalization_finite_over_excellent_dedekind
    {X S Y : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter03ExcellentDedekindScheme S)
    (hf : Chapter03ReducedFiniteTypeMorphism f)
    (ν : Y ⟶ X) (hν : Chapter03NormalizationMap ν) :
    IsFinite ν := by
  sorry

/-- Finite scheme morphisms are projective in the book-facing projectivity API. -/
theorem chapter03_finite_morphism_is_projective
    {X Y : Scheme.{u}} (ν : Y ⟶ X) (hν : IsFinite ν) :
    Chapter08IsProjective ν := by
  sorry

/-- A finite morphism followed by a proper morphism is proper. -/
theorem chapter03_finite_comp_proper
    {X Y S : Scheme.{u}} (ν : Y ⟶ X) (f : X ⟶ S)
    (hν : IsFinite ν) (hf : IsProper f) : IsProper (ν ≫ f) := by
  sorry

/-- A finite normalization over a proper model is proper over the base. -/
theorem chapter03_normalization_proper_over_base
    {X S Y : Scheme.{u}} (f : X ⟶ S) (ν : Y ⟶ X)
    (hν : IsFinite ν) (hf : IsProper f) : IsProper (ν ≫ f) := by
  exact chapter03_finite_comp_proper ν f hν hf

/-- Projectivity is preserved by composing the finite normalization with a projective model. -/
theorem chapter03_normalization_projective_over_base
    {X S Y : Scheme.{u}} (f : X ⟶ S) (ν : Y ⟶ X)
    (hν : IsFinite ν) (hf : Chapter08IsProjective f) :
    Chapter08IsProjective (ν ≫ f) := by
  sorry

/-- The two-dimensional finite-type theorem over a field. -/
theorem chapter03_two_dimensional_normalization_finite_over_field
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Scheme.Spec (.of k))
    (hX : Chapter03ReducedFiniteTypeMorphism f)
    (hdim : Chapter03SurfaceDimensionBound X)
    (ν : Y ⟶ X) (hν : Chapter03NormalizationMap ν) :
    IsFinite ν := by
  sorry

/-- The two-dimensional finite-type theorem over a complete noetherian local ring. -/
theorem chapter03_two_dimensional_normalization_finite_over_complete_local
    (R : Type u) [CommRing R] (hR : Chapter03CompleteNoetherianLocalRing R)
    {X Y : Scheme.{u}} (f : X ⟶ Scheme.Spec (.of R))
    (hX : Chapter03ReducedFiniteTypeMorphism f)
    (hdim : Chapter03SurfaceDimensionBound X)
    (ν : Y ⟶ X) (hν : Chapter03NormalizationMap ν) :
    IsFinite ν := by
  sorry

/-! ## 3.5. What fails without finiteness hypotheses -/

/-- A noetherian one-dimensional domain, packaged for counterexample statements. -/
structure Chapter03NoetherianOneDimensionalDomain where
  carrier : Type u
  [commRing : CommRing carrier]
  [domain : IsDomain carrier]
  [noetherian : IsNoetherianRing carrier]
  dimension_one : ringKrullDim carrier = 1

/-- Existence of a noetherian one-dimensional domain that is not Japanese. -/
def Chapter03NoetherianNonJapaneseDomainExists : Prop :=
  ∃ A : Chapter03NoetherianOneDimensionalDomain, ¬ Chapter03Japanese A.carrier

theorem chapter03_noetherian_does_not_imply_japanese :
    Chapter03NoetherianNonJapaneseDomainExists := by
  sorry

/-- The canonical normalization algebra is integral over its base. -/
theorem chapter03_normalizedRing_is_integral
    (A : Type u) [CommRing A] [IsDomain A]
    (E : Chapter03FiniteFractionFieldExtension A) :
    IsIntegralHom (algebraMap A (chapter03NormalizedRing E)) := by
  sorry

/-- Existence of a finite field extension with non-finite integral closure over a noetherian domain. -/
def Chapter03NonFiniteNormalizationExample : Prop :=
  ∃ A : Chapter03NoetherianOneDimensionalDomain,
    ∃ E : Chapter03FiniteFractionFieldExtension A.carrier,
      ¬ Module.Finite A.carrier (chapter03NormalizedRing E) ∧
        ¬ Algebra.FiniteType A.carrier (chapter03NormalizedRing E)

theorem chapter03_noetherian_normalization_need_not_be_finite :
    Chapter03NonFiniteNormalizationExample := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the preceding Chapter 2 API should eventually provide the canonical
   comparison between normalization after base change and base change after normalization. -/

/-- The two competing normalization constructions in a base-change comparison. -/
structure Chapter03NormalizationBaseChangeComparison where
  X T : Scheme.{u}
  baseChange : T ⟶ X
  normalizedBaseChange : Scheme.{u}
  baseChangedNormalization : Scheme.{u}
  normalizedBaseChange_to_T : normalizedBaseChange ⟶ T
  normalizedBaseChange_is_normalization :
    Chapter03NormalizationMap normalizedBaseChange_to_T
  baseChangedNormalization_to_T : baseChangedNormalization ⟶ T
  comparison : normalizedBaseChange ⟶ baseChangedNormalization
  comparison_compatibility :
    comparison ≫ baseChangedNormalization_to_T = normalizedBaseChange_to_T
  comparison_is_not_an_iso : ¬ IsIso comparison

/-- The normalization/base-change warning has a witness in the general, unrestricted setting. -/
def Chapter03NormalizationNeedNotCommuteWithBaseChange : Prop :=
  Nonempty (Chapter03NormalizationBaseChangeComparison)

theorem chapter03_normalization_need_not_commute_with_base_change :
    Chapter03NormalizationNeedNotCommuteWithBaseChange := by
  sorry

/-- A regular scheme in the stalkwise sense used to state the resolution warning. -/
def Chapter03RegularScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

/-- An excellent surface, expressed affine-locally. -/
def Chapter03ExcellentSurface (X : Scheme.{u}) : Prop :=
  IsNoetherian X ∧ Chapter03TwoDimensionalScheme X ∧
    ∀ U : X.affineOpens, Chapter03Excellent Γ(X, U)

/-- Normalization resolves singularities when its source is regular. -/
def Chapter03NormalizationResolvesSingularities
    {X Y : Scheme.{u}} (ν : Y ⟶ X) : Prop :=
  Chapter03RegularScheme Y

/-- Even an excellent surface can have a singular normalization. -/
def Chapter03ExcellentSurfaceNormalizationNeedNotResolve : Prop :=
  ∃ (X Y : Scheme.{u}) (ν : Y ⟶ X),
    Chapter03ExcellentSurface X ∧
      Chapter03NormalizationMap ν ∧
        ¬ Chapter03NormalizationResolvesSingularities ν

theorem chapter03_excellent_surface_normalization_need_not_be_regular :
    Chapter03ExcellentSurfaceNormalizationNeedNotResolve := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
