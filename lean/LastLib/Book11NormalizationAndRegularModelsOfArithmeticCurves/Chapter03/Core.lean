import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Section02TheHierarchyOfHypotheses

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
open Module
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08
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
  integral : Algebra.IsIntegral A B
  not_finite : ¬ Module.Finite A B

def Chapter03IntegralNeedNotBeFinite : Prop :=
  Nonempty (Chapter03IntegralNonFiniteExample.{u})

theorem chapter03_integral_need_not_be_finite :
    Chapter03IntegralNeedNotBeFinite := by
  classical
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  refine ⟨{ A := ULift (ZMod 2), B := ℕ → ULift (ZMod 2), integral := ?_, not_finite := ?_ }⟩
  · constructor
    intro x
    refine ⟨Polynomial.X ^ 2 - Polynomial.X,
      Polynomial.monic_X_pow_sub (p := Polynomial.X) (by
        rw [Polynomial.degree_X]
        norm_num), ?_⟩
    ext i
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Pi.sub_apply, Pi.pow_apply]
    change (x i).down ^ 2 - (x i).down = 0
    rw [ZMod.pow_card]
    exact sub_self _
  · intro hfinite
    have : Module.Finite (ULift (ZMod 2)) (ℕ → ULift (ZMod 2)) := hfinite
    have : Finite (ℕ → ULift (ZMod 2)) := Module.finite_of_finite (ULift (ZMod 2))
    exact (not_finite_iff_infinite.mpr
      (inferInstance : Infinite (ℕ → ULift (ZMod 2)))) inferInstance

/- The explicit `IsDomain` argument makes this property usable for prime quotients in the Nagata
  definition without manufacturing a global typeclass instance for every quotient. -/
/-- A domain is Japanese when every finite fraction-field extension has finite integral closure. -/
def Chapter03Japanese (A : Type u) [CommRing A] : Prop :=
  IsDomain A ∧
    ∀ (_hA : IsDomain A) (K L : Type u) [Field K] [Field L] [Algebra A K]
      [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
      [FiniteDimensional K L],
      Module.Finite A (chapter03IntegralClosure A L)

/-- The Chapter 1 Japanese class and the Chapter 3 proposition have the same content on domains. -/
theorem chapter03_japanese_iff_chapter11Japanese
    (A : Type u) [CommRing A] [IsDomain A] :
    Chapter03Japanese A ↔ Chapter11Japanese A := by
  constructor
  · intro h
    exact { finite_integral_closure := h.2 inferInstance }
  · intro h
    exact ⟨inferInstance, fun _hA => h.finite_integral_closure⟩

/-- The canonical Chapter 1 Japanese witness gives the Chapter 3 formulation. -/
theorem chapter03_japanese_of_chapter11Japanese
    (A : Type u) [CommRing A] [IsDomain A]
    (hA : Chapter11Japanese A) : Chapter03Japanese A := by
  exact ⟨inferInstance, fun _hA => hA.finite_integral_closure⟩

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

/- The pinned normalization API supplies the canonical constructions.  This local interface
   records the finite ambient algebra needed by the componentwise Nagata argument, whose reduced
   affine charts are more general than a single integral scheme. -/

/-- A finite reduced ambient algebra over a total fraction ring, allowing both absolute and
componentwise finite-field-extension normalizations. -/
structure Chapter03FiniteFractionAlgebra
    (A Q : Type u) [CommRing A] [CommRing Q] [Algebra A Q] where
  T : Type u
  [commRingT : CommRing T]
  [algebraAT : Algebra A T]
  [algebraTQ : Algebra T Q]
  [tower : IsScalarTower A T Q]
  [reducedQ : IsReduced Q]
  fraction : IsFractionRing A T
  finite : Module.Finite T Q

attribute [instance] Chapter03FiniteFractionAlgebra.commRingT
  Chapter03FiniteFractionAlgebra.algebraAT
  Chapter03FiniteFractionAlgebra.algebraTQ
  Chapter03FiniteFractionAlgebra.tower

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
  ambient_injective : Function.Injective (algebraMap B Q)
  finite_extension : Chapter03FiniteFractionAlgebra A Q
  closure : IsIntegralClosure B A Q

attribute [instance] Chapter03AffineIntegralClosurePresentation.commRingQ
  Chapter03AffineIntegralClosurePresentation.commRingB
  Chapter03AffineIntegralClosurePresentation.algebraAQ
  Chapter03AffineIntegralClosurePresentation.algebraAB
  Chapter03AffineIntegralClosurePresentation.algebraBQ
  Chapter03AffineIntegralClosurePresentation.tower

/-- A scheme whose local rings are normal domains. -/
def Chapter03NormalScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X,
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

/-- The affine-local normalization interface used by the scheme-level finiteness statements. -/
structure Chapter03NormalizationMap {X Y : Scheme.{u}} (ν : Y ⟶ X) : Prop where
  integral : IsIntegralHom ν
  dominant : IsDominant ν
  normal : Chapter03NormalScheme Y
  affine_chart :
    ∀ (U : X.Opens) (_hU : IsAffineOpen U),
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
  exact hJ.2 hA K L

/-- The domain case of the Japanese criterion in its canonical finite-extension presentation. -/
theorem chapter03_integralClosure_finite_of_nagata_domain
    (A : Type u) [CommRing A] [IsDomain A]
    (hA : Chapter03NagataRing A)
    (K L : Type u) [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] :
    Module.Finite A (chapter03IntegralClosure A L) := by
  classical
  let φ : (A ⧸ (⊥ : Ideal A)) ≃+* A := RingEquiv.quotientBot A
  let : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  let : Algebra (A ⧸ (⊥ : Ideal A)) K :=
    ((algebraMap A K).comp φ.toRingHom).toAlgebra
  let : Algebra (A ⧸ (⊥ : Ideal A)) L :=
    ((algebraMap A L).comp φ.toRingHom).toAlgebra
  let : IsScalarTower (A ⧸ (⊥ : Ideal A)) K L :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change algebraMap A L (φ x) =
        algebraMap K L (algebraMap A K (φ x))
      exact IsScalarTower.algebraMap_apply A K L (φ x))
  let : IsFractionRing (A ⧸ (⊥ : Ideal A)) K :=
    IsFractionRing.of_ringEquiv_left φ (by
      intro x
      rfl)
  have hJ := hA.2 (⊥ : Ideal A) Ideal.isPrime_bot
  have hfiniteQ : Module.Finite (A ⧸ (⊥ : Ideal A))
      (integralClosure (A ⧸ (⊥ : Ideal A)) L) :=
    hJ.2 inferInstance K L
  have hcompat :
      (algebraMap A L).comp φ.toRingHom =
        algebraMap (A ⧸ (⊥ : Ideal A)) L := by
    ext x
    rfl
  have hmem (x : L) :
      x ∈ integralClosure (A ⧸ (⊥ : Ideal A)) L ↔ x ∈ integralClosure A L := by
    simpa only [mem_integralClosure_iff] using
      RingEquiv.isIntegral_iff φ hcompat x
  let : Algebra A (integralClosure (A ⧸ (⊥ : Ideal A)) L) :=
    Algebra.compHom (integralClosure (A ⧸ (⊥ : Ideal A)) L)
      (algebraMap A (A ⧸ (⊥ : Ideal A)))
  let : IsScalarTower A (A ⧸ (⊥ : Ideal A))
      (integralClosure (A ⧸ (⊥ : Ideal A)) L) :=
    IsScalarTower.of_compHom A (A ⧸ (⊥ : Ideal A))
      (integralClosure (A ⧸ (⊥ : Ideal A)) L)
  let : Module.Finite (A ⧸ (⊥ : Ideal A))
      (integralClosure (A ⧸ (⊥ : Ideal A)) L) := hfiniteQ
  have hfiniteA :
      Module.Finite A (integralClosure (A ⧸ (⊥ : Ideal A)) L) := by
    exact Module.Finite.trans (A ⧸ (⊥ : Ideal A))
      (integralClosure (A ⧸ (⊥ : Ideal A)) L)
  let : Module.Finite A (integralClosure (A ⧸ (⊥ : Ideal A)) L) := hfiniteA
  let f : integralClosure (A ⧸ (⊥ : Ideal A)) L →ₗ[A] integralClosure A L :=
    { toFun := fun x => ⟨x.1, (hmem x.1).mp x.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        rfl
      map_smul' := by
        intro c x
        apply Subtype.ext
        simp [Algebra.compHom_smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
          φ, RingEquiv.quotientBot_mk] }
  exact Module.Finite.of_surjective f (by
    intro y
    refine ⟨⟨y.1, (hmem y.1).mpr y.2⟩, ?_⟩
    rfl)

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
    (A : Type u) [CommRing A] [IsDomain A]
    (hA : Chapter03NagataRing A) (K L : Type u) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] :
    Module.Finite A (chapter03IntegralClosure A L) := by
  exact chapter03_integralClosure_finite_of_nagata_domain A hA K L

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
  IsNoetherianRing A ∧
    ∀ (p q : PrimeSpectrum A), p ≤ q →
      ∀ (c d : Chapter03SaturatedPrimeChain A p q), c.length = d.length

/-- Universal catenarity, tested on finite-type algebras. -/
def Chapter03UniversallyCatenary (A : Type u) [CommRing A] : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    , Chapter03Catenary B

/-- The formal fiber of `A` at `p`, namely the completed local ring tensored with its residue field. -/
abbrev chapter03FormalFiber (A : Type u) [CommRing A] (p : PrimeSpectrum A) : Type u :=
  letI : p.asIdeal.IsPrime := p.isPrime
  IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal) ⊗[Localization.AtPrime p.asIdeal]
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
    Chapter03GeometricallyRegularAlgebra (IsLocalRing.ResidueField
      (Localization.AtPrime p.asIdeal))
      (chapter03FormalFiber A p)

/-- The regular locus of an affine ring, as a subset of its prime spectrum. -/
def chapter03RegularLocus (B : Type u) [CommRing B] : Set (PrimeSpectrum B) :=
  {p | letI : p.asIdeal.IsPrime := p.isPrime
    IsRegularLocalRing (Localization.AtPrime p.asIdeal)}

/-- The `J₂` condition: regular loci of finite-type algebras are open. -/
def Chapter03JTwo (A : Type u) [CommRing A] : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    , IsOpen (chapter03RegularLocus B)

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
  let hE : LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Chapter01ExcellentRing A :=
    { noetherian := hA.1
      universallyCatenary := by
        intro B _ _ _ p q hp c d
        let c' : Chapter03SaturatedPrimeChain B p q :=
          { length := c.length
            chain := c.chain
            first := c.first
            last := c.last
            strict := c.strict
            saturated := c.saturated }
        let d' : Chapter03SaturatedPrimeChain B p q :=
          { length := d.length
            chain := d.chain
            first := d.first
            last := d.last
            strict := d.strict
            saturated := d.saturated }
        exact (hA.2.1 B).2 p q hp c' d'
      geometricallyRegularFormalFibers := hA.2.2.1
      regularLocusOpen := hA.2.2.2 }
  have hN :=
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.chapter01_excellent_is_nagata A hE
  refine ⟨hN.noetherian, ?_⟩
  intro p hp
  let : p.IsPrime := hp
  exact ⟨inferInstance, fun _hA => (hN.japanese_quotient p).finite_integral_closure⟩

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
    : Chapter03NagataRing A := by
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
  ∃ hlocal : IsLocalRing A,
    letI : IsLocalRing A := hlocal
    IsNoetherianRing A ∧ IsAdicComplete (IsLocalRing.maximalIdeal A) A

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
    [IsScalarTower ℤ ℚ K]
    [FiniteDimensional ℚ K] :
    Module.Finite ℤ (integralClosure ℤ K) := by
  let htower' : @IsScalarTower ℤ ℚ K
      (inferInstance : Algebra ℤ ℚ).toSMul
      (inferInstance : Algebra ℚ K).toSMul
      (inferInstance : Algebra ℤ K).toSMul :=
    IsScalarTower.of_algebraMap_eq (R := ℤ) (S := ℚ) (A := K) (fun z => by simp)
  let : @IsScalarTower ℤ ℚ K
      (inferInstance : Algebra ℤ ℚ).toSMul
      (inferInstance : Algebra ℚ K).toSMul
      (inferInstance : Algebra ℤ K).toSMul := htower'
  let : Semiring ℤ := (inferInstance : CommRing ℤ).toCommSemiring.toSemiring
  let : AddCommMonoid (integralClosure ℤ K) :=
    (inferInstance : CommRing (integralClosure ℤ K)).toCommSemiring.toAddCommMonoid
  let : Module ℤ (integralClosure ℤ K) :=
    (inferInstance : Algebra ℤ (integralClosure ℤ K)).toModule
  let sourceSemiring : Semiring ℤ :=
    inferInstance
  let sourceAddCommMonoid : AddCommMonoid (integralClosure ℤ K) := inferInstance
  let sourceModule : Module ℤ (integralClosure ℤ K) := inferInstance
  have hfinite := IsIntegralClosure.finite ℤ ℚ K (integralClosure ℤ K)
  rcases Submodule.fg_def.mp hfinite.fg_top with ⟨S, hSfinite, hS⟩
  let P : @Submodule ℤ (integralClosure ℤ K)
      sourceSemiring sourceAddCommMonoid sourceModule :=
    @Submodule.span ℤ (integralClosure ℤ K)
      sourceSemiring sourceAddCommMonoid sourceModule S
  change P = ⊤ at hS
  let : Semiring ℤ := Int.instSemiring
  let : AddCommMonoid (integralClosure ℤ K) :=
    (inferInstance : AddCommGroup (integralClosure ℤ K)).toAddCommMonoid
  let : Module ℤ (integralClosure ℤ K) :=
    (inferInstance : AddCommGroup (integralClosure ℤ K)).toIntModule
  refine Module.Finite.of_fg_top ?_
  rw [Submodule.fg_def]
  refine ⟨S, hSfinite, ?_⟩
  let Q : Submodule ℤ (integralClosure ℤ K) :=
    Submodule.span ℤ (S : Set (integralClosure ℤ K))
  change Q = ⊤
  apply top_unique
  intro x _hx
  have hx' : x ∈ P := by
    rw [hS]
    trivial
  exact @Submodule.span_induction ℤ (integralClosure ℤ K)
    sourceSemiring sourceAddCommMonoid sourceModule S
    (p := fun y _ => y ∈ Q) (x := x)
    (fun y hy => by
      exact @Submodule.subset_span ℤ (integralClosure ℤ K)
        Int.instSemiring (inferInstance : AddCommMonoid (integralClosure ℤ K))
        (inferInstance : Module ℤ (integralClosure ℤ K)) S y hy)
    (by exact Q.zero_mem)
    (fun y z _ _ hy hz => Q.add_mem hy hz)
    (fun a y _ hy => by
      change sourceModule.smul a y ∈ Q
      rw [int_smul_eq_zsmul sourceModule a y]
      exact Q.smul_mem a hy)
    hx'

/-- A localization of the ring of integers of a number field, packaged by the canonical closure. -/
structure Chapter03LocalizedRingOfIntegers (A : Type u) [CommRing A] where
  K : Type u
  [fieldK : Field K]
  [algebraQK : Algebra ℚ K]
  [algebraZK : Algebra ℤ K]
  [tower : IsScalarTower ℤ ℚ K]
  [finiteK : FiniteDimensional ℚ K]
  S : Submonoid (integralClosure ℤ K)
  equivalence : Localization S ≃+* A

attribute [instance] Chapter03LocalizedRingOfIntegers.fieldK
  Chapter03LocalizedRingOfIntegers.algebraQK
  Chapter03LocalizedRingOfIntegers.algebraZK
  Chapter03LocalizedRingOfIntegers.tower
  Chapter03LocalizedRingOfIntegers.finiteK

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

attribute [instance] Chapter03FiniteFractionFieldExtension.fieldK
  Chapter03FiniteFractionFieldExtension.fieldL
  Chapter03FiniteFractionFieldExtension.algebraAK
  Chapter03FiniteFractionFieldExtension.fractionK
  Chapter03FiniteFractionFieldExtension.algebraKL
  Chapter03FiniteFractionFieldExtension.algebraAL
  Chapter03FiniteFractionFieldExtension.tower
  Chapter03FiniteFractionFieldExtension.finite

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
  classical
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A E.K E.L
  let B₀ : Subalgebra A E.L := Algebra.adjoin A (Set.range b)
  have hfinite : Module.Finite A B₀ :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range b) (by
      rintro x ⟨i, rfl⟩
      exact hb i)
  have common_denominator :
      ∀ (t : Finset s) (f : s → E.K),
        ∃ (a : s → A) (d : nonZeroDivisors A),
          ∀ i ∈ t, f i * algebraMap A E.K d = algebraMap A E.K (a i) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro f
        refine ⟨fun _ => 0, 1, ?_⟩
        simp
    | @insert i t hi ih =>
        intro f
        obtain ⟨a, d, ha⟩ := ih f
        obtain ⟨⟨ai, c⟩, hc⟩ := IsLocalization.surj (nonZeroDivisors A) (f i)
        refine ⟨fun j => if j = i then ai * (d : A) else a j * (c : A), d * c, ?_⟩
        intro j hj
        by_cases hji : j = i
        · have hnew : f i * algebraMap A E.K (d * c) =
              algebraMap A E.K (ai * (d : A)) := by
            calc
              f i * algebraMap A E.K (d * c) =
                  (f i * algebraMap A E.K c) * algebraMap A E.K d := by
                    simp [map_mul, mul_comm, mul_left_comm]
              _ = algebraMap A E.K ai * algebraMap A E.K d :=
                congrArg (fun x => x * algebraMap A E.K d) hc
              _ = algebraMap A E.K (ai * (d : A)) := by simp
          simpa [hji] using hnew
        · have hjt : j ∈ t := (Finset.mem_insert.mp hj).resolve_left hji
          have hold : f j * algebraMap A E.K (d * c) =
              algebraMap A E.K (a j * (c : A)) := by
            calc
              f j * algebraMap A E.K (d * c) =
                  (f j * algebraMap A E.K d) * algebraMap A E.K c := by
                    simp [map_mul, mul_comm, mul_left_comm]
              _ = algebraMap A E.K (a j) * algebraMap A E.K c :=
                congrArg (fun x => x * algebraMap A E.K c) (ha j hjt)
              _ = algebraMap A E.K (a j * (c : A)) := by simp
          simpa [hji] using hold
  have hAL : Function.Injective (algebraMap A E.L) := by
    intro x y hxy
    apply IsFractionRing.injective A E.K
    apply FaithfulSMul.algebraMap_injective E.K E.L
    simpa only [IsScalarTower.algebraMap_apply A E.K E.L] using hxy
  let M : Submonoid B₀ := Algebra.algebraMapSubmonoid B₀ (nonZeroDivisors A)
  have hloc : IsLocalization M E.L := by
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    · rintro ⟨x, hx⟩
      rcases hx with ⟨a, ha, rfl⟩
      apply isUnit_iff_ne_zero.mpr
      change algebraMap A E.L (a : A) ≠ 0
      exact (map_ne_zero_iff _ hAL).mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp ha)
    · intro z
      obtain ⟨a, d, ha⟩ := common_denominator Finset.univ (fun i => b.repr z i)
      have hsum :
          (∑ i, algebraMap A E.L (a i) • b i) ∈ B₀ := by
        apply B₀.sum_mem
        intro i hi
        simpa only [Algebra.smul_def, Algebra.algebraMap_self_apply] using
          B₀.smul_mem (Algebra.subset_adjoin ⟨i, rfl⟩) (a i)
      let x : B₀ := ⟨∑ i, algebraMap A E.L (a i) • b i, hsum⟩
      let m : M := ⟨algebraMap A B₀ d, Algebra.mem_algebraMapSubmonoid_of_mem d⟩
      refine ⟨⟨x, m⟩, ?_⟩
      change z * algebraMap A E.L (d : A) =
        ∑ i, algebraMap A E.L (a i) • b i
      have hcoeff (i : s) :
          algebraMap A E.L (a i) =
            algebraMap E.K E.L (b.repr z i) * algebraMap A E.L (d : A) := by
        have hi := ha i (Finset.mem_univ i)
        have hi' := congrArg (algebraMap E.K E.L) hi
        simpa only [map_mul, IsScalarTower.algebraMap_apply A E.K E.L] using hi'.symm
      calc
        z * algebraMap A E.L (d : A) =
            (∑ i, b.repr z i • b i) * algebraMap A E.L (d : A) := by
              rw [b.sum_repr]
        _ = ∑ i, (b.repr z i • b i) * algebraMap A E.L (d : A) := by
              rw [Finset.sum_mul]
        _ = ∑ i, algebraMap A E.L (a i) • b i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Algebra.smul_def, Algebra.smul_def, hcoeff]
          simp [mul_assoc, mul_comm]
    · intro x y hxy
      have hxy' : x = y := by exact Subtype.ext hxy
      exact ⟨1, by simp [hxy']⟩
  let : IsLocalization M E.L := hloc
  have hfrac : IsFractionRing B₀ E.L := by
    apply IsLocalization.of_le M (nonZeroDivisors B₀)
    · intro r hr
      rcases hr with ⟨a, ha, rfl⟩
      apply mem_nonZeroDivisors_iff_ne_zero.mpr
      intro h
      apply (mem_nonZeroDivisors_iff_ne_zero.mp ha)
      apply hAL
      simpa only [map_zero, IsScalarTower.algebraMap_apply A B₀ E.L] using
        congrArg (algebraMap B₀ E.L) h
    · intro r hr
      apply isUnit_iff_ne_zero.mpr
      change (r : E.L) ≠ 0
      intro h
      exact (mem_nonZeroDivisors_iff_ne_zero.mp hr) (Subtype.ext h)
  exact ⟨{ B₀ := B₀, finite := hfinite, fraction := hfrac }⟩

/-- The ring-theoretic one-dimensional excellent hypothesis. -/
def Chapter03OneDimensionalExcellentDomain (A : Type u) [CommRing A] : Prop :=
  Chapter03Excellent A ∧ IsDomain A ∧ ringKrullDim A = 1

/-- The normalization of an excellent one-dimensional domain in a finite extension is finite. -/
theorem chapter03_oneDimensional_normalization_finite
    (A : Type u) [CommRing A] [IsDomain A]
    (hA : Chapter03OneDimensionalExcellentDomain A)
    (E : Chapter03FiniteFractionFieldExtension A) :
    Module.Finite A (chapter03NormalizedRing E) := by
  exact chapter03_integralClosure_finite_of_nagata_domain A
    (chapter03_excellent_is_nagata A hA.1) E.K E.L

/-- A finite semilocal normal one-dimensional algebra, with finiteness over its base recorded. -/
def Chapter03FiniteSemilocalNormalOneDimensionalAlgebra
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  Module.Finite A B ∧ IsNoetherianRing B ∧ chapter11IsSemilocal B ∧
    IsDomain B ∧ IsIntegrallyClosed B ∧ ringKrullDim B = 1

/-- The localization of a finite fraction-field normalization at a nonzero prime is semilocal and normal. -/
theorem chapter03_localized_normalization_is_semilocal_normal_oneDimensional
    (A B K L : Type u) [CommRing A] [CommRing B]
    [IsDomain B] [Field K] [Field L] [IsDedekindDomain A]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A B] [Algebra A L] [Algebra B L] [IsScalarTower A K L]
    [IsScalarTower A B L] [FiniteDimensional K L]
    [IsIntegralClosure B A L]
    (hfinite : Module.Finite A B) (p : Ideal A) (hp : p.IsPrime) (hp0 : p ≠ ⊥) :
    Chapter03FiniteSemilocalNormalOneDimensionalAlgebra
      (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)) := by
  classical
  let : p.IsPrime := hp
  let : p.IsMaximal := hp.isMaximal hp0
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  let : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have hBic : IsIntegrallyClosed B := by
    rw [isIntegrallyClosed_iff_isIntegralClosure (K := L)]
    refine ⟨IsIntegralClosure.algebraMap_injective B A L, ?_⟩
    intro x
    constructor
    · intro hx
      exact (inferInstance : IsIntegralClosure B A L).isIntegral_iff.mp
        (isIntegral_trans (R := A) x hx)
    · rintro ⟨b, rfl⟩
      exact isIntegral_algebraMap
  have hBded : IsDedekindDomain B := by
    refine (isDedekindDomain_iff (A := B) L).2
      ⟨inferInstance, inferInstance, Ring.DimensionLEOne.of_isIntegral A B, ?_⟩
    intro x hx
    exact (isIntegrallyClosed_iff L).mp hBic hx
  let : IsIntegrallyClosed B := hBic
  let : IsDedekindDomain B := hBded
  have hABinj : Function.Injective (algebraMap A B) := by
    intro a b hab
    apply IsFractionRing.injective A K
    apply FaithfulSMul.algebraMap_injective K L
    rw [← IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply A K L]
    simpa only [IsScalarTower.algebraMap_apply A B L] using
      congrArg (algebraMap B L) hab
  let : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hABinj
  let : IsTorsionFree A B := inferInstance
  have hM :
      Algebra.algebraMapSubmonoid B p.primeCompl ≤ nonZeroDivisors B := by
    rintro x ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr <| map_ne_zero_of_mem_nonZeroDivisors
      (algebraMap A B) hABinj (p.primeCompl_le_nonZeroDivisors ha)
  let : IsDomain (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  let : IsDedekindDomain (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)) :=
    IsLocalization.isDedekindDomain B hM _
  let : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hp0 _
  let : IsLocalization (Submonoid.map (algebraMap A B) p.primeCompl)
      (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)) := by
    simpa only [Algebra.algebraMapSubmonoid] using
      (Localization.isLocalization :
        IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl)
          (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)))
  have hAinj : Function.Injective
      (algebraMap (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid B p.primeCompl))) := by
    change Function.Injective
      (IsLocalization.map (Localization (Algebra.algebraMapSubmonoid B p.primeCompl))
        (algebraMap A B) p.primeCompl.le_comap_map)
    exact IsLocalization.map_injective_of_injective p.primeCompl
      (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)) hABinj
  let : FaithfulSMul (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hAinj
  let m : Ideal (Localization.AtPrime p) := IsLocalRing.maximalIdeal _
  let : m.IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  let : m.IsPrime := inferInstance
  have hm0 : m ≠ (⊥ : Ideal (Localization.AtPrime p)) := by
    dsimp [m]
    exact IsDiscreteValuationRing.not_a_field _
  let : Fintype (m.primesOver (Localization (Algebra.algebraMapSubmonoid B p.primeCompl))) :=
    Set.Finite.fintype (Algebra.QuasiFinite.finite_primesOver m)
  have hmaxiff :
      ∀ P : Ideal (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)),
        P.IsMaximal ↔ P.IsPrime ∧ P.LiesOver m := by
    intro P
    constructor
    · intro hP
      let : P.IsMaximal := hP
      have hcomp :
          P.comap (algebraMap (Localization.AtPrime p)
            (Localization (Algebra.algebraMapSubmonoid B p.primeCompl))) = m :=
        IsLocalRing.eq_maximalIdeal
          (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)
      exact ⟨hP.isPrime, ⟨by simpa [m] using hcomp.symm⟩⟩
    · rintro ⟨hPprime, hPover⟩
      let : P.IsPrime := hPprime
      let : P.LiesOver m := hPover
      exact hPprime.isMaximal
        (Ideal.ne_bot_of_liesOver_of_ne_bot hm0 P)
  refine ⟨inferInstance, inferInstance, ?_, inferInstance, inferInstance, ?_⟩
  · change ∃ s : Finset (Ideal (Localization (Algebra.algebraMapSubmonoid B p.primeCompl))),
      ∀ P : Ideal (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)),
        P.IsMaximal ↔
          P ∈ (s : Set (Ideal (Localization (Algebra.algebraMapSubmonoid B p.primeCompl))))
    let s : Finset (Ideal (Localization (Algebra.algebraMapSubmonoid B p.primeCompl))) :=
      Finset.univ.image (fun q : m.primesOver
        (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)) => (q : Ideal _))
    refine ⟨s, ?_⟩
    intro P
    constructor
    · intro hP
      refine Finset.mem_image.mpr
        ⟨⟨P, ⟨hP.isPrime, (hmaxiff P).mp hP |>.2⟩⟩,
          Finset.mem_univ _, rfl⟩
    · intro hP
      rcases Finset.mem_image.mp hP with ⟨q, -, rfl⟩
      exact (hmaxiff q.1).mpr ⟨q.2.1, q.2.2⟩
  · have hnotfield :
        ¬ IsField (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)) := by
      intro hfield
      let : Field (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)) := hfield.toField
      obtain ⟨Q, hQmax, hQover⟩ :=
        Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S :=
          Localization (Algebra.algebraMapSubmonoid B p.primeCompl)) m
      let : Q.LiesOver m := hQover
      have hQne : Q ≠ (⊥ : Ideal (Localization (Algebra.algebraMapSubmonoid B p.primeCompl))) :=
        Ideal.ne_bot_of_liesOver_of_ne_bot hm0 Q
      exact hQne ((eq_bot_or_eq_top Q).resolve_right hQmax.ne_top)
    refine eq_of_le_of_not_lt
      (Ring.krullDimLE_iff.mp
        (inferInstance : Ring.KrullDimLE 1
          (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)))) ?_
    intro hlt
    have hzero : Ring.KrullDimLE 0
        (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)) :=
      Ring.krullDimLE_iff.mpr (ENat.WithBot.lt_add_one_iff.mp hlt)
    exact hnotfield Ring.KrullDimLE.isField_of_isDomain

/-- Every maximal local factor of a finite semilocal normal one-dimensional algebra is a DVR. -/
theorem chapter03_finite_semilocal_normal_oneDimensional_local_factor_isDVR
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (hB : Chapter03FiniteSemilocalNormalOneDimensionalAlgebra A B)
    (q : Ideal B) [hq : q.IsPrime] (hqmax : q.IsMaximal) :
    letI : IsDomain B := hB.2.2.2.1
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  classical
  let : IsDomain B := hB.2.2.2.1
  let : IsNoetherianRing B := hB.2.1
  let : IsIntegrallyClosed B := hB.2.2.2.2.1
  have hnotfield : ¬ IsField B := by
    intro hfield
    have hdim0 : ringKrullDim B = 0 := ringKrullDim_eq_zero_of_isField hfield
    rw [hB.2.2.2.2.2] at hdim0
    exact one_ne_zero hdim0
  have hqbot : q ≠ (⊥ : Ideal B) :=
    Ring.ne_bot_of_isMaximal_of_not_isField hqmax hnotfield
  have hheight_ne : q.height ≠ 0 := by
    intro hzero
    apply hqbot
    exact (Ideal.height_eq_zero_iff_eq_bot.mp hzero)
  have hheight : q.height = 1 := by
    apply le_antisymm
    · simpa [hB.2.2.2.2.2] using
        (Ideal.height_le_ringKrullDim_of_isPrime (I := q))
    · exact (Order.one_le_iff_ne_zero.mpr hheight_ne)
  let : IsLocalRing (Localization.AtPrime q) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime q) q
  let : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl (Localization.AtPrime q) inferInstance
  let hnormal : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q)
      q.primeCompl q.primeCompl_le_nonZeroDivisors
  exact LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.chapter01_normal_oneDimensional_local_isDVR
    hnormal (by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
      simp [hheight])

/-- A noetherian normal local domain of dimension one is a discrete valuation ring. -/
theorem chapter03_normal_noetherian_local_dim_one_isDVR
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain R] (hnormal : IsIntegrallyClosed R)
    (hdim : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  exact LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.chapter01_normal_oneDimensional_local_isDVR
    hnormal hdim

/-- A finite separable extension of a Dedekind domain has finite Dedekind normalization. -/
theorem chapter03_excellent_dedekind_separable_normalization_is_dedekind
    (A : Type u) [CommRing A] [IsDedekindDomain A]
    (hA : Chapter03Excellent A)
    (K L : Type u) [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsDedekindDomain (integralClosure A L) ∧
      Module.Finite A (integralClosure A L) := by
  have _ := hA
  exact ⟨integralClosure.isDedekindDomain A K L,
    IsIntegralClosure.finite A K L (integralClosure A L)⟩

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
  classical
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let e : (s : Type u) ≃ ULift (Fin (Fintype.card (s : Type u))) :=
    (Fintype.equivFin (s : Type u)).trans Equiv.ulift.symm
  exact ⟨{
    ι := ULift (Fin (Fintype.card (s : Type u)))
    basis := b.reindex e
    integral_basis := by
      intro i
      rw [Basis.reindex_apply]
      exact hb (e.symm i)
  }⟩

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
    (A K L : Type u) [CommRing A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [FiniteDimensional K L]
    (x y : L) (hxy : IsIntegral A (x * y)) :
    IsIntegral A (Algebra.trace K L (x * y)) := by
  exact Algebra.isIntegral_trace (R := A) (L := K) (F := L) hxy

/-- For an integrally closed base, the integral trace actually comes from the base ring. -/
theorem chapter03_trace_of_integral_mem_base
    (A K L : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsFractionRing A K] [IsScalarTower A K L] [FiniteDimensional K L]
    (x y : L) (hxy : IsIntegral A (x * y)) :
    ∃ a : A, algebraMap A K a = Algebra.trace K L (x * y) := by
  exact (IsIntegrallyClosed.isIntegral_iff (R := A)).mp
    (chapter03_trace_of_integral_is_integral A K L x y hxy)

/-- The integral closure is contained in the finite trace-dual lattice. -/
theorem chapter03_integralClosure_le_traceDualLattice
    (A K L : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsFractionRing A K] [IsScalarTower A K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] {ι : Type v} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) (hb : ∀ i, IsIntegral A (b i)) :
    Subalgebra.toSubmodule (integralClosure A L) ≤
      chapter03TraceDualLattice A K L b := by
  exact integralClosure_le_span_dualBasis b hb

/-- The trace-dual lattice is a finite `A`-module. -/
theorem chapter03_traceDualLattice_finite
    (A K L : Type u) [CommRing A] [IsNoetherianRing A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] {ι : Type v} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) :
    Module.Finite A (chapter03TraceDualLattice A K L b) := by
  change Module.Finite A (Submodule.span A (Set.range b.traceDual))
  exact Module.Finite.span_of_finite A (Set.finite_range b.traceDual)

/-- The trace-dual lattice is the finite free fractional module used in the trace proof. -/
theorem chapter03_traceDualLattice_free
    (A K L : Type u) [CommRing A] [IsDomain A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsFractionRing A K] [IsScalarTower A K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] {ι : Type v} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) :
    Module.Free A (chapter03TraceDualLattice A K L b) := by
  change Module.Free A (Submodule.span A (Set.range b.traceDual))
  exact Module.Free.of_basis (Module.Basis.span
    ((LinearIndependent.iff_fractionRing A K).mpr b.traceDual.linearIndependent))

/-- The trace-dual proof of finiteness for a separable normalization. -/
theorem chapter03_trace_argument_normalization_finite
    (A K L : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsNoetherianRing A] [Field K] [Field L] [Algebra A K] [Algebra A L]
    [Algebra K L] [IsFractionRing A K] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Module.Finite A (integralClosure A L) := by
  exact IsIntegralClosure.finite A K L (integralClosure A L)

/-- Every Dedekind domain has finite normalization in a finite separable extension. -/
theorem chapter03_dedekind_is_japanese_for_separable_extensions
    (A K L : Type u) [CommRing A] [IsDedekindDomain A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] :
    Module.Finite A (integralClosure A L) := by
  exact IsIntegralClosure.finite A K L (integralClosure A L)

/-- Trace-dual expansion of an element in a separable finite extension. -/
theorem chapter03_trace_dual_expansion
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type v} [Fintype ι] [DecidableEq ι] (b : Basis ι K L) (x : L) :
    x = ∑ i, Algebra.trace K L (x * b i) • b.traceDual i := by
  symm
  simpa only [Basis.traceDual_repr_apply, Algebra.traceForm_apply] using b.traceDual.sum_repr x

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
  intro hnondeg
  exact hsep ((chapter03_trace_form_nondegenerate_iff_separable K L).mp hnondeg)

/-! ## 3.4. The two-dimensional cases used here -/

/-- The generic fiber of a finite-type algebra over a domain. -/
abbrev chapter03GenericFiber
    (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] : Type u :=
  A ⊗[R] FractionRing R

/-- The generic fiber has dimension one. -/
def Chapter03GenericFiberDimensionOne
    (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] : Prop :=
  ringKrullDim (chapter03GenericFiber R A) = 1

/-- Dominance of an affine algebra over its base, in spectrum language. -/
def Chapter03DominatesBase
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : Prop :=
  DenseRange (PrimeSpectrum.comap (algebraMap R A))

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
    (hdimR : ringKrullDim R = 1)
    (hgeneric : Chapter03GenericFiberDimensionOne R A)
    (hdominant : Chapter03DominatesBase R A) :
    ringKrullDim A = 2 := by
  sorry

/-- The finite-type arithmetic-surface chart is excellent and therefore Nagata. -/
theorem chapter03_finiteType_domain_over_excellent_dedekind_is_excellent
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (hR : Chapter03Excellent R)
    (_hA : IsDomain A) : Chapter03Excellent A := by
  exact chapter03_finiteType_algebra_of_excellent_is_excellent R A hR

/-- Normalization in every finite extension of the fraction field of an arithmetic-surface chart
is finite. -/
theorem chapter03_arithmetic_surface_chart_normalization_finite
    (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.FiniteType R A]
    (hR : Chapter03Excellent R) (hDedekind : IsDedekindDomain R)
    (E : Chapter03FiniteFractionFieldExtension A) :
    Module.Finite A (chapter03NormalizedRing E) := by
  have _ := hDedekind
  exact chapter03_integralClosure_finite_of_nagata_domain A
    (chapter03_excellent_finiteType_domain_is_nagata A R hR) E.K E.L

/-- An excellent Dedekind scheme is expressed by its affine coordinate rings. -/
def Chapter03ExcellentDedekindScheme (S : Scheme.{u}) : Prop :=
  IsNoetherian S ∧
    _root_.IsConnected (Set.univ : Set S) ∧
      topologicalKrullDim S = (1 : WithBot ℕ∞) ∧
        ∀ U : S.affineOpens, (U : S.Opens) ≠ ⊥ →
          IsDedekindDomain Γ(S, U) ∧ Chapter03Excellent Γ(S, U)

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
  change topologicalKrullDim X ≤ 2
  change topologicalKrullDim X = 2 at hX
  exact hX.le

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
  let : IsFinite ν := hν
  let : IsProper f := hf
  exact IsProper.stableUnderComposition.comp_mem _ _ inferInstance inferInstance

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
    (f : X ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))
    (hX : Chapter03ReducedFiniteTypeMorphism f)
    (hdim : Chapter03SurfaceDimensionBound X)
    (ν : Y ⟶ X) (hν : Chapter03NormalizationMap ν) :
    IsFinite ν := by
  sorry

/-- The two-dimensional finite-type theorem over a complete noetherian local ring. -/
theorem chapter03_two_dimensional_normalization_finite_over_complete_local
    (R : Type u) [CommRing R] (hR : Chapter03CompleteNoetherianLocalRing R)
    {X Y : Scheme.{u}} (f : X ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of R)))
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

attribute [instance] Chapter03NoetherianOneDimensionalDomain.commRing
  Chapter03NoetherianOneDimensionalDomain.domain
  Chapter03NoetherianOneDimensionalDomain.noetherian

/-- Existence of a noetherian one-dimensional domain that is not Japanese. -/
def Chapter03NoetherianNonJapaneseDomainExists : Prop :=
  ∃ A : Chapter03NoetherianOneDimensionalDomain.{u}, ¬ Chapter03Japanese A.carrier

theorem chapter03_noetherian_does_not_imply_japanese :
    Chapter03NoetherianNonJapaneseDomainExists := by
  sorry

/-- The canonical normalization algebra is integral over its base. -/
theorem chapter03_normalizedRing_is_integral
    (A : Type u) [CommRing A] [IsDomain A]
    (E : Chapter03FiniteFractionFieldExtension A) :
    Algebra.IsIntegral A (chapter03NormalizedRing E) := by
  change Algebra.IsIntegral A (integralClosure A E.L)
  exact ⟨fun x => integralClosure.isIntegral x⟩

/-- Existence of a finite field extension with non-finite integral closure over a noetherian domain. -/
def Chapter03NonFiniteNormalizationExample : Prop :=
  ∃ A : Chapter03NoetherianOneDimensionalDomain.{u},
    ∃ E : Chapter03FiniteFractionFieldExtension.{u} A.carrier,
      ¬ Module.Finite A.carrier (chapter03NormalizedRing E) ∧
        ¬ Algebra.FiniteType A.carrier (chapter03NormalizedRing E)

theorem chapter03_noetherian_normalization_need_not_be_finite :
    Chapter03NonFiniteNormalizationExample := by
  sorry

/- The pinned normalization API provides the canonical comparison between normalization after base
   change and base change after normalization. -/

/-- A finite normalization whose canonical base-change comparison is not an isomorphism. -/
structure Chapter03NormalizationBaseChangeComparison where
  X : Scheme.{u}
  S : Scheme.{u}
  Y : Scheme.{u}
  normalization_source : X ⟶ S
  baseChange : Y ⟶ S
  [quasiCompact : QuasiCompact normalization_source]
  [quasiSeparated : QuasiSeparated normalization_source]
  normalization_finite : IsFinite normalization_source.fromNormalization
  comparison_is_not_an_iso :
    ¬ IsIso (normalization_source.normalizationPullback baseChange)

attribute [instance] Chapter03NormalizationBaseChangeComparison.quasiCompact
  Chapter03NormalizationBaseChangeComparison.quasiSeparated

/-- The normalization/base-change warning has a witness in the general, unrestricted setting. -/
def Chapter03NormalizationNeedNotCommuteWithBaseChange : Prop :=
  Nonempty (Chapter03NormalizationBaseChangeComparison.{u})

theorem chapter03_normalization_need_not_commute_with_base_change :
    Chapter03NormalizationNeedNotCommuteWithBaseChange := by
  sorry

/-- A regular scheme in the stalkwise sense used to state the resolution warning. -/
def Chapter03RegularScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

/-- An excellent surface, expressed affine-locally. -/
def Chapter03ExcellentSurface (X : Scheme.{u}) : Prop :=
  IsReduced X ∧ IsNoetherian X ∧ Chapter03TwoDimensionalScheme X ∧
    ∀ U : X.affineOpens, Chapter03Excellent Γ(X, U)

/-- Normalization resolves singularities when its source is regular. -/
def Chapter03NormalizationResolvesSingularities
    {X Y : Scheme.{u}} (_ν : Y ⟶ X) : Prop :=
  Chapter03RegularScheme Y

/-- Even an excellent surface can have a singular normalization. -/
def Chapter03ExcellentSurfaceNormalizationNeedNotResolve : Prop :=
  ∃ (X Y : Scheme.{u}) (ν : Y ⟶ X),
    Chapter03ExcellentSurface X ∧
      Chapter03NormalizationMap ν ∧
        IsFinite ν ∧
        ¬ Chapter03NormalizationResolvesSingularities ν

theorem chapter03_excellent_surface_normalization_need_not_be_regular :
    Chapter03ExcellentSurfaceNormalizationNeedNotResolve := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
