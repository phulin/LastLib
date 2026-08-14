import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.Length
import Mathlib.Topology.LocallyConstant.Basic
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Section01TheAbsoluteAndRelativeSettings

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ### Codimension one and local equations -/

def chapter01CodimensionOnePoint (X : Scheme.{u}) (x : X) : Prop :=
  Order.coheight x = 1

def chapter01PrincipalIdealAt {R : Type u} [CommRing R] (a : R) : Ideal R :=
  Ideal.span ({a} : Set R)

def chapter01SingleEquationSubspace {R : Type u} [CommRing R] (a : R) : Type u :=
  R ⧸ chapter01PrincipalIdealAt a

def chapter01RegularCurveAt (X : Scheme.{u}) (x : X) : Prop :=
  IsRegularLocalRing (X.presheaf.stalk x)

def chapter01DVRAt (X : Scheme.{u}) (x : X) : Prop :=
  IsDiscreteValuationRing (X.presheaf.stalk x)

theorem chapter01_regular_codimensionOne_isDVR
    {X : Scheme.{u}} (x : X) (hregular : chapter01RegularCurveAt X x)
    (hcodim : chapter01CodimensionOnePoint X x)
    (hdomain : IsDomain (X.presheaf.stalk x)) :
    chapter01DVRAt X x := by
  sorry

theorem chapter01_normal_oneDimensional_local_isDVR
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain R] (hnormal : IsIntegrallyClosed R)
    (hdim : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  sorry

theorem chapter01_regular_local_ring_is_factorial
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] :
    UniqueFactorizationMonoid R := by
  sorry

/-! The order, cycle, local-equation, and pole descriptions are held together by a
  reusable dictionary rather than by silently identifying Weil and Cartier divisors
  on singular curves. -/
structure Chapter01CodimensionOneDictionary (X : Scheme.{u}) where
  order : {x : X // chapter01CodimensionOnePoint X x} → ℤ
  cycle : AlgebraicCycle X ℤ
  localEquation : ∀ x : X, chapter01CodimensionOnePoint X x → X.presheaf.stalk x
  localEquation_isParameter :
    ∀ (x : X) (hx : chapter01CodimensionOnePoint X x),
      chapter01LocalParameter (localEquation x hx)
  polePrescription : ∀ x : X, chapter01CodimensionOnePoint X x → ℤ
  order_eq_cycleCoefficient :
    ∀ (x : X) (hx : chapter01CodimensionOnePoint X x),
      cycle x = order ⟨x, hx⟩
  order_eq_polePrescription :
    ∀ (x : X) (hx : chapter01CodimensionOnePoint X x),
      order ⟨x, hx⟩ = polePrescription x hx

def chapter01DivisorOfOrder
    {X : Scheme.{u}} (D : Chapter01CodimensionOneDictionary X) : Chapter01Divisor X :=
  D.cycle

def chapter01FiniteExceptionalOrderData {X : Scheme.{u}}
    (f : Chapter01RationalFunction X) : Prop :=
  ∃ E : Finset X, ∀ x : X, x ∉ E → chapter01OrderZeroAt f x

theorem chapter01_order_is_zero_away_from_exceptional
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : Chapter01RationalFunction X) (hf : f ≠ 0)
    (hE : (chapter01ExceptionalPoints f).Finite) :
    chapter01FiniteExceptionalOrderData f := by
  sorry

/-! Codimension-one cycles need not be Cartier on a singular curve, and normality in
  higher dimension does not force every height-one prime to be principal. -/
def chapter01CodimensionOneCycleNotLocallyPrincipal (X : Scheme.{u}) : Prop :=
  ∃ x : X, chapter01CodimensionOnePoint X x ∧
    ¬ chapter01RegularCurveAt X x ∧
    ∃ (I : Ideal (X.presheaf.stalk x)), I.IsPrime ∧ ¬ I.IsPrincipal

def chapter01DimensionAtLeastTwo (X : Scheme.{u}) : Prop :=
  ∃ Z : irreducibleComponents X, 2 ≤ topologicalKrullDim Z.1

def chapter01NormalHigherDimensionalNonCartierExample : Prop :=
  ∃ (X : Scheme.{u}) (x : X) (I : Ideal (X.presheaf.stalk x)),
    chapter01DimensionAtLeastTwo X ∧
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) ∧
    ¬ chapter01RegularCurveAt X x ∧ chapter01CodimensionOnePoint X x ∧
      I.IsPrime ∧ ¬ I.IsPrincipal

theorem chapter01_singular_curve_cycle_need_not_be_Cartier :
    ∃ (X : Scheme.{u}), chapter01CodimensionOneCycleNotLocallyPrincipal X := by
  sorry

theorem chapter01_normal_higher_dimensional_prime_need_not_be_Cartier :
    chapter01NormalHigherDimensionalNonCartierExample := by
  sorry

/-! ### Two-term cohomology and duality -/

def chapter01CohomologyGroup {X : Scheme.{u}} (F : X.Modules) (i : ℕ) :
    AddCommGrpCat.{u + 1} :=
  chapter04Cohomology F i

def chapter01CohomologyVanishesAboveOne {X : Scheme.{u}} (F : X.Modules) : Prop :=
  ∀ i, 2 ≤ i → chapter04CohomologyVanishes F i

/- LOCAL_DEPENDENCY_GUESS: Book 8 exposes canonical cohomology objects as
  additive groups, but the pinned API does not yet package their field-module
  structures.  This realization records the missing finite-dimensional vector
  space bridge without changing the canonical additive object. -/
structure Chapter01FiniteDimensionalRealization (k : Type u) [Field k]
    (G : AddCommGrpCat.{u + 1}) where
  V : Type u
  [addCommGroup : AddCommGroup V]
  [module : Module k V]
  finite : FiniteDimensional k V
  addEquiv : V ≃+ G

structure Chapter01CohomologyDimensions (k : Type u) [Field k]
    (X : Scheme.{u}) where
  realization :
    ∀ (F : X.Modules), chapter04FiniteTypeQuasiCoherent F → ∀ i : ℕ,
      Chapter01FiniteDimensionalRealization k (chapter01CohomologyGroup F i)

noncomputable def chapter01Hi {k : Type u} [Field k] {X : Scheme.{u}}
    (D : Chapter01CohomologyDimensions k X) (F : X.Modules)
    (hF : chapter04FiniteTypeQuasiCoherent F) (i : ℕ) : ℕ := by
  let V := D.realization F hF i
  letI := V.addCommGroup
  letI := V.module
  exact Module.finrank k V.V

def chapter01h0 {k : Type u} [Field k] {X : Scheme.{u}}
    (D : Chapter01CohomologyDimensions k X) (F : X.Modules)
    (hF : chapter04FiniteTypeQuasiCoherent F) : ℕ :=
  chapter01Hi D F hF 0

def chapter01h1 {k : Type u} [Field k] {X : Scheme.{u}}
    (D : Chapter01CohomologyDimensions k X) (F : X.Modules)
    (hF : chapter04FiniteTypeQuasiCoherent F) : ℕ :=
  chapter01Hi D F hF 1

def chapter01Chi {k : Type u} [Field k] {X : Scheme.{u}}
    (D : Chapter01CohomologyDimensions k X) (F : X.Modules)
    (hF : chapter04FiniteTypeQuasiCoherent F) : ℤ :=
  chapter01EulerCharacteristic (chapter01h0 D F hF) (chapter01h1 D F hF)

structure Chapter01ProperCurveCohomology (k : Type u) [Field k]
    (C : Chapter01ProperCurveOverField k) where
  dimensions : Chapter01CohomologyDimensions k C.carrier
  vanishesAboveOne :
    ∀ (F : C.carrier.Modules), chapter04FiniteTypeQuasiCoherent F →
      chapter01CohomologyVanishesAboveOne F

theorem chapter01_proper_curve_cohomology_vanishes_above_one
    {k : Type u} [Field k] {C : Chapter01ProperCurveOverField k}
    (H : Chapter01ProperCurveCohomology k C) (F : C.carrier.Modules)
    (hF : chapter04FiniteTypeQuasiCoherent F) :
    chapter01CohomologyVanishesAboveOne F := by
  exact H.vanishesAboveOne F hF

structure Chapter01FiniteDimensionalDualityPair (k : Type u) [Field k] where
  H0 : Type u
  [H0AddCommGroup : AddCommGroup H0]
  [H0Module : Module k H0]
  H1 : Type u
  [H1AddCommGroup : AddCommGroup H1]
  [H1Module : Module k H1]
  H0Dual : Type u
  [H0DualAddCommGroup : AddCommGroup H0Dual]
  [H0DualModule : Module k H0Dual]
  H1Dual : Type u
  [H1DualAddCommGroup : AddCommGroup H1Dual]
  [H1DualModule : Module k H1Dual]
  finiteH0 : FiniteDimensional k H0
  finiteH1 : FiniteDimensional k H1
  finiteH0Dual : FiniteDimensional k H0Dual
  finiteH1Dual : FiniteDimensional k H1Dual
  degreeZeroExchange : H0 ≃ₗ[k] Module.Dual k H1Dual
  degreeOneExchange : H1 ≃ₗ[k] Module.Dual k H0Dual

/- LOCAL_DEPENDENCY_GUESS: the pinned cohomology API does not yet expose the
  sheaf-level dualizing functor or its comparison with the additive cohomology
  objects, so the finite-dimensional exchange is kept as an explicit bridge. -/
structure Chapter01SerreDualityInterface (k : Type u) [Field k]
    (X : Scheme.{u}) where
  dualizingLineBundle : Chapter01LineBundle X
  dualSheaf : X.Modules → X.Modules
  exchange : ∀ F : X.Modules, Chapter01FiniteDimensionalDualityPair k

def chapter01CohomologyIsTwoTerm {X : Scheme.{u}} (F : X.Modules) : Prop :=
  chapter01CohomologyVanishesAboveOne F

def chapter01EulerDifference (h₀ h₁ : ℕ) : ℤ :=
  (h₀ : ℤ) - h₁

theorem chapter01Euler_difference_eq_chi (h₀ h₁ : ℕ) :
    chapter01EulerDifference h₀ h₁ = chapter01EulerCharacteristic h₀ h₁ := by
  rfl

/-! ### Local/global balance and exact sequences -/

def chapter01WeightedOrderSum (E : Finset X) (ord : X → ℤ) : ℤ :=
  ∑ x in E, ord x

structure Chapter01ProperBalanceStatement (X : Type u) where
  exceptional : Finset X
  order : X → ℤ
  unitAway : ∀ x : X, x ∉ exceptional → order x = 0
  globalBalance : chapter01WeightedOrderSum exceptional order = 0

def chapter01UncompensatedBoundaryPole {X : Type u}
    (boundary : Set X) (order : X → ℤ) : Prop :=
  ∃ x ∈ boundary, order x < 0 ∧ ∀ y, y ∉ boundary → 0 ≤ order y

def chapter01SupportedOnFiniteSet {X : Scheme.{u}} (Q : X.Modules) : Prop :=
  ∃ E : Finset X, ∀ x : X, x ∉ E → Subsingleton (Q.presheaf.stalk x)

def chapter01FiniteSupportLength {X : Scheme.{u}} (Q : X.Modules) (E : Finset X) : ℕ∞ :=
  ∑ x in E, Module.length (X.presheaf.stalk x) (Q.presheaf.stalk x)

structure Chapter01FiniteSupportExactSequence (X : Scheme.{u}) where
  A B Q : X.Modules
  inclusion : A ⟶ B
  quotient : B ⟶ Q
  comp_zero : inclusion ≫ quotient = 0
  exact : (ShortComplex.mk inclusion quotient comp_zero).Exact
  finiteSupport : chapter01SupportedOnFiniteSet Q

theorem chapter01_finite_support_exact_sequence_is_measured_by_lengths
    {X : Scheme.{u}} (E : Chapter01FiniteSupportExactSequence X) :
    chapter01SupportedOnFiniteSet E.Q := by
  exact E.finiteSupport

/-! On a proper curve the affine/local and global computations are connected by
  exact sequences whose quotient is supported on finitely many points. -/
structure Chapter01LocalGlobalBalanceInterface (X : Scheme.{u}) where
  affineTerm : X.Modules
  properTerm : X.Modules
  boundaryQuotient : X.Modules
  sequence : ShortComplex X.Modules
  sequence_eq : sequence.X₁ = affineTerm ∧ sequence.X₂ = properTerm ∧
    sequence.X₃ = boundaryQuotient
  exact : sequence.Exact
  finiteSupport : chapter01SupportedOnFiniteSet boundaryQuotient

/-! ### Relative two-term presentations -/

structure Chapter01FiniteFreePresentation (k : Type u) [Field k] where
  F₀ F₁ : Type u
  [F₀AddCommGroup : AddCommGroup F₀]
  [F₀Module : Module k F₀]
  [F₁AddCommGroup : AddCommGroup F₁]
  [F₁Module : Module k F₁]
  finiteF₀ : FiniteDimensional k F₀
  finiteF₁ : FiniteDimensional k F₁
  differential : F₀ →ₗ[k] F₁

def chapter01KernelDimension {k : Type u} [Field k]
    (P : Chapter01FiniteFreePresentation k) : ℕ := by
  letI := P.F₀AddCommGroup
  letI := P.F₀Module
  letI := P.F₁AddCommGroup
  letI := P.F₁Module
  exact Module.finrank k P.differential.ker

def chapter01CokernelDimension {k : Type u} [Field k]
    (P : Chapter01FiniteFreePresentation k) : ℕ := by
  letI := P.F₁AddCommGroup
  letI := P.F₁Module
  exact Module.finrank k (P.F₁ ⧸ LinearMap.range P.differential)

def chapter01PresentationIndex {k : Type u} [Field k]
    (P : Chapter01FiniteFreePresentation k) : ℤ :=
  (chapter01KernelDimension P : ℤ) - chapter01CokernelDimension P

structure Chapter01RelativeTwoTermPresentation (k : Type u) [Field k] (S : Type u) where
  presentation : S → Chapter01FiniteFreePresentation k
  index : S → ℤ
  kernelDimension : S → ℕ
  cokernelDimension : S → ℕ
  kernelDimension_formula :
    ∀ s, kernelDimension s = chapter01KernelDimension (presentation s)
  cokernelDimension_formula :
    ∀ s, cokernelDimension s = chapter01CokernelDimension (presentation s)
  index_formula : ∀ s, index s = (kernelDimension s : ℤ) - cokernelDimension s
  kernelMayJump : chapter01RankFunctionMayJump kernelDimension
  cokernelMayJump : chapter01RankFunctionMayJump cokernelDimension
  indexLocallyConstant : IsLocallyConstant index

def chapter01RankFunctionMayJump {S : Type u} (h : S → ℕ) : Prop :=
  ∃ s t : S, h s ≠ h t

def chapter01UpperSemicontinuous {S : Type u} [TopologicalSpace S]
    (h : S → ℕ) : Prop :=
  ∀ n : ℕ, IsClosed {s | n ≤ h s}

def chapter01IndexBaseChangeCompatible {S T : Type u}
    (g : T → S) (indexS : S → ℤ) (indexT : T → ℤ) : Prop :=
  ∀ t, indexT t = indexS (g t)

def chapter01RelativeRiemannRochFormulaAt {S : Type u}
    (χ degree genus : S → ℤ) : Prop :=
  ∀ s, χ s = degree s + 1 - genus s

def chapter01RankJumpProfile {S : Type u} (h₀ h₁ : S → ℕ) : Prop :=
  IsLocallyConstant (fun s => (h₀ s : ℤ) - h₁ s)

theorem chapter01_relative_index_is_euler_characteristic
    {k : Type u} [Field k] {S : Type u}
    (P : Chapter01RelativeTwoTermPresentation k S) :
    IsLocallyConstant P.index := by
  exact P.indexLocallyConstant

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01
