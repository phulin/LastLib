import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.DedekindDomain.Dvr
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

def chapter01DVRAt (X : Scheme.{u}) (x : X)
    [IsDomain (X.presheaf.stalk x)] : Prop :=
  IsDiscreteValuationRing (X.presheaf.stalk x)

theorem chapter01_regular_codimensionOne_isDVR
    {X : Scheme.{u}} (x : X) (hregular : chapter01RegularCurveAt X x)
    (hcodim : chapter01CodimensionOnePoint X x)
    [IsDomain (X.presheaf.stalk x)] :
    chapter01DVRAt X x := by
  change IsRegularLocalRing (X.presheaf.stalk x) at hregular
  change Order.coheight x = 1 at hcodim
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
    simpa only [ringKrullDim_stalk_eq_coheight] using
      (show (↑(Order.coheight x) : WithBot ℕ∞) = 1 by
        exact_mod_cast hcodim)
  have hcot := (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp hregular
  rw [hdim] at hcot
  apply (IsLocalRing.finrank_CotangentSpace_eq_one_iff).mp
  exact_mod_cast hcot

theorem chapter01_normal_oneDimensional_local_isDVR
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain R] (hnormal : IsIntegrallyClosed R)
    (hdim : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  have hdimLE : Ring.KrullDimLE 1 R := by
    rw [Ring.krullDimLE_iff]
    exact hdim.le
  have hDimOne : Ring.DimensionLEOne R :=
    ⟨fun {p} hp hprime =>
      @Ideal.IsPrime.isMaximal_of_ne_bot R _ _ hdimLE p hprime hp⟩
  have hDed : IsDedekindDomain R :=
    (isDedekindDomain_iff (A := R) (FractionRing R)).mpr
      ⟨inferInstance, inferInstance, hDimOne,
        fun {_} hx => (isIntegrallyClosed_iff (FractionRing R)).mp hnormal hx⟩
  have hnf : ¬ IsField R := by
    intro hF
    exact one_ne_zero (by rw [← hdim, ringKrullDim_eq_zero_of_isField hF])
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 0 2).mpr hDed

theorem chapter01_regular_local_ring_is_factorial
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] :
    UniqueFactorizationMonoid R := by
  sorry

/-! The order, cycle, local-equation, and pole descriptions are held together by a
  reusable dictionary rather than by silently identifying Weil and Cartier divisors
  on singular curves. -/
structure Chapter01CodimensionOneDictionary (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] where
  order : {x : X // chapter01CodimensionOnePoint X x} → ℤ
  cycle : Chapter01Divisor X
  localEquation :
    ∀ x : X, chapter01CodimensionOnePoint X x → Chapter01RationalFunction X
  localEquation_ne_zero :
    ∀ (x : X) (hx : chapter01CodimensionOnePoint X x),
      localEquation x hx ≠ 0
  localEquation_order :
    ∀ (x : X) (hx : chapter01CodimensionOnePoint X x),
      chapter01OrderAt x (localEquation x hx) = order ⟨x, hx⟩
  polePrescription : ∀ x : X, chapter01CodimensionOnePoint X x → ℤ
  order_eq_cycleCoefficient :
    ∀ (x : X) (hx : chapter01CodimensionOnePoint X x),
      cycle x = order ⟨x, hx⟩
  order_eq_polePrescription :
    ∀ (x : X) (hx : chapter01CodimensionOnePoint X x),
      order ⟨x, hx⟩ = polePrescription x hx

def chapter01DivisorOfOrder
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (D : Chapter01CodimensionOneDictionary X) : Chapter01Divisor X :=
  D.cycle

def chapter01FiniteExceptionalOrderData {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X]
    (f : Chapter01RationalFunction X) : Prop :=
  ∃ E : Finset X, ∀ x : X, x ∉ E → chapter01OrderZeroAt f x

theorem chapter01_order_is_zero_away_from_exceptional
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : Chapter01RationalFunction X) (_hf : f ≠ 0)
    (hE : (chapter01ExceptionalPoints f).Finite) :
    chapter01FiniteExceptionalOrderData f := by
  classical
  refine ⟨hE.toFinset, ?_⟩
  intro x hx
  by_contra hzero
  apply hx
  exact hE.mem_toFinset.mpr hzero

/-! Codimension-one cycles need not be Cartier on a singular curve, and normality in
  higher dimension does not force every height-one prime to be principal. -/
def chapter01CodimensionOneCycleNotLocallyPrincipal (X : Scheme.{u}) : Prop :=
  ∃ x : X, Chapter01PureDimensionOne X ∧ chapter01CodimensionOnePoint X x ∧
    chapter01ClosedPoint X x ∧ IsNoetherianRing (X.presheaf.stalk x) ∧
    ¬ chapter01RegularCurveAt X x ∧
    ¬ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).IsPrincipal

def chapter01DimensionAtLeastTwo (X : Scheme.{u}) : Prop :=
  ∃ Z : irreducibleComponents X, 2 ≤ topologicalKrullDim Z.1

def chapter01HeightOnePrimeIdeal {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  I.IsPrime ∧ Order.height I = 1

def chapter01NormalHigherDimensionalNonCartierExample : Prop :=
  ∃ (X : Scheme.{u}) (x : X) (I : Ideal (X.presheaf.stalk x)),
    chapter01DimensionAtLeastTwo X ∧
      IsNoetherianRing (X.presheaf.stalk x) ∧
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) ∧
    ¬ chapter01RegularCurveAt X x ∧
      chapter01HeightOnePrimeIdeal I ∧ ¬ I.IsPrincipal

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
  structures.  This realization records a chosen compatible module structure
  and a linear finite-dimensional bridge without changing the underlying object. -/
structure Chapter01FiniteDimensionalRealization (k : Type u) [Field k]
    (G : AddCommGrpCat.{u + 1}) where
  V : Type u
  [addCommGroup : AddCommGroup V]
  [module : Module k V]
  finite : FiniteDimensional k V
  [moduleG : Module k G]
  linearEquiv : V ≃ₗ[k] G

structure Chapter01CohomologyDimensions (k : Type u) [Field k]
    (X : Scheme.{u}) where
  structureMap : X ⟶ Spec (CommRingCat.of k)
  realization :
    ∀ (F : X.Modules), chapter04FiniteTypeQuasiCoherent F → ∀ i : ℕ,
      Chapter01FiniteDimensionalRealization k (chapter01CohomologyGroup F i)

/- LOCAL_DEPENDENCY_GUESS: the pinned cohomology API exposes the degree-zero
  object only as an additive group.  This bridge records the canonical
  structure-sheaf comparison needed to read its dimension as the dimension of
  global functions over the chosen field structure. -/
structure Chapter01DegreeZeroCohomologyGlobalSectionsBridge
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (D : Chapter01CohomologyDimensions k X)
    (hO : chapter04FiniteTypeQuasiCoherent
      (SheafOfModules.unit X.ringCatSheaf)) where
  structureMap_eq : D.structureMap = f
  linearEquiv :
    let V := D.realization (SheafOfModules.unit X.ringCatSheaf) hO 0
    letI := V.addCommGroup
    letI := V.module
    letI : Module k Γ(X, ⊤) :=
      Module.compHom _ (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom)
    V.V ≃ₗ[k] Γ(X, ⊤)

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
  dimensions_structureMap : dimensions.structureMap = C.structureMap
  vanishesAboveOne :
    ∀ (F : C.carrier.Modules), chapter04FiniteTypeQuasiCoherent F →
      chapter01CohomologyVanishesAboveOne F

theorem chapter01_proper_curve_cohomology_vanishes_above_one
    {k : Type u} [Field k] {C : Chapter01ProperCurveOverField k}
    (H : Chapter01ProperCurveCohomology k C) (F : C.carrier.Modules)
    (hF : chapter04FiniteTypeQuasiCoherent F) :
    chapter01CohomologyVanishesAboveOne F := by
  exact H.vanishesAboveOne F hF

structure Chapter01FiniteDimensionalDualityPair (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (F dualF : X.Modules) where
  sheaf : X.Modules
  sheaf_eq : sheaf = F
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
  H0Represents : Nonempty (H0 ≃+ chapter01CohomologyGroup F 0)
  H1Represents : Nonempty (H1 ≃+ chapter01CohomologyGroup F 1)
  H0DualRepresents : Nonempty (H0Dual ≃+ chapter01CohomologyGroup dualF 0)
  H1DualRepresents : Nonempty (H1Dual ≃+ chapter01CohomologyGroup dualF 1)
  degreeZeroExchange : H0 ≃ₗ[k] Module.Dual k H1Dual
  degreeOneExchange : H1 ≃ₗ[k] Module.Dual k H0Dual

/- LOCAL_DEPENDENCY_GUESS: the pinned cohomology API does not yet expose the
  sheaf-level dualizing functor or its comparison with the additive cohomology
  objects, so the finite-dimensional exchange is kept as an explicit bridge. -/
structure Chapter01SerreDualityInterface (k : Type u) [Field k]
    (X : Scheme.{u}) where
  structureMap : X ⟶ Spec (CommRingCat.of k)
  dualizingSheaf : X.Modules
  dualSheaf : X.Modules → X.Modules
  dualizingSheaf_eq : dualizingSheaf = dualSheaf (SheafOfModules.unit X.ringCatSheaf)
  exchange : ∀ (F : X.Modules), chapter04FiniteTypeQuasiCoherent F →
    Chapter01FiniteDimensionalDualityPair k structureMap F (dualSheaf F)

def chapter01CohomologyIsTwoTerm {X : Scheme.{u}} (F : X.Modules) : Prop :=
  chapter01CohomologyVanishesAboveOne F

def chapter01EulerDifference (h₀ h₁ : ℕ) : ℤ :=
  (h₀ : ℤ) - h₁

theorem chapter01Euler_difference_eq_chi (h₀ h₁ : ℕ) :
    chapter01EulerDifference h₀ h₁ = chapter01EulerCharacteristic h₀ h₁ := by
  rfl

/-! ### Local/global balance and exact sequences -/

/- The weight records residue-field degrees (or another chosen numerical
   multiplicity) when an order sum is used as a degree calculation. -/
def chapter01WeightedOrderSum {X : Type u} (E : Finset X)
    (ord weight : X → ℤ) : ℤ :=
  Finset.sum E (fun x => weight x * ord x)

structure Chapter01ProperBalanceStatement (X : Type u) where
  exceptional : Finset X
  order : X → ℤ
  weight : X → ℤ
  unitAway : ∀ x : X, x ∉ exceptional → order x = 0
  globalBalance : chapter01WeightedOrderSum exceptional order weight = 0

def chapter01UncompensatedBoundaryPole {X : Type u}
    (boundary : Set X) (order : X → ℤ) : Prop :=
  ∃ x ∈ boundary, order x < 0 ∧ ∀ y, y ∉ boundary → 0 ≤ order y

def chapter01SupportedOnFiniteSet {X : Scheme.{u}} (Q : X.Modules) : Prop :=
  ∃ E : Finset X, ∀ x : X, x ∉ E → Subsingleton (Q.presheaf.stalk x)

def chapter01FiniteSupportLength {X : Scheme.{u}} (Q : X.Modules) (E : Finset X) : ℕ∞ :=
  Finset.sum E (fun x =>
    Module.length (TopCat.Presheaf.stalk (C := RingCat) X.ringCatSheaf.obj x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) Q.val.presheaf x))

structure Chapter01FiniteSupportExactSequence (X : Scheme.{u}) where
  A : X.Modules
  B : X.Modules
  Q : X.Modules
  inclusion : A ⟶ B
  quotient : B ⟶ Q
  comp_zero : inclusion ≫ quotient = 0
  exact : (ShortComplex.mk inclusion quotient comp_zero).Exact
  finiteSupport : chapter01SupportedOnFiniteSet Q

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

/- A genuine relative two-term model is a single map between finite free
  modules over the base ring.  Choosing bases writes those modules as finite
  coordinate modules; the fiberwise profile below records the resulting
  kernel and cokernel dimensions. -/
structure Chapter01RelativeTwoTermModel (A : Type u) [CommRing A] where
  rank₀ : ℕ
  rank₁ : ℕ
  differential :
    (Fin rank₀ → A) →ₗ[A] (Fin rank₁ → A)

structure Chapter01FiniteFreePresentation (k : Type u) [Field k] where
  F₀ : Type u
  F₁ : Type u
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
  letI := P.F₀AddCommGroup
  letI := P.F₀Module
  letI := P.F₁AddCommGroup
  letI := P.F₁Module
  exact Module.finrank k (P.F₁ ⧸ LinearMap.range P.differential)

def chapter01PresentationIndex {k : Type u} [Field k]
    (P : Chapter01FiniteFreePresentation k) : ℤ :=
  (chapter01KernelDimension P : ℤ) - chapter01CokernelDimension P

def chapter01RankFunctionMayJump {S : Type u} (h : S → ℕ) : Prop :=
  ∃ s t : S, h s ≠ h t

def chapter01UpperSemicontinuous {S : Type u} [TopologicalSpace S]
    (h : S → ℕ) : Prop :=
  ∀ n : ℕ, IsClosed {s | n ≤ h s}

/- The following is deliberately a fiberwise profile over a topological
  parameter space; Chapter01RelativeTwoTermModel is the base-ring-level
  presentation and this record packages its possible rank behavior. -/
structure Chapter01RelativeTwoTermPresentation (k : Type u) [Field k]
    (S : Type u) [TopologicalSpace S] where
  presentation : S → Chapter01FiniteFreePresentation k
  index : S → ℤ
  kernelDimension : S → ℕ
  cokernelDimension : S → ℕ
  kernelDimension_formula :
    ∀ s, kernelDimension s = chapter01KernelDimension (presentation s)
  cokernelDimension_formula :
    ∀ s, cokernelDimension s = chapter01CokernelDimension (presentation s)
  kernelDimension_upperSemicontinuous :
    chapter01UpperSemicontinuous kernelDimension
  cokernelDimension_upperSemicontinuous :
    chapter01UpperSemicontinuous cokernelDimension
  index_formula : ∀ s, index s = (kernelDimension s : ℤ) - cokernelDimension s
  indexLocallyConstant : IsLocallyConstant index

def chapter01IndexBaseChangeCompatible {S T : Type u}
    (g : T → S) (indexS : S → ℤ) (indexT : T → ℤ) : Prop :=
  ∀ t, indexT t = indexS (g t)

def chapter01RelativeRiemannRochFormulaAt {S : Type u}
    (χ degree genus : S → ℤ) : Prop :=
  ∀ s, χ s = degree s + 1 - genus s

def chapter01RankJumpProfile {S : Type u} [TopologicalSpace S] (h₀ h₁ : S → ℕ) : Prop :=
  IsLocallyConstant (fun s => (h₀ s : ℤ) - h₁ s)

theorem chapter01_relative_index_is_euler_characteristic
    {k : Type u} [Field k] {S : Type u} [TopologicalSpace S]
    (P : Chapter01RelativeTwoTermPresentation k S) :
    IsLocallyConstant P.index ∧
      ∀ s, P.index s = (P.kernelDimension s : ℤ) - P.cokernelDimension s := by
  exact ⟨P.indexLocallyConstant, P.index_formula⟩

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01
