import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.PicardGroup

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry BigOperators

universe u v

/-!
Shared interfaces for Chapter 4.

The pinned Mathlib tree has the structure sheaf, function fields, orders of
vanishing, ideal sheaves, and module sheaves, but it does not yet expose a
global sheaf of total quotient rings or Cartier divisors.  The first two
interfaces below are the smallest bridges needed to write the textbook's
local-equation definitions without replacing them by arbitrary predicates.
-/

/-! ### Total quotient rings and local equations -/

/- LOCAL_DEPENDENCY_GUESS: Mathlib has the localization of an affine ring at
its regular elements, but no sheaf-level total-quotient construction.  This
record is the sheaf-level universal property used by the local Cartier data
below. -/
class Chapter04TotalQuotientRingAPI (X : Scheme.{u}) where
  carrier : TopCat.Sheaf CommRingCat.{u} X
  structureMap : X.sheaf.presheaf ⟶ carrier.presheaf
  regular_isUnit :
    ∀ (U : X.Opens) {a : Γ(X, U)},
      a ∈ nonZeroDivisors Γ(X, U) →
        IsUnit ((structureMap.app (Opposite.op U)).hom a)
  exists_fraction :
    ∀ (U : X.affineOpens) (z : carrier.presheaf.obj (Opposite.op U.1)),
      ∃ (a b : Γ(X, U.1)), b ∈ nonZeroDivisors Γ(X, U.1) ∧
        z * (structureMap.app (Opposite.op U.1)).hom b =
          (structureMap.app (Opposite.op U.1)).hom a
  structureMap_injective :
    ∀ U : X.Opens,
      Function.Injective (structureMap.app (Opposite.op U)).hom

abbrev Chapter04TotalQuotientSection (X : Scheme.{u})
    [Chapter04TotalQuotientRingAPI X] (U : X.Opens) :=
  Chapter04TotalQuotientRingAPI.carrier.presheaf.obj (Opposite.op U)

abbrev Chapter04NonemptyOpen (X : Scheme.{u}) :=
  {U : X.Opens // Set.Nonempty (U : Set X)}

def chapter04StructureToTotal {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] (U : X.Opens) :
    Γ(X, U) →+* Chapter04TotalQuotientSection X U :=
  (Chapter04TotalQuotientRingAPI.structureMap.app (Opposite.op U)).hom

def chapter04TotalQuotientRestriction {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] {U V : X.Opens} (h : V ≤ U) :
    Chapter04TotalQuotientSection X U →+* Chapter04TotalQuotientSection X V :=
  (Chapter04TotalQuotientRingAPI.carrier.presheaf.map (homOfLE h).op).hom

def chapter04StructureRestriction {X : Scheme.{u}}
    {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.sheaf.presheaf.map (homOfLE h).op).hom

def chapter04StructureRestrictUnit {X : Scheme.{u}}
    {U V : X.Opens} (h : V ≤ U) : (Γ(X, U))ˣ →* (Γ(X, V))ˣ :=
  Units.map (chapter04StructureRestriction h).toMonoidHom

def chapter04TotalQuotientRestrictUnit {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] {U V : X.Opens} (h : V ≤ U) :
    (Chapter04TotalQuotientSection X U)ˣ →* (Chapter04TotalQuotientSection X V)ˣ :=
  Units.map (chapter04TotalQuotientRestriction h).toMonoidHom

/- LOCAL_DEPENDENCY_GUESS: on an integral scheme the total quotient sheaf
embeds into the function field on every open.  The restriction-compatible
maps below expose that canonical bridge for rational-section coordinates. -/
class Chapter04RationalFunctionLocalValueAPI (X : Scheme.{u})
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X] where
  value : ∀ U : Chapter04NonemptyOpen X,
    X.functionField →+* Chapter04TotalQuotientSection X U.1
  value_restrict :
    ∀ (U V : Chapter04NonemptyOpen X) (h : V.1 ≤ U.1) (f : X.functionField),
      chapter04TotalQuotientRestriction h (value U f) = value V f
  toFunctionField : ∀ U : Chapter04NonemptyOpen X,
    Chapter04TotalQuotientSection X U.1 →+* X.functionField
  toFunctionField_restrict :
    ∀ (U V : Chapter04NonemptyOpen X) (h : V.1 ≤ U.1)
      (z : Chapter04TotalQuotientSection X U.1),
      toFunctionField V (chapter04TotalQuotientRestriction h z) =
        toFunctionField U z
  value_toFunctionField :
    ∀ (U : Chapter04NonemptyOpen X) (f : X.functionField),
      toFunctionField U (value U f) = f
  toFunctionField_value :
    ∀ (U : Chapter04NonemptyOpen X)
      (z : Chapter04TotalQuotientSection X U.1),
      value U (toFunctionField U z) = z

theorem chapter04_rationalFunctionLocalValueAPI_exists {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X] [IsLocallyNoetherian X] :
    Nonempty (Chapter04RationalFunctionLocalValueAPI X) := by
  sorry

@[instance_reducible]
noncomputable def chapter04RationalFunctionLocalValueAPI {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X] [IsLocallyNoetherian X] :
    Chapter04RationalFunctionLocalValueAPI X :=
  Classical.choice (chapter04_rationalFunctionLocalValueAPI_exists (X := X))

theorem chapter04_totalQuotientRingAPI_exists (X : Scheme.{u})
    [IsLocallyNoetherian X] : Nonempty (Chapter04TotalQuotientRingAPI X) := by
  sorry

@[instance_reducible]
noncomputable def chapter04TotalQuotientRing (X : Scheme.{u})
    [IsLocallyNoetherian X] : Chapter04TotalQuotientRingAPI X :=
  Classical.choice (chapter04_totalQuotientRingAPI_exists X)

/-! ### Cartier divisors as compatible local equations -/

structure Chapter04CartierDivisor (X : Scheme.{u})
    [Chapter04TotalQuotientRingAPI X] where
  cover : X.OpenCover
  equation : ∀ i : cover.I₀,
    Chapter04TotalQuotientSection X (cover.f i).opensRange
  equation_unit : ∀ i : cover.I₀,
    (Chapter04TotalQuotientSection X (cover.f i).opensRange)ˣ
  equation_unit_val : ∀ i : cover.I₀,
    (equation_unit i : Chapter04TotalQuotientSection X (cover.f i).opensRange) = equation i
  transition : ∀ i j : cover.I₀,
    (Γ(X, (cover.f i).opensRange ⊓ (cover.f j).opensRange))ˣ
  transition_equation :
    ∀ i j : cover.I₀,
      (chapter04StructureToTotal _ (transition i j :
          Γ(X, (cover.f i).opensRange ⊓ (cover.f j).opensRange)) *
        chapter04TotalQuotientRestriction (inf_le_right :
          (cover.f i).opensRange ⊓ (cover.f j).opensRange ≤ (cover.f j).opensRange)
          (equation j)) =
        chapter04TotalQuotientRestriction (inf_le_left :
          (cover.f i).opensRange ⊓ (cover.f j).opensRange ≤ (cover.f i).opensRange)
          (equation i)
  transition_self : ∀ i : cover.I₀, transition i i = 1
  transition_cocycle :
    ∀ i j k : cover.I₀,
      chapter04StructureRestrictUnit (inf_le_left :
          ((cover.f i).opensRange ⊓ (cover.f j).opensRange) ⊓ (cover.f k).opensRange ≤
            (cover.f i).opensRange ⊓ (cover.f j).opensRange) (transition i j) *
        chapter04StructureRestrictUnit (inf_le_inf inf_le_right le_rfl :
          ((cover.f i).opensRange ⊓ (cover.f j).opensRange) ⊓ (cover.f k).opensRange ≤
            (cover.f j).opensRange ⊓ (cover.f k).opensRange) (transition j k) =
        chapter04StructureRestrictUnit
          (inf_le_inf inf_le_left le_rfl :
            ((cover.f i).opensRange ⊓ (cover.f j).opensRange) ⊓ (cover.f k).opensRange ≤
              (cover.f i).opensRange ⊓ (cover.f k).opensRange) (transition i k)
  equation_unit_at : ∀ (_i : cover.I₀) (_x : X), Prop
  equation_unit_at_iff :
    ∀ (i : cover.I₀) (x : X) (_hx : x ∈ (cover.f i).opensRange),
      equation_unit_at i x ↔
        ∃ (U : X.Opens) (_hU : x ∈ U) (hUi : U ≤ (cover.f i).opensRange)
          (a : Γ(X, U)),
          IsUnit a ∧
            chapter04StructureToTotal U a =
              chapter04TotalQuotientRestriction hUi (equation i)
  support : Set X
  support_iff :
    ∀ x : X,
      x ∈ support ↔
        ∀ i : cover.I₀, x ∈ (cover.f i).opensRange → ¬ equation_unit_at i x

def chapter04CartierDivisorSupport {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] (D : Chapter04CartierDivisor X) : Set X :=
  D.support

theorem chapter04_cartierDivisor_support_isClosed {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsNoetherian X]
    (D : Chapter04CartierDivisor X) : IsClosed D.support := by
  sorry

def chapter04CartierDivisorIsEffective {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] (D : Chapter04CartierDivisor X) : Prop :=
  ∀ i : D.cover.I₀, ∀ x : X, x ∈ (D.cover.f i).opensRange →
    ∃ U : X.Opens, ∃ _hx : x ∈ U,
      ∃ hU : U ≤ (D.cover.f i).opensRange,
        ∃ a : Γ(X, U),
          a ∈ nonZeroDivisors Γ(X, U) ∧
            chapter04StructureToTotal U a =
              chapter04TotalQuotientRestriction hU (D.equation i)

def chapter04CartierLocalEquationRelation {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D E F : Chapter04CartierDivisor X) : Prop :=
  ∀ x : X, ∃ U : X.Opens, ∃ _hx : x ∈ U,
    ∃ i : D.cover.I₀, ∃ j : E.cover.I₀, ∃ k : F.cover.I₀,
      ∃ (hD : U ≤ (D.cover.f i).opensRange)
        (hE : U ≤ (E.cover.f j).opensRange)
        (hF : U ≤ (F.cover.f k).opensRange)
        (u : (Γ(X, U))ˣ),
        chapter04StructureToTotal U (u : Γ(X, U)) *
            chapter04TotalQuotientRestriction hD (D.equation i) *
            chapter04TotalQuotientRestriction hE (E.equation j) =
          chapter04TotalQuotientRestriction hF (F.equation k)

theorem chapter04_cartierDivisor_zero_exists {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] :
    Nonempty (Chapter04CartierDivisor X) := by
  sorry

theorem chapter04_cartierDivisor_add_exists {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D E : Chapter04CartierDivisor X) :
    ∃ F : Chapter04CartierDivisor X, chapter04CartierLocalEquationRelation D E F := by
  sorry

theorem chapter04_cartierDivisor_neg_exists {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) :
    ∃ F : Chapter04CartierDivisor X,
      chapter04CartierLocalEquationRelation F D
        (Classical.choice (chapter04_cartierDivisor_zero_exists (X := X))) := by
  sorry

noncomputable def chapter04CartierDivisorZero {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] : Chapter04CartierDivisor X :=
  Classical.choice (chapter04_cartierDivisor_zero_exists (X := X))

noncomputable def chapter04CartierDivisorAdd {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D E : Chapter04CartierDivisor X) : Chapter04CartierDivisor X :=
  Classical.choose (chapter04_cartierDivisor_add_exists D E)

theorem chapter04_cartierDivisorAdd_spec {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D E : Chapter04CartierDivisor X) :
    chapter04CartierLocalEquationRelation D E (chapter04CartierDivisorAdd D E) := by
  sorry

noncomputable def chapter04CartierDivisorNeg {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) : Chapter04CartierDivisor X :=
  Classical.choose (chapter04_cartierDivisor_neg_exists D)

theorem chapter04_cartierDivisorNeg_spec {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04CartierDivisor X) :
    chapter04CartierLocalEquationRelation (chapter04CartierDivisorNeg D) D
      (chapter04CartierDivisorZero (X := X)) := by
  exact Classical.choose_spec (chapter04_cartierDivisor_neg_exists D)

def chapter04CartierDivisorSub {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D E : Chapter04CartierDivisor X) : Chapter04CartierDivisor X :=
  chapter04CartierDivisorAdd D (chapter04CartierDivisorNeg E)

/-! ### Line bundles and the canonical tensor operations -/

noncomputable def chapter04Tensor {X : Scheme.{u}}
    (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModules.Monoidal.tensorObj M.val N.val)

def chapter04IsInvertibleSheaf {X : Scheme.{u}} (M : X.Modules) : Prop :=
  SheafOfModules.IsFiniteType M ∧
    ∃ N : X.Modules,
      Nonempty (chapter04Tensor M N ≅ SheafOfModules.unit X.ringCatSheaf)

structure Chapter04LineBundle (X : Scheme.{u}) where
  sheaf : X.Modules
  isInvertible : chapter04IsInvertibleSheaf sheaf

noncomputable def chapter04TrivialLineBundle (X : Scheme.{u}) : Chapter04LineBundle X :=
  { sheaf := SheafOfModules.unit X.ringCatSheaf
    isInvertible := by
      sorry }

noncomputable def chapter04LineBundleTensor {X : Scheme.{u}}
    (L M : Chapter04LineBundle X) : Chapter04LineBundle X :=
  { sheaf := chapter04Tensor L.sheaf M.sheaf
    isInvertible := by
      sorry }

noncomputable def chapter04LineBundleTensorPower {X : Scheme.{u}}
    (L : Chapter04LineBundle X) : ℕ → Chapter04LineBundle X
  | 0 => chapter04TrivialLineBundle X
  | n + 1 => chapter04LineBundleTensor (chapter04LineBundleTensorPower L n) L

def chapter04LineBundleIsomorphic {X : Scheme.{u}}
    (L M : Chapter04LineBundle X) : Prop := Nonempty (L.sheaf ≅ M.sheaf)

theorem chapter04_lineBundleIsomorphic_refl {X : Scheme.{u}}
    (L : Chapter04LineBundle X) : chapter04LineBundleIsomorphic L L := by
  exact ⟨Iso.refl L.sheaf⟩

theorem chapter04_lineBundleIsomorphic_symm {X : Scheme.{u}}
    {L M : Chapter04LineBundle X} (h : chapter04LineBundleIsomorphic L M) :
    chapter04LineBundleIsomorphic M L := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

theorem chapter04_lineBundleIsomorphic_trans {X : Scheme.{u}}
    {L M N : Chapter04LineBundle X}
    (hLM : chapter04LineBundleIsomorphic L M)
    (hMN : chapter04LineBundleIsomorphic M N) :
    chapter04LineBundleIsomorphic L N := by
  rcases hLM with ⟨e⟩
  rcases hMN with ⟨f⟩
  exact ⟨e ≪≫ f⟩

/- LOCAL_DEPENDENCY_GUESS: the sheaf internal-Hom presentation of the dual
of an invertible module is not exposed by the pinned imports.  The record
below retains the evaluation isomorphism, which is the only duality data used
by this chapter. -/
structure Chapter04DualLineBundleData {X : Scheme.{u}}
    (L : Chapter04LineBundle X) where
  dual : Chapter04LineBundle X
  evaluation : chapter04Tensor L.sheaf dual.sheaf ≅
    (chapter04TrivialLineBundle X).sheaf

theorem chapter04_dualLineBundle_exists {X : Scheme.{u}}
    (L : Chapter04LineBundle X) : Nonempty (Chapter04DualLineBundleData L) := by
  sorry

noncomputable def chapter04DualLineBundle {X : Scheme.{u}}
    (L : Chapter04LineBundle X) : Chapter04LineBundle X :=
  (Classical.choice (chapter04_dualLineBundle_exists L)).dual

theorem chapter04_dualLineBundle_evaluation {X : Scheme.{u}}
    (L : Chapter04LineBundle X) :
    chapter04LineBundleIsomorphic
      (chapter04LineBundleTensor L (chapter04DualLineBundle L))
      (chapter04TrivialLineBundle X) := by
  sorry

abbrev Chapter04GlobalSection {X : Scheme.{u}}
    (L : Chapter04LineBundle X) :=
  ↑(L.sheaf.val.presheaf.obj (Opposite.op (⊤ : X.Opens)))

/-! ### Effective ideals, sections, and associated points -/

def chapter04IsEffectiveCartierIdeal {X : Scheme.{u}}
    (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ a : Γ(X, U),
    I.ideal U = Ideal.span ({a} : Set Γ(X, U)) ∧
      a ∈ nonZeroDivisors Γ(X, U)

structure Chapter04EffectiveCartierDivisor (X : Scheme.{u})
    [Chapter04TotalQuotientRingAPI X] where
  cartier : Chapter04CartierDivisor X
  effective : chapter04CartierDivisorIsEffective cartier
  ideal : X.IdealSheafData
  ideal_isEffectiveCartier : chapter04IsEffectiveCartierIdeal ideal
  ideal_represents_cartier :
    ∀ (i : cartier.cover.I₀) (x : X),
      x ∈ (cartier.cover.f i).opensRange →
        ∃ (U : X.affineOpens) (_hU : x ∈ U.1)
          (hUi : U.1 ≤ (cartier.cover.f i).opensRange)
          (a : Γ(X, U)),
          a ∈ nonZeroDivisors Γ(X, U) ∧
            ideal.ideal U = Ideal.span ({a} : Set Γ(X, U)) ∧
            chapter04StructureToTotal U.1 a =
              chapter04TotalQuotientRestriction hUi (cartier.equation i)
  ideal_support : ideal.support = cartier.support
  closed : IsClosedImmersion ideal.subschemeι

abbrev Chapter04EffectiveCartierDivisor.support {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) : Set X := D.cartier.support

abbrev Chapter04EffectiveCartierDivisor.subscheme {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) : Scheme := D.ideal.subscheme

abbrev Chapter04EffectiveCartierDivisor.inclusion {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X]
    (D : Chapter04EffectiveCartierDivisor X) : D.subscheme ⟶ X := D.ideal.subschemeι

/-! ### Orders, Weil divisors, and degree -/

abbrev Chapter04CodimensionOnePoint (X : Scheme.{u}) :=
  {x : X // Order.coheight x = 1}

abbrev Chapter04WeilDivisor (X : Scheme.{u}) :=
  Chapter04CodimensionOnePoint X →₀ ℤ

def chapter04WeilDivisorDegree {X : Scheme.{u}}
    (degree : Chapter04CodimensionOnePoint X → ℕ)
    (Z : Chapter04WeilDivisor X) : ℤ :=
  Z.sum (fun x n => n * (degree x : ℤ))

/- LOCAL_DEPENDENCY_GUESS: the order of a general local-equation Cartier
divisor is mathematically canonical on a regular integral noetherian curve,
but the pinned tree only exposes `Scheme.ord` for rational functions. -/
class Chapter04CartierOrderAPI (X : Scheme.{u})
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter04RationalFunctionLocalValueAPI X] where
  order : Chapter04CartierDivisor X → Chapter04CodimensionOnePoint X → ℤ
  order_local_equation :
    ∀ (D : Chapter04CartierDivisor X) (x : Chapter04CodimensionOnePoint X)
      (i : D.cover.I₀) (hx : x.1 ∈ (D.cover.f i).opensRange),
      order D x =
        AlgebraicGeometry.Scheme.ord
          (Chapter04RationalFunctionLocalValueAPI.toFunctionField
            ⟨(D.cover.f i).opensRange, ⟨x.1, hx⟩⟩ (D.equation i)) x.1
  order_add :
    ∀ (D E : Chapter04CartierDivisor X) (x : Chapter04CodimensionOnePoint X),
      order (chapter04CartierDivisorAdd D E) x = order D x + order E x
  order_neg :
    ∀ (D : Chapter04CartierDivisor X) (x : Chapter04CodimensionOnePoint X),
      order (chapter04CartierDivisorNeg D) x = -order D x
  order_zero :
    ∀ x : Chapter04CodimensionOnePoint X,
      order (chapter04CartierDivisorZero (X := X)) x = 0
  order_respects_localEquationRelation :
    ∀ (D E F : Chapter04CartierDivisor X),
      chapter04CartierLocalEquationRelation D E F →
        ∀ x : Chapter04CodimensionOnePoint X,
          order F x = order D x + order E x
  order_support_finite :
    ∀ D : Chapter04CartierDivisor X,
      (Set.Finite {x : Chapter04CodimensionOnePoint X | order D x ≠ 0})
  principalOrder : X.functionFieldˣ → Chapter04CodimensionOnePoint X → ℤ
  principalOrder_one :
    principalOrder (1 : X.functionFieldˣ) = 0
  principalOrder_mul :
    ∀ f g : X.functionFieldˣ,
      principalOrder (f * g) = principalOrder f + principalOrder g
  principalOrder_inv :
    ∀ f : X.functionFieldˣ,
      principalOrder f⁻¹ = -principalOrder f
  principalOrder_eq_schemeOrder :
    ∀ (f : X.functionFieldˣ) (x : Chapter04CodimensionOnePoint X),
      principalOrder f x =
        AlgebraicGeometry.Scheme.ord (f : X.functionField) x.1
  principalOrder_support_finite :
    ∀ f : X.functionFieldˣ,
      Set.Finite {x : Chapter04CodimensionOnePoint X | principalOrder f x ≠ 0}

def chapter04CartierOrder {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (D : Chapter04CartierDivisor X) (x : Chapter04CodimensionOnePoint X) : ℤ :=
  Chapter04CartierOrderAPI.order D x

structure Chapter04ProperIntegralCurveOverField (k : Type u) [Field k] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ Spec (.of k)
  proper : IsProper structureMap
  finiteType : LocallyOfFiniteType structureMap
  pureDimensionOne : ∀ x : carrier, Order.coheight x ≤ 1
  hasCodimensionOnePoint : ∃ x : carrier, Order.coheight x = 1
  integral : IsIntegral carrier

instance chapter04ProperIntegralCurve_isIntegral {k : Type u} [Field k]
    (C : Chapter04ProperIntegralCurveOverField k) : IsIntegral C.carrier :=
  C.integral

def chapter04CurveConstantsMap {k : Type u} [Field k]
    (C : Chapter04ProperIntegralCurveOverField k) :
    k →+* Γ(C.carrier, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ C.structureMap.appTop).hom

def chapter04GlobalFunctionIsConstant {k : Type u} [Field k]
    (C : Chapter04ProperIntegralCurveOverField k)
    (a : Γ(C.carrier, ⊤)) : Prop :=
  ∃ b : k, chapter04CurveConstantsMap C b = a

noncomputable def chapter04PullbackLineBundle {X Y : Scheme.{u}}
    (g : Y ⟶ X) (L : Chapter04LineBundle X) : Chapter04LineBundle Y :=
  { sheaf := (Scheme.Modules.pullback g).obj L.sheaf
    isInvertible := by
      sorry }

def chapter04FiberwiseLineBundleEquivalent {X S : Scheme.{u}}
    (f : X ⟶ S) (L M : Chapter04LineBundle X) : Prop :=
  ∃ N : Chapter04LineBundle S,
    chapter04LineBundleIsomorphic
      (chapter04LineBundleTensor L (chapter04PullbackLineBundle f N)) M

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04
