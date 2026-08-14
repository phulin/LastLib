import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

/-!
Shared interfaces for Chapter 3.

Mathlib has the codimension function, function field, order of vanishing, and
closed-subscheme constructors used below.  It does not yet expose the full
Cartier-divisor group or a scheme-theoretic prime-divisor type, so the small
book-facing interfaces in this file keep those gaps explicit.
-/

/-- The codimension-one points of a scheme. -/
abbrev Chapter03CodimensionOnePoint (X : Scheme.{u}) :=
  {x : X // Order.coheight x = 1}

/--
A prime divisor is recorded by its integral closed subscheme and its generic
point.  The support equality makes the generic-point indexing convention
explicit instead of silently replacing a subscheme by its underlying set.
-/
structure Chapter03PrimeDivisor (X : Scheme.{u}) where
  closedSubscheme : X.IdealSheafData
  genericPoint : X
  codim_one : Order.coheight genericPoint = 1
  integral : IsIntegral closedSubscheme.subscheme
  support_eq_closure :
    (closedSubscheme.support : Set X) = closure ({genericPoint} : Set X)

def Chapter03PrimeDivisor.support {X : Scheme.{u}} (P : Chapter03PrimeDivisor X) : Set X :=
  (P.closedSubscheme.support : Set X)

theorem chapter03_primeDivisor_support_eq_closure {X : Scheme.{u}}
    (P : Chapter03PrimeDivisor X) :
    P.support = closure ({P.genericPoint} : Set X) :=
  P.support_eq_closure

theorem chapter03_primeDivisor_genericPoint_mem_support {X : Scheme.{u}}
    (P : Chapter03PrimeDivisor X) : P.genericPoint ∈ P.support := by
  rw [chapter03_primeDivisor_support_eq_closure]
  exact subset_closure (Set.mem_singleton P.genericPoint)

@[ext]
theorem chapter03_primeDivisor_ext {X : Scheme.{u}}
    {P Q : Chapter03PrimeDivisor X}
    (hclosed : P.closedSubscheme = Q.closedSubscheme)
    (hgeneric : P.genericPoint = Q.genericPoint) : P = Q := by
  cases P
  cases Q
  cases hclosed
  cases hgeneric
  rfl

theorem chapter03_primeDivisor_isClosedImmersion {X : Scheme.{u}}
    (P : Chapter03PrimeDivisor X) :
    IsClosedImmersion P.closedSubscheme.subschemeι := by
  infer_instance

/-- A Weil divisor is a finite formal sum of prime divisors. -/
abbrev Chapter03WeilDivisor (X : Scheme.{u}) :=
  Chapter03PrimeDivisor X →₀ ℤ

/-- The coefficient of a Weil divisor at a prime divisor. -/
abbrev chapter03WeilDivisorCoeff {X : Scheme.{u}}
    (D : Chapter03WeilDivisor X) (P : Chapter03PrimeDivisor X) : ℤ :=
  D P

/-- Effectivity means that every coefficient is nonnegative. -/
def Chapter03EffectiveWeilDivisor (X : Scheme.{u}) :=
  {D : Chapter03WeilDivisor X // ∀ P, 0 ≤ D P}

def chapter03EffectiveWeilDivisor.toWeil {X : Scheme.{u}}
    (D : Chapter03EffectiveWeilDivisor X) : Chapter03WeilDivisor X :=
  D.1

theorem chapter03_effectiveWeilDivisor_coeff_nonnegative {X : Scheme.{u}}
    (D : Chapter03EffectiveWeilDivisor X) (P : Chapter03PrimeDivisor X) :
    0 ≤ chapter03EffectiveWeilDivisor.toWeil D P :=
  D.2 P

theorem chapter03_effectiveWeilDivisor_iff {X : Scheme.{u}}
    (D : Chapter03WeilDivisor X) :
    (∀ P, 0 ≤ D P) ↔
      ∃ E : Chapter03EffectiveWeilDivisor X,
        chapter03EffectiveWeilDivisor.toWeil E = D := by
  constructor
  · intro h
    exact ⟨⟨D, h⟩, rfl⟩
  · rintro ⟨E, rfl⟩
    exact E.2

@[ext]
theorem chapter03_effectiveWeilDivisor_ext {X : Scheme.{u}}
    {D E : Chapter03EffectiveWeilDivisor X}
    (h : chapter03EffectiveWeilDivisor.toWeil D =
      chapter03EffectiveWeilDivisor.toWeil E) : D = E := by
  exact Subtype.ext h

@[ext]
theorem chapter03_weilDivisor_ext {X : Scheme.{u}}
    {D E : Chapter03WeilDivisor X}
    (h : ∀ P, D P = E P) : D = E := by
  exact Finsupp.ext h

def chapter03WeilDivisorSupport {X : Scheme.{u}}
    (D : Chapter03WeilDivisor X) : Finset (Chapter03PrimeDivisor X) :=
  D.support

def chapter03PrimeDivisorCycle {X : Scheme.{u}}
    (P : Chapter03PrimeDivisor X) (n : ℤ) : Chapter03WeilDivisor X :=
  Finsupp.single P n

theorem chapter03_primeDivisorCycle_coeff_self {X : Scheme.{u}}
    (P : Chapter03PrimeDivisor X) (n : ℤ) :
    chapter03PrimeDivisorCycle P n P = n := by
  simp [chapter03PrimeDivisorCycle]

theorem chapter03_primeDivisorCycle_coeff_ne {X : Scheme.{u}}
    {P Q : Chapter03PrimeDivisor X} (h : Q ≠ P) (n : ℤ) :
    chapter03PrimeDivisorCycle P n Q = 0 := by
  simp [chapter03PrimeDivisorCycle, h]

/-- Normality is the stalkwise integrally-closed condition. -/
class Chapter03Normal (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] : Prop where
  integrallyClosed_stalk : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

/-- Regularity is the stalkwise regular-local-ring condition. -/
class Chapter03Regular (X : Scheme.{u}) : Prop where
  regular_stalk : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

/-- A noetherian integral one-dimensional scheme, with the dimension condition visible. -/
class Chapter03IntegralNoetherianCurve (X : Scheme.{u}) : Prop where
  integral : IsIntegral X
  noetherian : IsNoetherian X
  dimension_le_one : ∀ x : X, Order.coheight x ≤ 1
  has_codimension_one_point : ∃ x : X, Order.coheight x = 1

attribute [instance] Chapter03IntegralNoetherianCurve.integral
  Chapter03IntegralNoetherianCurve.noetherian

/-- A Dedekind base written in scheme language. -/
class Chapter03DedekindBase (S : Scheme.{u}) : Prop where
  integral : IsIntegral S
  noetherian : IsNoetherian S
  regular : Chapter03Regular S
  dimension_le_one : ∀ x : S, Order.coheight x ≤ 1
  has_codimension_one_point : ∃ x : S, Order.coheight x = 1

attribute [instance] Chapter03DedekindBase.integral Chapter03DedekindBase.noetherian
  Chapter03DedekindBase.regular

/-- Local factoriality in the stalkwise formulation used by the Cartier--Weil dictionary. -/
def Chapter03LocallyFactorial (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsPrincipalIdealRing (X.presheaf.stalk x)

/- LOCAL_DEPENDENCY_GUESS: pinned Mathlib has effective Cartier divisors and
closed ideal sheaves, but not the full group of Cartier divisors together with
its valuation map.  This class is the minimal book-facing interface needed to
state the Cartier-to-Weil map and its injectivity/surjectivity criteria. -/
class Chapter03CartierDivisorTheory (X : Scheme.{u}) where
  CartierDivisor : Type u
  addCommGroup : AddCommGroup CartierDivisor
  toWeil : CartierDivisor →+ Chapter03WeilDivisor X
  valuation : CartierDivisor → Chapter03PrimeDivisor X → ℤ
  toWeil_coeff : ∀ D P, toWeil D P = valuation D P

abbrev Chapter03CartierDivisor (X : Scheme.{u})
    [Chapter03CartierDivisorTheory X] :=
  Chapter03CartierDivisorTheory.CartierDivisor (X := X)

instance chapter03CartierDivisorAddCommGroup (X : Scheme.{u})
    [T : Chapter03CartierDivisorTheory X] :
    AddCommGroup (Chapter03CartierDivisor X) :=
  T.addCommGroup

def chapter03CartierDivisorToWeil (X : Scheme.{u})
    [T : Chapter03CartierDivisorTheory X] :
    Chapter03CartierDivisor X →+ Chapter03WeilDivisor X :=
  T.toWeil

/-- Reuse the earlier book's effective-Cartier interface. -/
abbrev Chapter03EffectiveCartierDivisor (X : Scheme.{u}) :=
  Chapter09EffectiveCartierDivisor X

/-- Reuse the earlier book's explicit relative-curve marker. -/
abbrev Chapter03RelativeCurve {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter09RelativeCurve f

def chapter03_relativeCurve_fibers_are_curves {X S : Scheme.{u}} {f : X ⟶ S}
    (h : Chapter03RelativeCurve f) : Prop :=
  Chapter09RelativeCurve.fibers_are_curves h

/-- The morphism-theoretic package of quasi-finiteness used in the relative model. -/
def Chapter03QuasiFiniteMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  LocallyQuasiFinite f ∧ QuasiCompact f

/- LOCAL_DEPENDENCY_GUESS: a relative curve is used with the missing finite
presentation hypothesis made explicit, since proper plus quasi-finite only
becomes the desired finite morphism after this standard finiteness package is
available. -/
class Chapter03RelativeCurveModel {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03DedekindBase S] : Prop where
  proper : IsProper f
  flat : Flat f
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  relative_curve : Chapter03RelativeCurve f

attribute [instance] Chapter03RelativeCurveModel.proper Chapter03RelativeCurveModel.flat
  Chapter03RelativeCurveModel.locallyOfFinitePresentation

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03
