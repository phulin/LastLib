import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TensorProduct.Quotient

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07

universe u v

/-- A local equation for an effective Cartier curve at a point. -/
structure Chapter07LocalEffectiveCartierCurve (A : Type u) [CommRing A] where
  equation : A
  equation_is_regular : equation ∈ nonZeroDivisors A

/-- The local equation of a curve vanishes at the chosen closed point. -/
def Chapter07PassesThrough {A : Type u} [CommRing A] [IsLocalRing A]
    (C : Chapter07LocalEffectiveCartierCurve A) : Prop :=
  C.equation ∈ IsLocalRing.maximalIdeal A

/-- The local ring of the curve cut out by a local equation. -/
abbrev Chapter07CurveRing {A : Type u} [CommRing A]
    (C : Chapter07LocalEffectiveCartierCurve A) : Type u :=
  A ⧸ Ideal.span ({C.equation} : Set A)

/-- The ideal defining the scheme-theoretic intersection of two local curves. -/
def Chapter07IntersectionIdeal {A : Type u} [CommRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A) : Ideal A :=
  Ideal.span ({C.equation, D.equation} : Set A)

/-- The local ring of the scheme-theoretic intersection of two curves. -/
abbrev Chapter07SchemeTheoreticIntersectionRing {A : Type u} [CommRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A) : Type u :=
  A ⧸ Chapter07IntersectionIdeal C D

/-- The m-primary algebraic formulation of “no common curve component through the point”. -/
def Chapter07MPrimaryIntersection {A : Type u} [CommRing A] [IsLocalRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A) : Prop :=
  (Chapter07IntersectionIdeal C D).radical = IsLocalRing.maximalIdeal A

/-- A local pair is proper either when it has empty support at the point or when it is m-primary. -/
def Chapter07ProperIntersectionAt {A : Type u} [CommRing A] [IsLocalRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A) : Prop :=
  Chapter07IntersectionIdeal C D = ⊤ ∨ Chapter07MPrimaryIntersection C D

/-- A prime-ideal formulation of the absence of a common one-dimensional component. -/
def Chapter07NoCommonCurveComponentAt {A : Type u} [CommRing A] [IsLocalRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A) : Prop :=
  ¬ ∃ p : Ideal A, p.IsPrime ∧ p ≠ IsLocalRing.maximalIdeal A ∧
    C.equation ∈ p ∧ D.equation ∈ p

/-- The local intersection multiplicity, valued in `ℕ∞` so that improper pairs retain their
infinite length instead of being silently truncated. -/
noncomputable def Chapter07LocalIntersectionMultiplicity {A : Type u} [CommRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A) : ℕ∞ :=
  Module.length A (A ⧸ Chapter07IntersectionIdeal C D)

/-- The integer-valued local number used after properness has supplied finiteness. -/
noncomputable def Chapter07LocalIntersectionNumber {A : Type u} [CommRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A) : ℕ :=
  (Chapter07LocalIntersectionMultiplicity C D).toNat

/-- A two-dimensional regular local ring, in the normalization used by this chapter. -/
def Chapter07IsTwoDimensionalRegularLocalRing (A : Type u) [CommRing A]
    [IsRegularLocalRing A] : Prop :=
  ringKrullDim A = (2 : WithBot ℕ∞)

/-- The two-dimensional Cohen–Macaulay consequence needed for parameter ideals. -/
def Chapter07CohenMacaulaySurfaceCriterion (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] : Prop :=
  ∀ ⦃f g : A⦄,
    f ∈ IsLocalRing.maximalIdeal A →
    g ∈ IsLocalRing.maximalIdeal A →
    (Ideal.span ({f, g} : Set A)).radical = IsLocalRing.maximalIdeal A →
    RingTheory.Sequence.IsRegular A [f, g]

/-- The m-adic order of an element, with units having order zero. -/
noncomputable def Chapter07MAdicOrder {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A]
    (f : A) : ℕ :=
  sInf {n : ℕ | f ∉ (IsLocalRing.maximalIdeal A) ^ (n + 1)}

/-- The multiplicity of an effective Cartier curve at the chosen point. -/
noncomputable def Chapter07CurveMultiplicity {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A]
    (C : Chapter07LocalEffectiveCartierCurve A) : ℕ :=
  Chapter07MAdicOrder C.equation

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07
