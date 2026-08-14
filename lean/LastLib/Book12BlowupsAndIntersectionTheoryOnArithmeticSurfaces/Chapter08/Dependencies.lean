import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Data.Finsupp.Basic
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter08

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

universe u v

/-!
Shared interfaces for Chapter 8.

The preceding Book 12 chapters are still being drafted in the current source
tree.  This file therefore keeps the geometric facts that those chapters will
eventually provide explicit, while using the earlier scheme and line-bundle
objects whenever the pinned library already has them.  In particular, the
point, local-length, degree, and norm records below are interfaces, not
alternative definitions of schemes or invertible sheaves.
-/

/-! ### Schemes, arithmetic surfaces, and closed points -/

abbrev Chapter08LineBundle (Y : Scheme.{u}) :=
  LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11.Chapter11LineBundle Y

def chapter08LineBundleIsomorphic {Y : Scheme.{u}}
    (L M : Chapter08LineBundle Y) : Prop :=
  LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11.chapter11LineBundleIsomorphic
    L M

theorem chapter08_lineBundleIsomorphic_refl {Y : Scheme.{u}}
    (L : Chapter08LineBundle Y) : chapter08LineBundleIsomorphic L L := by
  exact LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11.chapter11_lineBundleIsomorphic_refl L

theorem chapter08_lineBundleIsomorphic_symm {Y : Scheme.{u}}
    {L M : Chapter08LineBundle Y}
    (h : chapter08LineBundleIsomorphic L M) :
    chapter08LineBundleIsomorphic M L := by
  exact LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11.chapter11_lineBundleIsomorphic_symm h

theorem chapter08_lineBundleIsomorphic_trans {Y : Scheme.{u}}
    {L M N : Chapter08LineBundle Y}
    (hLM : chapter08LineBundleIsomorphic L M)
    (hMN : chapter08LineBundleIsomorphic M N) :
    chapter08LineBundleIsomorphic L N := by
  exact LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11.chapter11_lineBundle_isomorphic_trans hLM hMN

instance chapter08LineBundleSetoid (Y : Scheme.{u}) : Setoid (Chapter08LineBundle Y) where
  r := chapter08LineBundleIsomorphic
  iseqv := ⟨chapter08_lineBundleIsomorphic_refl,
    chapter08_lineBundleIsomorphic_symm, chapter08_lineBundleIsomorphic_trans⟩

abbrev Chapter08LineBundleClass (Y : Scheme.{u}) :=
  Quotient (chapter08LineBundleSetoid Y)

def chapter08LineBundleClassMk {Y : Scheme.{u}}
    (L : Chapter08LineBundle Y) : Chapter08LineBundleClass Y :=
  Quotient.mk _ L

theorem chapter08_lineBundleClassMk_eq_iff {Y : Scheme.{u}}
    (L M : Chapter08LineBundle Y) :
    chapter08LineBundleClassMk L = chapter08LineBundleClassMk M ↔
      chapter08LineBundleIsomorphic L M := by
  sorry

noncomputable def chapter08StructureSheafLineBundle (Y : Scheme.{u}) :
    Chapter08LineBundle Y :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.chapter09StructureSheafLineBundle Y

noncomputable def chapter08PullbackLineBundle
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) (L : Chapter08LineBundle Y) :
    Chapter08LineBundle Z :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.chapter09PullbackLineBundle g L

theorem chapter08_pullback_lineBundle_isomorphic
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    {L M : Chapter08LineBundle Y}
    (h : chapter08LineBundleIsomorphic L M) :
    chapter08LineBundleIsomorphic
      (chapter08PullbackLineBundle g L) (chapter08PullbackLineBundle g M) := by
  sorry

theorem chapter08_pullback_structureSheaf_isomorphic
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    chapter08LineBundleIsomorphic
      (chapter08PullbackLineBundle g (chapter08StructureSheafLineBundle Y))
      (chapter08StructureSheafLineBundle Z) := by
  sorry

theorem chapter08_pullback_lineBundle_comp_isomorphic
    {W Y Z : Scheme.{u}} (f : W ⟶ Y) (g : Y ⟶ Z)
    (L : Chapter08LineBundle Z) :
    chapter08LineBundleIsomorphic
      (chapter08PullbackLineBundle (f ≫ g) L)
      (chapter08PullbackLineBundle f (chapter08PullbackLineBundle g L)) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the preceding Book 12 chapters will eventually
replace these book-facing predicates and point/residue-degree records by their
canonical arithmetic-surface and fiber APIs.  Properness is deliberately
separated from the surface record because §8.1 uses it only for global
finiteness over the base. -/
structure Chapter08ArithmeticSurface where
  base : Scheme.{u}
  carrier : Scheme.{u}
  structureMap : carrier ⟶ base
  baseIsDedekind : Prop
  baseIsField : Prop
  integral : Prop
  regular : Prop
  flat : Flat structureMap
  relativeDimensionOne : Prop

def chapter08ProperOverBase (X : Chapter08ArithmeticSurface) : Prop :=
  IsProper X.structureMap

def chapter08ProperSurfaceOverField (X : Chapter08ArithmeticSurface) : Prop :=
  X.baseIsField ∧ chapter08ProperOverBase X

structure Chapter08BaseClosedPoint (X : Chapter08ArithmeticSurface) where
  point : X.base
  isClosed : Prop

structure Chapter08ClosedPoint (X : Chapter08ArithmeticSurface) where
  point : X.carrier
  isClosed : Prop
  basePoint : Chapter08BaseClosedPoint X
  /-- The finite residue-field degree `[κ(x) : κ(s)]`. -/
  residueDegree : ℕ

def chapter08PointInFiber (X : Chapter08ArithmeticSurface)
    (s : Chapter08BaseClosedPoint X) (x : Chapter08ClosedPoint X) : Prop :=
  x.basePoint = s

/-! ### Prime curves and Cartier divisors -/

structure Chapter08PrimeCurve (X : Chapter08ArithmeticSurface) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ X.carrier
  genericPoint : X.carrier
  irreducible : Prop
  vertical : Prop
  horizontal : Prop

structure Chapter08CartierDivisor (X : Chapter08ArithmeticSurface) where
  lineBundle : Chapter08LineBundle X.carrier
  coefficient : Chapter08PrimeCurve X → ℤ
  support : Finset (Chapter08PrimeCurve X)
  support_contains_nonzero :
    ∀ C, coefficient C ≠ 0 → C ∈ support

def chapter08CartierDivisorIsEffective
    {X : Chapter08ArithmeticSurface} (D : Chapter08CartierDivisor X) : Prop :=
  ∀ C, 0 ≤ D.coefficient C

def chapter08CartierDivisorIsVertical
    {X : Chapter08ArithmeticSurface} (D : Chapter08CartierDivisor X) : Prop :=
  ∀ C ∈ D.support, C.vertical

def chapter08NoCommonIrreducibleComponent
    {X : Chapter08ArithmeticSurface}
    (D G : Chapter08CartierDivisor X) : Prop :=
  ∀ C, D.coefficient C ≠ 0 → G.coefficient C = 0

def chapter08HorizontalGenericDisjoint
    {X : Chapter08ArithmeticSurface}
    (D G : Chapter08CartierDivisor X) : Prop :=
  ∀ C, D.coefficient C ≠ 0 →
    ∀ E, G.coefficient E ≠ 0 →
      C.horizontal → E.horizontal → C.genericPoint ≠ E.genericPoint

def chapter08HorizontalGenericIntersection
    {X : Chapter08ArithmeticSurface}
    (D G : Chapter08CartierDivisor X) : Prop :=
  ∃ C, D.coefficient C ≠ 0 ∧ ∃ E, G.coefficient E ≠ 0 ∧
    C.horizontal ∧ E.horizontal ∧ C.genericPoint = E.genericPoint

structure Chapter08VerticalCurve (X : Chapter08ArithmeticSurface) where
  prime : Chapter08PrimeCurve X
  basePoint : Chapter08BaseClosedPoint X
  residueField : Type u
  residueField_isField : Field residueField
  integral : Prop
  properOverResidue : Prop
  liesInFiber : Prop
  pointOnCurve : Chapter08ClosedPoint X → Prop
  asCartierDivisor : Chapter08CartierDivisor X
  asCartierComponent : asCartierDivisor.coefficient prime ≠ 0

def chapter08DivisorMeetsCurveProperly
    {X : Chapter08ArithmeticSurface}
    (D : Chapter08CartierDivisor X) (C : Chapter08VerticalCurve X) : Prop :=
  D.coefficient C.prime = 0

/-! ### Local intersection and degree interfaces -/

/- LOCAL_DEPENDENCY_GUESS: Chapter 7 will eventually supply the local
intersection multiplicity and quotient-length calculations.  The class keeps
the local output in `ℕ` and records the one bridge needed in §8.2. -/
class Chapter08LocalIntersectionTheory (X : Chapter08ArithmeticSurface) where
  localMultiplicity :
    Chapter08CartierDivisor X → Chapter08CartierDivisor X →
      Chapter08ClosedPoint X → ℕ
  localLength :
    Chapter08CartierDivisor X → Chapter08VerticalCurve X →
      Chapter08ClosedPoint X → ℕ
  localLength_eq_multiplicity :
    ∀ (D : Chapter08CartierDivisor X) (C : Chapter08VerticalCurve X)
      (x : Chapter08ClosedPoint X),
      chapter08DivisorMeetsCurveProperly D C →
        localLength D C x = localMultiplicity D C.asCartierDivisor x
  finite_intersection_support :
    ∀ (D G : Chapter08CartierDivisor X),
      chapter08NoCommonIrreducibleComponent D G →
        chapter08HorizontalGenericDisjoint D G →
          ∃ support : Finset (Chapter08ClosedPoint X),
            ∀ x, localMultiplicity D G x ≠ 0 → x ∈ support

def chapter08LocalIntersectionMultiplicity
    {X : Chapter08ArithmeticSurface} [Chapter08LocalIntersectionTheory X]
    (D G : Chapter08CartierDivisor X) (x : Chapter08ClosedPoint X) : ℕ :=
  Chapter08LocalIntersectionTheory.localMultiplicity D G x

def chapter08LocalIntersectionLength
    {X : Chapter08ArithmeticSurface} [Chapter08LocalIntersectionTheory X]
    (D : Chapter08CartierDivisor X) (C : Chapter08VerticalCurve X)
    (x : Chapter08ClosedPoint X) : ℕ :=
  Chapter08LocalIntersectionTheory.localLength D C x

structure Chapter08ProperIntersectionWitness
    {X : Chapter08ArithmeticSurface} [Chapter08LocalIntersectionTheory X]
    (D G : Chapter08CartierDivisor X) where
  support : Finset (Chapter08ClosedPoint X)
  support_contains_nonzero :
    ∀ x, chapter08LocalIntersectionMultiplicity D G x ≠ 0 → x ∈ support
  noCommonComponent : chapter08NoCommonIrreducibleComponent D G
  horizontalGenericDisjoint : chapter08HorizontalGenericDisjoint D G

abbrev Chapter08ZeroCycle (X : Chapter08ArithmeticSurface) :=
  Chapter08ClosedPoint X →₀ ℤ

abbrev Chapter08BaseDivisor (X : Chapter08ArithmeticSurface) :=
  Chapter08BaseClosedPoint X →₀ ℤ

def chapter08PointCycle
    {X : Chapter08ArithmeticSurface} (x : Chapter08ClosedPoint X) :
    Chapter08ZeroCycle X :=
  Finsupp.single x 1

@[ext] theorem chapter08_zeroCycle_ext
    {X : Chapter08ArithmeticSurface} {z w : Chapter08ZeroCycle X}
    (h : ∀ x, z x = w x) : z = w := by
  ext x
  exact h x

/-! ### Additive and degree bridges -/

noncomputable def chapter08CartierDivisorAdd
    {X : Chapter08ArithmeticSurface}
    [LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09LineBundleTensorTheory X.carrier]
    (D G : Chapter08CartierDivisor X) : Chapter08CartierDivisor X :=
  by
    classical
    exact
      { lineBundle :=
          LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.chapter09Tensor
            D.lineBundle G.lineBundle
        coefficient := fun C => D.coefficient C + G.coefficient C
        support := D.support ∪ G.support
        support_contains_nonzero := by
          intro C hC
          by_cases hD : D.coefficient C = 0
          · have hG : G.coefficient C ≠ 0 := by
              intro hG
              apply hC
              simp [hD, hG]
            exact Finset.mem_union.mpr (Or.inr (G.support_contains_nonzero C hG))
          · exact Finset.mem_union.mpr (Or.inl (D.support_contains_nonzero C hD)) }

class Chapter08CurveDegreeTheory
    {X : Chapter08ArithmeticSurface} (C : Chapter08VerticalCurve X) where
  degree : Chapter08LineBundle C.prime.carrier → ℤ
  degree_structureSheaf :
    degree (chapter08StructureSheafLineBundle C.prime.carrier) = 0
  degree_isomorphic :
    ∀ {L M : Chapter08LineBundle C.prime.carrier},
      chapter08LineBundleIsomorphic L M → degree L = degree M

class Chapter08CurveDegreeTensorTheory
    {X : Chapter08ArithmeticSurface} (C : Chapter08VerticalCurve X)
    [LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09LineBundleTensorTheory C.prime.carrier]
    [Chapter08CurveDegreeTheory C] where
  degree_tensor :
    ∀ (L M : Chapter08LineBundle C.prime.carrier),
      Chapter08CurveDegreeTheory.degree
          (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.chapter09Tensor L M) =
        Chapter08CurveDegreeTheory.degree L +
          Chapter08CurveDegreeTheory.degree M

def chapter08Degree
    {X : Chapter08ArithmeticSurface} (C : Chapter08VerticalCurve X)
    [Chapter08CurveDegreeTheory C]
    (L : Chapter08LineBundle C.prime.carrier) : ℤ :=
  Chapter08CurveDegreeTheory.degree L

def chapter08DivisorCurveIntersection
    {X : Chapter08ArithmeticSurface} (D : Chapter08CartierDivisor X)
    (C : Chapter08VerticalCurve X) [Chapter08CurveDegreeTheory C] : ℤ :=
  chapter08Degree C (chapter08PullbackLineBundle C.prime.inclusion D.lineBundle)

abbrev Chapter08VerticalOneCycle (X : Chapter08ArithmeticSurface) :=
  Chapter08VerticalCurve X →₀ ℤ

def chapter08DivisorOneCycleIntersection
    {X : Chapter08ArithmeticSurface} (D : Chapter08CartierDivisor X)
    (V : Chapter08VerticalOneCycle X)
    [∀ C : Chapter08VerticalCurve X, Chapter08CurveDegreeTheory C] : ℤ :=
  ∑ C ∈ V.support, V C * chapter08DivisorCurveIntersection D C

/- LOCAL_DEPENDENCY_GUESS: the principal-divisor construction and its
trivializing section are supplied by the Cartier-divisor chapter. -/
structure Chapter08PrincipalDivisorData (X : Chapter08ArithmeticSurface) where
  rationalFunctions : Type u
  f : rationalFunctions
  f_isNonzero : Prop
  divisor : Chapter08CartierDivisor X
  lineBundle_trivialization :
    chapter08LineBundleIsomorphic divisor.lineBundle
      (chapter08StructureSheafLineBundle X.carrier)

/-! ### A chosen degree on the base -/

structure Chapter08BaseDegreeChoice (X : Chapter08ArithmeticSurface) where
  degree : Chapter08BaseDivisor X → ℤ

def chapter08FiberwiseDegree
    {X : Chapter08ArithmeticSurface}
    (d : Chapter08BaseDegreeChoice X) (Z : Chapter08BaseDivisor X) : ℤ :=
  d.degree Z

end
end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter08
