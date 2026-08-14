import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Polynomial.Basic
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Section02RelativeEffectiveCartierDivisors

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
open scoped BigOperators

noncomputable section

universe u v

/-!
The preceding chapters already contain the canonical ideal-sheaf, effective-Cartier,
finite-flat, line-bundle, and fiber constructions.  Chapter 5 keeps book-facing
names as abbreviations so that its numerical statements do not introduce parallel
geometric objects.
-/

abbrev Chapter05LineBundle (X : Scheme) := Chapter09LineBundle X

abbrev Chapter05LineBundleIso {X : Scheme}
    (L M : Chapter05LineBundle X) := Chapter09LineBundleIso L M

abbrev Chapter05EffectiveCartierDivisor (X : Scheme) :=
  Chapter10EffectiveCartierDivisor X

abbrev Chapter05CartierExactSequence {X : Scheme}
    (D : Chapter05EffectiveCartierDivisor X) :=
  Chapter10CartierExactSequence D

abbrev Chapter05FiniteLocallyFreeProfile {X Y : Scheme} (q : X ⟶ Y) (d : ℕ) :=
  Chapter10FiniteLocallyFreeProfile q d

abbrev Chapter05LocallyConstant {α β : Type*} [TopologicalSpace α] (g : α → β) : Prop :=
  Chapter08LocallyConstant g

abbrev Chapter05ProperCurveOverField (k : Type u) [Field k] :=
  Chapter09ProperCurveOverField k

/-! A regular integral proper curve retains the regularity hypothesis at its
local rings, since the pinned scheme API has no single scheme-level regularity
predicate.  The other fields are the standard scheme-theoretic predicates. -/

structure Chapter05ProperRegularIntegralCurve (k : Type u) [Field k] where
  curve : Chapter05ProperCurveOverField k
  integral : IsIntegral curve.carrier
  locallyNoetherian : IsLocallyNoetherian curve.carrier
  regular_stalk : ∀ x : curve.carrier,
    IsRegularLocalRing (curve.carrier.presheaf.stalk x)

instance (C : Chapter05ProperRegularIntegralCurve k) : IsIntegral C.curve.carrier :=
  C.integral

instance (C : Chapter05ProperRegularIntegralCurve k) :
    IsLocallyNoetherian C.curve.carrier := C.locallyNoetherian

abbrev Chapter05ProperRegularIntegralCurve.carrier
    (C : Chapter05ProperRegularIntegralCurve k) : Scheme := C.curve.carrier

abbrev Chapter05ProperRegularIntegralCurve.structureMap
    (C : Chapter05ProperRegularIntegralCurve k) : C.carrier ⟶ Spec (.of k) :=
  C.curve.structureMap

instance (C : Chapter05ProperRegularIntegralCurve k) : IsProper C.structureMap :=
  C.curve.proper

instance (C : Chapter05ProperRegularIntegralCurve k) : QuasiCompact C.structureMap :=
  C.curve.quasiCompact

/-! A divisor is a finite integral combination of closed points.  `Finsupp`
provides the finite support, while the predicate records the closed-point
condition which is implicit in the textbook notation `∑ nₓ[x]`. -/

structure Chapter05Divisor (X : Scheme) where
  coeff : X →₀ ℤ
  closed_support : ∀ x, x ∈ coeff.support → IsClosed ({x} : Set X)

@[ext]
theorem chapter05_divisor_ext {X : Scheme} {D E : Chapter05Divisor X}
    (h : D.coeff = E.coeff) : D = E := by
  cases D
  cases E
  cases h
  rfl

def chapter05DivisorAdd {X : Scheme} (D E : Chapter05Divisor X) : Chapter05Divisor X :=
  { coeff := D.coeff + E.coeff
    closed_support := by
      classical
      intro x hx
      rw [Finsupp.mem_support_iff] at hx
      by_cases hD : D.coeff x = 0
      · have hE : E.coeff x ≠ 0 := by
          intro hE
          apply hx
          simp [hD, hE]
        exact E.closed_support x (by simpa [Finsupp.mem_support_iff] using hE)
      · exact D.closed_support x (by simpa [Finsupp.mem_support_iff] using hD) }

def chapter05DivisorNeg {X : Scheme} (D : Chapter05Divisor X) : Chapter05Divisor X :=
  { coeff := -D.coeff
    closed_support := by
      intro x hx
      exact D.closed_support x (by simpa using hx) }

/-! Formula (5.1), with Mathlib's residue-degree function supplying
`[κ(x) : k]`. -/

noncomputable def chapter05Degree {k : Type u} [Field k]
    {X : Scheme} (f : X ⟶ Spec (.of k)) (D : Chapter05Divisor X) : ℤ :=
  ∑ x in D.coeff.support, D.coeff x * (f.residueDegree x : ℤ)

theorem chapter05_degree_formula {k : Type u} [Field k]
    {X : Scheme} (f : X ⟶ Spec (.of k)) (D : Chapter05Divisor X) :
    chapter05Degree f D =
      ∑ x in D.coeff.support, D.coeff x * (f.residueDegree x : ℤ) :=
  rfl

theorem chapter05_degree_add {k : Type u} [Field k]
    {X : Scheme} (f : X ⟶ Spec (.of k)) (D E : Chapter05Divisor X) :
    chapter05Degree f (chapter05DivisorAdd D E) =
      chapter05Degree f D + chapter05Degree f E := by
  sorry

theorem chapter05_degree_neg {k : Type u} [Field k]
    {X : Scheme} (f : X ⟶ Spec (.of k)) (D : Chapter05Divisor X) :
    chapter05Degree f (chapter05DivisorNeg D) = -chapter05Degree f D := by
  sorry

def chapter05SinglePointDivisor {k : Type u} [Field k]
    {X : Scheme} (f : X ⟶ Spec (.of k)) (x : X)
    (hx : IsClosed ({x} : Set X)) : Chapter05Divisor X :=
  { coeff := Finsupp.single x 1
    closed_support := by
      classical
      intro y hy
      have : y = x := by simpa [Finsupp.mem_support_iff] using hy
      simpa [this] using hx }

/-! A rational point is kept as a section over the base field.  The closedness
field makes the induced point divisor available without importing an additional
finite-type/closed-point theorem at every use site. -/

structure Chapter05RationalPoint {k : Type u} [Field k]
    {X : Scheme} (f : X ⟶ Spec (.of k)) where
  section_ : Spec (.of k) ⟶ X
  over : section_ ≫ f = 𝟙 _
  point : X
  point_eq_image : point = section_ (IsLocalRing.closedPoint k)
  closed : IsClosed ({point} : Set X)

theorem chapter05_rational_point_degree_one {k : Type u} [Field k]
    {X : Scheme} (f : X ⟶ Spec (.of k)) (p : Chapter05RationalPoint f) :
    chapter05Degree f (chapter05SinglePointDivisor f p.point p.closed) = 1 := by
  sorry

/-! The projective-line example is phrased by the residue-field presentation
of the closed point.  This is the canonical algebraic meaning of being cut out
by an irreducible polynomial, and it also records the degree used by (5.1). -/

structure Chapter05ProjectiveLinePolynomialPoint (k : Type u) [Field k] where
  polynomial : Polynomial k
  irreducible : Irreducible polynomial
  point : chapter04ProjectiveLine k
  closed : IsClosed ({point} : Set (chapter04ProjectiveLine k))
  residueFieldIso :
    (chapter04ProjectiveLine k).residueField point ≅
      CommRingCat.of (AdjoinRoot polynomial)

theorem chapter05_projective_line_irreducible_polynomial_point_degree
    (k : Type u) [Field k] (P : Chapter05ProjectiveLinePolynomialPoint k) :
    chapter05Degree (chapter04ProjectiveLineStructureMap k)
        (chapter05SinglePointDivisor
          (chapter04ProjectiveLineStructureMap k) P.point P.closed) =
      P.polynomial.natDegree := by
  sorry

/-! Mathlib supplies the function field and order of vanishing.  The finite
support packaging of the resulting Weil divisor is isolated as the one local
interface needed by this chapter. -/

structure Chapter05PrincipalDivisorData {X : Scheme}
    [IsIntegral X] [IsLocallyNoetherian X] (g : X.functionField) where
  nonzero : g ≠ 0
  divisor : Chapter05Divisor X
  coefficient_eq : ∀ x : X,
    divisor.coeff x = if h : coheight x = 1 then Scheme.ord g x else 0

theorem chapter05_principal_divisor_exists
    (C : Chapter05ProperRegularIntegralCurve k)
    (g : C.carrier.functionField) (hg : g ≠ 0) :
    Nonempty (Chapter05PrincipalDivisorData g) := by
  sorry

/-! The base-field algebra is canonical from the structure morphism, but the
pinned snapshot does not expose its global-section-to-function-field bridge.
This small class records that bridge without changing the meaning of
nonconstant rational function. -/

class Chapter05FunctionFieldBaseAlgebra (C : Chapter05ProperRegularIntegralCurve k) where
  toAlgebra : Algebra k C.carrier.functionField

instance (C : Chapter05ProperRegularIntegralCurve k)
    [h : Chapter05FunctionFieldBaseAlgebra C] :
    Algebra k C.carrier.functionField := h.toAlgebra

def chapter05NonconstantRationalFunction
    (C : Chapter05ProperRegularIntegralCurve k)
    [Chapter05FunctionFieldBaseAlgebra C]
    (g : C.carrier.functionField) : Prop :=
  ∀ a : k, algebraMap k C.carrier.functionField a ≠ g

structure Chapter05RationalFunctionMapData
    (C : Chapter05ProperRegularIntegralCurve k)
    [Chapter05FunctionFieldBaseAlgebra C]
    (g : C.carrier.functionField) where
  map : C.carrier ⟶ chapter04ProjectiveLine k
  over : map ≫ chapter04ProjectiveLineStructureMap k = C.structureMap
  nonconstant : chapter05NonconstantRationalFunction C g
  finite : IsFinite map

theorem chapter05_nonconstant_rational_function_gives_finite_map
    (C : Chapter05ProperRegularIntegralCurve k)
    [Chapter05FunctionFieldBaseAlgebra C]
    (g : C.carrier.functionField)
    (hg : chapter05NonconstantRationalFunction C g) :
    Nonempty (Chapter05RationalFunctionMapData C g) := by
  sorry

theorem chapter05_rational_function_map_is_proper_and_quasiFinite
    (C : Chapter05ProperRegularIntegralCurve k)
    [Chapter05FunctionFieldBaseAlgebra C]
    (g : C.carrier.functionField)
    (W : Chapter05RationalFunctionMapData C g) :
    IsProper W.map ∧ QuasiFinite W.map := by
  letI : IsFinite W.map := W.finite
  constructor <;> infer_instance

def chapter05LinearlyEquivalent {X : Scheme}
    [IsIntegral X] [IsLocallyNoetherian X]
    (D E : Chapter05Divisor X) : Prop :=
  ∃ g : X.functionField, ∃ P : Chapter05PrincipalDivisorData g,
    D.coeff - E.coeff = P.divisor.coeff

theorem chapter05_linearlyEquivalent_refl {X : Scheme}
    [IsIntegral X] [IsLocallyNoetherian X] (D : Chapter05Divisor X) :
    chapter05LinearlyEquivalent D D := by
  sorry

theorem chapter05_linearlyEquivalent_symm {X : Scheme}
    [IsIntegral X] [IsLocallyNoetherian X] {D E : Chapter05Divisor X} :
    chapter05LinearlyEquivalent D E → chapter05LinearlyEquivalent E D := by
  sorry

theorem chapter05_linearlyEquivalent_trans {X : Scheme}
    [IsIntegral X] [IsLocallyNoetherian X] {D E F : Chapter05Divisor X} :
    chapter05LinearlyEquivalent D E → chapter05LinearlyEquivalent E F →
      chapter05LinearlyEquivalent D F := by
  sorry

def chapter05LinearEquivalenceSetoid (X : Scheme)
    [IsIntegral X] [IsLocallyNoetherian X] : Setoid (Chapter05Divisor X) :=
  { r := chapter05LinearlyEquivalent
    iseqv :=
      { refl := chapter05_linearlyEquivalent_refl
        symm := chapter05_linearlyEquivalent_symm
        trans := chapter05_linearlyEquivalent_trans } }

abbrev Chapter05PicardQuotient (C : Chapter05ProperRegularIntegralCurve k) :=
  Quotient (chapter05LinearEquivalenceSetoid C.carrier)

/-! Degree via Euler characteristic is kept at the module-sheaf level.  The
exact-additivity field is the missing coherent-cohomology interface; all
numerical definitions below are genuine consequences of this canonical shape. -/

class Chapter05EulerCharacteristicTheory (X : Scheme) where
  eulerCharacteristic : X.Modules → ℤ
  exact_additive : ∀ {A B C : X.Modules} (i : A ⟶ B) (p : B ⟶ C)
    (hzero : i ≫ p = 0),
    (ShortComplex.mk i p hzero).Exact →
      eulerCharacteristic B = eulerCharacteristic A + eulerCharacteristic C

def chapter05EulerCharacteristic {X : Scheme}
    [Chapter05EulerCharacteristicTheory X] (M : X.Modules) : ℤ :=
  Chapter05EulerCharacteristicTheory.eulerCharacteristic M

def chapter05LineBundleDegree {X : Scheme}
    [Chapter05EulerCharacteristicTheory X] (L : Chapter05LineBundle X) : ℤ :=
  chapter05EulerCharacteristic L.module -
    chapter05EulerCharacteristic (chapter09StructureSheafLineBundle X).module

theorem chapter05_lineBundleDegree_formula {X : Scheme}
    [Chapter05EulerCharacteristicTheory X] (L : Chapter05LineBundle X) :
    chapter05LineBundleDegree L =
      chapter05EulerCharacteristic L.module -
        chapter05EulerCharacteristic (chapter09StructureSheafLineBundle X).module :=
  rfl

structure Chapter05DivisorPresentation {X : Scheme}
    (L : Chapter05LineBundle X) where
  divisor : Chapter05Divisor X
  associatedLineBundle : Chapter05LineBundle X
  isomorphic : Nonempty (Chapter05LineBundleIso L associatedLineBundle)

class Chapter05DivisorRepresentationTheory (X : Scheme) where
  every_line_bundle_has_divisor :
    ∀ L : Chapter05LineBundle X, Nonempty (Chapter05DivisorPresentation L)

/-! Relative curves and their fiberwise Euler-characteristic profile. -/

structure Chapter05ProjectiveFlatRelativeCurve where
  S : Scheme
  X : Scheme
  f : X ⟶ S
  baseLocallyNoetherian : IsLocallyNoetherian S
  totalLocallyNoetherian : IsLocallyNoetherian X
  projective : Chapter08IsProjective f
  flat : Flat f
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  relativeCurve : Chapter09RelativeCurve f

instance (F : Chapter05ProjectiveFlatRelativeCurve) :
    IsLocallyNoetherian F.S := F.baseLocallyNoetherian

instance (F : Chapter05ProjectiveFlatRelativeCurve) :
    IsLocallyNoetherian F.X := F.totalLocallyNoetherian

instance (F : Chapter05ProjectiveFlatRelativeCurve) : Flat F.f := F.flat

instance (F : Chapter05ProjectiveFlatRelativeCurve) :
    LocallyOfFinitePresentation F.f := F.locallyOfFinitePresentation

theorem chapter05_projective_family_is_proper
    (F : Chapter05ProjectiveFlatRelativeCurve) : IsProper F.f := by
  letI : Chapter08IsProjective F.f := F.projective
  exact chapter08_projective_is_proper (f := F.f)

instance (F : Chapter05ProjectiveFlatRelativeCurve) : IsProper F.f :=
  chapter05_projective_family_is_proper F

def chapter05FiberLineBundle (F : Chapter05ProjectiveFlatRelativeCurve)
    (L : Chapter05LineBundle F.X) (s : F.S) :
    Chapter05LineBundle (F.f.fiber s) :=
  chapter09PullbackLineBundle (F.f.fiberι s) L

class Chapter05FiberEulerCharacteristicTheory
    (F : Chapter05ProjectiveFlatRelativeCurve) where
  eulerCharacteristic :
    ∀ (s : F.S), Chapter05LineBundle (F.f.fiber s) → ℤ
  locally_constant :
    ∀ L : Chapter05LineBundle F.X,
      Chapter05LocallyConstant
        (fun s => eulerCharacteristic s (chapter05FiberLineBundle F L s))

def chapter05FiberEulerCharacteristic
    (F : Chapter05ProjectiveFlatRelativeCurve)
    [Chapter05FiberEulerCharacteristicTheory F]
    (s : F.S) (L : Chapter05LineBundle (F.f.fiber s)) : ℤ :=
  Chapter05FiberEulerCharacteristicTheory.eulerCharacteristic s L

def chapter05FiberDegree
    (F : Chapter05ProjectiveFlatRelativeCurve)
    [Chapter05FiberEulerCharacteristicTheory F]
    (L : Chapter05LineBundle F.X) (s : F.S) : ℤ :=
  chapter05FiberEulerCharacteristic F s (chapter05FiberLineBundle F L s) -
    chapter05FiberEulerCharacteristic F s
      (chapter09StructureSheafLineBundle (F.f.fiber s))

structure Chapter05FpqcCover (S : Scheme) where
  total : Scheme
  map : total ⟶ S
  flat : Flat map
  quasiCompact : QuasiCompact map
  surjective : Surjective map

structure Chapter05ProjectiveAfterFpqcCover {X S : Scheme} (f : X ⟶ S) where
  cover : Chapter05FpqcCover S
  baseChange : Scheme := pullback f cover.map
  projection : baseChange ⟶ cover.total := pullback.snd f cover.map
  projective : Chapter09ProjectiveMorphism projection

def chapter05BaseChangeTotal {X S T : Scheme}
    (f : X ⟶ S) (g : T ⟶ S) : Scheme := pullback f g

def chapter05BaseChangeProjection {X S T : Scheme}
    (f : X ⟶ S) (g : T ⟶ S) : chapter05BaseChangeTotal f g ⟶ T :=
  pullback.snd f g

def chapter05BaseChangeLineBundle {X S T : Scheme}
    (f : X ⟶ S) (g : T ⟶ S) (L : Chapter05LineBundle X) :
    Chapter05LineBundle (chapter05BaseChangeTotal f g) :=
  chapter09PullbackLineBundle (pullback.fst f g) L

/-! Local intersection multiplicity is the length of the stalk quotient. -/

noncomputable def chapter05LocalIntersectionQuotient
    {X : Scheme} (x : X) (a b : X.presheaf.stalk x) :=
  (X.presheaf.stalk x) ⧸ Ideal.span ({a, b} : Set (X.presheaf.stalk x))

structure Chapter05ProperIntersectionPoint
    {X S : Scheme} (f : X ⟶ S)
    (D : Chapter05EffectiveCartierDivisor X) (s : S) where
  point : X
  on_divisor : point ∈ D.ideal.support
  on_fiber : f point = s
  divisor_equation : X.presheaf.stalk point
  fiber_equation : X.presheaf.stalk point
  divisor_equation_local_generator :
    ∃ (U : X.affineOpens) (hx : point ∈ U.1) (a : Γ(X, U)),
      D.ideal U = Ideal.span {a} ∧
        divisor_equation = (X.presheaf.germ U point hx).hom a
  regular_sequence :
    RingTheory.Sequence.IsRegular (X.presheaf.stalk point)
      [divisor_equation, fiber_equation]

noncomputable def chapter05LocalIntersectionMultiplicity
    {X S : Scheme} {f : X ⟶ S}
    {D : Chapter05EffectiveCartierDivisor X} {s : S}
    (p : Chapter05ProperIntersectionPoint f D s) : ℕ :=
  (Module.length (X.presheaf.stalk p.point)
      (chapter05LocalIntersectionQuotient p.point
        p.divisor_equation p.fiber_equation)).toNat

def chapter05LocalIntersectionTerm
    {X S : Scheme} {f : X ⟶ S}
    {D : Chapter05EffectiveCartierDivisor X} {s : S}
    (p : Chapter05ProperIntersectionPoint f D s) : ℤ :=
  (chapter05LocalIntersectionMultiplicity p : ℤ) * (f.residueDegree p.point : ℤ)

structure Chapter05ProperIntersectionData
    {X S : Scheme} (f : X ⟶ S)
    (D : Chapter05EffectiveCartierDivisor X) (s : S) where
  points : Finset X
  point_data : ∀ x, x ∈ points → Chapter05ProperIntersectionPoint f D s
  point_data_eq : ∀ x hx, (point_data x hx).point = x
  support_exact : ∀ x : X,
    x ∈ D.ideal.support → (f x = s ↔ x ∈ points)

def chapter05IntersectionNumber
    {X S : Scheme} {f : X ⟶ S}
    {D : Chapter05EffectiveCartierDivisor X} {s : S}
    (I : Chapter05ProperIntersectionData f D s) : ℤ :=
  ∑ x in I.points, chapter05LocalIntersectionTerm (I.point_data x (by simp))

def chapter05ContainsFiber
    {X S : Scheme} (f : X ⟶ S)
    (D : Chapter05EffectiveCartierDivisor X) (s : S) : Prop :=
  ∀ x : X, f x = s → x ∈ D.ideal.support

theorem chapter05_vertical_divisor_has_no_proper_intersection
    {X S : Scheme} (f : X ⟶ S)
    (D : Chapter05EffectiveCartierDivisor X) (s : S)
    (hvertical : chapter05ContainsFiber f D s)
    (hfiber_not_finite : ¬ (Set.Finite (f ⁻¹' ({s} : Set S)))) :
    ¬ Nonempty (Chapter05ProperIntersectionData f D s) := by
  sorry

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05
