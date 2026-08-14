import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Section03SectionsWithoutCommonZeros
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finite.Vector
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory

/-!
## 2.4 Closed subschemes from homogeneous ideals

For `S = Spec R`, the homogeneous-ideal construction is first stated using the canonical
`Ideal.IsHomogeneous` predicate for a selected graded algebra.  The quotient grading and the
relative base map are isolated as local dependencies because the pinned Proj API does not package
relative quotient gradings.
-/

abbrev chapter02Spec (R : Type u) [CommRing R] : Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of R)

def Chapter02IsHomogeneousIdeal
    {R A : Type u} [CommSemiring R] [Semiring A] [Algebra R A]
    (G : Chapter02GradedAlgebra R A) (I : Ideal A) : Prop := by
  letI : GradedAlgebra G.component := G.graded
  exact I.IsHomogeneous G.component

/-!
This structure packages a Mathlib homogeneous ideal together with the induced quotient grading
needed by the projective-spectrum construction.
-/
structure Chapter02HomogeneousIdealData
    {R A : Type u} [CommSemiring R] [CommRing A] [Algebra R A]
    (G : Chapter02GradedAlgebra R A) where
  ideal : Ideal A
  is_homogeneous : Chapter02IsHomogeneousIdeal G ideal
  /-- The grading on the quotient is part of the induced quotient construction. -/
  quotientGrading : Chapter02GradedAlgebra R (A ⧸ ideal)
  quotientGrading_component_iff :
    ∀ d (x : A ⧸ ideal),
      x ∈ quotientGrading.component d ↔
        ∃ a : A, a ∈ G.component d ∧ Ideal.Quotient.mk ideal a = x

/-!
The data structure above records the quotient grading explicitly because that construction is not
yet exposed by the pinned projective-spectrum API.  Keep a constructor-level interface for the
actual mathematical input (a homogeneous ideal); returning a prebuilt `Chapter02HomogeneousIdealData`
is materially stronger than asking callers to supply the desired quotient grading themselves.
-/
theorem chapter02_homogeneous_ideal_data_exists
    {R A : Type u} [CommSemiring R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A} (I : Ideal A)
    (hI : Chapter02IsHomogeneousIdeal G I) :
    Nonempty {J : Chapter02HomogeneousIdealData G // J.ideal = I} := by
  sorry

noncomputable def chapter02HomogeneousIdealDataOf
    {R A : Type u} [CommSemiring R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A} (I : Ideal A)
    (hI : Chapter02IsHomogeneousIdeal G I) :
    Chapter02HomogeneousIdealData G :=
  (Classical.choice (chapter02_homogeneous_ideal_data_exists I hI)).1

theorem chapter02_homogeneous_ideal_data_of_ideal
    {R A : Type u} [CommSemiring R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A} (I : Ideal A)
    (hI : Chapter02IsHomogeneousIdeal G I) :
    (chapter02HomogeneousIdealDataOf I hI).ideal = I := by
  exact (Classical.choice (chapter02_homogeneous_ideal_data_exists I hI)).2

def chapter02HomogeneousIdealToIdeal
    {R A : Type u} [CommSemiring R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) : Ideal A :=
  I.ideal

theorem chapter02_homogeneous_ideal_to_ideal_data_of
    {R A : Type u} [CommSemiring R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A} (I : Ideal A)
    (hI : Chapter02IsHomogeneousIdeal G I) :
    chapter02HomogeneousIdealToIdeal (chapter02HomogeneousIdealDataOf I hI) = I := by
  exact chapter02_homogeneous_ideal_data_of_ideal I hI

theorem chapter02_homogeneous_ideal_is_homogeneous
    {R A : Type u} [CommSemiring R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) :
    Chapter02IsHomogeneousIdeal G (chapter02HomogeneousIdealToIdeal I) :=
  I.is_homogeneous

abbrev Chapter02PolynomialHomogeneousIdealData (R : Type u) [CommRing R] (r : ℕ) :=
  Chapter02HomogeneousIdealData (chapter02PolynomialGradedAlgebra R r)

abbrev chapter02HomogeneousQuotientRing
    {R A : Type u} [CommSemiring R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) : Type u :=
  A ⧸ I.ideal

/- LOCAL_DEPENDENCY_GUESS: a homogeneous ideal induces the standard quotient grading. -/
theorem chapter02_homogeneous_quotient_grading_exists
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) :
    Nonempty (Chapter02GradedAlgebra R (chapter02HomogeneousQuotientRing I)) := by
  exact ⟨I.quotientGrading⟩

noncomputable def chapter02HomogeneousQuotientGrading
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) :
    Chapter02GradedAlgebra R (chapter02HomogeneousQuotientRing I) :=
  I.quotientGrading

def chapter02VPlus
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) : Scheme.{u} :=
  chapter02ProjOfGradedAlgebra (chapter02HomogeneousQuotientGrading I)

theorem chapter02_vplus_is_proj_of_homogeneous_quotient
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) :
    chapter02VPlus I =
      chapter02ProjOfGradedAlgebra (chapter02HomogeneousQuotientGrading I) :=
  rfl

/-!
The structure map is obtained from `Proj.toSpecZero` and the degree-zero projection of the
graded `R`-algebra.  This avoids choosing an unrelated morphism merely because one exists.
-/
noncomputable def chapter02GradedAlgebraProjection
    (R : Type u) [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    (G : Chapter02GradedAlgebra R A) :
    chapter02ProjOfGradedAlgebra G ⟶ chapter02Spec R := by
  exact chapter02GradedAlgebraToSpec R G

theorem chapter02_vplus_base_map_exists
    (R : Type u) [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) :
    Nonempty (chapter02VPlus I ⟶ chapter02Spec R) := by
  exact ⟨chapter02GradedAlgebraProjection R (chapter02HomogeneousQuotientGrading I)⟩

noncomputable def chapter02VPlusProjection
    (R : Type u) [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) : chapter02VPlus I ⟶ chapter02Spec R :=
  chapter02GradedAlgebraProjection R (chapter02HomogeneousQuotientGrading I)

def Chapter02HomogeneousPolynomial
    {R A : Type u} [CommSemiring R] [Semiring A] [Algebra R A]
    (G : Chapter02GradedAlgebra R A) (d : ℕ) :=
  {F : A // F ∈ G.component d}

def Chapter02HomogeneousPolynomialInIdeal
    {R A : Type u} [CommSemiring R] [CommRing A] [Algebra R A]
    {G : Chapter02GradedAlgebra R A}
    (I : Chapter02HomogeneousIdealData G) (d : ℕ) :=
  {F : A // F ∈ I.ideal ∧ F ∈ G.component d}

/-!
The following point API is specialized to the source assertion `R[x_0, …, x_r]`; the polynomial
ring, its grading, and the coordinate module therefore share the same `r` instead of being
independent parameters.
-/
abbrev Chapter02PolynomialHomogeneousPolynomial (R : Type u) [CommRing R]
    (r d : ℕ) :=
  Chapter02HomogeneousPolynomial (chapter02PolynomialGradedAlgebra R r) d

abbrev Chapter02PolynomialHomogeneousPolynomialInIdeal (R : Type u) [CommRing R]
    (r : ℕ) (I : Chapter02PolynomialHomogeneousIdealData R r) (d : ℕ) :=
  Chapter02HomogeneousPolynomialInIdeal I d

abbrev Chapter02PolynomialVPlus
    (R : Type u) [CommRing R] (r : ℕ)
    (I : Chapter02PolynomialHomogeneousIdealData R r) : Scheme.{u} :=
  chapter02VPlus I

abbrev chapter02PolynomialVPlusProjection
    (R : Type u) [CommRing R] (r : ℕ)
    (I : Chapter02PolynomialHomogeneousIdealData R r) :
    Chapter02PolynomialVPlus R r I ⟶ chapter02Spec R :=
  chapter02VPlusProjection R I

/- LOCAL_DEPENDENCY_GUESS: the homogeneous quotient map induces the closed immersion into
the polynomial projective space, with the displayed structure morphism over `Spec R`. -/
theorem chapter02_polynomial_vplus_is_closed_subscheme
    (R : Type u) [CommRing R] (r : ℕ)
    (I : Chapter02PolynomialHomogeneousIdealData R r) :
    ∃ i : Chapter02PolynomialVPlus R r I ⟶ chapter02ProjectiveSpaceOverRing R r,
      i ≫ chapter02ProjectiveSpaceOverRingProjection R r =
          chapter02PolynomialVPlusProjection R r I ∧
        IsClosedImmersion i := by
  sorry

/-!
The value of a homogeneous polynomial on a quotient is the only sheaf-tensor operation needed
for the pointwise statement.  It is a named interface so that the later tensor-power API can
replace it without changing the `V_+(I)` point type.
-/
def chapter02PolynomialCoordinate
    (R : Type u) [CommRing R] (r : ℕ) (i : Fin (r + 1)) :
    Chapter02PolynomialHomogeneousPolynomial R r 1 :=
  ⟨MvPolynomial.X i, by
    change MvPolynomial.X i ∈
      MvPolynomial.homogeneousSubmodule (σ := Fin (r + 1)) (R := R) 1
    exact (MvPolynomial.mem_homogeneousSubmodule 1 (MvPolynomial.X i)).2
      (MvPolynomial.isHomogeneous_X (R := R) i)⟩

def chapter02PolynomialQuotientCoordinateSection
    (R : Type u) [CommRing R] (r : ℕ)
    {T : Scheme.{u}}
    (q : Chapter02InvertibleQuotientPair
      (chapter02FreeQuasiCoherentModule T (Chapter02ProjectiveSpaceIndex r)).carrier)
    (i : Fin (r + 1)) : q.line.carrier.sections :=
  SheafOfModules.sectionsMap q.quotient
    (SheafOfModules.freeSection (R := T.ringCatSheaf) (ULift.up i))

structure Chapter02PolynomialHomogeneousEvaluation
    (R : Type u) [CommRing R] (r : ℕ)
    {T : Scheme.{u}} (f : T ⟶ chapter02Spec R)
    (q : Chapter02InvertibleQuotientPair
      (chapter02FreeQuasiCoherentModule T (Chapter02ProjectiveSpaceIndex r)).carrier) where
  /-- The degreewise evaluation of homogeneous polynomials in the quotient line. -/
  value : ∀ d, Chapter02PolynomialHomogeneousPolynomial R r d →
    (chapter02LineBundlePowerBundle q.line d).carrier.sections
  /-- Evaluation sends a zero homogeneous polynomial to the zero section. -/
  value_zero : ∀ d (F : Chapter02PolynomialHomogeneousPolynomial R r d),
    F.1 = 0 →
      value d F = chapter02ZeroSection (chapter02LineBundlePowerBundle q.line d).carrier
  /-- Evaluation is additive in each homogeneous degree. -/
  value_add : ∀ d (F G H : Chapter02PolynomialHomogeneousPolynomial R r d),
    H.1 = F.1 + G.1 →
      value d H =
        chapter02AddSection (chapter02LineBundlePowerBundle q.line d).carrier
          (value d F) (value d G)
  /-- Evaluation uses the base coefficient action on homogeneous sections. -/
  value_smul : ∀ d (c : R) (F H : Chapter02PolynomialHomogeneousPolynomial R r d),
    H.1 = c • F.1 →
      value d H =
        chapter02BaseScalarAction R (Chapter02ProjectiveSpaceIndex r) f q d c
          (value d F)
  /-- Evaluation is multiplicative across homogeneous degrees. -/
  value_mul : ∀ m n (F : Chapter02PolynomialHomogeneousPolynomial R r m)
      (G : Chapter02PolynomialHomogeneousPolynomial R r n)
      (H : Chapter02PolynomialHomogeneousPolynomial R r (m + n)),
    H.1 = F.1 * G.1 →
      value (m + n) H =
        chapter02PowerSectionProduct q.line m n (value m F) (value n G)
  /-- The constant polynomial `1` evaluates to the unit section in degree zero. -/
  value_one : ∀ F : Chapter02PolynomialHomogeneousPolynomial R r 0,
    F.1 = 1 →
      value 0 F =
        SheafOfModules.sectionsMap
          (chapter02LineBundlePowerData q.line).power_zero.inv
          ((SheafOfModules.unit T.ringCatSheaf).unitHomEquiv (𝟙 _))
  /-- Degree-one evaluation is the quotient's coordinate section, transported to `L¹`. -/
  value_on_coordinate : ∀ i,
    value 1 (chapter02PolynomialCoordinate R r i) =
      SheafOfModules.sectionsMap
        (chapter02LineBundlePowerData q.line).power_one.inv
        (chapter02PolynomialQuotientCoordinateSection R r q i)

/- LOCAL_DEPENDENCY_GUESS: evaluation of homogeneous polynomials in the quotient sections. -/
theorem chapter02_polynomial_homogeneous_evaluation_exists
    (R : Type u) [CommRing R] (r : ℕ)
    {T : Scheme.{u}} (f : T ⟶ chapter02Spec R)
    (q : Chapter02InvertibleQuotientPair
      (chapter02FreeQuasiCoherentModule T (Chapter02ProjectiveSpaceIndex r)).carrier) :
    Nonempty (Chapter02PolynomialHomogeneousEvaluation R r f q) := by
  sorry

/-!
The point condition must use one graded evaluation family for all representatives of a quotient
class.  Its transport field is the compatibility that makes vanishing independent of the chosen
line-bundle presentation.
-/
structure Chapter02PolynomialHomogeneousEvaluationFamily
    (R : Type u) [CommRing R] (r : ℕ)
    {T : Scheme.{u}} (f : T ⟶ chapter02Spec R) where
  evaluation : ∀ q : Chapter02InvertibleQuotientPair
      (chapter02FreeQuasiCoherentModule T (Chapter02ProjectiveSpaceIndex r)).carrier,
    Chapter02PolynomialHomogeneousEvaluation R r f q
  /-- Equivalent quotient representatives admit a compatible transport of all evaluations. -/
  transport : ∀ {q q'}
      (h : chapter02QuotientPairEquivalent q q'),
      ∀ (d : ℕ) (F : Chapter02PolynomialHomogeneousPolynomial R r d),
        SheafOfModules.sectionsMap
            (chapter02LineBundlePowerTransport (Classical.choose h) d).hom
            ((evaluation q).value d F) =
          (evaluation q').value d F

/- LOCAL_DEPENDENCY_GUESS: the quotient-compatible graded evaluation family exists. -/
theorem chapter02_polynomial_homogeneous_evaluation_family_exists
    (R : Type u) [CommRing R] (r : ℕ)
    {T : Scheme.{u}} (f : T ⟶ chapter02Spec R) :
    Nonempty (Chapter02PolynomialHomogeneousEvaluationFamily R r f) := by
  sorry

noncomputable def chapter02PolynomialHomogeneousEvaluationFamily
    (R : Type u) [CommRing R] (r : ℕ)
    {T : Scheme.{u}} (f : T ⟶ chapter02Spec R) :
    Chapter02PolynomialHomogeneousEvaluationFamily R r f :=
  Classical.choice (chapter02_polynomial_homogeneous_evaluation_family_exists R r f)

noncomputable def chapter02PolynomialHomogeneousEvaluation
    (R : Type u) [CommRing R] (r : ℕ)
    {T : Scheme.{u}} (f : T ⟶ chapter02Spec R)
    (q : Chapter02InvertibleQuotientPair
      (chapter02FreeQuasiCoherentModule T (Chapter02ProjectiveSpaceIndex r)).carrier) :
    Chapter02PolynomialHomogeneousEvaluation R r f q :=
  (chapter02PolynomialHomogeneousEvaluationFamily R r f).evaluation q

/-- A quotient-class point on `V_+(I)`, with all homogeneous elements of `I` evaluating to zero. -/
structure Chapter02PolynomialVPlusPoint
    (R : Type u) [CommRing R] (r : ℕ)
    (I : Chapter02PolynomialHomogeneousIdealData R r)
    {T : Scheme.{u}} (f : T ⟶ chapter02Spec R) where
  quotientClass :
    Chapter02InvertibleQuotientClass
      (chapter02FreeQuasiCoherentModule T (Chapter02ProjectiveSpaceIndex r)).carrier
  vanishes_on_ideal :
    ∀ q : Chapter02InvertibleQuotientPair
        (chapter02FreeQuasiCoherentModule T (Chapter02ProjectiveSpaceIndex r)).carrier,
      chapter02QuotientClassMk q = quotientClass →
        ∀ d (F : Chapter02PolynomialHomogeneousPolynomialInIdeal R r I d),
          ((chapter02PolynomialHomogeneousEvaluationFamily R r f).evaluation q).value
              d ⟨F.1, F.2.2⟩ =
            chapter02ZeroSection (chapter02LineBundlePowerBundle q.line d).carrier

abbrev Chapter02PolynomialVPlusPointOver
    (R : Type u) [CommRing R] (r : ℕ)
    (I : Chapter02PolynomialHomogeneousIdealData R r)
    {T : Scheme.{u}} (f : T ⟶ chapter02Spec R) :=
  {t : T ⟶ Chapter02PolynomialVPlus R r I //
    t ≫ chapter02PolynomialVPlusProjection R r I = f}

/- LOCAL_DEPENDENCY_GUESS: the quotient-point correspondence, including nilpotents and gluing. -/
theorem chapter02_polynomial_vplus_points_equiv
    (R : Type u) [CommRing R] (r : ℕ)
    (I : Chapter02PolynomialHomogeneousIdealData R r)
    {T : Scheme.{u}} (f : T ⟶ chapter02Spec R) :
    Nonempty (Chapter02PolynomialVPlusPointOver R r I f ≃
      Chapter02PolynomialVPlusPoint R r I f) := by
  sorry

/-!
### Veronese maps

The degree-`d` monomials are indexed by exponent vectors of total degree `d`.  This finite index
type has the binomial cardinality in the source, so its projective space is the displayed
`P^{binom{r+d}{d}-1}` up to the canonical finite-index reindexing.
-/

def Chapter02MonomialIndex (r d : ℕ) :=
  {a : Fin (r + 1) →₀ ℕ // a.sum (fun _ n => n) = d}

/- LOCAL_DEPENDENCY_GUESS: exponent vectors of fixed total degree form a finite type. -/
theorem chapter02_monomial_index_finite (r d : ℕ) :
    Finite (Chapter02MonomialIndex r d) := by
  change Finite {a : Fin (r + 1) →₀ ℕ // a.sum (fun _ n => n) = d}
  exact Finite.of_equiv (Sym (Fin (r + 1)) d)
    (Sym.equivNatSum (Fin (r + 1)) d)

noncomputable instance chapter02_monomial_index_fintype (r d : ℕ) :
    Fintype (Chapter02MonomialIndex r d) := by
  letI : Finite (Chapter02MonomialIndex r d) := chapter02_monomial_index_finite r d
  exact Fintype.ofFinite _

theorem chapter02_monomial_index_cardinality (r d : ℕ) :
    Fintype.card (Chapter02MonomialIndex r d) = Nat.choose (r + d) d := by
  have e : Sym (Fin (r + 1)) d ≃ Chapter02MonomialIndex r d :=
    Sym.equivNatSum (Fin (r + 1)) d
  rw [← Fintype.card_congr e]
  rw [Sym.card_sym_eq_choose]
  simp

def chapter02VeroneseTargetDimension (r d : ℕ) : ℕ :=
  Nat.choose (r + d) d - 1

theorem chapter02_veronese_target_dimension_succ (r d : ℕ) :
    chapter02VeroneseTargetDimension r d + 1 = Nat.choose (r + d) d := by
  simpa [chapter02VeroneseTargetDimension] using
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr (Nat.choose_pos (Nat.le_add_left d r)))

theorem chapter02_veronese_target_index_reindexing (r d : ℕ) :
    Nonempty (Chapter02MonomialIndex r d ≃
      Fin (chapter02VeroneseTargetDimension r d + 1)) := by
  refine ⟨?_⟩
  simpa [chapter02_monomial_index_cardinality,
    chapter02_veronese_target_dimension_succ] using
    (Fintype.equivFin (Chapter02MonomialIndex r d))

abbrev chapter02VeroneseTargetIndex (r d : ℕ) : Type u :=
  ULift.{u} (Chapter02MonomialIndex r d)

def chapter02VeroneseTargetData (S : Scheme.{u}) (r d : ℕ) :
    Chapter02ProjectiveSpaceData S (chapter02VeroneseTargetIndex r d) :=
  chapter02ProjectiveSpaceData S (chapter02VeroneseTargetIndex r d)

abbrev chapter02VeroneseTarget (S : Scheme.{u}) (r d : ℕ) : Scheme.{u} :=
  (chapter02VeroneseTargetData S r d).bundle.scheme

abbrev chapter02VeroneseStandardTarget (S : Scheme.{u}) (r d : ℕ) : Scheme.{u} :=
  chapter02ProjectiveSpace S (chapter02VeroneseTargetDimension r d)

/- LOCAL_DEPENDENCY_GUESS: reindexing a free projective bundle along the finite-coordinate equivalence. -/
theorem chapter02_veronese_target_reindexed_standard_projective_space
    (S : Scheme.{u}) (r d : ℕ) :
    ∃ e : chapter02VeroneseTarget S r d ≅
        chapter02VeroneseStandardTarget S r d,
      e.hom ≫ chapter02ProjectiveSpaceProjection S
          (chapter02VeroneseTargetDimension r d) =
        (chapter02VeroneseTargetData S r d).bundle.projection := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: multiplication of sections in the tensor powers constructs monomial sections. -/
def chapter02VeroneseMonomialSection
    {S : Scheme.{u}}
    (P : Chapter02ProjectiveSpaceData S (Chapter02ProjectiveSpaceIndex r))
    (d : ℕ) (a : Chapter02MonomialIndex r d) :
    (chapter02LineBundlePowerBundle P.bundle.twistingLineBundle d).carrier.sections := by
  sorry

structure Chapter02VeroneseCoordinateData
    (S : Scheme.{u}) (r d : ℕ)
    (P : Chapter02ProjectiveSpaceData S (Chapter02ProjectiveSpaceIndex r)) where
  coordinateSections :
    Chapter02MonomialIndex r d →
      (chapter02LineBundlePowerBundle P.bundle.twistingLineBundle d).carrier.sections
  coordinate_is_monomial :
    ∀ a, coordinateSections a = chapter02VeroneseMonomialSection P d a
  sections_generate :
    Chapter02SectionsGenerate
      (chapter02LineBundlePowerBundle P.bundle.twistingLineBundle d)
      (fun a : chapter02VeroneseTargetIndex r d => coordinateSections a.down)

/- LOCAL_DEPENDENCY_GUESS: the monomial sections generate the degree-d power of `𝒪(1)`. -/
theorem chapter02_veronese_coordinate_data_exists
    (S : Scheme.{u}) (r d : ℕ)
    (P : Chapter02ProjectiveSpaceData S (Chapter02ProjectiveSpaceIndex r)) :
    Nonempty (Chapter02VeroneseCoordinateData S r d P) := by
  sorry

noncomputable def chapter02VeroneseCoordinateData
    (S : Scheme.{u}) (r d : ℕ)
    (P : Chapter02ProjectiveSpaceData S (Chapter02ProjectiveSpaceIndex r)) :
    Chapter02VeroneseCoordinateData S r d P :=
  Classical.choice (chapter02_veronese_coordinate_data_exists S r d P)

structure Chapter02VeroneseMapData
    (S : Scheme.{u}) (r d : ℕ) where
  coordinateData : Chapter02VeroneseCoordinateData S r d
    (chapter02ProjectiveSpaceData S (Chapter02ProjectiveSpaceIndex r))
  map : chapter02ProjectiveSpace S r ⟶ (chapter02VeroneseTargetData S r d).bundle.scheme
  over : map ≫ (chapter02VeroneseTargetData S r d).bundle.projection =
    chapter02ProjectiveSpaceProjection S r
  pullbackTwistingLineIso :
    (Scheme.Modules.pullback map).obj
        (chapter02VeroneseTargetData S r d).bundle.twistingLineBundle.carrier ≅
      (chapter02LineBundlePowerBundle
        (chapter02ProjectiveSpaceTwistingLine S r) d).carrier
  coordinate_pullback :
    ∀ a : chapter02VeroneseTargetIndex r d,
      SheafOfModules.sectionsMap pullbackTwistingLineIso.hom
        ((chapter02PullbackSectionData map
          (chapter02VeroneseTargetData S r d).bundle.twistingLineBundle.carrier).map
          ((chapter02VeroneseTargetData S r d).coordinateSections a)) =
        coordinateData.coordinateSections a.down

/- LOCAL_DEPENDENCY_GUESS: the universal-property construction of the Veronese morphism. -/
theorem chapter02_veronese_map_data_exists (S : Scheme.{u}) (r d : ℕ) :
    Nonempty (Chapter02VeroneseMapData S r d) := by
  sorry

noncomputable def chapter02VeroneseMapData (S : Scheme.{u}) (r d : ℕ) :
    Chapter02VeroneseMapData S r d :=
  Classical.choice (chapter02_veronese_map_data_exists S r d)

abbrev chapter02VeroneseMap (S : Scheme.{u}) (r d : ℕ) :
    chapter02ProjectiveSpace S r ⟶
      (chapter02VeroneseTargetData S r d).bundle.scheme :=
  (chapter02VeroneseMapData S r d).map

theorem chapter02_veronese_map_is_over
    (S : Scheme.{u}) (r d : ℕ) :
    chapter02VeroneseMap S r d ≫
        (chapter02VeroneseTargetData S r d).bundle.projection =
      chapter02ProjectiveSpaceProjection S r :=
  (chapter02VeroneseMapData S r d).over

noncomputable def chapter02_veronese_pullback_of_twisting_line
    (S : Scheme.{u}) (r d : ℕ) :
      (Scheme.Modules.pullback (chapter02VeroneseMap S r d)).obj
        (chapter02VeroneseTargetData S r d).bundle.twistingLineBundle.carrier ≅
      (chapter02LineBundlePowerBundle
        (chapter02ProjectiveSpaceTwistingLine S r) d).carrier :=
  (chapter02VeroneseMapData S r d).pullbackTwistingLineIso

theorem chapter02_veronese_map_is_closed_immersion
    (S : Scheme.{u}) (r d : ℕ) (hd : 0 < d) :
    IsClosedImmersion (chapter02VeroneseMap S r d) := by
  sorry

/-!
On each standard chart, the target ratios contain the original affine coordinates.  The
chart-level package below is the precise algebraic interface used by the closed-immersion proof.
-/
structure Chapter02VeroneseAffineChartData (R : Type u) [CommRing R] (r d : ℕ) where
  sourceRing : Type u
  targetRing : Type u
  [sourceRingCommRing : CommRing sourceRing]
  [targetRingCommRing : CommRing targetRing]
  [sourceRingAlgebra : Algebra R sourceRing]
  [targetRingAlgebra : Algebra R targetRing]
  chartMap : targetRing →ₐ[R] sourceRing
  sourceCoordinate : Fin (r + 1) → sourceRing
  targetCoordinate : Chapter02MonomialIndex r d → targetRing
  targetRatio : Chapter02MonomialIndex r d → sourceRing
  targetRatio_eq_chartMap :
    ∀ a, targetRatio a = chartMap (targetCoordinate a)
  sourceCoordinate_in_target_ratios :
    ∀ i, ∃ a, sourceCoordinate i = targetRatio a
  sourceCoordinate_generate : Algebra.adjoin R (Set.range sourceCoordinate) = ⊤

attribute [instance] Chapter02VeroneseAffineChartData.sourceRingCommRing
  Chapter02VeroneseAffineChartData.targetRingCommRing
  Chapter02VeroneseAffineChartData.sourceRingAlgebra
  Chapter02VeroneseAffineChartData.targetRingAlgebra

def Chapter02VeroneseRatiosContainOriginalCoordinates
    {R : Type u} [CommRing R] {r d : ℕ}
    (c : Chapter02VeroneseAffineChartData R r d) : Prop :=
  ∀ i, ∃ a, c.sourceCoordinate i = c.targetRatio a

theorem chapter02_veronese_chart_ratio_criterion
    {R : Type u} [CommRing R] {r d : ℕ}
    (c : Chapter02VeroneseAffineChartData R r d) :
    Chapter02VeroneseRatiosContainOriginalCoordinates c ↔
      ∀ i, ∃ a, c.sourceCoordinate i = c.targetRatio a :=
  Iff.rfl

theorem chapter02_veronese_chart_ratios_generate_source_algebra
    {R : Type u} [CommRing R] {r d : ℕ}
    (c : Chapter02VeroneseAffineChartData R r d) :
    Algebra.adjoin R (Set.range c.targetRatio) = ⊤ := by
  sorry

/-!
The target-coordinate quadratic relations are the toric relations
`Y_a Y_b - Y_c Y_e` whenever `a+b=c+e` as exponent vectors.
-/
def chapter02VeroneseQuadraticRelation
    (R : Type u) [CommRing R] (r d : ℕ)
    (a b c e : Chapter02MonomialIndex r d) :
    MvPolynomial (Chapter02MonomialIndex r d) R :=
  MvPolynomial.monomial (Finsupp.single a 1 + Finsupp.single b 1) 1 -
    MvPolynomial.monomial (Finsupp.single c 1 + Finsupp.single e 1) 1

def Chapter02VeroneseQuadraticRelationPredicate
    (r d : ℕ) (a b c e : Chapter02MonomialIndex r d) : Prop :=
  a.1 + b.1 = c.1 + e.1

def chapter02VeroneseImageIdeal
    (R : Type u) [CommRing R] (r d : ℕ) :
    Ideal (MvPolynomial (Chapter02MonomialIndex r d) R) :=
  Ideal.span {F |
    ∃ a b c e : Chapter02MonomialIndex r d,
      Chapter02VeroneseQuadraticRelationPredicate r d a b c e ∧
        F = chapter02VeroneseQuadraticRelation R r d a b c e}

def chapter02VeroneseMonomialRingHom
    (R : Type u) [CommRing R] (r d : ℕ) :
    MvPolynomial (Chapter02MonomialIndex r d) R →ₐ[R]
      MvPolynomial (Fin (r + 1)) R :=
  MvPolynomial.aeval (fun a => MvPolynomial.monomial a.1 1)

theorem chapter02_veronese_quadratic_relation_maps_to_zero
    (R : Type u) [CommRing R] (r d : ℕ)
    (a b c e : Chapter02MonomialIndex r d)
    (h : Chapter02VeroneseQuadraticRelationPredicate r d a b c e) :
    chapter02VeroneseMonomialRingHom R r d
        (chapter02VeroneseQuadraticRelation R r d a b c e) = 0 := by
  simp only [chapter02VeroneseQuadraticRelation, map_sub]
  apply sub_eq_zero.mpr
  have h_eval (s : Chapter02MonomialIndex r d →₀ ℕ) :
      chapter02VeroneseMonomialRingHom R r d
          (MvPolynomial.monomial s (1 : R)) =
        MvPolynomial.monomial (s.sum (fun i n => n • i.1)) (1 : R) := by
    simp only [chapter02VeroneseMonomialRingHom, MvPolynomial.aeval_monomial,
      map_one, one_mul]
    simp_rw [MvPolynomial.monomial_pow]
    simpa using
      (MvPolynomial.monomial_finsupp_sum_index s (fun i n => n • i.1) (1 : R)).symm
  rw [h_eval, h_eval]
  congr 1
  have hab :
      (Finsupp.single a 1 + Finsupp.single b 1).sum (fun i n => n • i.1) =
        a.1 + b.1 := by
    rw [Finsupp.sum_add_index' (fun _ => by simp)
      (fun _ m n => by rw [add_smul])]
    simp
  have hce :
      (Finsupp.single c 1 + Finsupp.single e 1).sum (fun i n => n • i.1) =
        c.1 + e.1 := by
    rw [Finsupp.sum_add_index' (fun _ => by simp)
      (fun _ m n => by rw [add_smul])]
    simp
  rw [hab, hce, h]

theorem chapter02_veronese_image_ideal_le_kernel
    (R : Type u) [CommRing R] (r d : ℕ) :
    chapter02VeroneseImageIdeal R r d ≤
      RingHom.ker (chapter02VeroneseMonomialRingHom R r d).toRingHom := by
  apply Ideal.span_le.2
  rintro F ⟨a, b, c, e, h, rfl⟩
  exact chapter02_veronese_quadratic_relation_maps_to_zero R r d a b c e h

/- LOCAL_DEPENDENCY_GUESS: the quadratic toric relations generate the full Veronese kernel. -/
theorem chapter02_veronese_image_ideal_eq_kernel
    (R : Type u) [CommRing R] (r d : ℕ) (hd : 0 < d) :
    chapter02VeroneseImageIdeal R r d =
      RingHom.ker (chapter02VeroneseMonomialRingHom R r d).toRingHom := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
