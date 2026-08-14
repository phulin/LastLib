import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Section03NormalSurfacesNeedNotBeRegular

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open scoped AlgebraicGeometry BigOperators Matrix

noncomputable section

universe u v

/-! ### 4.4 Jacobian and fiberwise criteria -/

/-- The formal Jacobian matrix of a list of polynomial equations. -/
def Chapter04JacobianMatrix (k : Type u) [CommRing k]
    (n m : ℕ) (F : Fin m → MvPolynomial (Fin n) k) :
    Matrix (Fin m) (Fin n) (MvPolynomial (Fin n) k) :=
  fun i j => MvPolynomial.pderiv j (F i)

/-- Full-rank of the Jacobian at a prime, expressed by an invertible maximal minor. -/
def Chapter04JacobianFullRankAt (k : Type u) [CommRing k]
    (n m : ℕ) (F : Fin m → MvPolynomial (Fin n) k)
    (p : Ideal (MvPolynomial (Fin n) k)) : Prop :=
  ∃ σ : Fin m → Fin n, Function.Injective σ ∧
    IsUnit (Ideal.Quotient.mk p
      (Matrix.det (fun i j => Chapter04JacobianMatrix k n m F i (σ j))))

/- LOCAL_DEPENDENCY_GUESS: the pinned snapshot has the polynomial partial
derivatives but not a scheme-level Jacobian criterion packaged with the
separability hypotheses.  This interface records the exact rank condition and
the local smoothness predicate supplied by a later implementation. -/
structure Chapter04JacobianCriterionData (k : Type u) [Field k]
    (n m : ℕ) where
  equations : Fin m → MvPolynomial (Fin n) k
  finiteType : Prop
  separable : Prop
  smoothAt : Ideal (MvPolynomial (Fin n) k) → Prop
  smoothAt_iff_jacobian :
    ∀ (p : Ideal (MvPolynomial (Fin n) k)), p.IsPrime →
      Ideal.span (Set.range equations) ≤ p →
      finiteType → separable →
      (smoothAt p ↔ Chapter04JacobianFullRankAt k n m equations p)

theorem chapter04_jacobian_criterion
    {k : Type u} [Field k] {n m : ℕ}
    (J : Chapter04JacobianCriterionData k n m)
    (p : Ideal (MvPolynomial (Fin n) k)) (hp : p.IsPrime)
    (hequations : Ideal.span (Set.range J.equations) ≤ p)
    (hfiniteType : J.finiteType) (hseparable : J.separable) :
    J.smoothAt p ↔ Chapter04JacobianFullRankAt k n m J.equations p := by
  exact J.smoothAt_iff_jacobian p hp hequations hfiniteType hseparable

/-- The local hypersurface quotient used in the linear-term criterion. -/
abbrev Chapter04HypersurfaceRing (P : Type u) [CommRing P] (f : P) :=
  P ⧸ Ideal.span ({f} : Set P)

def Chapter04HypersurfaceRegular (P : Type u) [CommRing P] (f : P) : Prop :=
  IsRegularLocalRing (Chapter04HypersurfaceRing P f)

def Chapter04HypersurfaceHasNonzeroInitialLinearTerm
    (P : Type u) [CommRing P] (f : P) : Prop :=
  f ∉ (maximalIdeal P) ^ 2

/-- A hypersurface in a regular local ring is regular exactly when its equation
has a nonzero linear term. -/
theorem chapter04_hypersurface_regular_iff_nonzero_initial_linear_term
    (P : Type u) [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    [IsRegularLocalRing P] (f : P) (hf : f ≠ 0) (hunit : ¬ IsUnit f) :
    Chapter04HypersurfaceRegular P f ↔
      Chapter04HypersurfaceHasNonzeroInitialLinearTerm P f := by
  sorry

/-- The dimension formula for a nonzero nonunit hypersurface equation. -/
theorem chapter04_hypersurface_dimension_formula
    (P : Type u) [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    [IsRegularLocalRing P] (f : P) (hf : f ≠ 0) (hunit : ¬ IsUnit f) :
    ringKrullDim (Chapter04HypersurfaceRing P f) = ringKrullDim P - 1 := by
  sorry

/-- The embedding dimension drops by one precisely when the initial linear form is nonzero. -/
def Chapter04HypersurfaceEmbeddingDimensionDrops
    (P : Type u) [CommRing P] [IsLocalRing P] (f : P) : Prop :=
  (maximalIdeal P).spanFinrank =
    (maximalIdeal (Chapter04HypersurfaceRing P f)).spanFinrank + 1

theorem chapter04_hypersurface_embedding_dimension_drops_iff
    (P : Type u) [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    [IsRegularLocalRing P] (f : P) (hf : f ≠ 0) (hunit : ¬ IsUnit f) :
    Chapter04HypersurfaceEmbeddingDimensionDrops P f ↔
      Chapter04HypersurfaceHasNonzeroInitialLinearTerm P f := by
  sorry

/-- The affine cotangent sequence for a quotient, in the canonical Mathlib form. -/
theorem chapter04_exact_cotangent_sequence_for_quotient
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (hsurj : Function.Surjective (algebraMap A B)) :
    Function.Exact (KaehlerDifferential.kerCotangentToTensor R A B)
      (KaehlerDifferential.mapBaseChange R A B) := by
  exact KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B hsurj

/-- The local equation `xy-π` has a linear parameter in the ambient regular local ring. -/
theorem chapter04_dvr_node_regular_by_linear_parameter
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π)
    (hprime : (chapter04DvrNodeMaximalIdeal R π).IsPrime) :
    Chapter04DvrNodeRegularAtNode R π hprime := by
  sorry

/-- Smoothness is flatness, finite presentation, and geometric regularity of the fibers. -/
theorem chapter04_smooth_iff_flat_finitePresentation_geometrically_regular_fibers
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Smooth f ↔
      Flat f ∧ LocallyOfFinitePresentation f ∧
        Chapter04GeometricallyRegularFibers f := by
  sorry

/-- Flat finite-presentation morphisms with geometrically regular fibers are smooth. -/
theorem chapter04_smooth_of_flat_finitePresentation_geometrically_regular_fibers
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f]
    (hfiber : Chapter04GeometricallyRegularFibers f) :
    Smooth f := by
  sorry

/-- Over a regular base, a smooth total space is regular. -/
theorem chapter04_regular_total_space_of_regular_base_and_regular_fibers
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f]
    (hbase : Chapter04RegularScheme S)
    (hfiber : Chapter04GeometricallyRegularFibers f) :
    Chapter04RegularScheme X := by
  sorry

/-- A regular total space can have a geometrically nonregular fiber. -/
def Chapter04RegularTotalSpaceWithNonregularFiber
    {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter04RegularScheme X ∧ ¬ Chapter04GeometricallyRegularFibers f

def Chapter04RegularFlatFamilyWithNonregularFiber
    {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Flat f ∧ LocallyOfFinitePresentation f ∧ Chapter04RegularScheme S ∧
    Chapter04RegularScheme X ∧ ¬ Chapter04GeometricallyRegularFibers f

theorem chapter04_regular_total_space_need_not_have_regular_fibers :
    ∃ (X S : Scheme.{u}) (f : X ⟶ S),
      Chapter04RegularTotalSpaceWithNonregularFiber f := by
  sorry

theorem chapter04_regular_flat_family_need_not_have_regular_fibers :
    ∃ (X S : Scheme.{u}) (f : X ⟶ S),
      Chapter04RegularFlatFamilyWithNonregularFiber f := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
