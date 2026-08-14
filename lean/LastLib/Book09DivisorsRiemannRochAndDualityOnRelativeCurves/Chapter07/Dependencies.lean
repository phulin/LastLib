import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Module.Presentation.Differentials
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u v

/-!
Shared interfaces for Chapter 7.

The affine part of the chapter is expressed with the pinned Mathlib
`KaehlerDifferential` API.  The global sheaf of relative differentials and
the divisor/dualizing-sheaf constructions are not yet packaged by the
earlier books, so the small records below keep those missing interfaces
explicit instead of identifying them with unrelated sheaves.
-/

abbrev Chapter07LineBundle (X : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09LineBundle X

abbrev Chapter07IsLineBundle {X : Scheme.{u}} (M : X.Modules) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.chapter09IsInvertibleSheaf M

abbrev Chapter07WeilDivisor (X : Scheme.{u}) := AlgebraicCycle X ℤ

abbrev Chapter07SmoothRelativeCurve {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  SmoothOfRelativeDimension 1 f

structure Chapter07SmoothProperGeometricallyConnectedCurve
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) : Prop where
  smooth : SmoothOfRelativeDimension 1 f
  proper : IsProper f
  geometricallyConnected : GeometricallyConnected f

/- LOCAL_DEPENDENCY_GUESS: Mathlib has affine Kähler differentials but not a
global sheaf-valued relative cotangent construction with the chapter's
book-facing interface.  This record is deliberately only the data needed by
the smooth-curve statements; its existence is supplied in the section where
the geometric assertion is used. -/
structure Chapter07SmoothRelativeDifferentialData
    {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] where
  module : X.Modules
  isQuasicoherent : module.IsQuasicoherent
  isLineBundle : Chapter07IsLineBundle module

/- The affine universal property is canonical and does not depend on the
global sheaf placeholder above. -/
abbrev Chapter07AffineDifferential (R A : Type*) [CommRing R] [CommRing A]
    [Algebra R A] := Ω[A⁄R]

abbrev Chapter07AffineDerivation (R A M : Type*)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] :=
  Derivation R A M

noncomputable def chapter07AffineDifferentialDerivationEquiv
    (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] :
    (Ω[A⁄R] →ₗ[A] M) ≃ₗ[A] Derivation R A M :=
  KaehlerDifferential.linearMapEquivDerivation R A

theorem chapter07_affine_differential_represents_derivations
    (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] :
    Nonempty ((Ω[A⁄R] →ₗ[A] M) ≃ₗ[A] Derivation R A M) :=
  ⟨chapter07AffineDifferentialDerivationEquiv R A M⟩

@[simp]
theorem chapter07_differential_add
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (a b : A) :
    KaehlerDifferential.D R A (a + b) =
      KaehlerDifferential.D R A a + KaehlerDifferential.D R A b := by
  exact (KaehlerDifferential.D R A).map_add a b

@[simp]
theorem chapter07_differential_mul
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (a b : A) :
    KaehlerDifferential.D R A (a * b) =
      a • KaehlerDifferential.D R A b +
        b • KaehlerDifferential.D R A a := by
  exact (KaehlerDifferential.D R A).leibniz a b

@[simp]
theorem chapter07_differential_base
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (c : R) :
    KaehlerDifferential.D R A (algebraMap R A c) = 0 := by
  exact (KaehlerDifferential.D R A).map_algebraMap c

noncomputable def chapter07AffineDifferentialMap
    (R S A B : Type*) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B] [Algebra R B]
    [Algebra A B] [IsScalarTower R S B] [IsScalarTower R A B]
    [SMulCommClass S A B] :
    Ω[A⁄R] →ₗ[A] Ω[B⁄S] :=
  KaehlerDifferential.map R S A B

theorem chapter07_affine_differential_map_D
    (R S A B : Type*) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B] [Algebra R B]
    [Algebra A B] [IsScalarTower R S B] [IsScalarTower R A B]
    [SMulCommClass S A B] (a : A) :
    chapter07AffineDifferentialMap R S A B (KaehlerDifferential.D R A a) =
      KaehlerDifferential.D S B (algebraMap A B a) := by
  exact KaehlerDifferential.map_D R S A B a

/- The affine conormal sequence is the exact sequence supplied by Mathlib.
Its first map is A-linear and its second map is B-linear, exactly as in the
restriction of the sheaf sequence to an affine closed subscheme. -/
structure Chapter07AffineConormalSequenceData
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (h : Function.Surjective (algebraMap A B)) where
  conormal : (RingHom.ker (algebraMap A B)).Cotangent
  ambient : B ⊗[A] Ω[A⁄R]
  target : Ω[B⁄R]
  first : conormal →ₗ[A] ambient
  second : ambient →ₗ[B] target
  first_eq : first = KaehlerDifferential.kerCotangentToTensor R A B
  second_eq : second = KaehlerDifferential.mapBaseChange R A B
  exact : Function.Exact first second
  second_surjective : Function.Surjective second

noncomputable def chapter07AffineConormalSequence
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (h : Function.Surjective (algebraMap A B)) :
    Chapter07AffineConormalSequenceData R A B h where
  conormal := (RingHom.ker (algebraMap A B)).Cotangent
  ambient := B ⊗[A] Ω[A⁄R]
  target := Ω[B⁄R]
  first := KaehlerDifferential.kerCotangentToTensor R A B
  second := KaehlerDifferential.mapBaseChange R A B
  first_eq := rfl
  second_eq := rfl
  exact := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h
  second_surjective := KaehlerDifferential.mapBaseChange_surjective R A B h

theorem chapter07_affine_conormal_sequence_exact
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (h : Function.Surjective (algebraMap A B)) :
    Function.Exact (KaehlerDifferential.kerCotangentToTensor R A B)
      (KaehlerDifferential.mapBaseChange R A B) :=
  KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h

theorem chapter07_affine_conormal_sequence_surjective
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (h : Function.Surjective (algebraMap A B)) :
    Function.Surjective (KaehlerDifferential.mapBaseChange R A B) :=
  KaehlerDifferential.mapBaseChange_surjective R A B h

/- LOCAL_DEPENDENCY_GUESS: the sheaf-valued cotangent construction for a
closed immersion into a smooth ambient scheme is not in the pinned tree.  The
record retains the categorical exact sequence and its epimorphism to the
target, while the affine realization above is canonical. -/
structure Chapter07ConormalSequenceData
    {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    [IsClosedImmersion i] [Smooth p] where
  conormal : X.Modules
  ambient : X.Modules
  target : X.Modules
  first : conormal ⟶ ambient
  second : ambient ⟶ target
  comp_zero : first ≫ second = 0
  exact : (ShortComplex.mk first second comp_zero).Exact
  target_epimorphism : Epi second

theorem chapter07_conormal_sequence_exists
    {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    [IsClosedImmersion i] [Smooth p] :
    Nonempty (Chapter07ConormalSequenceData i p) := by
  sorry

def chapter07HypersurfaceQuotient
    (A : Type*) [CommRing A]
    {ι : Type*} (F : MvPolynomial ι A) : Type* :=
  MvPolynomial ι A ⧸ Ideal.span {F}

def chapter07HypersurfaceEquationDifferential
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} (F : MvPolynomial ι A) : Ω[MvPolynomial ι A⁄R] :=
  KaehlerDifferential.D R (MvPolynomial ι A) F

def chapter07HypersurfaceEquationClass
    (A : Type*) [CommRing A] {ι : Type*} (F : MvPolynomial ι A) :
    (RingHom.ker (algebraMap (MvPolynomial ι A)
      (chapter07HypersurfaceQuotient A F))).Cotangent := by
  apply Ideal.toCotangent
  exact ⟨F, by
    change Ideal.Quotient.mk (Ideal.span {F}) F = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton F)⟩

theorem chapter07_hypersurface_equation_maps_to_differential
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} (F : MvPolynomial ι A) :
    KaehlerDifferential.kerCotangentToTensor R (MvPolynomial ι A)
        (chapter07HypersurfaceQuotient A F)
        (chapter07HypersurfaceEquationClass A F) =
      1 ⊗ₜ[MvPolynomial ι A] chapter07HypersurfaceEquationDifferential R A F := by
  exact KaehlerDifferential.kerCotangentToTensor_toCotangent _

def chapter07PartialsNonvanishing {B : Type*} [CommRing B]
    (partials : Set B) : Prop :=
  Ideal.span partials = ⊤

theorem chapter07_partials_nonvanishing_iff_jacobian_ideal_top
    {B : Type*} [CommRing B] (partials : Set B) :
    chapter07PartialsNonvanishing partials ↔ Ideal.span partials = ⊤ :=
  Iff.rfl

def chapter07HypersurfacePartialDerivatives
    (A : Type*) [CommRing A] {ι : Type*} (F : MvPolynomial ι A) :
    Set (chapter07HypersurfaceQuotient A F) :=
  Set.range (fun i : ι =>
    Ideal.Quotient.mk (Ideal.span {F}) (MvPolynomial.pderiv i F))

def chapter07HypersurfaceJacobianCondition
    (A : Type*) [CommRing A] {ι : Type*} (F : MvPolynomial ι A) : Prop :=
  chapter07PartialsNonvanishing (chapter07HypersurfacePartialDerivatives A F)

theorem chapter07_hypersurface_jacobian_condition_is_unit_ideal
    (A : Type*) [CommRing A] {ι : Type*} (F : MvPolynomial ι A) :
    chapter07HypersurfaceJacobianCondition A F ↔
      Ideal.span (chapter07HypersurfacePartialDerivatives A F) = ⊤ :=
  Iff.rfl

/- LOCAL_DEPENDENCY_GUESS: the pinned standard-smooth criterion is stated for
algebra presentations, while the textbook uses the geometric fibrewise
Jacobian wording.  Over a field and a finite variable set, this bridge has
the expected relative dimension `card ι - 1`. -/
theorem chapter07_hypersurface_jacobian_condition_gives_standard_smooth
    (A : Type*) [Field A] {ι : Type*} [Fintype ι]
    (F : MvPolynomial ι A)
    (hF : chapter07HypersurfaceJacobianCondition A F) :
    Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card ι - 1) A
      (chapter07HypersurfaceQuotient A F) := by
  sorry

/- A local parameter records the basis assertion and the unit transition
factor separately, so both parts can be reused without choosing a global
coordinate. -/
structure Chapter07LocalParameterChangeData
    (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] where
  t u : A
  differential : Derivation R A M
  jacobian : A
  dt_is_basis : ∃ e : Basis (Fin 1) A M, e 0 = differential t
  du_eq_jacobian_smul_dt : differential u = jacobian • differential t
  jacobian_isUnit : IsUnit jacobian

theorem chapter07_local_parameter_change_formula
    (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    (P : Chapter07LocalParameterChangeData R A M) :
    P.differential P.u = P.jacobian • P.differential P.t :=
  P.du_eq_jacobian_smul_dt

theorem chapter07_local_parameter_change_factor_isUnit
    (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    (P : Chapter07LocalParameterChangeData R A M) : IsUnit P.jacobian :=
  P.jacobian_isUnit

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07
