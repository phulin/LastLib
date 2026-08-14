import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
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
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Section01CodimensionOneCycles
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u v

/-!
Shared interfaces for Chapter 7.

The affine part of the chapter is expressed with the pinned Mathlib
`KaehlerDifferential` API.  The sheaf-valued relative-differential interface
and the affine realization are kept explicit, so later constructions can
refer to the differential sheaf without identifying it with an unrelated
module.
-/

abbrev Chapter07LineBundle (X : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09LineBundle X

abbrev Chapter07IsLineBundle {X : Scheme.{u}} (M : X.Modules) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.chapter09IsInvertibleSheaf M

/- Chapter 3 already supplies the codimension-one indexing and finite-support
   Weil-divisor API.  `AlgebraicCycle X ℤ` is indexed by all scheme points,
   so it is too weak for a divisor on a regular curve. -/
abbrev Chapter07WeilDivisor (X : Scheme.{u}) :=
  LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03WeilDivisor X

abbrev Chapter07SmoothRelativeCurve {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  SmoothOfRelativeDimension 1 f

/- The identity-site presheaf construction is the canonical sheaf-valued
   relative-differential interface available in the pinned Mathlib tree.  It
   specializes objectwise to affine Kähler differentials and carries the
   universal derivation, so the chapter does not replace it by a bare module
   field. -/
abbrev Chapter07PresheafRelativeDifferentials
    {C : Type u} [Category.{v} C]
    {S R : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ R) :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ

noncomputable def Chapter07PresheafRelativeDerivation
    {C : Type u} [Category.{v} C]
    {S R : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ R) :=
  PresheafOfModules.DifferentialsConstruction.derivation' φ

theorem chapter07_presheaf_relative_differentials_are_universal
    {C : Type u} [Category.{v} C]
    {S R : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ R) :
    Nonempty (PresheafOfModules.Derivation.Universal
      (Chapter07PresheafRelativeDerivation φ)) := by
  sorry

structure Chapter07RelativeDifferentialSheafData
    {X S : Scheme.{u}} (f : X ⟶ S) where
  relativeDifferentials : X.Modules
  isQuasicoherent : relativeDifferentials.IsQuasicoherent

structure Chapter07SmoothProperGeometricallyConnectedCurve
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) : Prop where
  smooth : SmoothOfRelativeDimension 1 f
  proper : IsProper f
  geometricallyConnected : GeometricallyConnected f

structure Chapter07SmoothRelativeDifferentialData
    {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] where
  relativeDifferentials : Chapter07RelativeDifferentialSheafData f
  isLineBundle :
    Chapter07IsLineBundle relativeDifferentials.relativeDifferentials

/- The affine universal property is canonical and complements the
sheaf-valued interface above. -/
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
  first : (RingHom.ker (algebraMap A B)).Cotangent →ₗ[A] B ⊗[A] Ω[A⁄R]
  second : B ⊗[A] Ω[A⁄R] →ₗ[B] Ω[B⁄R]
  first_eq : first = KaehlerDifferential.kerCotangentToTensor R A B
  second_eq : second = KaehlerDifferential.mapBaseChange R A B
  exact : Function.Exact first second
  second_surjective : Function.Surjective second

noncomputable def chapter07AffineConormalSequence
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (h : Function.Surjective (algebraMap A B)) :
    Chapter07AffineConormalSequenceData R A B h where
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

structure Chapter07ConormalSequenceData
    {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    (ambientDifferentials : Chapter07RelativeDifferentialSheafData p)
    (targetDifferentials : Chapter07RelativeDifferentialSheafData (i ≫ p))
    [IsClosedImmersion i] [Smooth p] where
  conormal : X.Modules
  first : conormal ⟶
    (Scheme.Modules.pullback i).obj ambientDifferentials.relativeDifferentials
  second :
    (Scheme.Modules.pullback i).obj ambientDifferentials.relativeDifferentials ⟶
      targetDifferentials.relativeDifferentials
  comp_zero : first ≫ second = 0
  exact : (ShortComplex.mk first second comp_zero).Exact
  target_epimorphism : Epi second

def chapter07ConormalSequenceStatement
    {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    (ambientDifferentials : Chapter07RelativeDifferentialSheafData p)
    (targetDifferentials : Chapter07RelativeDifferentialSheafData (i ≫ p))
    [IsClosedImmersion i] [Smooth p] :
    Prop :=
  Nonempty (Chapter07ConormalSequenceData i p ambientDifferentials targetDifferentials)

abbrev chapter07HypersurfaceQuotient
    (A : Type u) [CommRing A]
    {ι : Type v} (F : MvPolynomial ι A) : Type (max u v) :=
  MvPolynomial ι A ⧸ Ideal.span ({F} : Set (MvPolynomial ι A))

def chapter07HypersurfaceEquationDifferential
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} (F : MvPolynomial ι A) : Ω[MvPolynomial ι A⁄R] :=
  KaehlerDifferential.D R (MvPolynomial ι A) F

def chapter07HypersurfaceEquationClass
    (A : Type*) [CommRing A] {ι : Type*} (F : MvPolynomial ι A) :
    (RingHom.ker (algebraMap (MvPolynomial ι A)
      (chapter07HypersurfaceQuotient A F))).Cotangent := by
  exact Ideal.toCotangent _ ⟨F, by
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
  sorry

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
    Ideal.Quotient.mk (Ideal.span ({F} : Set (MvPolynomial ι A)))
      (MvPolynomial.pderiv i F))

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

structure Chapter07LocalParameterChangeData
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] where
  t : A
  u : A
  dt_is_basis : ∃ e : Module.Basis (Fin 1) A Ω[A⁄R],
    e 0 = KaehlerDifferential.D R A t
  du_is_basis : ∃ e : Module.Basis (Fin 1) A Ω[A⁄R],
    e 0 = KaehlerDifferential.D R A u

theorem chapter07_local_parameter_change_formula
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (P : Chapter07LocalParameterChangeData R A) :
    ∃ jacobian : A,
      KaehlerDifferential.D R A P.u =
        jacobian • KaehlerDifferential.D R A P.t ∧
      IsUnit jacobian := by
  sorry

theorem chapter07_local_parameter_change_factor_isUnit
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (P : Chapter07LocalParameterChangeData R A) :
    ∃ jacobian : A, IsUnit jacobian := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07
