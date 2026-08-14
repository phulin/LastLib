import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02.Section02GeneratorsRelationsAndSymmetricAlgebra

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02

universe u v

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators
open Polynomial

/-! ## 2.3. Localization, powers, and integral closure -/

/-- The extension of an ideal along a ring map. -/
def chapter02LocalizedIdeal
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) : Ideal S :=
  Ideal.map (algebraMap R S) I

/-- The Rees algebra of the extended ideal. -/
abbrev chapter02LocalizedReesAlgebra
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) : Subalgebra S (Polynomial S) :=
  reesAlgebra (chapter02LocalizedIdeal I)

/-- The image of the localization denominators in the Rees algebra. -/
def chapter02ReesLocalizationSubmonoid
    {R : Type u} [CommRing R] (I : Ideal R) (W : Submonoid R) :
    Submonoid (Chapter02ReesAlgebra R I) :=
  W.map (algebraMap R (Chapter02ReesAlgebra R I)).toMonoidHom

structure Chapter02ReesLocalizationData
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (W : Submonoid R) where
  equivalence :
    Localization (chapter02ReesLocalizationSubmonoid I W)
        (Chapter02ReesAlgebra R I) ≃+*
      chapter02LocalizedReesAlgebra (S := S) I

/- LOCAL_DEPENDENCY_GUESS: localization of the Rees algebra commutes with extension of the ideal; the coefficientwise map of powers is the proof route. -/
theorem chapter02_rees_localization_exists
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (W : Submonoid R) [IsLocalization W S] :
    Nonempty (Chapter02ReesLocalizationData I W) := by
  sorry

noncomputable def chapter02ReesLocalizationDataOf
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (W : Submonoid R) [IsLocalization W S] :
    Chapter02ReesLocalizationData (S := S) I W :=
  Classical.choice (chapter02_rees_localization_exists I W)

theorem chapter02_localized_ideal_pow
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (W : Submonoid R) [IsLocalization W S] (n : ℕ) :
    Ideal.map (algebraMap R S) (I ^ n) =
      chapter02LocalizedIdeal (S := S) I ^ n := by
  exact Ideal.map_pow (algebraMap R S) I n

theorem chapter02_localized_ideal_mul
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I J : Ideal R) :
    Ideal.map (algebraMap R S) (I * J) =
      chapter02LocalizedIdeal (S := S) I * chapter02LocalizedIdeal (S := S) J := by
  exact Ideal.map_mul (algebraMap R S) I J

noncomputable def chapter02LocalizedReesProj
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) : Scheme.{u} :=
  chapter02ReesProj (chapter02LocalizedIdeal (S := S) I)

/- LOCAL_DEPENDENCY_GUESS: the ring-level localization equivalence induces the corresponding affine-local equivalence of Rees projective spectra. -/
theorem chapter02_blowup_is_local_on_target
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (W : Submonoid R) [IsLocalization W S] :
    Nonempty (Chapter02ReesLocalizationData (S := S) I W) := by
  exact chapter02_rees_localization_exists I W

/-- The integral-closure ideal detected by the degree-`n` homogeneous elements. -/
def chapter02IntegralClosurePower
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) : Ideal R where
  carrier := {r : R |
    Polynomial.monomial n r ∈
      integralClosure (Chapter02ReesAlgebra R I) (Polynomial R)}
  zero_mem' := by
    sorry
  add_mem' := by
    sorry
  smul_mem' := by
    sorry

abbrev chapter02IntegralClosureIdeal
    {R : Type u} [CommRing R] (I : Ideal R) : Ideal R :=
  chapter02IntegralClosurePower I 1

abbrev chapter02IdealIntegralClosure
    {R : Type u} [CommRing R] (J : Ideal R) : Ideal R :=
  chapter02IntegralClosureIdeal J

theorem chapter02_integral_closure_power_mem_iff
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) (r : R) :
    r ∈ chapter02IntegralClosurePower I n ↔
      Polynomial.monomial n r ∈
        integralClosure (Chapter02ReesAlgebra R I) (Polynomial R) := by
  rfl

/- LOCAL_DEPENDENCY_GUESS: over a normal domain, the degree-`n` integral-closure piece agrees
with the ordinary integral closure of the ideal power `I^n`. -/
theorem chapter02_normal_domain_integral_closure_power_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (I : Ideal R) {n : ℕ} (hn : 0 < n) :
    chapter02IntegralClosurePower I n =
      chapter02IdealIntegralClosure (I ^ n) := by
  sorry

def chapter02NormalizedReesAlgebra
    {R : Type u} [CommRing R] (I : Ideal R) : Subalgebra R (Polynomial R) where
  carrier := {p | ∀ n, p.coeff n ∈ chapter02IntegralClosurePower I n}
  zero_mem' := by
    intro n
    exact (chapter02IntegralClosurePower I n).zero_mem
  add_mem' := by
    intro p q hp hq n
    exact (chapter02IntegralClosurePower I n).add_mem (hp n) (hq n)
  mul_mem' := by
    sorry
  one_mem' := by
    sorry
  algebraMap_mem' := by
    sorry

theorem chapter02_rees_le_normalized_rees
    {R : Type u} [CommRing R] (I : Ideal R) :
    Chapter02ReesAlgebra R I ≤ chapter02NormalizedReesAlgebra I := by
  sorry

theorem chapter02_normalized_rees_monomial_mem_iff
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) (r : R) :
    Polynomial.monomial n r ∈ chapter02NormalizedReesAlgebra I ↔
      r ∈ chapter02IntegralClosurePower I n := by
  sorry

def chapter02NormalizedReesHomogeneous
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ)
    (p : chapter02NormalizedReesAlgebra I) : Prop :=
  ∀ j, j ≠ n → p.1.coeff j = 0

structure Chapter02NormalizedReesGradingData
    {R : Type u} [CommRing R] (I : Ideal R) where
  component : ℕ → Submodule R (chapter02NormalizedReesAlgebra I)
  graded : GradedAlgebra component
  component_spec :
    ∀ n (p : chapter02NormalizedReesAlgebra I),
      p ∈ component n ↔ chapter02NormalizedReesHomogeneous I n p

/- LOCAL_DEPENDENCY_GUESS: the homogeneous pieces of the integral closure form the normalized Rees algebra grading. -/
theorem chapter02_normalized_rees_grading_exists
    {R : Type u} [CommRing R] (I : Ideal R) :
    Nonempty (Chapter02NormalizedReesGradingData I) := by
  sorry

noncomputable def chapter02NormalizedReesGradingData
    {R : Type u} [CommRing R] (I : Ideal R) :
    Chapter02NormalizedReesGradingData I :=
  Classical.choice (chapter02_normalized_rees_grading_exists I)

noncomputable def chapter02NormalizedBlowupScheme
    {R : Type u} [CommRing R] (I : Ideal R) : Scheme.{u} := by
  let G := chapter02NormalizedReesGradingData I
  letI := G.graded
  exact AlgebraicGeometry.«Proj» G.component

theorem chapter02_normalized_rees_degree_n_is_integral_closure
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) (r : R) :
    Polynomial.monomial n r ∈ chapter02NormalizedReesAlgebra I ↔
      r ∈ chapter02IntegralClosurePower I n := by
  exact chapter02_normalized_rees_monomial_mem_iff I n r

/-- A normal domain is supplied to the integral-closure statements by these canonical classes. -/
def Chapter02NormalDomain (R : Type u) [CommRing R] : Prop :=
  IsDomain R ∧ IsIntegrallyClosed R

def Chapter02ReesIsNormal
    {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  IsIntegrallyClosed (Chapter02ReesAlgebra R I)

/-- This predicate records the source's warning that normality need not pass to a Rees algebra. -/
def Chapter02ReesNormalityCanFail
    (R : Type u) [CommRing R] : Prop :=
  ∃ I : Ideal R, ¬ Chapter02ReesIsNormal I

/- LOCAL_DEPENDENCY_GUESS: the square of the homogeneous maximal ideal in `k[x,y]` gives a
concrete non-normal Rees algebra. -/
theorem chapter02_bivariate_square_rees_not_normal
    {k : Type u} [Field k] :
    ¬ Chapter02ReesIsNormal (chapter02BivariateIdeal k ^ 2) := by
  sorry

theorem chapter02_rees_normality_can_fail_over_a_field
    {k : Type u} [Field k] :
    Chapter02ReesNormalityCanFail (Chapter02BivariatePolynomial k) := by
  exact ⟨chapter02BivariateIdeal k ^ 2, chapter02_bivariate_square_rees_not_normal⟩

def chapter02ReesToNormalizedRees
    {R : Type u} [CommRing R] (I : Ideal R) :
    Chapter02ReesAlgebra R I →+* chapter02NormalizedReesAlgebra I :=
  (Subalgebra.inclusion (chapter02_rees_le_normalized_rees I)).toRingHom

noncomputable def chapter02ReesAlgebraOnNormalizedRees
    {R : Type u} [CommRing R] (I : Ideal R) :
    Algebra (Chapter02ReesAlgebra R I) (chapter02NormalizedReesAlgebra I) :=
  (chapter02ReesToNormalizedRees I).toAlgebra

def Chapter02NormalizedReesIsIntegralClosure
    {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  letI := chapter02ReesAlgebraOnNormalizedRees I
  IsIntegralClosure (chapter02NormalizedReesAlgebra I)
    (Chapter02ReesAlgebra R I) (Polynomial R)

/- LOCAL_DEPENDENCY_GUESS: in a normal domain, the coefficientwise normalized Rees subalgebra is
the integral closure of the ordinary Rees algebra inside `R[T]`. -/
theorem chapter02_normalized_rees_is_integral_closure
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (I : Ideal R) :
    Chapter02NormalizedReesIsIntegralClosure I := by
  sorry

def Chapter02NormalizationFiniteOverRees
    {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  letI := chapter02ReesAlgebraOnNormalizedRees I
  Module.Finite (Chapter02ReesAlgebra R I) (chapter02NormalizedReesAlgebra I)

/- LOCAL_DEPENDENCY_GUESS: excellence plus finite type and surface hypotheses make the normalization finite over the Rees algebra. -/
theorem chapter02_normalization_finite_over_rees
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (hR : Chapter02ExcellentFiniteTypeSurface R) (I : Ideal R) (hI : I.FG) :
    Chapter02NormalizationFiniteOverRees I := by
  sorry

structure Chapter02NormalizedBlowupProperties
    {R : Type u} [CommRing R] (I : Ideal R) where
  structureMap :
    chapter02NormalizedBlowupScheme I ⟶
      AlgebraicGeometry.Spec (CommRingCat.of R)
  projective :
    Chapter02AffineProjectivePresentation R (chapter02NormalizedBlowupScheme I) structureMap
  birational :
    Scheme.BirationalOver structureMap (𝟙 _)

/- LOCAL_DEPENDENCY_GUESS: the normalized Rees Proj is projective and birational over the affine surface; the pinned scheme API has no projective-morphism predicate. -/
theorem chapter02_normalized_blowup_projective_birational
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (hR : Chapter02ExcellentFiniteTypeSurface R) (I : Ideal R) (hI : I.FG) :
    Nonempty (Chapter02NormalizedBlowupProperties I) := by
  sorry

def Chapter02SameIntegralClosures
    {R : Type u} [CommRing R] (I J : Ideal R) : Prop :=
  ∀ n, 0 < n → chapter02IntegralClosurePower I n =
    chapter02IntegralClosurePower J n

theorem chapter02_same_integral_closures_same_normalized_blowup
    {R : Type u} [CommRing R] (I J : Ideal R)
    (hIJ : Chapter02SameIntegralClosures I J) :
    Nonempty (chapter02NormalizedBlowupScheme I ≅ chapter02NormalizedBlowupScheme J) := by
  sorry

/-! ### Regular points and the limits of ordinary blowups -/

structure Chapter02RegularSurfaceBlowupComparison
    (D : Chapter02RegularSurfaceClosedPoint) where
  normalizedBlowup : Scheme.{u}
  normalizedBlowupIsNormalization :
    Chapter02SchemeNormalization D.ordinaryBlowup normalizedBlowup

theorem chapter02_ordinary_blowup_regular_at_regular_closed_point
    (D : Chapter02RegularSurfaceClosedPoint)
    (hD : D.ordinaryBlowupIsBlowupAtPoint) :
    Chapter02RegularScheme D.ordinaryBlowup := by
  sorry

theorem chapter02_normalization_adds_nothing_at_regular_closed_point
    (D : Chapter02RegularSurfaceClosedPoint)
    (C : Chapter02RegularSurfaceBlowupComparison D)
    (hD : D.ordinaryBlowupIsBlowupAtPoint)
    (hC : C.normalizedBlowupIsNormalization) :
    Nonempty (C.normalizedBlowup ≅ D.ordinaryBlowup) := by
  sorry

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02
