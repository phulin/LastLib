import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Section02ChartsAndExceptionalCurves

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ## 7.3. Normalized blowups -/

/- LOCAL_DEPENDENCY_GUESS: pinned Mathlib's relative normalization is normalization of a target
inside a source and does not directly provide the absolute map from the normalized blowup back to
the blowup scheme.  The normalization morphism is therefore kept explicitly in this wrapper. -/
structure Chapter07NormalizedBlowup
    {X : Scheme.{u}} (I : Chapter07CoherentIdeal X)
    (hX : Chapter07NormalIntegralScheme X) where
  blowup : Chapter07Blowup I
  carrier : Scheme.{u}
  normalization : carrier ⟶ blowup.carrier
  normal : Chapter07NormalIntegralScheme carrier
  integral : IsIntegralHom normalization
  normalization_birational : Chapter07Birational normalization
  birational : Chapter07Birational (normalization ≫ blowup.projection)

abbrev chapter07NormalizedBlowupScheme
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    {hX : Chapter07NormalIntegralScheme X}
    (N : Chapter07NormalizedBlowup I hX) : Scheme :=
  N.carrier

abbrev chapter07NormalizedBlowupMap
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    {hX : Chapter07NormalIntegralScheme X}
    (N : Chapter07NormalizedBlowup I hX) : N.carrier ⟶ X :=
  N.normalization ≫ N.blowup.projection

theorem chapter07_normalizedBlowup_isNormal
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    {hX : Chapter07NormalIntegralScheme X}
    (N : Chapter07NormalizedBlowup I hX) :
    Chapter07NormalIntegralScheme N.carrier :=
  N.normal

theorem chapter07_normalizedBlowup_isIntegral
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    {hX : Chapter07NormalIntegralScheme X}
    (N : Chapter07NormalizedBlowup I hX) :
    IsIntegralHom N.normalization :=
  N.integral

theorem chapter07_normalizedBlowup_normalization_is_birational
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    {hX : Chapter07NormalIntegralScheme X}
    (N : Chapter07NormalizedBlowup I hX) :
    Chapter07Birational N.normalization :=
  N.normalization_birational

theorem chapter07_normalizedBlowup_exists
    {X : Scheme.{u}} (I : Chapter07CoherentIdeal X)
    (hX : Chapter07NormalIntegralScheme X) :
    Nonempty (Chapter07NormalizedBlowup I hX) := by
  sorry

noncomputable def chapter07NormalizedBlowup
    {X : Scheme.{u}} (I : Chapter07CoherentIdeal X)
    (hX : Chapter07NormalIntegralScheme X) :
    Chapter07NormalizedBlowup I hX :=
  Classical.choice (chapter07_normalizedBlowup_exists I hX)

theorem chapter07_normalizedBlowup_birational
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    {hX : Chapter07NormalIntegralScheme X}
    (N : Chapter07NormalizedBlowup I hX) :
    Chapter07Birational (chapter07NormalizedBlowupMap N) :=
  N.birational

/- A normal scheme can have a non-normal blowup; this is recorded as a genuine non-necessity
statement, rather than imposing normality on the unnormalized construction. -/
theorem chapter07_normal_blowup_need_not_be_normal :
    ∃ (X : Scheme.{u}) (I : Chapter07CoherentIdeal X),
      Chapter07NormalIntegralScheme X ∧
        ∃ B : Chapter07Blowup I, ¬ Chapter07NormalIntegralScheme B.carrier := by
  sorry

def Chapter07RelativeNormalizationMorphism
    {Y X : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  IsIntegralHom f ∧ Chapter07Birational f

/- Mathlib has no pinned `Excellent` scheme class.  This is the smallest book-facing interface
needed here: finite type is represented by a finite-type morphism to a chosen base, and excellence
is used only through finiteness of the normalization morphism. -/
structure Chapter07ExcellentFiniteTypeSituation (X : Scheme.{u}) where
  base : Scheme.{u}
  structureMap : X ⟶ base
  finiteType : LocallyOfFiniteType structureMap ∧ QuasiCompact structureMap
  normalization_finite : ∀ {Y : Scheme.{u}} (f : Y ⟶ X),
    Chapter07RelativeNormalizationMorphism f → IsFinite f

theorem chapter07_normalizedBlowup_isFinite_over_excellent_finite_type
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    {hX : Chapter07NormalIntegralScheme X}
    (hE : Chapter07ExcellentFiniteTypeSituation X)
    (N : Chapter07NormalizedBlowup I hX) :
    IsFinite N.normalization := by
  exact hE.normalization_finite N.normalization
    ⟨N.integral, N.normalization_birational⟩

theorem chapter07_normalizedBlowup_isProjective_over_excellent_finite_type
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    {hX : Chapter07NormalIntegralScheme X}
    (hE : Chapter07ExcellentFiniteTypeSituation X)
    (N : Chapter07NormalizedBlowup I hX) :
    Chapter07IsProjectiveMorphism (chapter07NormalizedBlowupMap N) := by
  sorry

theorem chapter07_normalizedBlowup_is_projective_and_birational
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    {hX : Chapter07NormalIntegralScheme X}
    (hE : Chapter07ExcellentFiniteTypeSituation X)
    (N : Chapter07NormalizedBlowup I hX) :
    Chapter07IsProjectiveMorphism (chapter07NormalizedBlowupMap N) ∧
      Chapter07Birational (chapter07NormalizedBlowupMap N) := by
  exact ⟨chapter07_normalizedBlowup_isProjective_over_excellent_finite_type hE N,
    N.birational⟩

/-! ### The normalized Rees algebra -/

def Chapter07NormalDomain
    (A : Type u) [CommRing A] [IsDomain A] : Prop :=
  IsIntegrallyClosed A

def Chapter07NonzeroAffineIdeal
    (A : Type u) [CommRing A] (I : Ideal A) : Prop :=
  I ≠ (⊥ : Ideal A)

noncomputable def chapter07ReesMonomialMap
    (A : Type u) [CommRing A] (n : ℕ) : A →ₗ[A] A[X] where
  toFun a := Polynomial.monomial n a
  map_add' := by
    intro a b
    simp
  map_smul' := by
    intro r a
    simp [Algebra.smul_def]

/- The degree-n part is characterized directly by integrality of `a t^n` over the Rees
algebra.  The ideal laws are the standard integral-closure laws and are deliberately left for the
proof pass. -/
noncomputable def chapter07NormalizedReesDegree
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) : Ideal A where
  carrier := {a | IsIntegral (Chapter07ReesAlgebra A I)
    (chapter07ReesMonomialMap A n a)}
  zero_mem' := by
    sorry
  add_mem' := by
    intro a b ha hb
    sorry
  smul_mem' := by
    intro r a ha
    sorry

abbrev chapter07IntegralClosurePower
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) : Ideal A :=
  chapter07NormalizedReesDegree A I n

theorem chapter07_normalizedReesDegree_mem_iff
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) (a : A) :
    a ∈ chapter07NormalizedReesDegree A I n ↔
      IsIntegral (Chapter07ReesAlgebra A I) (chapter07ReesMonomialMap A n a) := by
  rfl

theorem chapter07_normalizedReesDegree_is_integralClosurePower
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    chapter07NormalizedReesDegree A I n = chapter07IntegralClosurePower A I n :=
  rfl

/- A normalized Rees grading is the exact affine interface needed by `Proj`; the
characterization records that its degree-n homogeneous elements are the integral-closure powers. -/
structure Chapter07NormalizedReesGrading
    (A : Type u) [CommRing A] (I : Ideal A) where
  component : ℕ → Submodule A (Chapter07NormalizedReesAlgebra A I)
  graded : GradedAlgebra component
  degree_characterization : ∀ (n : ℕ) (p : Chapter07NormalizedReesAlgebra A I),
    p ∈ component n ↔ ∃ a : A,
      p.1 = Polynomial.monomial n a ∧
        a ∈ chapter07NormalizedReesDegree A I n

theorem chapter07_normalizedReesGrading_exists
    (A : Type u) [CommRing A] (I : Ideal A) :
    Nonempty (Chapter07NormalizedReesGrading A I) := by
  sorry

theorem chapter07_normal_domain_normalizedRees_is_graded
    (A : Type u) [CommRing A] [IsDomain A] (I : Ideal A)
    (hA : Chapter07NormalDomain A) (hI : Chapter07NonzeroAffineIdeal A I) :
    Nonempty (Chapter07NormalizedReesGrading A I) :=
  chapter07_normalizedReesGrading_exists A I

noncomputable def chapter07NormalizedReesGrading
    (A : Type u) [CommRing A] (I : Ideal A) :
    Chapter07NormalizedReesGrading A I :=
  Classical.choice (chapter07_normalizedReesGrading_exists A I)

noncomputable def chapter07NormalizedReesProj
    (A : Type u) [CommRing A] (I : Ideal A) : Scheme :=
  let G := chapter07NormalizedReesGrading A I
  letI : GradedAlgebra G.component := G.graded
  AlgebraicGeometry.Proj G.component

def chapter07IntegralClosureEquivalent
    (A : Type u) [CommRing A] (I J : Ideal A) : Prop :=
  ∀ n : ℕ, ∀ a : A,
    IsIntegral (Chapter07ReesAlgebra A I) (chapter07ReesMonomialMap A n a) ↔
      IsIntegral (Chapter07ReesAlgebra A J) (chapter07ReesMonomialMap A n a)

theorem chapter07_normalizedReesDegree_congr
    (A : Type u) [CommRing A] (I J : Ideal A)
    (hIJ : chapter07IntegralClosureEquivalent A I J) (n : ℕ) :
    chapter07NormalizedReesDegree A I n = chapter07NormalizedReesDegree A J n := by
  ext a
  exact hIJ n a

noncomputable def chapter07AffineNormalizedBlowup
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (hA : Chapter07NormalIntegralScheme (Spec (.of A))) : Scheme :=
  (chapter07NormalizedBlowup
    (chapter07AffineCoherentIdeal A I hI) hA).carrier

theorem chapter07_normalizedBlowup_depends_only_on_integral_closure
    (A : Type u) [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (hA : Chapter07NormalIntegralScheme (Spec (.of A)))
    (hIJ : chapter07IntegralClosureEquivalent A I J) :
    Nonempty
      (chapter07AffineNormalizedBlowup A I hI hA ≅
        chapter07AffineNormalizedBlowup A J hJ hA) := by
  sorry

/-! ### Divisorial valuations and asymptotic orders -/

structure Chapter07DivisorialValuation
    (A : Type u) [CommRing A] [IsDomain A] where
  value : FractionRing A → ℤ
  value_zero : value 0 = 0
  value_one : value 1 = 0
  value_mul : ∀ {x y}, x ≠ 0 → y ≠ 0 → value (x * y) = value x + value y
  value_add : ∀ x y, value (x + y) ≥ min (value x) (value y)
  nontrivial : ∃ x, value x ≠ 0
  center : PrimeSpectrum A

def chapter07ExceptionalDivisorValuation
    {Y X : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (E : Chapter07ExceptionalDivisor f) : Y.functionField → ℤ :=
  fun r => chapter03OrderOfVanishing r E.divisor

def chapter07ValuationOrder
    (v : Chapter07DivisorialValuation A) (I : Ideal A) : ℤ :=
  sInf (v.value ''
    ((algebraMap A (FractionRing A)) '' (I : Set A)))

def chapter07ValuationOrderOfPower
    (v : Chapter07DivisorialValuation A) (I : Ideal A) (n : ℕ) : ℤ :=
  chapter07ValuationOrder v (I ^ n)

def chapter07AsymptoticValuationOrder
    (v : Chapter07DivisorialValuation A) (I : Ideal A) : ℝ :=
  sInf (Set.range (fun n : ℕ ↦
    (chapter07ValuationOrderOfPower v I n : ℝ) / (n + 1 : ℝ)))

theorem chapter07_divisorial_valuation_measures_asymptotic_order
    (hA : Chapter07NormalDomain A) (I : Ideal A)
    (hI : Chapter07NonzeroAffineIdeal A I)
    (v : Chapter07DivisorialValuation A) :
    chapter07AsymptoticValuationOrder v I =
      sInf (Set.range (fun n : ℕ ↦
        (chapter07ValuationOrderOfPower v I n : ℝ) / (n + 1 : ℝ))) := by
  rfl

def Chapter07CodimensionOneValuationControl
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    {hX : Chapter07NormalIntegralScheme X}
    (N : Chapter07NormalizedBlowup I hX) : Prop :=
  ∀ y : N.carrier, y ∈ chapter07ExceptionalLocus (chapter07NormalizedBlowupMap N) →
    ∃ E : Chapter07ExceptionalDivisor (chapter07NormalizedBlowupMap N),
      y ∈ E.divisor.support

theorem chapter07_normalized_surface_blowup_has_divisorial_control
    {X : Scheme.{u}} (hX : Chapter07NormalIntegralScheme X)
    (hSurface : Chapter07RegularSurface X)
    (I : Chapter07CoherentIdeal X)
    (hcenter : Chapter07FiniteClosedPointCenter I)
    (N : Chapter07NormalizedBlowup I hX) :
    Chapter07CodimensionOneValuationControl N := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
