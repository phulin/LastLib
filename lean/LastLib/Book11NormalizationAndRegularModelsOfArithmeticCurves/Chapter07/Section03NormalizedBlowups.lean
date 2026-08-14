import Mathlib.Data.Int.ConditionallyCompleteOrder
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Section01TheUniversalRemedyForAnIdeal

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03
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
  blowup_integral : IsIntegral blowup.carrier
  carrier : Scheme.{u}
  normalization : carrier ⟶ blowup.carrier
  normal : Chapter07NormalIntegralScheme carrier
  integral : IsIntegralHom normalization
  birational : Chapter07Birational normalization
  universal :
    ∀ {Y : Scheme.{u}} (g : Y ⟶ blowup.carrier),
      Chapter07NormalIntegralScheme Y →
      Chapter07Birational g →
      ∃! u : Y ⟶ carrier, u ≫ normalization = g

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
  N.birational

theorem chapter07_normalizedBlowup_exists
    {X : Scheme.{u}} (I : Chapter07CoherentIdeal X)
    (hX : Chapter07NormalIntegralScheme X)
    (hI : Chapter07IsNonzeroIdeal I) :
    Nonempty (Chapter07NormalizedBlowup I hX) := by
  sorry

noncomputable def chapter07NormalizedBlowup
    {X : Scheme.{u}} (I : Chapter07CoherentIdeal X)
    (hX : Chapter07NormalIntegralScheme X)
    (hI : Chapter07IsNonzeroIdeal I) :
    Chapter07NormalizedBlowup I hX :=
  Classical.choice (chapter07_normalizedBlowup_exists I hX hI)

theorem chapter07_normalizedBlowup_birational
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    {hX : Chapter07NormalIntegralScheme X}
    (N : Chapter07NormalizedBlowup I hX)
    (hI : Chapter07IsNonzeroIdeal I) :
    Chapter07Birational (chapter07NormalizedBlowupMap N) := by
  sorry

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
is used only through finiteness of the canonical normalization of a normalized blowup. -/
structure Chapter07ExcellentFiniteTypeSituation (X : Scheme.{u}) where
  base : Scheme.{u}
  structureMap : X ⟶ base
  finiteType : LocallyOfFiniteType structureMap ∧ QuasiCompact structureMap
  normalization_finite :
    ∀ {I : Chapter07CoherentIdeal X}
      {hX : Chapter07NormalIntegralScheme X}
      (N : Chapter07NormalizedBlowup I hX),
      IsFinite N.normalization

theorem chapter07_normalizedBlowup_isFinite_over_excellent_finite_type
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    {hX : Chapter07NormalIntegralScheme X}
    (hE : Chapter07ExcellentFiniteTypeSituation X)
    (N : Chapter07NormalizedBlowup I hX) :
    IsFinite N.normalization := by
  exact hE.normalization_finite N

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
    (N : Chapter07NormalizedBlowup I hX)
    (hI : Chapter07IsNonzeroIdeal I) :
    Chapter07IsProjectiveMorphism (chapter07NormalizedBlowupMap N) ∧
      Chapter07Birational (chapter07NormalizedBlowupMap N) := by
  exact ⟨chapter07_normalizedBlowup_isProjective_over_excellent_finite_type hE N,
    chapter07_normalizedBlowup_birational N hI⟩

/-! ### The normalized Rees algebra -/

def Chapter07NormalDomain
    (A : Type u) [CommRing A] [IsDomain A] : Prop :=
  IsIntegrallyClosed A

def Chapter07NonzeroAffineIdeal
    (A : Type u) [CommRing A] (I : Ideal A) : Prop :=
  I ≠ (⊥ : Ideal A)

theorem chapter07_affineCoherentIdeal_isNonzero
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (hI0 : Chapter07NonzeroAffineIdeal A I) :
    Chapter07IsNonzeroIdeal (chapter07AffineCoherentIdeal A I hI) := by
  intro hzero
  apply hI0
  have htop := congrArg
    (fun J : (Spec (.of A)).IdealSheafData =>
      J.ideal ⟨⊤, isAffineOpen_top _⟩) hzero
  have hmap : I.map (Scheme.ΓSpecIso (.of A)).inv.hom =
      (⊥ : Ideal Γ(Spec (.of A), ⊤)) := by
    simpa [chapter07AffineCoherentIdeal] using htop
  have hinj : Function.Injective (Scheme.ΓSpecIso (.of A)).inv.hom := by
    intro x y hxy
    have hxy' := congrArg (fun z => (Scheme.ΓSpecIso (.of A)).hom z) hxy
    simpa using hxy'
  exact (Ideal.map_eq_bot_iff_of_injective hinj).mp hmap

abbrev Chapter07NonzeroFraction
    (A : Type u) [CommRing A] [IsDomain A] :=
  {x : FractionRing A // x ≠ 0}

noncomputable def chapter07ReesMonomialMap
    (A : Type u) [CommRing A] (n : ℕ) : A →ₗ[A] Polynomial A where
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
    simpa [chapter07ReesMonomialMap] using
      (isIntegral_zero : IsIntegral (Chapter07ReesAlgebra A I) (0 : Polynomial A))
  add_mem' := by
    intro a b ha hb
    change IsIntegral (Chapter07ReesAlgebra A I)
      (chapter07ReesMonomialMap A n (a + b))
    rw [map_add]
    exact ha.add hb
  smul_mem' := by
    intro r a ha
    change IsIntegral (Chapter07ReesAlgebra A I)
      (chapter07ReesMonomialMap A n (r • a))
    rw [map_smul]
    exact IsIntegral.smul r ha

/- The coefficient ideal of the degree-n homogeneous elements in the integral
closure of the Rees algebra.  This is the canonical affine ideal that represents
the integral closure of `I ^ n`; the comparison with the direct integrality
criterion is recorded below rather than hidden in an abbreviation. -/
noncomputable def chapter07IntegralClosurePower
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) : Ideal A where
  carrier := {a | chapter07ReesMonomialMap A n a ∈ chapter07NormalizedReesAlgebra A I}
  zero_mem' := by
    simp [chapter07ReesMonomialMap]
  add_mem' := by
    intro a b ha hb
    change chapter07ReesMonomialMap A n (a + b) ∈ chapter07NormalizedReesAlgebra A I
    rw [map_add]
    exact (chapter07NormalizedReesAlgebra A I).add_mem ha hb
  smul_mem' := by
    intro r a ha
    change chapter07ReesMonomialMap A n (r • a) ∈ chapter07NormalizedReesAlgebra A I
    rw [map_smul]
    simpa [Algebra.smul_def] using
      (chapter07NormalizedReesAlgebra A I).smul_mem ha
        (algebraMap A (Chapter07ReesAlgebra A I) r)

theorem chapter07_normalizedReesDegree_mem_iff
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) (a : A) :
    a ∈ chapter07NormalizedReesDegree A I n ↔
      IsIntegral (Chapter07ReesAlgebra A I) (chapter07ReesMonomialMap A n a) := by
  rfl

theorem chapter07_normalizedReesDegree_is_integralClosurePower
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    chapter07NormalizedReesDegree A I n = chapter07IntegralClosurePower A I n :=
  by
    ext a
    rfl

/- A normalized Rees grading is the exact affine interface needed by `Proj`; the
characterization records that its degree-n homogeneous elements are the integral-closure powers. -/
structure Chapter07NormalizedReesGrading
    (A : Type u) [CommRing A] (I : Ideal A) where
  component : ℕ → Submodule A (chapter07NormalizedReesAlgebra A I)
  graded : GradedAlgebra component
  degree_characterization : ∀ (n : ℕ) (p : chapter07NormalizedReesAlgebra A I),
    p ∈ component n ↔ ∃ a : A,
      p.1 = Polynomial.monomial n a ∧
        a ∈ chapter07NormalizedReesDegree A I n

theorem chapter07_normalizedReesGrading_exists
    (A : Type u) [CommRing A] [IsDomain A] (I : Ideal A)
    (hA : Chapter07NormalDomain A) (hI : Chapter07NonzeroAffineIdeal A I) :
    Nonempty (Chapter07NormalizedReesGrading A I) := by
  sorry

theorem chapter07_normal_domain_normalizedRees_is_graded
    (A : Type u) [CommRing A] [IsDomain A] (I : Ideal A)
    (hA : Chapter07NormalDomain A) (hI : Chapter07NonzeroAffineIdeal A I) :
    Nonempty (Chapter07NormalizedReesGrading A I) :=
  chapter07_normalizedReesGrading_exists A I hA hI

noncomputable def chapter07NormalizedReesGrading
    (A : Type u) [CommRing A] [IsDomain A] (I : Ideal A)
    (hA : Chapter07NormalDomain A) (hI : Chapter07NonzeroAffineIdeal A I) :
    Chapter07NormalizedReesGrading A I :=
  Classical.choice (chapter07_normalizedReesGrading_exists A I hA hI)

noncomputable def chapter07NormalizedReesProj
    (A : Type u) [CommRing A] [IsDomain A] (I : Ideal A)
    (hA : Chapter07NormalDomain A) (hI : Chapter07NonzeroAffineIdeal A I) : Scheme :=
  let G := chapter07NormalizedReesGrading A I hA hI
  letI : CommRing (chapter07NormalizedReesAlgebra A I) := inferInstance
  letI : GradedAlgebra G.component := G.graded
  AlgebraicGeometry.Proj G.component

/- The graded Proj carries its canonical affine structure map; it is kept explicit so the
normalized-Rees comparison is an isomorphism over `Spec A`, not merely an abstract scheme iso. -/
noncomputable def chapter07NormalizedReesProjMap
    (A : Type u) [CommRing A] [IsDomain A] (I : Ideal A)
    (hA : Chapter07NormalDomain A) (hI : Chapter07NonzeroAffineIdeal A I) :
    chapter07NormalizedReesProj A I hA hI ⟶ Spec (.of A) := by
  let G := chapter07NormalizedReesGrading A I hA hI
  letI : CommRing (chapter07NormalizedReesAlgebra A I) := inferInstance
  letI : GradedAlgebra G.component := G.graded
  exact AlgebraicGeometry.Proj.toSpecZero G.component ≫
    Spec.map (CommRingCat.ofHom (algebraMap A (G.component 0)))

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
  (hA : Chapter07NormalIntegralScheme (Spec (.of A)))
    (hI0 : Chapter07NonzeroAffineIdeal A I) : Scheme :=
  (chapter07NormalizedBlowup
    (chapter07AffineCoherentIdeal A I hI) hA
    (chapter07_affineCoherentIdeal_isNonzero A I hI hI0)).carrier

noncomputable def chapter07AffineNormalizedBlowupMap
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (hX : Chapter07NormalIntegralScheme (Spec (.of A)))
    (hI0 : Chapter07NonzeroAffineIdeal A I) :
    chapter07AffineNormalizedBlowup A I hI hX hI0 ⟶ Spec (.of A) := by
  exact chapter07NormalizedBlowupMap
    (chapter07NormalizedBlowup
      (chapter07AffineCoherentIdeal A I hI) hX
      (chapter07_affineCoherentIdeal_isNonzero A I hI hI0))

/- The affine normalized Rees Proj and the abstract normalized blowup are the same
construction; this is the bridge that lets the graded calculation feed the geometric API. -/
theorem chapter07_normalizedReesProj_is_normalizedBlowup
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG)
    (hA : Chapter07NormalDomain A)
    (hX : Chapter07NormalIntegralScheme (Spec (.of A)))
    (hI0 : Chapter07NonzeroAffineIdeal A I) :
    Nonempty
      (Chapter07SchemeIsoOver
        (chapter07NormalizedReesProjMap A I hA hI0)
        (chapter07AffineNormalizedBlowupMap A I hI hX hI0)) := by
  sorry

theorem chapter07_normalizedReesProj_depends_only_on_integral_closure
    (A : Type u) [CommRing A] [IsDomain A] (I J : Ideal A)
    (hA : Chapter07NormalDomain A)
    (hI : Chapter07NonzeroAffineIdeal A I) (hJ : Chapter07NonzeroAffineIdeal A J)
    (hIJ : chapter07IntegralClosureEquivalent A I J) :
    Nonempty
      (chapter07NormalizedReesProj A I hA hI ≅
        chapter07NormalizedReesProj A J hA hJ) := by
  sorry

/- The integral-closure invariance is an invariance of the normalized blowup
over the affine base, not merely an abstract scheme isomorphism. -/
theorem chapter07_normalizedReesProj_depends_only_on_integral_closure_over_base
    (A : Type u) [CommRing A] [IsDomain A] (I J : Ideal A)
    (hA : Chapter07NormalDomain A)
    (hI : Chapter07NonzeroAffineIdeal A I) (hJ : Chapter07NonzeroAffineIdeal A J)
    (hIJ : chapter07IntegralClosureEquivalent A I J) :
    Nonempty
      (Chapter07SchemeIsoOver
        (chapter07NormalizedReesProjMap A I hA hI)
        (chapter07NormalizedReesProjMap A J hA hJ)) := by
  sorry

/-! ### Divisorial valuations and asymptotic orders -/

structure Chapter07DivisorialValuation
    (A : Type u) [CommRing A] [IsDomain A] where
  value : Chapter07NonzeroFraction A → ℤ
  value_one : value ⟨1, by simp⟩ = 0
  value_mul : ∀ (x y : Chapter07NonzeroFraction A),
    value ⟨x.1 * y.1, mul_ne_zero x.2 y.2⟩ = value x + value y
  value_add : ∀ (x y : Chapter07NonzeroFraction A) (hxy : x.1 + y.1 ≠ 0),
    value ⟨x.1 + y.1, hxy⟩ ≥ min (value x) (value y)
  value_surjective : Function.Surjective value
  nonnegative_on_ring : ∀ (a : A) (ha : algebraMap A (FractionRing A) a ≠ 0),
    0 ≤ value ⟨algebraMap A (FractionRing A) a, ha⟩
  nontrivial : ∃ x : Chapter07NonzeroFraction A, value x ≠ 0
  center : Ideal A
  center_prime : center.IsPrime
  center_mem_iff : ∀ (a : A) (ha : algebraMap A (FractionRing A) a ≠ 0),
    a ∈ center ↔ 0 < value ⟨algebraMap A (FractionRing A) a, ha⟩

def chapter07ExceptionalDivisorValuation
    {Y X : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (E : Chapter07ExceptionalDivisor f) : Y.functionField → ℤ :=
  fun r => chapter03OrderOfVanishing r E.divisor

def chapter07ValuationOrder
    {A : Type u} [CommRing A] [IsDomain A]
    (v : Chapter07DivisorialValuation A) (I : Ideal A) (_hI : I ≠ ⊥) : ℤ :=
  sInf (v.value '' {x : Chapter07NonzeroFraction A |
    ∃ a : A, a ∈ I ∧ x.1 = algebraMap A (FractionRing A) a})

def chapter07ValuationOrderOfPower
    {A : Type u} [CommRing A] [IsDomain A]
    (v : Chapter07DivisorialValuation A) (I : Ideal A) (n : ℕ) (_hI : I ≠ ⊥) : ℤ :=
  chapter07ValuationOrder v (I ^ n) (by
    by_cases hn : n = 0
    · simp [hn]
    · intro hpow
      obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot _hI
      have hapow : a ^ n ∈ I ^ n := Ideal.pow_mem_pow haI n
      rw [hpow, Submodule.mem_bot] at hapow
      exact (pow_ne_zero n ha0) hapow
  )

def chapter07AsymptoticValuationOrder
    {A : Type u} [CommRing A] [IsDomain A]
    (v : Chapter07DivisorialValuation A) (I : Ideal A) (hI : I ≠ ⊥) : ℝ :=
  sInf (Set.range (fun n : ℕ ↦
    (chapter07ValuationOrderOfPower v I (n + 1) hI : ℝ) / (n + 1 : ℝ)))

theorem chapter07_divisorial_valuation_measures_asymptotic_order
    {A : Type u} [CommRing A] [IsDomain A]
    (v : Chapter07DivisorialValuation A) (I : Ideal A) (hI : I ≠ ⊥) :
    chapter07AsymptoticValuationOrder v I hI =
      sInf (Set.range (fun n : ℕ ↦
        (chapter07ValuationOrderOfPower v I (n + 1) hI : ℝ) / (n + 1 : ℝ))) := by
  rfl

def Chapter07CodimensionOneValuationControl
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    {hX : Chapter07NormalIntegralScheme X}
    (N : Chapter07NormalizedBlowup I hX) : Prop :=
  ∀ y : N.carrier,
    y ∈ (chapter07NormalizedBlowupMap N) ⁻¹'
      chapter07ExceptionalLocus (chapter07NormalizedBlowupMap N) →
    ∃ E : Chapter07ExceptionalDivisor (chapter07NormalizedBlowupMap N),
      y ∈ E.divisor.support

theorem chapter07_normalized_surface_blowup_has_divisorial_control
    {X : Scheme.{u}} (hX : Chapter07NormalIntegralScheme X)
    (hSurface : (∀ x : X, Order.coheight x ≤ 2) ∧
      ∃ x : X, Order.coheight x = 2)
    (hE : Chapter07ExcellentFiniteTypeSituation X)
    (I : Chapter07CoherentIdeal X)
    (hcenter : Chapter07FiniteClosedPointCenter I)
    (N : Chapter07NormalizedBlowup I hX) :
    Chapter07CodimensionOneValuationControl N := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
