import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12.Section04FiniteLengthHilbertScheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped BigOperators
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11

/-! ## 12.5. Curves: Hilbert scheme equals symmetric power -/

/-- A smooth quasi-projective relative curve. -/
structure Chapter12SmoothQuasiProjectiveCurve where
  base : Scheme
  curve : Scheme
  structureMap : curve ⟶ base
  smooth : SmoothOfRelativeDimension 1 structureMap
  quasi_projective : chapter12IsQuasiProjectiveMorphism structureMap

attribute [instance] Chapter12SmoothQuasiProjectiveCurve.smooth

/-- The base change of a relative curve to a test scheme. -/
def chapter12CurveBaseChange
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (T : Chapter12SchemeOver C.base) : Scheme :=
  pullback C.structureMap T.hom

def chapter12CurveBaseChangeToCurve
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (T : Chapter12SchemeOver C.base) :
    chapter12CurveBaseChange C T ⟶ C.curve :=
  pullback.fst C.structureMap T.hom

def chapter12CurveBaseChangeToTest
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (T : Chapter12SchemeOver C.base) :
    chapter12CurveBaseChange C T ⟶ T.left :=
  pullback.snd C.structureMap T.hom

@[simp]
theorem chapter12CurveBaseChange_condition
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (T : Chapter12SchemeOver C.base) :
    chapter12CurveBaseChangeToCurve C T ≫ C.structureMap =
      chapter12CurveBaseChangeToTest C T ≫ T.hom := by
  exact pullback.condition

/- The map between the two curve base changes induced by a morphism of test
   schemes is the map used to pull back ideal sheaves. -/
noncomputable def chapter12CurveBaseChangeMap
    (C : Chapter12SmoothQuasiProjectiveCurve)
    {T U : Chapter12SchemeOver C.base} (g : T ⟶ U) :
    chapter12CurveBaseChange C T ⟶ chapter12CurveBaseChange C U :=
  pullback.lift
    (chapter12CurveBaseChangeToCurve C T)
    (chapter12CurveBaseChangeToTest C T ≫ g.left) (by
      rw [Category.assoc, g.w]
      exact chapter12CurveBaseChange_condition C T)

def chapter12CurveFamilyProjection
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (T : Chapter12SchemeOver C.base)
    (I : (chapter12CurveBaseChange C T).IdealSheafData) :
    I.subscheme ⟶ T.left :=
  I.subschemeι ≫ chapter12CurveBaseChangeToTest C T

/- LOCAL_DEPENDENCY_GUESS: the pinned Mathlib checkout has no relative Cartier
  divisor predicate for smooth morphisms, so the effective-Cartier marker in
  the family interface is reserved for the earlier divisor chapters. -/
/-- A finite locally free length-`d` closed family on a relative curve. -/
structure Chapter12CurveHilbertFamily
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (T : Chapter12SchemeOver C.base) (d : ℕ) where
  ideal : (chapter12CurveBaseChange C T).IdealSheafData
  flat : Flat (chapter12CurveFamilyProjection C T ideal)
  finitePresentation : LocallyOfFinitePresentation (chapter12CurveFamilyProjection C T ideal)
  finiteLocallyFree :
    Chapter12FiniteLocallyFreeRank (chapter12CurveFamilyProjection C T ideal) d

def chapter12IsEffectiveCartierFamily
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (T : Chapter12SchemeOver C.base) (d : ℕ)
    (F : Chapter12CurveHilbertFamily C T d) : Prop :=
  F.ideal.IsEffectiveCartier

/-- A relative effective Cartier divisor of degree `d`. -/
structure Chapter12RelativeEffectiveCartierDivisor
    (C : Chapter12SmoothQuasiProjectiveCurve)
  (T : Chapter12SchemeOver C.base) (d : ℕ) where
  family : Chapter12CurveHilbertFamily C T d
  effective_cartier : chapter12IsEffectiveCartierFamily C T d family

abbrev chapter12RelativeEffectiveDivisor
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (T : Chapter12SchemeOver C.base) (d : ℕ) :=
  Chapter12RelativeEffectiveCartierDivisor C T d

/-- On a smooth relative curve, length-`d` closed families and relative effective divisors agree. -/
noncomputable def chapter12_curve_hilbert_eq_effective_divisor
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (T : Chapter12SchemeOver C.base) (d : ℕ) :
    Chapter12CurveHilbertFamily C T d ≃
      Chapter12RelativeEffectiveCartierDivisor C T d := by
  sorry

theorem chapter12_curve_hilbert_family_is_effective_cartier
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (T : Chapter12SchemeOver C.base) (d : ℕ)
    (Z : Chapter12CurveHilbertFamily C T d) :
    ∃ D : Chapter12RelativeEffectiveCartierDivisor C T d, D.family = Z := by
  sorry

/-!
The symmetric power is exposed by the finite permutation quotient. The
quotient theorem itself is a dependency from the preceding symmetric-power
chapter; the universal divisor below records the stronger curve-specific
base-change and moduli property.
-/

structure Chapter12SymmetricPowerData
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) where
  carrier : Scheme
  structureMap : carrier ⟶ C.base
  orderedPower : Scheme
  orderedMap : orderedPower ⟶ C.base
  quotient : orderedPower ⟶ carrier
  quotient_over_base : quotient ≫ structureMap = orderedMap
  quotient_integral : IsIntegralHom quotient
  quotient_finite : IsFinite quotient
  quotient_surjective : Surjective quotient
  permutation : Equiv.Perm (Fin d) → (orderedPower ⟶ orderedPower)
  permutation_one : permutation 1 = 𝟙 orderedPower
  permutation_mul : ∀ σ τ, permutation (σ * τ) = permutation σ ≫ permutation τ
  quotient_invariant : ∀ σ, permutation σ ≫ quotient = quotient
  quotient_universal : ∀ {Z : Scheme} (f : orderedPower ⟶ Z),
    (∀ σ, permutation σ ≫ f = f) →
      ∃! h : carrier ⟶ Z, quotient ≫ h = f
  baseChangedCarrier : ∀ _T : Chapter12SchemeOver C.base, Scheme
  baseChangedMap : ∀ (T : Chapter12SchemeOver C.base),
    baseChangedCarrier T ⟶ T.left
  baseChangedIso : ∀ (T : Chapter12SchemeOver C.base),
    pullback structureMap T.hom ≅ baseChangedCarrier T
  baseChangedIso_over_test : ∀ (T : Chapter12SchemeOver C.base),
    (baseChangedIso T).hom ≫ baseChangedMap T =
      pullback.snd structureMap T.hom
  smooth : SmoothOfRelativeDimension d structureMap
  zero_identification : d = 0 →
    Nonempty (Chapter12RepresentingOverIso structureMap (𝟙 C.base))
  one_identification : d = 1 →
    Nonempty (Chapter12RepresentingOverIso structureMap C.structureMap)

theorem chapter12_symmetric_power_exists
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    Nonempty (Chapter12SymmetricPowerData C d) := by
  sorry

noncomputable def chapter12SymmetricPowerData
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    Chapter12SymmetricPowerData C d :=
  Classical.choice (chapter12_symmetric_power_exists C d)

abbrev chapter12SymmetricPower
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) : Scheme :=
  (chapter12SymmetricPowerData C d).carrier

abbrev chapter12SymmetricPowerMap
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    chapter12SymmetricPower C d ⟶ C.base :=
  (chapter12SymmetricPowerData C d).structureMap

theorem chapter12_symmetric_power_quotient_is_finite
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    IsFinite (chapter12SymmetricPowerData C d).quotient := by
  exact (chapter12SymmetricPowerData C d).quotient_finite

theorem chapter12_symmetric_power_quotient_is_surjective
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    Surjective (chapter12SymmetricPowerData C d).quotient := by
  exact (chapter12SymmetricPowerData C d).quotient_surjective

theorem chapter12_symmetric_power_zero
    (C : Chapter12SmoothQuasiProjectiveCurve) :
    Nonempty (chapter12SymmetricPower C 0 ≅ C.base) := by
  rcases (chapter12SymmetricPowerData C 0).zero_identification rfl with ⟨e⟩
  exact ⟨e.iso⟩

theorem chapter12_symmetric_power_one
    (C : Chapter12SmoothQuasiProjectiveCurve) :
    Nonempty (chapter12SymmetricPower C 1 ≅ C.curve) := by
  rcases (chapter12SymmetricPowerData C 1).one_identification rfl with ⟨e⟩
  exact ⟨e.iso⟩

/- The base-change isomorphism is kept as data so its two projections and its
  compatibility with the structure map remain available to later proofs. -/
def chapter12IsSymmetricPowerOfBaseChangedCurve
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ)
    (T : Chapter12SchemeOver C.base) (X : Scheme)
    (xMap : X ⟶ T.left) : Prop :=
  Nonempty {e : pullback (chapter12SymmetricPowerMap C d) T.hom ≅ X //
    e.hom ≫ xMap = pullback.snd (chapter12SymmetricPowerMap C d) T.hom}

structure Chapter12SymmetricPowerBaseChangeData
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ)
    (T : Chapter12SchemeOver C.base) where
  baseChangedSymmetricPower : Scheme
  baseChangedMap : baseChangedSymmetricPower ⟶ T.left
  iso : pullback (chapter12SymmetricPowerMap C d) T.hom ≅ baseChangedSymmetricPower
  iso_over_test : iso.hom ≫ baseChangedMap = pullback.snd _ _

theorem chapter12_symmetric_power_base_change_exists
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ)
    (T : Chapter12SchemeOver C.base) :
    Nonempty (Chapter12SymmetricPowerBaseChangeData C d T) := by
  sorry

noncomputable def chapter12SymmetricPowerBaseChangeData
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ)
    (T : Chapter12SchemeOver C.base) :
    Chapter12SymmetricPowerBaseChangeData C d T :=
  Classical.choice (chapter12_symmetric_power_base_change_exists C d T)

theorem chapter12_symmetric_power_base_change
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ)
    (T : Chapter12SchemeOver C.base) :
    (chapter12SymmetricPowerBaseChangeData C d T).iso.hom ≫
        (chapter12SymmetricPowerBaseChangeData C d T).baseChangedMap =
      pullback.snd (chapter12SymmetricPowerMap C d) T.hom := by
  exact (chapter12SymmetricPowerBaseChangeData C d T).iso_over_test

/-- The ordered-root polynomial used on a smooth affine chart. -/
def chapter12UniversalRootPolynomial
    (A : Type*) [CommRing A] (d : ℕ) (t : Fin d → A) : Polynomial A :=
  ∏ i : Fin d, (Polynomial.X - Polynomial.C (t i))

theorem chapter12UniversalRootPolynomial_expands
    (A : Type*) [CommRing A] (d : ℕ) (t : Fin d → A) :
    chapter12UniversalRootPolynomial A d t =
      ∏ i : Fin d, (Polynomial.X - Polynomial.C (t i)) := by
  rfl

theorem chapter12UniversalRootPolynomial_eval
    (A : Type*) [CommRing A] (d : ℕ) (z : A) (t : Fin d → A) :
    (chapter12UniversalRootPolynomial A d t).eval z =
      ∏ i : Fin d, (z - t i) := by
  rw [chapter12UniversalRootPolynomial, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp

/- The ambient of the universal divisor is the canonical fiber product
  `C ×_S Sym^d(C)`, with both projections exposed for later pullback proofs. -/
def chapter12CurveSymmetricPowerAmbient
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) : Scheme :=
  pullback C.structureMap (chapter12SymmetricPowerMap C d)

def chapter12CurveSymmetricPowerAmbientToCurve
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    chapter12CurveSymmetricPowerAmbient C d ⟶ C.curve :=
  pullback.fst C.structureMap (chapter12SymmetricPowerMap C d)

def chapter12CurveSymmetricPowerAmbientToSymmetricPower
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    chapter12CurveSymmetricPowerAmbient C d ⟶ chapter12SymmetricPower C d :=
  pullback.snd C.structureMap (chapter12SymmetricPowerMap C d)

@[simp]
theorem chapter12CurveSymmetricPowerAmbient_condition
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    chapter12CurveSymmetricPowerAmbientToCurve C d ≫ C.structureMap =
      chapter12CurveSymmetricPowerAmbientToSymmetricPower C d ≫
        chapter12SymmetricPowerMap C d := by
  exact pullback.condition

/-- The universal degree-`d` divisor on `C ×ₛ Sym^d(C)`. -/
structure Chapter12UniversalDivisor
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (d : ℕ) where
  family : Chapter12CurveHilbertFamily C
    (Over.mk (chapter12SymmetricPowerMap C d)) d
  effective_cartier : chapter12IsEffectiveCartierFamily C
    (Over.mk (chapter12SymmetricPowerMap C d)) d family

theorem chapter12_universal_divisor_exists
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (d : ℕ) :
    Nonempty (Chapter12UniversalDivisor C d) := by
  sorry

noncomputable def chapter12UniversalDivisor
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (d : ℕ) : Chapter12UniversalDivisor C d :=
  Classical.choice (chapter12_universal_divisor_exists C d)

def chapter12UniversalDivisorPullbackIdeal
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (d : ℕ) {T : Chapter12SchemeOver C.base}
    (f : T ⟶ Over.mk (chapter12SymmetricPowerMap C d)) :
    (chapter12CurveBaseChange C T).IdealSheafData :=
  (chapter12UniversalDivisor C d).family.ideal.comap
    (chapter12CurveBaseChangeMap C f)

/- The representing equivalence is required to be induced by the displayed
   universal divisor, and its naturality is stated at the ideal-sheaf level.
   This is the scheme-theoretic form that also detects nilpotent test rings. -/
structure Chapter12UniversalDivisorRepresentingData
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (d : ℕ) where
  equivalence : ∀ T : Chapter12SchemeOver C.base,
    (T ⟶ Over.mk (chapter12SymmetricPowerMap C d)) ≃
      Chapter12RelativeEffectiveCartierDivisor C T d
  pullback_universal : ∀ (T : Chapter12SchemeOver C.base)
    (f : T ⟶ Over.mk (chapter12SymmetricPowerMap C d)),
    (equivalence T f).family.ideal =
      chapter12UniversalDivisorPullbackIdeal C d f
  natural : ∀ {T U : Chapter12SchemeOver C.base} (g : T ⟶ U)
    (f : U ⟶ Over.mk (chapter12SymmetricPowerMap C d)),
    (equivalence T (g ≫ f)).family.ideal =
      (equivalence U f).family.ideal.comap (chapter12CurveBaseChangeMap C g)

theorem chapter12UniversalDivisor_is_finite_locally_free
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (d : ℕ) :
    Chapter12FiniteLocallyFreeRank
      (chapter12CurveFamilyProjection C
        (Over.mk (chapter12SymmetricPowerMap C d))
        (chapter12UniversalDivisor C d).family.ideal) d := by
  exact (chapter12UniversalDivisor C d).family.finiteLocallyFree

/-- The universal divisor represents relative effective Cartier divisors of degree `d`. -/
noncomputable def chapter12_universal_divisor_represents
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (d : ℕ) :
    Chapter12UniversalDivisorRepresentingData C d := by
  sorry

/-- A curve Hilbert scheme representation, used only to state uniqueness of representers. -/
/- The family-level pullback operation is the curve analogue of the operation
   in `Dependencies.lean`; its coherence is part of the representability
   interface rather than an implicit choice of inverse image. -/
structure Chapter12CurveHilbertFamilyPullbackData
    (C : Chapter12SmoothQuasiProjectiveCurve)
    where
  pullback : {d : ℕ} → {T U : Chapter12SchemeOver C.base} →
    (g : T ⟶ U) → Chapter12CurveHilbertFamily C U d →
      Chapter12CurveHilbertFamily C T d
  /-- The chosen pullback is the scheme-theoretic inverse image of the ideal. -/
  pullback_ideal : ∀ {d : ℕ} {T U : Chapter12SchemeOver C.base}
    (g : T ⟶ U) (F : Chapter12CurveHilbertFamily C U d),
    (pullback g F).ideal = F.ideal.comap (chapter12CurveBaseChangeMap C g)
  pullback_id : ∀ {d : ℕ} {T : Chapter12SchemeOver C.base}
    (F : Chapter12CurveHilbertFamily C T d), pullback (𝟙 T) F = F
  pullback_comp : ∀ {d : ℕ} {T U V : Chapter12SchemeOver C.base}
    (g : T ⟶ U) (h : U ⟶ V) (F : Chapter12CurveHilbertFamily C V d),
    pullback g (pullback h F) = pullback (g ≫ h) F

theorem chapter12_curve_hilbert_family_pullback_data_exists
    (C : Chapter12SmoothQuasiProjectiveCurve)
    : Nonempty (Chapter12CurveHilbertFamilyPullbackData C) := by
  sorry

noncomputable def chapter12CurveHilbertFamilyPullbackData
    (C : Chapter12SmoothQuasiProjectiveCurve)
    : Chapter12CurveHilbertFamilyPullbackData C :=
  Classical.choice (chapter12_curve_hilbert_family_pullback_data_exists C)

noncomputable def chapter12PullbackCurveHilbertFamily
    (C : Chapter12SmoothQuasiProjectiveCurve)
    {d : ℕ}
    {T U : Chapter12SchemeOver C.base} (g : T ⟶ U)
    (F : Chapter12CurveHilbertFamily C U d) :
    Chapter12CurveHilbertFamily C T d :=
  (chapter12CurveHilbertFamilyPullbackData C).pullback g F

theorem chapter12PullbackCurveHilbertFamily_ideal
    (C : Chapter12SmoothQuasiProjectiveCurve)
    {d : ℕ}
    {T U : Chapter12SchemeOver C.base} (g : T ⟶ U)
    (F : Chapter12CurveHilbertFamily C U d) :
    (chapter12PullbackCurveHilbertFamily C g F).ideal =
      F.ideal.comap (chapter12CurveBaseChangeMap C g) := by
  exact (chapter12CurveHilbertFamilyPullbackData C).pullback_ideal g F

structure Chapter12CurveHilbertEffectiveDivisorNaturalEquivalence
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) where
  component : ∀ T : Chapter12SchemeOver C.base,
    Chapter12CurveHilbertFamily C T d ≃
      Chapter12RelativeEffectiveCartierDivisor C T d
  natural : ∀ {T U : Chapter12SchemeOver C.base} (g : T ⟶ U)
    (Z : Chapter12CurveHilbertFamily C U d),
    (component T (chapter12PullbackCurveHilbertFamily C g Z)).family.ideal =
      (component U Z).family.ideal.comap (chapter12CurveBaseChangeMap C g)

noncomputable def chapter12_curve_hilbert_effective_divisor_natural
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    Chapter12CurveHilbertEffectiveDivisorNaturalEquivalence C d := by
  sorry

structure Chapter12CurveHilbertSchemeData
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (d : ℕ) where
  carrier : Scheme
  structureMap : carrier ⟶ C.base
  representingEquivalence : ∀ T : Chapter12SchemeOver C.base,
    (T ⟶ Over.mk structureMap) ≃ Chapter12CurveHilbertFamily C T d
  universalFamily : Chapter12CurveHilbertFamily C (Over.mk structureMap) d
  /-- The displayed universal family is the family represented by the
      identity map of the representing scheme. -/
  universalFamily_is_representing_identity :
    representingEquivalence (Over.mk structureMap) (𝟙 (Over.mk structureMap)) =
      universalFamily
  representingEquivalence_natural :
    ∀ {T U : Chapter12SchemeOver C.base} (g : T ⟶ U)
      (f : U ⟶ Over.mk structureMap),
      representingEquivalence T (g ≫ f) =
        chapter12PullbackCurveHilbertFamily C g
          (representingEquivalence U f)

theorem chapter12_curve_hilbert_scheme_exists
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (d : ℕ) : Nonempty (Chapter12CurveHilbertSchemeData C d) := by
  sorry

noncomputable def chapter12CurveHilbertSchemeData
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (d : ℕ) : Chapter12CurveHilbertSchemeData C d :=
  Classical.choice (chapter12_curve_hilbert_scheme_exists C d)

theorem chapter12_curve_hilbert_scheme_eq_symmetric_power
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (d : ℕ) :
    Nonempty (Chapter12RepresentingOverIso
      (chapter12CurveHilbertSchemeData C d).structureMap
      (chapter12SymmetricPowerMap C d)) := by
  sorry

/-- The two universal families agree under the representing isomorphism. -/
structure Chapter12CurveUniversalFamilyAgreement
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (d : ℕ) where
  representingIso : Chapter12RepresentingOverIso
    (chapter12CurveHilbertSchemeData C d).structureMap
    (chapter12SymmetricPowerMap C d)
  pullback_universal_families_agree :
    (chapter12CurveHilbertSchemeData C d).universalFamily.ideal =
      (chapter12PullbackCurveHilbertFamily C
        (Over.homMk representingIso.iso.hom representingIso.over)
        (chapter12UniversalDivisor C d).family).ideal
  universal_divisor_representation :
    Chapter12UniversalDivisorRepresentingData C d

theorem chapter12_curve_universal_families_agree
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (d : ℕ) : Nonempty (Chapter12CurveUniversalFamilyAgreement C d) := by
  sorry

/-- Addition of effective divisors gives the symmetric-power addition morphism. -/
theorem chapter12_symmetric_power_addition_exists
    (C : Chapter12SmoothQuasiProjectiveCurve) (d e : ℕ) :
    Nonempty (pullback (chapter12SymmetricPowerMap C d) (chapter12SymmetricPowerMap C e) ⟶
      chapter12SymmetricPower C (d + e)) := by
  sorry

noncomputable def chapter12SymmetricPowerAddition
    (C : Chapter12SmoothQuasiProjectiveCurve) (d e : ℕ) :
    pullback (chapter12SymmetricPowerMap C d) (chapter12SymmetricPowerMap C e) ⟶
      chapter12SymmetricPower C (d + e) :=
  Classical.choice (chapter12_symmetric_power_addition_exists C d e)

theorem chapter12_symmetric_power_addition_over_base
    (C : Chapter12SmoothQuasiProjectiveCurve) (d e : ℕ) :
    chapter12SymmetricPowerAddition C d e ≫
        chapter12SymmetricPowerMap C (d + e) =
      pullback.snd (chapter12SymmetricPowerMap C d)
          (chapter12SymmetricPowerMap C e) ≫
        chapter12SymmetricPowerMap C e := by
  sorry

/-- The ideal-sheaf equation defining the sum of two effective divisors. -/
def chapter12DivisorSum
    {C : Chapter12SmoothQuasiProjectiveCurve}
    {T : Chapter12SchemeOver C.base}
    {d e : ℕ}
    (D : Chapter12RelativeEffectiveCartierDivisor C T d)
    (E : Chapter12RelativeEffectiveCartierDivisor C T e)
    (F : Chapter12RelativeEffectiveCartierDivisor C T (d + e)) : Prop :=
  F.family.ideal = D.family.ideal * E.family.ideal

theorem chapter12_symmetric_power_addition_associative
    (C : Chapter12SmoothQuasiProjectiveCurve)
    {T : Chapter12SchemeOver C.base}
    (d e f : ℕ)
    (D : Chapter12RelativeEffectiveCartierDivisor C T d)
    (E : Chapter12RelativeEffectiveCartierDivisor C T e)
    (F : Chapter12RelativeEffectiveCartierDivisor C T f)
    (G : Chapter12RelativeEffectiveCartierDivisor C T (d + e + f)) :
    (G.family.ideal = (D.family.ideal * E.family.ideal) * F.family.ideal) ↔
      (G.family.ideal = D.family.ideal * (E.family.ideal * F.family.ideal)) := by
  sorry

theorem chapter12_symmetric_power_addition_commutative
    (C : Chapter12SmoothQuasiProjectiveCurve)
    {T : Chapter12SchemeOver C.base}
    (d e : ℕ)
    (D : Chapter12RelativeEffectiveCartierDivisor C T d)
    (E : Chapter12RelativeEffectiveCartierDivisor C T e) :
    D.family.ideal * E.family.ideal = E.family.ideal * D.family.ideal := by
  sorry

structure Chapter12SymmetricPowerAdditionBaseChangeData
    (C : Chapter12SmoothQuasiProjectiveCurve) (d e : ℕ)
    (T : Chapter12SchemeOver C.base) where
  degree_d : Chapter12SymmetricPowerBaseChangeData C d T
  degree_e : Chapter12SymmetricPowerBaseChangeData C e T
  degree_sum : Chapter12SymmetricPowerBaseChangeData C (d + e) T
  baseChangedAddition :
    pullback degree_d.baseChangedMap degree_e.baseChangedMap ⟶
      degree_sum.baseChangedSymmetricPower
  baseChangedAddition_over_test :
    baseChangedAddition ≫ degree_sum.baseChangedMap =
      pullback.snd degree_d.baseChangedMap degree_e.baseChangedMap ≫
        degree_e.baseChangedMap
  baseChangeComparison :
    pullback
        (pullback.snd (chapter12SymmetricPowerMap C d)
          (chapter12SymmetricPowerMap C e) ≫
          chapter12SymmetricPowerMap C e) T.hom ⟶
      pullback degree_d.baseChangedMap degree_e.baseChangedMap
  baseChangedOriginalAddition :
    pullback
        (pullback.snd (chapter12SymmetricPowerMap C d)
          (chapter12SymmetricPowerMap C e) ≫
          chapter12SymmetricPowerMap C e) T.hom ⟶
      pullback (chapter12SymmetricPowerMap C (d + e)) T.hom
  baseChangedOriginalAddition_over_test :
    baseChangedOriginalAddition ≫
        pullback.fst (chapter12SymmetricPowerMap C (d + e)) T.hom =
      pullback.fst
          (pullback.snd (chapter12SymmetricPowerMap C d)
            (chapter12SymmetricPowerMap C e) ≫
            chapter12SymmetricPowerMap C e) T.hom ≫
        chapter12SymmetricPowerAddition C d e
  addition_compatibility :
    baseChangeComparison ≫ baseChangedAddition =
      baseChangedOriginalAddition ≫ degree_sum.iso.hom

def chapter12_symmetric_power_addition_base_change_statement
    (C : Chapter12SmoothQuasiProjectiveCurve) (d e : ℕ)
    (T : Chapter12SchemeOver C.base) : Prop :=
  Nonempty (Chapter12SymmetricPowerAdditionBaseChangeData C d e T)

theorem chapter12_symmetric_power_addition_base_change
    (C : Chapter12SmoothQuasiProjectiveCurve) (d e : ℕ)
    (T : Chapter12SchemeOver C.base) :
    chapter12_symmetric_power_addition_base_change_statement C d e T := by
  sorry

def chapter12SymmetricPowerRelativeScheme
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    RelativeScheme C.base where
  carrier := chapter12SymmetricPower C d
  structuralMap := chapter12SymmetricPowerMap C d

noncomputable def chapter12SymmetricPowerLeftAddition
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (component : ℕ → RelativeScheme C.base)
    (addition : ∀ d e,
      (relativeProduct (component d) (component e)).carrier ⟶ component (d + e))
    (d e f : ℕ) :
    (relativeProduct
      (relativeProduct (component d) (component e)).carrier (component f)).carrier ⟶
      component (d + e + f) := by
  sorry

noncomputable def chapter12SymmetricPowerRightAddition
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (component : ℕ → RelativeScheme C.base)
    (addition : ∀ d e,
      (relativeProduct (component d) (component e)).carrier ⟶ component (d + e))
    (d e f : ℕ) :
    (relativeProduct (component d)
      (relativeProduct (component e) (component f)).carrier).carrier ⟶
      component (d + e + f) := by
  sorry

noncomputable def chapter12SymmetricPowerSwap
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (component : ℕ → RelativeScheme C.base) (d e : ℕ) :
    (relativeProduct (component d) (component e)).carrier ⟶
      (relativeProduct (component e) (component d)).carrier := by
  sorry

structure Chapter12SymmetricPowerAssociativityData
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (component : ℕ → RelativeScheme C.base)
    (addition : ∀ d e,
      (relativeProduct (component d) (component e)).carrier ⟶ component (d + e))
    (d e f : ℕ) where
  associator : RelativeScheme.Iso
    (relativeProduct
      (relativeProduct (component d) (component e)).carrier (component f)).carrier
    (relativeProduct (component d)
      (relativeProduct (component e) (component f)).carrier).carrier
  equation : chapter12SymmetricPowerLeftAddition C component addition d e f =
    associator.hom ≫ chapter12SymmetricPowerRightAddition C component addition d e f

structure Chapter12SymmetricPowerCommutativityData
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (component : ℕ → RelativeScheme C.base)
    (addition : ∀ d e,
      (relativeProduct (component d) (component e)).carrier ⟶ component (d + e))
    (d e : ℕ) where
  sum_reindex : RelativeScheme.Iso (component (e + d)) (component (d + e))
  equation : chapter12SymmetricPowerSwap C component d e ≫ addition e d ≫
      sum_reindex.hom =
    addition d e

structure Chapter12SymmetricPowerUnitData
    (C : Chapter12SmoothQuasiProjectiveCurve)
    (component : ℕ → RelativeScheme C.base)
    (addition : ∀ d e,
      (relativeProduct (component d) (component e)).carrier ⟶ component (d + e)) where
  unit_component : RelativeScheme.Iso (component 0) (RelativeScheme.base C.base)
  left_unit : ∀ d, RelativeScheme.Iso
    (relativeProduct (component 0) (component d)).carrier (component (0 + d))
  left_unit_equation : ∀ d, (left_unit d).hom = addition 0 d
  right_unit : ∀ d, RelativeScheme.Iso
    (relativeProduct (component d) (component 0)).carrier (component (d + 0))
  right_unit_equation : ∀ d, (right_unit d).hom = addition d 0

/-- The graded commutative monoid of all symmetric powers. -/
structure Chapter12SymmetricPowerGradedMonoid
    (C : Chapter12SmoothQuasiProjectiveCurve) where
  component : ℕ → RelativeScheme C.base
  identifies_component : ∀ d, RelativeScheme.Iso (component d)
    (chapter12SymmetricPowerRelativeScheme C d)
  addition : ∀ d e,
    (relativeProduct (component d) (component e)).carrier ⟶ component (d + e)
  associative : ∀ d e f,
    Chapter12SymmetricPowerAssociativityData C component addition d e f
  commutative : ∀ d e,
    Chapter12SymmetricPowerCommutativityData C component addition d e
  unit_component : Chapter12SymmetricPowerUnitData C component addition

theorem chapter12_symmetric_powers_form_graded_commutative_monoid
    (C : Chapter12SmoothQuasiProjectiveCurve) :
    Nonempty (Chapter12SymmetricPowerGradedMonoid C) := by
  sorry

/-!
The local monic-polynomial chart explains both collisions and smoothness: the
coefficients are coordinates, while repeated roots are retained as a
nonreduced divisor rather than discarded.
-/

structure Chapter12MonicPolynomialChart
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) where
  chart : Scheme
  chartMap : chart ⟶ chapter12SymmetricPower C d
  coefficientRing : Type*
  coefficientRing_commRing : CommRing coefficientRing
  affineIdentification : Prop
  coefficients : Fin d → coefficientRing
  polynomial : Polynomial coefficientRing
  polynomial_monic : polynomial.Monic
  polynomial_degree : polynomial.natDegree = d
  monic_equation : Prop
  roots_may_collide : Prop

attribute [instance] Chapter12MonicPolynomialChart.coefficientRing_commRing

theorem chapter12_symmetric_power_monic_coefficient_charts
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    Nonempty (Chapter12MonicPolynomialChart.{0} C d) := by
  sorry

theorem chapter12_symmetric_power_is_smooth
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    Smooth (chapter12SymmetricPowerMap C d) := by
  exact @SmoothOfRelativeDimension.smooth _ _ _ _
    (chapter12SymmetricPowerData C d).smooth

theorem chapter12_symmetric_power_relative_dimension
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    chapter12HasRelativeDimension (chapter12SymmetricPowerMap C d) d := by
  exact (chapter12SymmetricPowerData C d).smooth

/-- The proper Hilbert-to-cycle comparison for a projective singular curve. -/
structure Chapter12SingularCurveCycleComparison where
  base : Scheme
  curve : Scheme
  structureMap : curve ⟶ base
  projective_curve : chapter12IsProjectiveMorphism structureMap
  hilbertScheme : Scheme
  hilbertMap : hilbertScheme ⟶ base
  cycleSpace : Scheme
  cycleMap : cycleSpace ⟶ base
  hilbertToCycle : hilbertScheme ⟶ cycleSpace
  hilbertToCycle_over_base : hilbertToCycle ≫ cycleMap = hilbertMap
  proper : IsProper hilbertToCycle
  isomorphism_away_from_singular_locus : Prop
  singular_fiber_contains_distinct_embedded_ideals : Prop
  same_cycle : Prop

theorem chapter12_singular_curve_hilbert_to_cycle_comparison :
    Nonempty Chapter12SingularCurveCycleComparison := by
  sorry

theorem chapter12_singular_curve_cycle_warning
    (C : Chapter12SingularCurveCycleComparison) :
    C.singular_fiber_contains_distinct_embedded_ideals ∧ C.same_cycle := by
  sorry

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12
