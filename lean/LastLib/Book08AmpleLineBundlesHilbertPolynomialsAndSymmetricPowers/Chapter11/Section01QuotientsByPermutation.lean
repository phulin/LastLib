import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeScheme
open scoped BigOperators Polynomial

universe u v

/-!
### 11.1 Quotients by permutation

The quotient package below separates the categorical quotient from the
particular symmetric-power construction.  The affine polynomial declarations
are the ring-theoretic input used by the finite-group quotient theorem.
-/

/-- The monic orbit polynomial of an element of an affine invariant algebra. -/
def affineOrbitPolynomial {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type v) [Fintype G] [Group G] [MulSemiringAction G B] (b : B) : B[X] :=
  ∏ g : G, (Polynomial.X - Polynomial.C (g • b))

theorem affineOrbitPolynomial_monic {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (G : Type v) [Fintype G] [Group G] [MulSemiringAction G B] (b : B) :
    (affineOrbitPolynomial (A := A) (B := B) G b).Monic := by
  sorry

theorem affineOrbitPolynomial_eval {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (G : Type v) [Fintype G] [Group G] [MulSemiringAction G B] (b : B) :
    (affineOrbitPolynomial (A := A) (B := B) G b).eval b = 0 := by
  sorry

theorem affineOrbitPolynomial_coeff_invariant {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (G : Type v) [Fintype G] [Group G] [MulSemiringAction G B] (b : B)
    (n : ℕ) (g : G) :
    g • (affineOrbitPolynomial (A := A) (B := B) G b).coeff n =
      (affineOrbitPolynomial (A := A) (B := B) G b).coeff n := by
  sorry

/-- Every element is integral over the fixed subalgebra in the invariant-algebra API. -/
theorem invariant_element_is_integral {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (G : Type v) [Fintype G] [Group G] [MulSemiringAction G B]
    [Algebra.IsInvariant A B G] : Algebra.IsIntegral A B := by
  sorry

/-- The affine quotient ring attached to a finite action. -/
def invariantAffineSubring {B : Type u} [CommRing B] (G : Type v) [Group G]
    [MulSemiringAction G B] : Subring B :=
  FixedPoints.subring B (⊤ : Subgroup G)

/-- The affine quotient chart `Spec (B^G)`. -/
def invariantAffineQuotient {B : Type u} [CommRing B] (G : Type v) [Group G]
    [MulSemiringAction G B] : Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (invariantAffineSubring (B := B) G))

theorem invariant_element_integral_over_fixedSubring {B : Type u} [CommRing B]
    (G : Type v) [Fintype G] [Group G] [MulSemiringAction G B] :
    Algebra.IsIntegral (invariantAffineSubring (B := B) G) B := by
  sorry

theorem invariantAffineSubring_contains_coefficients {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] (G : Type v) [Fintype G] [Group G]
    [MulSemiringAction G B] (b : B) (n : ℕ) :
    (affineOrbitPolynomial (A := A) (B := B) G b).coeff n ∈
      invariantAffineSubring (B := B) G := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: this instance should be supplied by the earlier
   relative projective-space chapters once those chapters are elaborated. -/
instance relativePower_quasiProjective {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    Chapter11QuasiProjectiveOver (relativePower X d).carrier := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: quasi-projectivity is stable under the base changes
   used by the book-facing slice interface. -/
instance relativeBaseChange_quasiProjective {S : Scheme.{u}} (X T : RelativeScheme S)
    [Chapter11QuasiProjectiveOver X] :
    Chapter11QuasiProjectiveOver (RelativeScheme.baseChange X T) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: add the proper/projective embedding field to the
   earlier projective morphism interface when it becomes available. -/
class Chapter11ProjectiveOver {S : Scheme.{u}} (X : RelativeScheme S)
    extends Chapter11QuasiProjectiveOver X where
  proper : IsProper X.structuralMap

theorem finite_group_quotient_theorem {S : Scheme.{u}} {Y : RelativeScheme S}
    {G : Type v} [Finite G] [Group G] (act : RelativeAction Y G)
    [Chapter11QuasiProjectiveOver Y] :
    ∃ Q : RelativeCategoricalQuotient Y G act,
      IsIntegralHom Q.quotientMap.hom ∧ IsFinite Q.quotientMap.hom ∧
        Surjective Q.quotientMap.hom := by
  sorry

theorem finite_group_quotient_categorical_universal_property
    {S : Scheme.{u}} {Y : RelativeScheme S} {G : Type v} [Finite G] [Group G]
    (act : RelativeAction Y G) [Chapter11QuasiProjectiveOver Y] :
    ∃ (Q : RelativeCategoricalQuotient Y G act),
      ∀ {Z : RelativeScheme S} (f : Y ⟶ Z),
        (∀ g, act.hom g ≫ f = f) →
          ∃! h : Q.carrier ⟶ Z, Q.quotientMap ≫ h = f := by
  sorry

/-- The chosen symmetric power and its quotient map. -/
noncomputable def symmetricPowerQuotient {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    RelativeFiniteGroupQuotient (relativePower X d).carrier
      (Equiv.Perm (Fin d)) (relativePower X d).permutationAction :=
  finiteGroupQuotient (relativePower X d).permutationAction

abbrev symmetricPower {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] : RelativeScheme S :=
  (symmetricPowerQuotient X d).carrier

abbrev symmetricPowerMap {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    (relativePower X d).carrier ⟶ symmetricPower X d :=
  (symmetricPowerQuotient X d).quotientMap

theorem symmetricPower_integral {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    IsIntegralHom (symmetricPowerMap X d).hom := by
  exact (symmetricPowerQuotient X d).integral

theorem symmetricPower_finite {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    IsFinite (symmetricPowerMap X d).hom := by
  exact (symmetricPowerQuotient X d).finite

theorem symmetricPower_surjective {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    Surjective (symmetricPowerMap X d).hom := by
  exact (symmetricPowerQuotient X d).surjective

theorem symmetricPower_flat_base_change {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] (T : RelativeScheme S)
    (hT : Flat T.structuralMap) :
    ∃ Q : RelativeCategoricalQuotient
        (RelativeScheme.baseChange (relativePower X d).carrier T)
        (Equiv.Perm (Fin d))
        ((relativePower X d).permutationAction.baseChange T),
      ∃ e : RelativeScheme.Iso
          (RelativeScheme.baseChange (symmetricPower X d) T) Q.carrier,
        RelativeScheme.baseChangeHom (symmetricPowerMap X d) T ≫ e.hom =
          Q.quotientMap := by
  exact (symmetricPowerQuotient X d).flat_base_change T hT

/- The canonical comparison of powers after base change, defined by the
   projection universal property. -/
noncomputable def relativePowerBaseChangeComparison {S : Scheme.{u}}
    (X T : RelativeScheme S) (d : ℕ) :
    RelativeScheme.baseChange (relativePower X d).carrier T ⟶
      (relativePower (RelativeScheme.baseChange X T) d).carrier :=
  RelativePower.lift (relativePower (RelativeScheme.baseChange X T) d)
    (fun i => RelativeScheme.baseChangeHom ((relativePower X d).projection i) T)

/-!
The next theorem records the stronger statement for permutation quotients of
powers.  It is intentionally separate from the general flat-base-change
field: arbitrary invariant rings need not commute with arbitrary scalar
extension, whereas elementary symmetric polynomials do.
-/
theorem symmetricPower_arbitrary_base_change {S : Scheme.{u}} (X : RelativeScheme S)
    (d : ℕ) [Chapter11QuasiProjectiveOver X] (T : RelativeScheme S) :
    ∃ e : RelativeScheme.Iso
        (RelativeScheme.baseChange (symmetricPower X d) T)
        (symmetricPower (RelativeScheme.baseChange X T) d),
      RelativeScheme.baseChangeHom (symmetricPowerMap X d) T ≫ e.hom =
        relativePowerBaseChangeComparison X T d ≫
          symmetricPowerMap (RelativeScheme.baseChange X T) d := by
  sorry

@[instance_reducible]
noncomputable def symmetricPower_quasiProjective {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    Chapter11QuasiProjectiveOver (symmetricPower X d) := by
  sorry

@[instance_reducible]
noncomputable def symmetricPower_projective {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11ProjectiveOver X] :
    Chapter11ProjectiveOver (symmetricPower X d) := by
  sorry

noncomputable def symmetricPower_zero_iso {S : Scheme.{u}} (X : RelativeScheme S)
    [Chapter11QuasiProjectiveOver X] :
    RelativeScheme.Iso (symmetricPower X 0) (RelativeScheme.base S) := by
  sorry

noncomputable def symmetricPower_one_iso {S : Scheme.{u}} (X : RelativeScheme S)
    [Chapter11QuasiProjectiveOver X] :
    RelativeScheme.Iso (symmetricPower X 1) X := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
