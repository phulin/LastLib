import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Section03ConfigurationSpaces

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeScheme
open scoped BigOperators Polynomial

universe u v

/-!
### 11.4 The universal divisor on a smooth curve
-/

/- LOCAL_DEPENDENCY_GUESS: package the smooth quasi-projective curve hypotheses
   from the earlier chapters as a reusable class. -/
class Chapter11SmoothQuasiProjectiveCurve {S : Scheme.{u}} (C : RelativeScheme S)
    extends Chapter11QuasiProjectiveOver C where
  smooth : SmoothOfRelativeDimension 1 C.structuralMap

instance chapter11SmoothQuasiProjectiveCurve_baseChange {S : Scheme.{u}}
    (C T : RelativeScheme S) [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter11SmoothQuasiProjectiveCurve (RelativeScheme.baseChange C T) where
  toChapter11QuasiProjectiveOver := relativeBaseChange_quasiProjective C T
  smooth := by sorry

abbrev curvePowerAmbient {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ) : Scheme.{u} :=
  pullback C.structuralMap (relativePower C d).carrier.structuralMap

abbrev curveSymmetricAmbient {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver C] : Scheme.{u} :=
  pullback C.structuralMap (symmetricPower C d).structuralMap

noncomputable def orderedToSymmetricAmbient {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver C] :
    curvePowerAmbient C d ⟶ curveSymmetricAmbient C d :=
  pullback.lift
    (pullback.fst C.structuralMap (relativePower C d).carrier.structuralMap)
    (pullback.snd C.structuralMap (relativePower C d).carrier.structuralMap ≫
      (symmetricPowerMap C d).hom) (by sorry)

noncomputable def curveGraphMap {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ) (i : Fin d) :
    (relativePower C d).carrier.carrier ⟶ curvePowerAmbient C d :=
  pullback.lift
    ((relativePower C d).projection i).hom
    (𝟙 (relativePower C d).carrier.carrier) (by sorry)

structure GraphCartierDivisor {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    (i : Fin d) where
  divisor : EffectiveCartierDivisor (curvePowerAmbient C d)
  support_eq_graph : (divisor.ideal.support : Set (curvePowerAmbient C d)) =
    Set.range (curveGraphMap C d i)

theorem graphCartierDivisor_exists {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] (i : Fin d) :
    Nonempty (GraphCartierDivisor C d i) := by
  sorry

noncomputable def graphCartierDivisor {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] (i : Fin d) : GraphCartierDivisor C d i :=
  Classical.choice (graphCartierDivisor_exists C d i)

noncomputable def orderedUniversalDivisor {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] : EffectiveCartierDivisor (curvePowerAmbient C d) :=
  EffectiveCartierDivisor.sum (fun i => (graphCartierDivisor C d i).divisor)

def Chapter11DivisorPermutationInvariant {X : Scheme.{u}}
    (D : EffectiveCartierDivisor X) (G : Type v) [Group G] : Prop :=
  ∀ _g : G, ∃ e : X ⟶ X, IsIso e ∧ D.inclusion ≫ e = D.inclusion

theorem orderedUniversalDivisor_invariant {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter11DivisorPermutationInvariant (orderedUniversalDivisor C d)
      (Equiv.Perm (Fin d)) := by
  sorry

def elementarySymmetricCoefficient {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (k : ℕ) : R :=
  ((Finset.univ : Finset (Finset (Fin d))).filter (fun s => s.card = k)).sum
    (fun s => s.prod t)

noncomputable def universalMonicPolynomial {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) : R[X] :=
  ∏ i, (Polynomial.X - Polynomial.C (t i))

theorem universalMonicPolynomial_monic {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) : (universalMonicPolynomial t).Monic := by
  sorry

theorem universalMonicPolynomial_has_coordinate_root {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (i : Fin d) :
    Polynomial.eval (t i) (universalMonicPolynomial t) = 0 := by
  sorry

theorem universalMonicPolynomial_expansion {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (k : ℕ) (hk : k ≤ d) :
    (universalMonicPolynomial t).coeff (d - k) =
      (-1 : R) ^ k * elementarySymmetricCoefficient t k := by
  sorry

theorem elementarySymmetricCoefficient_permutation {R : Type u} [CommRing R] {d : ℕ}
    (t : Fin d → R) (σ : Equiv.Perm (Fin d)) (k : ℕ) :
    elementarySymmetricCoefficient (fun i => t (σ i)) k =
      elementarySymmetricCoefficient t k := by
  sorry

/- The coefficients above are the affine descent calculation.  The following
   existence statement is the geometric gluing of those affine charts. -/
theorem universalDivisor_exists {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    Nonempty (EffectiveCartierDivisor (curveSymmetricAmbient C d)) := by
  sorry

noncomputable def universalDivisor {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
  EffectiveCartierDivisor (curveSymmetricAmbient C d) :=
  Classical.choice (universalDivisor_exists C d)

/- The support relation is the deliberately small bridge to the ideal-sheaf
   pullback API; the later fixup can strengthen it to equality of Cartier
   ideals if that API is available. -/
def Chapter11DivisorSupportPullbackRelation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : EffectiveCartierDivisor Y) (E : EffectiveCartierDivisor X) : Prop :=
  (E.ideal.support : Set X) = f.base ⁻¹' (D.ideal.support : Set Y)

theorem universalDivisor_descends_ordered_divisor {S : Scheme.{u}} (C : RelativeScheme S)
    (d : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter11DivisorSupportPullbackRelation (orderedToSymmetricAmbient C d)
      (universalDivisor C d) (orderedUniversalDivisor C d) := by
  sorry

theorem universalDivisor_finiteLocallyFree {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter11FiniteLocallyFreeOfRank
      ((universalDivisor C d).inclusion ≫
        pullback.snd C.structuralMap (symmetricPower C d).structuralMap) d := by
  sorry

theorem universalDivisor_repeated_roots_are_allowed {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    ∀ T : RelativeScheme S,
      ∃ D : RelativeEffectiveCartierDivisor C T d,
        Chapter11FiniteLocallyFreeOfRank
          (D.divisor.inclusion ≫ pullback.snd C.structuralMap T.structuralMap) d := by
  sorry

structure Chapter11MonicChartWitness (d : ℕ) where
  R : Type u
  A : Type u
  [commRingR : CommRing R]
  [commRingA : CommRing A]
  [algebraRA : Algebra R A]
  chart : MonicPolynomialChart R A d

theorem finite_flat_cartier_divisor_etale_locally_monic
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C]
    (D : RelativeEffectiveCartierDivisor C T d) :
    ∃ (U : Scheme.{u}) (u : U ⟶ T.carrier),
      Etale u ∧ Surjective u ∧
        Nonempty (Chapter11MonicChartWitness d) := by
  sorry

theorem monic_equation_recovers_chart {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] {d : ℕ} (P Q : MonicPolynomialChart R A d)
    (hparameter : P.parameter = Q.parameter) (hpolynomial : P.polynomial = Q.polynomial) :
    P = Q := by
  exact MonicPolynomialChart.ext hparameter hpolynomial

noncomputable def pullbackUniversalDivisor {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C]
    (f : T ⟶ symmetricPower C d) : RelativeEffectiveCartierDivisor C T d := by
  sorry

noncomputable def divisorToSymmetricPoint {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C]
    (D : RelativeEffectiveCartierDivisor C T d) : T ⟶ symmetricPower C d := by
  sorry

noncomputable def universalDivisorEquiv {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    (T ⟶ symmetricPower C d) ≃ RelativeEffectiveCartierDivisor C T d where
  toFun f := pullbackUniversalDivisor C T d f
  invFun D := divisorToSymmetricPoint C T d D
  left_inv := by
    intro f
    sorry
  right_inv := by
    intro D
    sorry

def divisorRestriction {S : Scheme.{u}} {C T U : RelativeScheme S} (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] (u : U ⟶ T)
    (D : RelativeEffectiveCartierDivisor C T d) :
    RelativeEffectiveCartierDivisor C U d := by
  sorry

theorem universalDivisorEquiv_natural {S : Scheme.{u}} (C T U : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] (u : U ⟶ T)
    (f : T ⟶ symmetricPower C d) :
    divisorRestriction d u (universalDivisorEquiv C T d f) =
      universalDivisorEquiv C U d (u ≫ f) := by
  sorry

theorem universal_divisor_pointwise_bijection {S : Scheme.{u}} (C T : RelativeScheme S)
    (d : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    Function.Bijective (fun f : T ⟶ symmetricPower C d =>
      (universalDivisorEquiv C T d) f) := by
  exact (universalDivisorEquiv C T d).bijective

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
