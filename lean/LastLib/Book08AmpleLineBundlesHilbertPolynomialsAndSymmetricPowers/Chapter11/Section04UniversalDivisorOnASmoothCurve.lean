import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Section01QuotientsByPermutation

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

/- The permutation action on the power lifts to the product with the curve. -/
noncomputable def curvePowerPermutationMap {S : Scheme.{u}} (C : RelativeScheme S)
    (d : ℕ) (σ : Equiv.Perm (Fin d)) :
    curvePowerAmbient C d ⟶ curvePowerAmbient C d :=
  pullback.lift
    (pullback.fst C.structuralMap (relativePower C d).carrier.structuralMap)
    ((pullback.snd C.structuralMap (relativePower C d).carrier.structuralMap) ≫
      ((relativePower C d).permutation σ).hom) (by sorry)

structure GraphCartierDivisor {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    (i : Fin d) where
  divisor : EffectiveCartierDivisor (curvePowerAmbient C d)
  graphIso : divisor.subscheme ≅ (relativePower C d).carrier.carrier
  graphIso_inv : graphIso.inv ≫ divisor.inclusion = curveGraphMap C d i

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
    (D : EffectiveCartierDivisor X) (G : Type v) [Group G]
    (action : G → (X ⟶ X)) : Prop :=
  ∀ g : G, IsIso (action g) ∧
    ∃ e : D.subscheme ⟶ D.subscheme,
      IsIso e ∧ e ≫ D.inclusion = D.inclusion ≫ action g

theorem orderedUniversalDivisor_invariant {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter11DivisorPermutationInvariant (orderedUniversalDivisor C d)
      (Equiv.Perm (Fin d)) (curvePowerPermutationMap C d) := by
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

/- A divisor pullback is recorded scheme-theoretically: the divisor subscheme
   is the pullback of the original Cartier subscheme.  This retains
   multiplicities and nilpotent structure, unlike equality of supports. -/
def Chapter11DivisorPullbackRelation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : EffectiveCartierDivisor Y) (E : EffectiveCartierDivisor X) : Prop :=
  ∃ e : E.subscheme ≅ pullback D.inclusion f,
    e.hom ≫ pullback.snd D.inclusion f = E.inclusion

/- The coefficients above are the affine descent calculation.  This existence
   statement records the descended Cartier divisor and its finite-flat degree.
   The representing equivalence is kept as a separate package below, so that
   existence of a divisor is not confused with its universal property. -/
theorem universalDivisor_exists {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    Nonempty
      {D : EffectiveCartierDivisor (curveSymmetricAmbient C d) //
        Chapter11DivisorPullbackRelation (orderedToSymmetricAmbient C d) D
            (orderedUniversalDivisor C d) ∧
          Chapter11FiniteLocallyFreeOfRank
            (D.inclusion ≫
              pullback.snd C.structuralMap (symmetricPower C d).structuralMap) d} := by
  sorry

noncomputable def universalDivisorData {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    {D : EffectiveCartierDivisor (curveSymmetricAmbient C d) //
      Chapter11DivisorPullbackRelation (orderedToSymmetricAmbient C d) D
          (orderedUniversalDivisor C d) ∧
        Chapter11FiniteLocallyFreeOfRank
          (D.inclusion ≫
            pullback.snd C.structuralMap (symmetricPower C d).structuralMap) d} :=
  Classical.choice (universalDivisor_exists C d)

noncomputable def universalDivisor {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
  EffectiveCartierDivisor (curveSymmetricAmbient C d) :=
  (universalDivisorData C d).1

theorem universalDivisor_descends_ordered_divisor {S : Scheme.{u}} (C : RelativeScheme S)
    (d : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter11DivisorPullbackRelation (orderedToSymmetricAmbient C d)
      (universalDivisor C d) (orderedUniversalDivisor C d) := by
  exact (universalDivisorData C d).2.1

theorem universalDivisor_finiteLocallyFree {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter11FiniteLocallyFreeOfRank
      ((universalDivisor C d).inclusion ≫
        pullback.snd C.structuralMap (symmetricPower C d).structuralMap) d := by
  exact (universalDivisorData C d).2.2

structure Chapter11MonicChartWitness (d : ℕ) where
  R : Type u
  A : Type u
  [commRingR : CommRing R]
  [commRingA : CommRing A]
  [algebraRA : Algebra R A]
  chart : MonicPolynomialChart R A d

theorem monic_equation_recovers_chart {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] {d : ℕ} (P Q : MonicPolynomialChart R A d)
    (hparameter : P.parameter = Q.parameter) (hpolynomial : P.polynomial = Q.polynomial) :
    P = Q := by
  exact MonicPolynomialChart.ext hparameter hpolynomial

noncomputable def curveBaseChangeToSymmetricAmbient {S : Scheme.{u}}
    (C T : RelativeScheme S) (d : ℕ) [Chapter11SmoothQuasiProjectiveCurve C]
    (f : T ⟶ symmetricPower C d) :
    pullback C.structuralMap T.structuralMap ⟶ curveSymmetricAmbient C d :=
  pullback.lift
    (pullback.fst C.structuralMap T.structuralMap)
    ((pullback.snd C.structuralMap T.structuralMap) ≫ f.hom) (by sorry)

def Chapter11UniversalDivisorPullbackRelation {S : Scheme.{u}}
    (C T : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C]
    (f : T ⟶ symmetricPower C d) (D : RelativeEffectiveCartierDivisor C T d) : Prop :=
  Chapter11DivisorPullbackRelation (curveBaseChangeToSymmetricAmbient C T d f)
    (universalDivisor C d) D.divisor

def divisorRestriction {S : Scheme.{u}} {C T U : RelativeScheme S} (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] (u : U ⟶ T)
    (D : RelativeEffectiveCartierDivisor C T d) :
    RelativeEffectiveCartierDivisor C U d := by
  sorry

/- The universal divisor must carry the full functor-of-points data: a
   divisor on every test scheme, compatibility with the displayed Cartier
   pullback, and naturality under restriction. -/
structure Chapter11UniversalDivisorRepresentingData {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] where
  equivalence : ∀ T : RelativeScheme S,
    (T ⟶ symmetricPower C d) ≃ RelativeEffectiveCartierDivisor C T d
  pullback_universal : ∀ (T : RelativeScheme S)
    (f : T ⟶ symmetricPower C d),
    Chapter11UniversalDivisorPullbackRelation C T d f (equivalence T f)
  natural : ∀ {T U : RelativeScheme S} (u : U ⟶ T)
    (f : T ⟶ symmetricPower C d),
    divisorRestriction d u (equivalence T f) =
      equivalence U (u ≫ f)

noncomputable def universalDivisorRepresentingData {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter11UniversalDivisorRepresentingData C d := by
  sorry

noncomputable def pullbackUniversalDivisor {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C]
    (f : T ⟶ symmetricPower C d) : RelativeEffectiveCartierDivisor C T d := by
  exact (universalDivisorRepresentingData C d).equivalence T f

theorem pullbackUniversalDivisor_is_universal {S : Scheme.{u}}
    (C T : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] (f : T ⟶ symmetricPower C d) :
    Chapter11UniversalDivisorPullbackRelation C T d f
      (pullbackUniversalDivisor C T d f) := by
  exact (universalDivisorRepresentingData C d).pullback_universal T f

theorem universalDivisor_repeated_roots_are_allowed {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
  ∀ (T : RelativeScheme S) (f : T ⟶ symmetricPower C d),
      Chapter11FiniteLocallyFreeOfRank
        ((pullbackUniversalDivisor C T d f).divisor.inclusion ≫
          pullback.snd C.structuralMap T.structuralMap) d := by
  intro T f
  exact (pullbackUniversalDivisor C T d f).finite_flat_rank

noncomputable def divisorToSymmetricPoint {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C]
    (D : RelativeEffectiveCartierDivisor C T d) : T ⟶ symmetricPower C d := by
  exact ((universalDivisorRepresentingData C d).equivalence T).symm D

noncomputable def universalDivisorEquiv {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    (T ⟶ symmetricPower C d) ≃ RelativeEffectiveCartierDivisor C T d where
  toFun f := (universalDivisorRepresentingData C d).equivalence T f
  invFun D := ((universalDivisorRepresentingData C d).equivalence T).symm D
  left_inv f := ((universalDivisorRepresentingData C d).equivalence T).left_inv f
  right_inv D := ((universalDivisorRepresentingData C d).equivalence T).right_inv D

theorem universalDivisorEquiv_natural {S : Scheme.{u}} (C T U : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] (u : U ⟶ T)
    (f : T ⟶ symmetricPower C d) :
    divisorRestriction d u (universalDivisorEquiv C T d f) =
      universalDivisorEquiv C U d (u ≫ f) := by
  exact (universalDivisorRepresentingData C d).natural u f

theorem universal_divisor_pointwise_bijection {S : Scheme.{u}} (C T : RelativeScheme S)
    (d : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    Function.Bijective (fun f : T ⟶ symmetricPower C d =>
      (universalDivisorEquiv C T d) f) := by
  exact (universalDivisorEquiv C T d).bijective

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
