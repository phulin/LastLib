import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Section01QuotientsByPermutation

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeScheme

universe u v

/-!
### 11.2 Sheaf quotients and orbit functors

The categorical quotient and the orbit presheaf are kept as separate
interfaces.  The local lifting and local uniqueness predicates below are the
precise fppf-sheafification data used whenever the quotient map is fppf.
-/

abbrev OrderedTuple {S : Scheme.{u}} (X T : RelativeScheme S) (d : ℕ) :=
  Fin d → (T ⟶ X)

def permutedTuple {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    (σ : Equiv.Perm (Fin d)) (x : OrderedTuple X T d) : OrderedTuple X T d :=
  fun i => x (σ i)

def tupleOrbitRelation {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    (x y : OrderedTuple X T d) : Prop :=
  ∃ σ : Equiv.Perm (Fin d), ∀ i, x (σ i) = y i

def tupleOrbitSetoid {S : Scheme.{u}} (X T : RelativeScheme S) (d : ℕ) :
    Setoid (OrderedTuple X T d) where
  r := tupleOrbitRelation
  iseqv := by
    sorry

/-- The orbit presheaf evaluated on a relative test scheme. -/
def orbitPresheaf {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    (T : RelativeScheme S) : Type _ :=
  Quotient (tupleOrbitSetoid X T d)

/-- Restriction of orbit classes along a morphism of test schemes. -/
noncomputable def orbitPresheafRestriction {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    {T U : RelativeScheme S} (u : U ⟶ T) :
    orbitPresheaf X d T → orbitPresheaf X d U := by
  refine Quotient.map (fun x i => u ≫ x i) ?_
  intro x y hxy
  sorry

theorem orbitPresheafRestriction_id {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    (T : RelativeScheme S) :
    orbitPresheafRestriction X d (𝟙 T) = id := by
  sorry

theorem orbitPresheafRestriction_comp {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    {T U V : RelativeScheme S} (u : U ⟶ T) (v : V ⟶ U) :
    orbitPresheafRestriction X d (v ≫ u) =
      orbitPresheafRestriction X d v ∘ orbitPresheafRestriction X d u := by
  sorry

/-- Ordered points of a power are naturally the tuples of ordered points. -/
noncomputable def tuplePointEquiv {S : Scheme.{u}} {X T : RelativeScheme S} (d : ℕ)
    (P : RelativePower X d) :
    (T ⟶ P.carrier) ≃ OrderedTuple X T d where
  toFun f := fun i => f ≫ P.projection i
  invFun x := P.lift x
  left_inv := by
    intro f
    apply Hom.ext
    sorry
  right_inv := by
    intro x
    funext i
    exact P.lift_projection x i

/-- The map from an orbit class to a point of a categorical quotient. -/
noncomputable def quotientPointOfOrbit {S : Scheme.{u}} {X : RelativeScheme S} (d : ℕ)
    (P : RelativePower X d) (Q : RelativeCategoricalQuotient P.carrier
      (Equiv.Perm (Fin d)) P.permutationAction) (T : RelativeScheme S) :
    orbitPresheaf X d T → (T ⟶ Q.carrier) := by
  refine Quotient.lift (fun x => P.lift x ≫ Q.quotientMap) ?_
  intro x y hxy
  sorry

theorem quotientPointOfOrbit_restriction {S : Scheme.{u}} {X : RelativeScheme S} (d : ℕ)
    (P : RelativePower X d) (Q : RelativeCategoricalQuotient P.carrier
      (Equiv.Perm (Fin d)) P.permutationAction)
    {T U : RelativeScheme S} (u : U ⟶ T) (x : orbitPresheaf X d T) :
    quotientPointOfOrbit d P Q U (orbitPresheafRestriction X d u x) =
      u ≫ quotientPointOfOrbit d P Q T x := by
  sorry

abbrev symmetricPowerOrbitPoint {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] (T : RelativeScheme S) : Type _ :=
  orbitPresheaf X d T

noncomputable def symmetricPowerOrbitPointMap {S : Scheme.{u}} (X : RelativeScheme S)
    (d : ℕ) [Chapter11QuasiProjectiveOver X] (T : RelativeScheme S) :
    symmetricPowerOrbitPoint X d T → (T ⟶ symmetricPower X d) :=
  quotientPointOfOrbit d (relativePower X d)
    (symmetricPowerQuotient X d).quotient T

def Chapter11RepresentsOrbitPresheaf {S : Scheme.{u}} {X : RelativeScheme S} (d : ℕ)
    (Q : RelativeCategoricalQuotient (relativePower X d).carrier
      (Equiv.Perm (Fin d)) (relativePower X d).permutationAction) : Prop :=
  ∀ T : RelativeScheme S,
    Function.Bijective (quotientPointOfOrbit d (relativePower X d)
      Q T)

/-!
The categorical quotient does not by itself assert the preceding bijectivity.
The next two predicates record the local statements that replace it for the
fppf sheafification of the orbit presheaf.
-/

/- SOURCE_ISSUE: §11.2 infers local uniqueness of lifts from the fppf property
   of the quotient map alone.  Fppf descent gives local lifts, but for a
   nonfree action it does not by itself say that two lifts differ by a group
   element.  The orbit-sheaf assertion should therefore be restricted to the
   free locus, while the smooth-curve statement should use the divisor functor.
-/

def Chapter11FppfLocallyLiftsOrbitPoints {S : Scheme.{u}} {X : RelativeScheme S}
    (d : ℕ) (Q : RelativeCategoricalQuotient (relativePower X d).carrier
      (Equiv.Perm (Fin d)) (relativePower X d).permutationAction) : Prop :=
  ∀ (T : RelativeScheme S) (z : T ⟶ Q.carrier),
    ∃ (U : RelativeScheme S) (u : U ⟶ T),
      Chapter11Fppf u.hom ∧
        ∃ x : OrderedTuple X U d,
          RelativePower.lift (relativePower X d) x ≫ Q.quotientMap = u ≫ z

def Chapter11FppfLocallyUniqueOrbitLifts {S : Scheme.{u}} {X : RelativeScheme S}
    (d : ℕ) (Q : RelativeCategoricalQuotient (relativePower X d).carrier
      (Equiv.Perm (Fin d)) (relativePower X d).permutationAction) : Prop :=
  ∀ (T : RelativeScheme S) (u : T ⟶ Q.carrier)
    (U : RelativeScheme S) (v : U ⟶ T)
    (x y : OrderedTuple X U d),
      Chapter11Fppf v.hom →
        RelativePower.lift (relativePower X d) x ≫ Q.quotientMap = v ≫ u →
        RelativePower.lift (relativePower X d) y ≫ Q.quotientMap = v ≫ u →
      ∃ (V : RelativeScheme S) (w : V ⟶ U),
        Chapter11Fppf w.hom ∧
          ∃ σ : Equiv.Perm (Fin d), ∀ i, w ≫ x i = w ≫ y (σ i)

def Chapter11RepresentsFppfOrbitSheaf {S : Scheme.{u}} {X : RelativeScheme S}
    (d : ℕ) (Q : RelativeCategoricalQuotient (relativePower X d).carrier
      (Equiv.Perm (Fin d)) (relativePower X d).permutationAction) : Prop :=
  Chapter11FppfLocallyLiftsOrbitPoints d Q ∧
    Chapter11FppfLocallyUniqueOrbitLifts d Q

theorem fppf_quotient_represents_orbit_sheaf {S : Scheme.{u}} {X : RelativeScheme S}
    (d : ℕ) (Q : RelativeCategoricalQuotient (relativePower X d).carrier
      (Equiv.Perm (Fin d)) (relativePower X d).permutationAction)
    (hq : Chapter11Fppf Q.quotientMap.hom) :
    Chapter11RepresentsFppfOrbitSheaf d Q := by
  sorry

/-- Pairwise distinct ordered points, used to define the free locus. -/
def PairwiseDistinctTuple {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    (x : OrderedTuple X T d) : Prop :=
  Pairwise (fun i j => x i ≠ x j)

theorem pairwiseDistinctTuple_invariant {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    (x : OrderedTuple X T d) (σ : Equiv.Perm (Fin d)) :
    PairwiseDistinctTuple (permutedTuple σ x) ↔ PairwiseDistinctTuple x := by
  sorry

/- The source's separable-point example is made explicit through a residue
   extension, an ordered geometric tuple, and its descended symmetric point. -/
structure SeparableDegreeDClosedPointData {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ) where
  point : AlgebraicGeometry.Spec (CommRingCat.of L) ⟶ C.carrier
  basePoint : AlgebraicGeometry.Spec (CommRingCat.of L) ⟶ S
  over_base : point ≫ C.structuralMap = basePoint
  degree : Module.finrank K L = d
  separable : Algebra.IsSeparable K L
  geometricTuple : Fin d →
    (AlgebraicGeometry.Spec (CommRingCat.of L) ⟶ C.carrier)
  geometricTuple_over_base : ∀ i, geometricTuple i ≫ C.structuralMap = basePoint

noncomputable def separableOrbitPoint {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    {C : RelativeScheme (AlgebraicGeometry.Spec (CommRingCat.of K))} {d : ℕ}
    [Chapter11QuasiProjectiveOver C]
    (p : SeparableDegreeDClosedPointData (K := K) (L := L) C d) :
    ({ carrier := AlgebraicGeometry.Spec (CommRingCat.of L), structuralMap := p.basePoint } :
        RelativeScheme (AlgebraicGeometry.Spec (CommRingCat.of K))) ⟶
      symmetricPower C d := by
  let Lpoint : RelativeScheme (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    { carrier := AlgebraicGeometry.Spec (CommRingCat.of L), structuralMap := p.basePoint }
  let x : OrderedTuple C Lpoint d := fun i =>
    { hom := p.geometricTuple i, comm := p.geometricTuple_over_base i }
  exact quotientPointOfOrbit d (relativePower C d)
    (symmetricPowerQuotient C d).quotient Lpoint
      (Quotient.mk (tupleOrbitSetoid C Lpoint d) x)

def relativeStructuralMapHom {S : Scheme.{u}} (T : RelativeScheme S) : T ⟶ base S where
  hom := T.structuralMap
  comm := by
    change T.structuralMap ≫ 𝟙 S = T.structuralMap
    simp

theorem separable_closed_point_gives_symmetric_point {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    {C : RelativeScheme (AlgebraicGeometry.Spec (CommRingCat.of K))} {d : ℕ}
    [Chapter11QuasiProjectiveOver C]
    [SmoothOfRelativeDimension 1 C.structuralMap]
    (p : SeparableDegreeDClosedPointData (K := K) (L := L) C d) :
    ∃ y : RelativeScheme.base (AlgebraicGeometry.Spec (CommRingCat.of K)) ⟶ symmetricPower C d,
      relativeStructuralMapHom
          ({ carrier := AlgebraicGeometry.Spec (CommRingCat.of L), structuralMap := p.basePoint } :
            RelativeScheme (AlgebraicGeometry.Spec (CommRingCat.of K))) ≫ y =
        separableOrbitPoint p := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
