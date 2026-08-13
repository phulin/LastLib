import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Dependencies
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

/-- The orbit presheaf as an actual presheaf on the relative fppf site. -/
def orbitPresheafFunctor {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ) :
    (RelativeScheme S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := ULift.{u + 1} (orbitPresheaf X d T.unop)
  map f := TypeCat.ofHom (fun x =>
    ULift.up (orbitPresheafRestriction X d f.unop x.down))
  map_id := by
    sorry
  map_comp := by
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

/-- The quotient map induces a natural transformation from orbit points to quotient points. -/
noncomputable def quotientPointOfOrbitNatTrans {S : Scheme.{u}} {X : RelativeScheme S} (d : ℕ)
    (P : RelativePower X d) (Q : RelativeCategoricalQuotient P.carrier
      (Equiv.Perm (Fin d)) P.permutationAction) :
    orbitPresheafFunctor X d ⟶ uliftYoneda.{u + 1}.obj Q.carrier where
  app T := TypeCat.ofHom (fun x =>
    ULift.up (quotientPointOfOrbit d P Q T.unop x.down))
  naturality := by
    sorry

/-- The actual sheafification object of the orbit presheaf on the relative fppf site. -/
noncomputable def Chapter11FppfOrbitPresheafSheafification
    {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ) :
    Sheaf (relativeSchemeFppfTopology S)
      (Type (u + 1)) :=
  (presheafToSheaf (relativeSchemeFppfTopology S) (Type (u + 1))).obj
    (orbitPresheafFunctor X d)

/-- The canonical map from orbit points to their fppf sheafification. -/
noncomputable def Chapter11FppfOrbitSheafificationMap
    {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ) :
    orbitPresheafFunctor X d ⟶
      (Chapter11FppfOrbitPresheafSheafification X d).obj :=
  toSheafify
    (relativeSchemeFppfTopology S)
    (orbitPresheafFunctor X d)

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
  (∀ T : RelativeScheme S,
    Function.Bijective (quotientPointOfOrbit d (relativePower X d)
      Q T)) ∧
    (∀ {T U : RelativeScheme S} (u : U ⟶ T)
      (x : orbitPresheaf X d T),
      quotientPointOfOrbit d (relativePower X d) Q U
          (orbitPresheafRestriction X d u x) =
        u ≫ quotientPointOfOrbit d (relativePower X d) Q T x)

/-!
The categorical quotient does not by itself assert the preceding bijectivity.
The next two predicates record the local statements that replace it for the
fppf sheafification of the orbit presheaf.
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

/- The local uniqueness condition is the pointwise form of the epimorphism
   from the disjoint union of action maps to the kernel pair. -/
abbrev Chapter11FppfOrbitKernelPairEpimorphic {S : Scheme.{u}} {X : RelativeScheme S}
    (d : ℕ) (Q : RelativeCategoricalQuotient (relativePower X d).carrier
      (Equiv.Perm (Fin d)) (relativePower X d).permutationAction) : Prop :=
  Chapter11FppfLocallyUniqueOrbitLifts d Q

/- The quotient presheaf is required to be a genuine sheaf on the induced
   fppf site before the orbit map can be lifted through sheafification. -/
structure Chapter11FppfOrbitSheafificationData {S : Scheme.{u}}
    {X : RelativeScheme S} (d : ℕ)
    (Q : RelativeCategoricalQuotient (relativePower X d).carrier
      (Equiv.Perm (Fin d)) (relativePower X d).permutationAction) where
  quotientPresheafIsSheaf :
    Presheaf.IsSheaf
      (relativeSchemeFppfTopology S)
      (uliftYoneda.{u + 1}.obj Q.carrier)
  orbitSheafificationIso :
    (Chapter11FppfOrbitPresheafSheafification X d).obj ≅
      uliftYoneda.{u + 1}.obj Q.carrier
  comparison_spec :
    Chapter11FppfOrbitSheafificationMap X d ≫ orbitSheafificationIso.hom =
      quotientPointOfOrbitNatTrans d (relativePower X d) Q

noncomputable def Chapter11FppfOrbitSheafificationData.sheafificationLift
    {S : Scheme.{u}} {X : RelativeScheme S} (d : ℕ)
    (Q : RelativeCategoricalQuotient (relativePower X d).carrier
      (Equiv.Perm (Fin d)) (relativePower X d).permutationAction)
    (H : Chapter11FppfOrbitSheafificationData d Q) :
    (Chapter11FppfOrbitPresheafSheafification X d).obj ⟶
      uliftYoneda.{u + 1}.obj Q.carrier :=
  H.orbitSheafificationIso.hom

theorem Chapter11FppfOrbitSheafificationData.sheafificationLift_spec
    {S : Scheme.{u}} {X : RelativeScheme S} (d : ℕ)
    (Q : RelativeCategoricalQuotient (relativePower X d).carrier
      (Equiv.Perm (Fin d)) (relativePower X d).permutationAction)
    (H : Chapter11FppfOrbitSheafificationData d Q) :
    Chapter11FppfOrbitSheafificationMap X d ≫
        Chapter11FppfOrbitSheafificationData.sheafificationLift d Q H =
      quotientPointOfOrbitNatTrans d (relativePower X d) Q := by
  sorry

/- This is the local lifting/uniqueness criterion together with the actual
   sheafification interface on the induced relative fppf site. -/
def Chapter11FppfOrbitSheafCriteria {S : Scheme.{u}} {X : RelativeScheme S}
    (d : ℕ) (Q : RelativeCategoricalQuotient (relativePower X d).carrier
      (Equiv.Perm (Fin d)) (relativePower X d).permutationAction) : Prop :=
  Chapter11FppfLocallyLiftsOrbitPoints d Q ∧
    Chapter11FppfOrbitKernelPairEpimorphic d Q

theorem fppf_quotient_satisfies_orbit_sheaf_criteria {S : Scheme.{u}} {X : RelativeScheme S}
    (d : ℕ) (Q : RelativeCategoricalQuotient (relativePower X d).carrier
      (Equiv.Perm (Fin d)) (relativePower X d).permutationAction)
    (hq : Chapter11Fppf Q.quotientMap.hom)
    (hunique : Chapter11FppfLocallyUniqueOrbitLifts d Q) :
    Chapter11FppfOrbitSheafCriteria d Q := by
  sorry

theorem fppf_orbit_sheafification_of_criteria {S : Scheme.{u}} {X : RelativeScheme S}
    (d : ℕ) (Q : RelativeCategoricalQuotient (relativePower X d).carrier
      (Equiv.Perm (Fin d)) (relativePower X d).permutationAction)
    (h : Chapter11FppfOrbitSheafCriteria d Q) :
    Nonempty (Chapter11FppfOrbitSheafificationData d Q) := by
  sorry

/-- Pairwise distinct ordered points, used to define the free locus. -/
abbrev PairwiseDistinctTuple {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    (x : OrderedTuple X T d) : Prop :=
  Chapter11PairwiseDistinctOrderedTuple x

theorem pairwiseDistinctTuple_invariant {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    (x : OrderedTuple X T d) (σ : Equiv.Perm (Fin d)) :
    PairwiseDistinctTuple (permutedTuple σ x) ↔ PairwiseDistinctTuple x := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
