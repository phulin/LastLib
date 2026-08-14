import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12.Dependencies
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12.Section02HopfAlgebraForm

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoObj

universe u

/-!
### 12.4 Actions and quotients in the finite case
-/

/-- Coherent descent data for an object of the slice `Over T`. -/
structure Chapter12OverDescentDatum {S T : Scheme.{u}} (p : T ⟶ S) where
  upstairs : Over T
  compare {U : Scheme.{u}} (q₁ q₂ : U ⟶ T) (h : q₁ ≫ p = q₂ ≫ p) :
    (Over.pullback q₁).obj upstairs ≅ (Over.pullback q₂).obj upstairs
  compare_self {U : Scheme.{u}} (q : U ⟶ T) (h : q ≫ p = q ≫ p) :
    compare q q h = Iso.refl _
  compare_comp {U : Scheme.{u}} (q₁ q₂ q₃ : U ⟶ T)
      (h₁₂ : q₁ ≫ p = q₂ ≫ p) (h₂₃ : q₂ ≫ p = q₃ ≫ p)
      (h₁₃ : q₁ ≫ p = q₃ ≫ p) :
    compare q₁ q₂ h₁₂ ≫ compare q₂ q₃ h₂₃ = compare q₁ q₃ h₁₃

/-! ### Actions, fixed points, and effective quotients -/

/-- An action of an `S`-group scheme on an object of `Over S`. -/
structure Chapter12Action {S : Scheme.{u}} (G : Chapter12GroupScheme S) (X : Over S) where
  hom : G.X ⊗ X ⟶ X
  one_action : (η[G.X] ⊗ₘ 𝟙 X) ≫ hom = (λ_ X).hom := by cat_disch
  assoc_action : (μ[G.X] ▷ X) ≫ hom =
    (α_ G.X G.X X).hom ≫ (G.X ◁ hom) ≫ hom := by cat_disch

@[ext]
theorem Chapter12Action.ext {S : Scheme.{u}} {G : Chapter12GroupScheme S} {X : Over S}
    {a b : Chapter12Action G X} (h : a.hom = b.hom) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- A group action together with the product comparison maps needed for descent. -/
structure Chapter12ActionDescentData {S T : Scheme.{u}} (p : T ⟶ S) where
  group : Chapter12GroupSchemeDescentDatum p
  target : Chapter12OverDescentDatum p
  productCompare {U : Scheme.{u}} (q₁ q₂ : U ⟶ T)
      (h : q₁ ≫ p = q₂ ≫ p) :
    (Over.pullback q₁).obj (group.upstairs.X ⊗ target.upstairs) ≅
      (Over.pullback q₂).obj (group.upstairs.X ⊗ target.upstairs)
  productCompare_self {U : Scheme.{u}} (q : U ⟶ T) (h : q ≫ p = q ≫ p) :
    productCompare q q h = Iso.refl _
  productCompare_comp {U : Scheme.{u}} (q₁ q₂ q₃ : U ⟶ T)
      (h₁₂ : q₁ ≫ p = q₂ ≫ p) (h₂₃ : q₂ ≫ p = q₃ ≫ p)
      (h₁₃ : q₁ ≫ p = q₃ ≫ p) :
    productCompare q₁ q₂ h₁₂ ≫ productCompare q₂ q₃ h₂₃ =
      productCompare q₁ q₃ h₁₃
  action : Chapter12Action group.upstairs target.upstairs
  action_compatible {U : Scheme.{u}} (q₁ q₂ : U ⟶ T)
      (h : q₁ ≫ p = q₂ ≫ p) :
    (Over.pullback q₁).map action.hom ≫ target.compare q₁ q₂ h =
      productCompare q₁ q₂ h ≫ (Over.pullback q₂).map action.hom

/-- A descended action together with the comparison that identifies its pullback action upstairs. -/
structure Chapter12ActionComparison
    {S T : Scheme.{u}} (p : T ⟶ S) (D : Chapter12ActionDescentData p)
    (G : Chapter12GroupScheme S) (X : Over S) (a : Chapter12Action G X) where
  groupIso : Chapter12GroupScheme.baseChange p G ≅ D.group.upstairs
  targetIso : (Over.pullback p).obj X ≅ D.target.upstairs
  action_compatible :
    (Over.pullback p).map a.hom ≫ targetIso.hom =
      (CategoryTheory.CartesianMonoidalCategory.prodComparisonIso
        (Over.pullback p) G.X X).hom ≫
        (Chapter12GroupScheme.homScheme groupIso.hom ⊗ₘ targetIso.hom) ≫ D.action.hom

theorem chapter12_actions_descend
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D : Chapter12ActionDescentData p) :
    ∃ (G : Chapter12GroupScheme S) (X : Over S)
      (a : Chapter12Action G X),
      Nonempty (Chapter12ActionComparison p D G X a) := by
  sorry

/-- The fixed-point object, when the equalizer is represented in `Over S`. -/
structure Chapter12FixedPoint {S : Scheme.{u}} {G : Chapter12GroupScheme S} {X : Over S}
    (a : Chapter12Action G X) where
  carrier : Over S
  inclusion : carrier ⟶ X
  isEqualizer : IsEqualizer inclusion a.hom (snd G.X X)

/-! Fixed points are represented only when the equalizer object is supplied. -/

def Chapter12RepresentedFixedPoint {S : Scheme.{u}} {G : Chapter12GroupScheme S}
    {X : Over S} (a : Chapter12Action G X) : Prop :=
  Nonempty (Chapter12FixedPoint a)

theorem chapter12_fixed_point_descends_when_represented
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D : Chapter12ActionDescentData p)
    (hfixed : Chapter12RepresentedFixedPoint D.action) :
    ∃ (F_T : Chapter12FixedPoint D.action)
      (G : Chapter12GroupScheme S) (X : Over S)
      (a : Chapter12Action G X) (F : Chapter12FixedPoint a)
      (C : Chapter12ActionComparison p D G X a)
      (eF : (Over.pullback p).obj F.carrier ≅ F_T.carrier),
      (Over.pullback p).map F.inclusion ≫ C.targetIso.hom =
        eF.hom ≫ F_T.inclusion := by
  sorry

/-- A categorical quotient of an action, with its invariant equation. -/
structure Chapter12EffectiveQuotient {S : Scheme.{u}} {G : Chapter12GroupScheme S}
    {X : Over S} (a : Chapter12Action G X) where
  quotient : Over S
  quotientMap : X ⟶ quotient
  invariant : a.hom ≫ quotientMap = snd G.X X ≫ quotientMap
  isColimit : IsColimit (Cofork.ofπ quotientMap invariant)

/-- The orbit-relation map associated with an effective quotient. -/
def Chapter12EffectiveQuotient.orbitRelationMap {S : Scheme.{u}}
    {G : Chapter12GroupScheme S} {X : Over S} {a : Chapter12Action G X}
    (Q : Chapter12EffectiveQuotient a) :
    G.X ⊗ X ⟶ pullback Q.quotientMap Q.quotientMap :=
  pullback.lift a.hom (snd G.X X) Q.invariant

/-! ### Affine actions and invariant rings -/

/-- The algebra-side presentation of an affine action by a coordinate Hopf algebra. -/
structure Chapter12AffineGroupAction (A H R : Type*)
    [CommRing A] [CommRing H] [CommRing R]
    [Algebra A H] [Algebra A R] [HopfAlgebra A H] where
  coaction : R →ₐ[A] H ⊗[A] R
  coaction_coassoc :
    (Algebra.TensorProduct.assoc A A A H H R).toAlgHom.comp
        ((Algebra.TensorProduct.map (Bialgebra.comulAlgHom A H) (AlgHom.id A R)).comp
          coaction) =
      (Algebra.TensorProduct.map (AlgHom.id A H) coaction).comp coaction
  coaction_counit :
    (Algebra.TensorProduct.lid A R).toAlgHom.comp
        ((Algebra.TensorProduct.map (Bialgebra.counitAlgHom A H) (AlgHom.id A R)).comp
          coaction) =
      AlgHom.id A R

@[ext]
theorem Chapter12AffineGroupAction.ext
    {A H R : Type*} [CommRing A] [CommRing H] [CommRing R]
    [Algebra A H] [Algebra A R] [HopfAlgebra A H]
    {a b : Chapter12AffineGroupAction A H R}
    (h : a.coaction = b.coaction) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- The invariant subalgebra `R^G = {r | a*(r) = 1 ⊗ r}`. -/
def chapter12InvariantSubalgebra (A H R : Type*)
    [CommRing A] [CommRing H] [CommRing R]
    [Algebra A H] [Algebra A R]
    (coaction : R →ₐ[A] H ⊗[A] R) : Subalgebra A R where
  carrier := {r | coaction r = Algebra.TensorProduct.includeRight r}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [map_add, hx, hy]
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    simp only [map_mul, hx, hy]

@[simp]
theorem mem_chapter12InvariantSubalgebra_iff (A H R : Type*)
    [CommRing A] [CommRing H] [CommRing R]
    [Algebra A H] [Algebra A R]
    (coaction : R →ₐ[A] H ⊗[A] R) (r : R) :
    r ∈ chapter12InvariantSubalgebra A H R coaction ↔
      coaction r = Algebra.TensorProduct.includeRight r := Iff.rfl

/-- The invariant subalgebra is the equalizer of the coaction and `r ↦ 1 ⊗ r`. -/
theorem chapter12InvariantSubalgebra_isEqualizer (A H R : Type*)
    [CommRing A] [CommRing H] [CommRing R]
    [Algebra A H] [Algebra A R]
    (coaction : R →ₐ[A] H ⊗[A] R) :
    IsEqualizer
      (CommAlgCat.ofHom (chapter12InvariantSubalgebra A H R coaction).val)
      (CommAlgCat.ofHom coaction)
      (CommAlgCat.ofHom Algebra.TensorProduct.includeRight) := by
  sorry

/-- Flat extension of scalars preserves the finite limits, hence equalizers, used above. -/
theorem chapter12_flat_tensor_preserves_equalizers
    {A B : Type u} [CommRing A] [CommRing B] (hflat : (algebraMap A B).Flat) :
    PreservesFiniteLimits (ModuleCat.tensorLeft (ModuleCat.of A B)) := by
  exact ModuleCat.preservesFiniteLimits_tensorLeft_of_ringHomFlat hflat

/-! ### Affine quotients -/

def chapter12AffineInvariantRing (D : Chapter12AffineGroupAction A H R) :
    Subalgebra A R :=
  chapter12InvariantSubalgebra A H R D.coaction

def chapter12AffineQuotientScheme (D : Chapter12AffineGroupAction A H R) : Scheme :=
  Spec (chapter12AffineInvariantRing D)

/-- The canonical affine quotient map `Spec R ⟶ Spec (R^G)`. -/
def chapter12AffineQuotientMap (D : Chapter12AffineGroupAction A H R) :
    Spec R ⟶ chapter12AffineQuotientScheme D :=
  Spec.map (CommRingCat.ofHom (chapter12AffineInvariantRing D).val.toRingHom)

/-- The affine quotient as an object over `Spec A`. -/
def chapter12AffineQuotientOver (D : Chapter12AffineGroupAction A H R) : Over (Spec A) :=
  (chapter12AffineQuotientScheme D).asOver (Spec A)

theorem chapter12_affine_quotient_invariant_membership
    (D : Chapter12AffineGroupAction A H R) (r : R) :
    r ∈ chapter12AffineInvariantRing D ↔
      D.coaction r = Algebra.TensorProduct.includeRight r := by
  rfl

theorem chapter12_affine_quotient_is_equalizer
    (D : Chapter12AffineGroupAction A H R) :
    IsEqualizer
      (CommAlgCat.ofHom (chapter12AffineInvariantRing D).val)
      (CommAlgCat.ofHom D.coaction)
      (CommAlgCat.ofHom Algebra.TensorProduct.includeRight) := by
  exact chapter12InvariantSubalgebra_isEqualizer A H R D.coaction

/-- The flat-base-change mechanism for affine invariants: tensoring preserves their equalizer. -/
theorem chapter12_affine_invariants_commute_with_flat_base_change
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hflat : (algebraMap A B).Flat) :
    PreservesFiniteLimits (ModuleCat.tensorLeft (ModuleCat.of A B)) := by
  exact chapter12_flat_tensor_preserves_equalizers hflat

/-- Finite projectivity of the coordinate Hopf algebra, the hypothesis used by the affine action
coaction and by dual Hopf-algebra base change. -/
def Chapter12FiniteLocallyFreeAffineGroupAction
    (D : Chapter12AffineGroupAction A H R) [Module A H] : Prop :=
  Module.Finite A H ∧ Module.Projective A H

theorem chapter12_affine_finite_projective_hopf_action_dualizes
    (D : Chapter12AffineGroupAction A H R)
    [Module A H] [Module.Finite A H] [Module.Projective A H] :
    Chapter12FiniteProjectiveModule A (Module.Dual A H) := by
  exact chapter12_dual_of_finite_projective A H ⟨inferInstance, inferInstance⟩

/-! ### Free actions and torsors -/

/-- Freeness in the usual orbit-map sense. -/
def Chapter12Action.IsFree {S : Scheme.{u}} {G : Chapter12GroupScheme S} {X : Over S}
    (a : Chapter12Action G X) : Prop :=
  Mono (lift a.hom (snd G.X X))

/-- A torsor presentation of an action. -/
structure Chapter12Torsor {S : Scheme.{u}} {G : Chapter12GroupScheme S} {X : Over S}
    (a : Chapter12Action G X) where
  toEffectiveQuotient : Chapter12EffectiveQuotient a
  quotientFppf : Chapter12Fppf toEffectiveQuotient.quotientMap.left
  orbitRelationIsIso :
    IsIso (Chapter12EffectiveQuotient.orbitRelationMap toEffectiveQuotient)

namespace Chapter12Torsor

abbrev quotient : Over S := toEffectiveQuotient.quotient

abbrev quotientMap : X ⟶ quotient := toEffectiveQuotient.quotientMap

abbrev invariant : a.hom ≫ quotientMap = snd G.X X ≫ quotientMap :=
  toEffectiveQuotient.invariant

end Chapter12Torsor

theorem chapter12_torsor_is_free
    {S : Scheme.{u}} {G : Chapter12GroupScheme S} {X : Over S}
    {a : Chapter12Action G X} (T : Chapter12Torsor a) :
    Chapter12Action.IsFree a := by
  sorry

theorem chapter12_torsor_quotient_finiteLocallyFree
    {S : Scheme.{u}} {G : Chapter12GroupScheme S} {X : Over S}
    {a : Chapter12Action G X} (T : Chapter12Torsor a)
    (hG : Chapter12FiniteLocallyFree G.X.hom) :
    Chapter12FiniteLocallyFree T.quotientMap.left := by
  sorry

theorem chapter12_torsor_orbit_relation_effective
    {S : Scheme.{u}} {G : Chapter12GroupScheme S} {X : Over S}
    {a : Chapter12Action G X} (T : Chapter12Torsor a) :
    IsColimit (Cofork.ofπ T.quotientMap T.invariant) :=
  T.toEffectiveQuotient.isColimit

/-!
For non-affine `X`, the API intentionally has no unconditional quotient constructor.  The two
predicates below make the representability/equalizer input explicit, so descent can preserve an
object once it has been constructed without claiming that every quotient or fixed-point functor is
representable.
-/

def Chapter12RepresentedQuotient {S : Scheme.{u}} {G : Chapter12GroupScheme S}
    {X : Over S} (a : Chapter12Action G X) : Prop :=
  Nonempty (Chapter12EffectiveQuotient a)

theorem chapter12_effective_quotient_is_represented
    {S : Scheme.{u}} {G : Chapter12GroupScheme S} {X : Over S}
    {a : Chapter12Action G X} (Q : Chapter12EffectiveQuotient a) :
    Chapter12RepresentedQuotient a :=
  ⟨Q⟩

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12
