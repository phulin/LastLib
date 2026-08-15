import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12.Dependencies
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12.Section01GroupLawsDescend
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12.Section02HopfAlgebraForm
import Mathlib.RingTheory.Flat.CategoryTheory

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open TensorProduct
open scoped MonObj

universe u

/-!
### 12.4 Actions and quotients in the finite case
-/

def chapter12OverBaseChangeCompIso
    {S T U : Scheme.{u}} (p : T ⟶ S) (q : U ⟶ T) (X : Over S) :
    (Over.pullback q).obj ((Over.pullback p).obj X) ≅
      (Over.pullback (q ≫ p)).obj X := by
  exact (Over.pullbackComp q p).app X |>.symm

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
      (compare q₁ q₂ h₁₂).hom ≫ (compare q₂ q₃ h₂₃).hom =
        (compare q₁ q₃ h₁₃).hom
  compare_pull {U V : Scheme.{u}} (r : V ⟶ U) (q₁ q₂ : U ⟶ T)
      (h : q₁ ≫ p = q₂ ≫ p)
      (h' : (r ≫ q₁) ≫ p = (r ≫ q₂) ≫ p) :
    (Over.pullback r).map (compare q₁ q₂ h).hom =
      (chapter12OverBaseChangeCompIso q₁ r upstairs).hom ≫
        (compare (r ≫ q₁) (r ≫ q₂) h').hom ≫
          (chapter12OverBaseChangeCompIso q₂ r upstairs).inv

def chapter12OverBaseChangeComparison
    {S T U : Scheme.{u}} (p : T ⟶ S) (X : Over S)
    (q₁ q₂ : U ⟶ T) (h : q₁ ≫ p = q₂ ≫ p) :
    (Over.pullback q₁).obj ((Over.pullback p).obj X) ≅
      (Over.pullback q₂).obj ((Over.pullback p).obj X) := by
  exact (Over.pullbackComp q₁ p).app X |>.symm ≪≫
    eqToIso (by rw [h]) ≪≫ (Over.pullbackComp q₂ p).app X

def chapter12OverDescentComparisonCompatible
    {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter12OverDescentDatum p) (X : Over S)
    (e : (Over.pullback p).obj X ≅ D.upstairs) : Prop :=
  ∀ {U : Scheme.{u}} (q₁ q₂ : U ⟶ T) (h : q₁ ≫ p = q₂ ≫ p),
    (Over.pullback q₁).map e.hom ≫ (D.compare q₁ q₂ h).hom =
        (chapter12OverBaseChangeComparison p X q₁ q₂ h).hom ≫
          (Over.pullback q₂).map e.hom

/-! A morphism between two over-scheme descent data is compatible when it intertwines their
comparison isomorphisms.  This is the map-level input needed when a represented quotient is to be
descended; existence of a quotient upstairs alone does not provide such a datum. -/

def chapter12OverDescentHomCompatible
    {S T : Scheme.{u}} {p : T ⟶ S}
    (D₁ D₂ : Chapter12OverDescentDatum p)
    (f : D₁.upstairs ⟶ D₂.upstairs) : Prop :=
  ∀ {U : Scheme.{u}} (q₁ q₂ : U ⟶ T) (h : q₁ ≫ p = q₂ ≫ p),
    (Over.pullback q₁).map f ≫ (D₂.compare q₁ q₂ h).hom =
      (D₁.compare q₁ q₂ h).hom ≫ (Over.pullback q₂).map f

def chapter12ActionProductBaseChangeComparison
    {S T U : Scheme.{u}} {p : T ⟶ S}
    (groupD : Chapter12GroupSchemeDescentDatum p)
    (targetD : Chapter12OverDescentDatum p)
    (q₁ q₂ : U ⟶ T) (h : q₁ ≫ p = q₂ ≫ p) :
    (Over.pullback q₁).obj (groupD.upstairs.X ⊗ targetD.upstairs) ≅
      (Over.pullback q₂).obj (groupD.upstairs.X ⊗ targetD.upstairs) := by
  exact (Over.pullbackComp q₁ p).app (groupD.upstairs.X ⊗ targetD.upstairs) |>.symm ≪≫
    eqToIso (by rw [h]) ≪≫
      (Over.pullbackComp q₂ p).app (groupD.upstairs.X ⊗ targetD.upstairs)

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
    (productCompare q₁ q₂ h₁₂).hom ≫ (productCompare q₂ q₃ h₂₃).hom =
      (productCompare q₁ q₃ h₁₃).hom
  productCompare_compatible {U : Scheme.{u}} (q₁ q₂ : U ⟶ T)
      (h : q₁ ≫ p = q₂ ≫ p) :
    productCompare q₁ q₂ h =
      chapter12ActionProductBaseChangeComparison group target q₁ q₂ h
  action : Chapter12Action group.upstairs target.upstairs
  action_compatible {U : Scheme.{u}} (q₁ q₂ : U ⟶ T)
      (h : q₁ ≫ p = q₂ ≫ p) :
    (Over.pullback q₁).map action.hom ≫ (target.compare q₁ q₂ h).hom =
      (productCompare q₁ q₂ h).hom ≫ (Over.pullback q₂).map action.hom

/-- A descended action together with the comparison that identifies its pullback action upstairs. -/
structure Chapter12ActionComparison
    {S T : Scheme.{u}} (p : T ⟶ S) (D : Chapter12ActionDescentData p)
    (G : Chapter12GroupScheme S) (X : Over S) (a : Chapter12Action G X) where
  groupIso : Chapter12GroupScheme.baseChange p G ≅ D.group.upstairs
  groupIso_compatible :
    chapter12GroupSchemeDescentComparisonCompatible D.group G groupIso
  targetIso : (Over.pullback p).obj X ≅ D.target.upstairs
  targetIso_compatible :
    chapter12OverDescentComparisonCompatible D.target X targetIso
  action_compatible :
    (Over.pullback p).map a.hom ≫ targetIso.hom =
      (CategoryTheory.CartesianMonoidalCategory.prodComparisonIso
        (Over.pullback p) G.X X).hom ≫
        (groupIso.hom.hom.hom ⊗ₘ targetIso.hom) ≫ D.action.hom

theorem chapter12_actions_descend
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D : Chapter12ActionDescentData p) :
    ∃ (G : Chapter12GroupScheme S) (X : Over S)
      (a : Chapter12Action G X),
      Nonempty (Chapter12ActionComparison p D G X a) := by
  sorry

/-- The fixed-point object when the common fixed-point subfunctor is represented in `Over S`. -/
structure Chapter12FixedPoint {S : Scheme.{u}} {G : Chapter12GroupScheme S} {X : Over S}
    (a : Chapter12Action G X) where
  carrier : Over S
  inclusion : carrier ⟶ X
  inclusion_fixed :
    (G.X ◁ inclusion) ≫ a.hom = CartesianMonoidalCategory.snd G.X carrier ≫ inclusion
  represents :
    ∀ {Y : Over S} (x : Y ⟶ X),
      ((G.X ◁ x) ≫ a.hom = CartesianMonoidalCategory.snd G.X Y ≫ x) ↔
        ∃! z : Y ⟶ carrier, z ≫ inclusion = x

/-! Fixed points are represented only when this universal property is supplied. -/

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
  invariant : a.hom ≫ quotientMap =
    CartesianMonoidalCategory.snd G.X X ≫ quotientMap
  isColimit : IsColimit (Cofork.ofπ quotientMap invariant)

/-- The orbit-relation map associated with an effective quotient. -/
def Chapter12EffectiveQuotient.orbitRelationMap {S : Scheme.{u}}
    {G : Chapter12GroupScheme S} {X : Over S} {a : Chapter12Action G X}
  (Q : Chapter12EffectiveQuotient a) :
    G.X ⊗ X ⟶ pullback Q.quotientMap Q.quotientMap :=
  pullback.lift a.hom (CartesianMonoidalCategory.snd G.X X) Q.invariant

/-! ### Affine actions and invariant rings -/

/-- The algebra-side presentation of an affine action by a coordinate Hopf algebra. -/
structure Chapter12AffineGroupAction (A H R : Type u)
    [CommRing A] [CommRing H] [CommRing R]
    [Algebra A R] [HopfAlgebra A H] where
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
    {A H R : Type u} [CommRing A] [CommRing H] [CommRing R]
    [Algebra A R] [HopfAlgebra A H]
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
    change coaction (x + y) = Algebra.TensorProduct.includeRight (x + y)
    rw [map_add, map_add, hx, hy]
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change coaction (x * y) = Algebra.TensorProduct.includeRight (x * y)
    rw [map_mul, map_mul, hx, hy]
  algebraMap_mem' := by
    intro r
    exact (coaction.commutes r).trans (Algebra.TensorProduct.includeRight.commutes r).symm

@[simp]
theorem mem_chapter12InvariantSubalgebra_iff (A H R : Type*)
    [CommRing A] [CommRing H] [CommRing R]
    [Algebra A H] [Algebra A R]
    (coaction : R →ₐ[A] H ⊗[A] R) (r : R) :
    r ∈ chapter12InvariantSubalgebra A H R coaction ↔
      coaction r = Algebra.TensorProduct.includeRight r := Iff.rfl

/-- The invariant subalgebra is the equalizer of the coaction and `r ↦ 1 ⊗ r`. -/
def chapter12InvariantSubalgebra_isEqualizer (A H R : Type u)
    [CommRing A] [CommRing H] [CommRing R]
    [Algebra A H] [Algebra A R]
    (coaction : R →ₐ[A] H ⊗[A] R) :
      IsLimit
      (Fork.ofι
        (f := CommRingCat.ofHom coaction.toRingHom)
        (g := CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := A) (A := H) (B := R)).toRingHom)
        (CommRingCat.ofHom (chapter12InvariantSubalgebra A H R coaction).val.toRingHom)
        (by
          ext r
          exact (chapter12InvariantSubalgebra A H R coaction).property r)) := by
  fapply Fork.IsLimit.mk'
  intro s
  use CommRingCat.ofHom <| s.ι.hom.codRestrict _ (fun r => ?_)
  · change coaction (s.ι.hom r) = Algebra.TensorProduct.includeRight (s.ι.hom r)
    exact ConcreteCategory.congr_hom s.condition r
  constructor
  · ext
    rfl
  · intro m hm
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    apply Subtype.ext
    exact RingHom.congr_fun (congrArg Hom.hom hm) r

/-- Flat extension of scalars preserves the finite limits, hence equalizers, used above. -/
theorem chapter12_flat_tensor_preserves_equalizers
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hflat : (algebraMap A B).Flat) :
    PreservesFiniteLimits (tensorLeft (ModuleCat.of A B)) := by
  letI : Module.Flat A B := (RingHom.flat_algebraMap_iff).mp hflat
  exact inferInstance

/-! ### Affine quotients -/

def chapter12AffineInvariantRing {A H R : Type u}
    [CommRing A] [CommRing H] [CommRing R] [Algebra A R] [HopfAlgebra A H]
    (D : Chapter12AffineGroupAction A H R) :
    Subalgebra A R :=
  chapter12InvariantSubalgebra A H R D.coaction

def chapter12AffineQuotientScheme {A H R : Type u}
    [CommRing A] [CommRing H] [CommRing R] [Algebra A R] [HopfAlgebra A H]
    (D : Chapter12AffineGroupAction A H R) : Scheme :=
  Spec (CommRingCat.of (chapter12AffineInvariantRing D))

/-- The canonical affine quotient map `Spec R ⟶ Spec (R^G)`. -/
def chapter12AffineQuotientMap {A H R : Type u}
    [CommRing A] [CommRing H] [CommRing R] [Algebra A R] [HopfAlgebra A H]
    (D : Chapter12AffineGroupAction A H R) :
    Spec (CommRingCat.of R) ⟶ chapter12AffineQuotientScheme D :=
  Spec.map (CommRingCat.ofHom (chapter12AffineInvariantRing D).val.toRingHom)

/-- The affine quotient as an object over `Spec A`. -/
def chapter12AffineQuotientOver {A H R : Type u}
    [CommRing A] [CommRing H] [CommRing R] [Algebra A R] [HopfAlgebra A H]
    (D : Chapter12AffineGroupAction A H R) :
    Over (Spec (CommRingCat.of A)) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap A (chapter12AffineInvariantRing D))))

theorem chapter12_affine_quotient_invariant_membership
    {A H R : Type u} [CommRing A] [CommRing H] [CommRing R]
    [Algebra A R] [HopfAlgebra A H]
    (D : Chapter12AffineGroupAction A H R) (r : R) :
    r ∈ chapter12AffineInvariantRing D ↔
      D.coaction r = Algebra.TensorProduct.includeRight r := by
  rfl

def chapter12_affine_quotient_is_equalizer
    {A H R : Type u} [CommRing A] [CommRing H] [CommRing R]
    [Algebra A R] [HopfAlgebra A H]
    (D : Chapter12AffineGroupAction A H R) :
      IsLimit
      (Fork.ofι
        (f := CommRingCat.ofHom D.coaction.toRingHom)
        (g := CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := A) (A := H) (B := R)).toRingHom)
        (CommRingCat.ofHom (chapter12AffineInvariantRing D).val.toRingHom)
        (by
          ext r
          exact (chapter12AffineInvariantRing D).property r)) := by
  simpa [chapter12AffineInvariantRing] using
    (chapter12InvariantSubalgebra_isEqualizer A H R D.coaction)

/-- The flat-base-change mechanism for affine invariants: tensoring preserves their equalizer. -/
theorem chapter12_affine_invariants_equalizer_preserved_by_flat_base_change
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hflat : (algebraMap A B).Flat) :
    PreservesFiniteLimits (tensorLeft (ModuleCat.of A B)) := by
  exact chapter12_flat_tensor_preserves_equalizers hflat

/-- Finite projectivity of the coordinate Hopf algebra, the hypothesis used by the affine action
coaction and by dual Hopf-algebra base change. -/
def Chapter12FiniteLocallyFreeAffineGroupAction
    {A H R : Type u} [CommRing A] [CommRing H] [CommRing R]
    [Algebra A R] [HopfAlgebra A H]
    (_D : Chapter12AffineGroupAction A H R) : Prop :=
  Module.Finite A H ∧ Module.Projective A H

theorem chapter12_affine_finite_projective_hopf_action_dualizes
    {A H R : Type u} [CommRing A] [CommRing H] [CommRing R]
    [Algebra A R] [HopfAlgebra A H]
    (D : Chapter12AffineGroupAction A H R)
    (hD : Chapter12FiniteLocallyFreeAffineGroupAction D) :
    Chapter12FiniteProjectiveModule A (Module.Dual A H) := by
  exact chapter12_dual_of_finite_projective A H hD

/-! ### Free actions and torsors -/

/-- Freeness in the usual orbit-map sense. -/
def Chapter12Action.IsFree {S : Scheme.{u}} {G : Chapter12GroupScheme S} {X : Over S}
    (a : Chapter12Action G X) : Prop :=
  Mono (CartesianMonoidalCategory.lift a.hom
    (CartesianMonoidalCategory.snd G.X X))

/-- A torsor presentation of an action. -/
structure Chapter12Torsor {S : Scheme.{u}} {G : Chapter12GroupScheme S} {X : Over S}
    (a : Chapter12Action G X) where
  toEffectiveQuotient : Chapter12EffectiveQuotient a
  quotientFppf : Chapter12Fppf toEffectiveQuotient.quotientMap.left
  orbitRelationIsIso :
    IsIso (Chapter12EffectiveQuotient.orbitRelationMap toEffectiveQuotient)

namespace Chapter12Torsor

variable {S : Scheme.{u}} {G : Chapter12GroupScheme S} {X : Over S}
  {a : Chapter12Action G X}

abbrev quotient (T : Chapter12Torsor a) : Over S := T.toEffectiveQuotient.quotient

abbrev quotientMap (T : Chapter12Torsor a) : X ⟶ T.quotient :=
  T.toEffectiveQuotient.quotientMap

abbrev invariant (T : Chapter12Torsor a) :
    a.hom ≫ T.quotientMap = CartesianMonoidalCategory.snd G.X X ≫ T.quotientMap :=
  T.toEffectiveQuotient.invariant

end Chapter12Torsor

theorem chapter12_torsor_is_free
    {S : Scheme.{u}} {G : Chapter12GroupScheme S} {X : Over S}
    {a : Chapter12Action G X} (T : Chapter12Torsor a) :
    Chapter12Action.IsFree a := by
  letI := T.orbitRelationIsIso
  have horbit :
      CartesianMonoidalCategory.lift a.hom
          (CartesianMonoidalCategory.snd G.X X) =
        Chapter12EffectiveQuotient.orbitRelationMap T.toEffectiveQuotient := by
    apply Over.OverMorphism.ext
    rfl
  change Mono (CartesianMonoidalCategory.lift a.hom
    (CartesianMonoidalCategory.snd G.X X))
  rw [horbit]
  infer_instance

theorem chapter12_torsor_quotient_finiteLocallyFree
    {S : Scheme.{u}} {G : Chapter12GroupScheme S} {X : Over S}
    {a : Chapter12Action G X} (T : Chapter12Torsor a)
    (hq : QuasiCompact T.quotientMap.left)
    (hG : Chapter12FiniteLocallyFree G.X.hom) :
    Chapter12FiniteLocallyFree T.quotientMap.left := by
  sorry

def chapter12_torsor_orbit_relation_effective
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

theorem chapter12_effective_quotient_descends_when_represented
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D : Chapter12ActionDescentData p)
    (Q_T : Chapter12EffectiveQuotient D.action)
    (Q_D : Chapter12OverDescentDatum p)
    (eQ_T : Q_D.upstairs ≅ Q_T.quotient)
    (hQ : chapter12OverDescentHomCompatible D.target Q_D
      (Q_T.quotientMap ≫ eQ_T.inv)) :
    ∃ (G : Chapter12GroupScheme S) (X : Over S)
      (a : Chapter12Action G X) (Q : Chapter12EffectiveQuotient a)
      (C : Chapter12ActionComparison p D G X a)
      (eQ : (Over.pullback p).obj Q.quotient ≅ Q_T.quotient),
      (Over.pullback p).map Q.quotientMap ≫ eQ.hom =
        C.targetIso.hom ≫ Q_T.quotientMap := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12
