import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Sites.InducedTopology
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03.Section01DefinitionsThatSurviveChangeOfBase

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators Polynomial

universe u v

/-!
Shared interfaces for Chapter 11.

The checkout currently has no elaborated Book 8 Chapters 1--10.  The relative
scheme and quotient records below are therefore deliberately small bridges to
the canonical scheme APIs in Mathlib.  They record universal properties rather
than replacing them by hypotheses containing the conclusions of this chapter.
-/

/-- A scheme equipped with a chosen structural morphism to `S`. -/
structure RelativeScheme (S : Scheme.{u}) where
  carrier : Scheme.{u}
  structuralMap : carrier ⟶ S

namespace RelativeScheme

/-- A morphism in the book-facing slice of schemes over `S`. -/
structure Hom {S : Scheme.{u}} (X Y : RelativeScheme S) where
  hom : X.carrier ⟶ Y.carrier
  comm : hom ≫ Y.structuralMap = X.structuralMap

@[ext]
theorem Hom.ext {S : Scheme.{u}} {X Y : RelativeScheme S}
    {f g : RelativeScheme.Hom X Y}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance (S : Scheme.{u}) : Category.{u} (RelativeScheme S) where
  Hom X Y := RelativeScheme.Hom X Y
  id X :=
    { hom := 𝟙 X.carrier
      comm := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      comm := by rw [Category.assoc, g.comm, f.comm] }

@[simp]
theorem id_hom {S : Scheme.{u}} (X : RelativeScheme S) :
    (𝟙 X : RelativeScheme.Hom X X).hom = 𝟙 X.carrier :=
  rfl

@[simp]
theorem comp_hom {S : Scheme.{u}} {X Y Z : RelativeScheme S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

/-- The base scheme viewed as an object over itself. -/
def base (S : Scheme.{u}) : RelativeScheme S where
  carrier := S
  structuralMap := 𝟙 S

/-- An isomorphism in the book-facing slice. -/
structure Iso {S : Scheme.{u}} (X Y : RelativeScheme S) where
  hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv_id : hom ≫ inv = 𝟙 X
  inv_hom_id : inv ≫ hom = 𝟙 Y

@[ext]
theorem Iso.ext {S : Scheme.{u}} {X Y : RelativeScheme S}
    {e e' : RelativeScheme.Iso X Y}
    (h : e.hom = e'.hom) : e = e' := by
  cases e with
  | mk hom inv hom_inv_id inv_hom_id =>
    cases e' with
    | mk hom' inv' hom_inv_id' inv_hom_id' =>
      cases h
      have hinv : inv = inv' := by
        calc
          inv = 𝟙 Y ≫ inv := by simp
          _ = (inv' ≫ hom) ≫ inv := by rw [inv_hom_id']
          _ = inv' ≫ (hom ≫ inv) := by simp only [Category.assoc]
          _ = inv' ≫ 𝟙 X := by rw [hom_inv_id]
          _ = inv' := by simp
      cases hinv
      rfl

@[simp]
theorem Iso.hom_inv_id_apply {S : Scheme.{u}} {X Y : RelativeScheme S}
    (e : RelativeScheme.Iso X Y) :
    e.hom ≫ e.inv = 𝟙 X :=
  e.hom_inv_id

@[simp]
theorem Iso.inv_hom_id_apply {S : Scheme.{u}} {X Y : RelativeScheme S}
    (e : RelativeScheme.Iso X Y) :
    e.inv ≫ e.hom = 𝟙 Y :=
  e.inv_hom_id

/-- The identity isomorphism in the book-facing slice. -/
def Iso.refl {S : Scheme.{u}} (X : RelativeScheme S) : RelativeScheme.Iso X X where
  hom := 𝟙 X
  inv := 𝟙 X
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- Base change of a relative scheme along another object of the same slice. -/
def baseChange {S : Scheme.{u}} (X T : RelativeScheme S) : RelativeScheme T.carrier where
  carrier := pullback X.structuralMap T.structuralMap
  structuralMap := pullback.snd X.structuralMap T.structuralMap

/-- The canonical base change of a relative morphism. -/
def baseChangeHom {S : Scheme.{u}} {X Y : RelativeScheme S}
    (f : X ⟶ Y)
    (T : RelativeScheme S) : baseChange X T ⟶ baseChange Y T where
  hom := pullback.lift
    (pullback.fst X.structuralMap T.structuralMap ≫ f.hom)
    (pullback.snd X.structuralMap T.structuralMap)
    (by sorry)
  comm := by
    exact pullback.lift_snd _ _ _

@[simp]
theorem baseChangeHom_fst {S : Scheme.{u}} {X Y : RelativeScheme S}
    (f : X ⟶ Y)
    (T : RelativeScheme S) :
    (baseChangeHom f T).hom ≫ pullback.fst Y.structuralMap T.structuralMap =
      pullback.fst X.structuralMap T.structuralMap ≫ f.hom :=
  pullback.lift_fst _ _ _

@[simp]
theorem baseChangeHom_snd {S : Scheme.{u}} {X Y : RelativeScheme S}
    (f : X ⟶ Y)
    (T : RelativeScheme S) :
    (baseChangeHom f T).hom ≫ pullback.snd Y.structuralMap T.structuralMap =
      pullback.snd X.structuralMap T.structuralMap :=
  pullback.lift_snd _ _ _

end RelativeScheme

open RelativeScheme

open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03

/-- Forget the chosen structural morphism of a relative scheme. -/
def RelativeScheme.toScheme (S : Scheme.{u}) : RelativeScheme S ⥤ Scheme.{u} where
  obj X := X.carrier
  map f := f.hom
  map_id := by sorry
  map_comp := by sorry

/-- The fppf topology on the book-facing slice, induced from schemes. -/
abbrev relativeSchemeFppfTopology (S : Scheme.{u}) :
    GrothendieckTopology (RelativeScheme S) :=
  (RelativeScheme.toScheme S).inducedTopology AlgebraicGeometry.Scheme.fppfTopology

/-- A binary product in the slice, expressed by its universal property. -/
structure RelativeProduct {S : Scheme.{u}} (X Y : RelativeScheme S) where
  carrier : RelativeScheme S
  fst : carrier ⟶ X
  snd : carrier ⟶ Y
  isProduct : ∀ {T : RelativeScheme S} (f : T ⟶ X)
    (g : T ⟶ Y),
    ∃! h : T ⟶ carrier, h ≫ fst = f ∧ h ≫ snd = g

theorem relativeProduct_exists {S : Scheme.{u}} (X Y : RelativeScheme S) :
    Nonempty (RelativeProduct X Y) := by
  sorry

noncomputable def relativeProduct {S : Scheme.{u}} (X Y : RelativeScheme S) :
    RelativeProduct X Y :=
  Classical.choice (relativeProduct_exists X Y)

noncomputable def RelativeProduct.lift {S : Scheme.{u}} {X Y T : RelativeScheme S}
    (P : RelativeProduct X Y) (f : T ⟶ X)
    (g : T ⟶ Y) : T ⟶ P.carrier :=
  (P.isProduct f g).choose

@[simp]
theorem RelativeProduct.lift_fst {S : Scheme.{u}} {X Y T : RelativeScheme S}
    (P : RelativeProduct X Y) (f : T ⟶ X)
    (g : T ⟶ Y) :
    P.lift f g ≫ P.fst = f :=
  by
    simpa [RelativeProduct.lift] using (P.isProduct f g).choose_spec.1.1

@[simp]
theorem RelativeProduct.lift_snd {S : Scheme.{u}} {X Y T : RelativeScheme S}
    (P : RelativeProduct X Y) (f : T ⟶ X)
    (g : T ⟶ Y) :
    P.lift f g ≫ P.snd = g :=
  by
    simpa [RelativeProduct.lift] using (P.isProduct f g).choose_spec.1.2

theorem RelativeProduct.lift_unique {S : Scheme.{u}} {X Y T : RelativeScheme S}
    (P : RelativeProduct X Y) (f : T ⟶ X)
    (g : T ⟶ Y)
    (h : T ⟶ P.carrier) (hf : h ≫ P.fst = f)
    (hg : h ≫ P.snd = g) :
    h = P.lift f g := by
  simpa [RelativeProduct.lift] using
    (P.isProduct f g).unique ⟨hf, hg⟩ (P.isProduct f g).choose_spec.1

/-- A chosen finite product of `d` copies of `X` in the slice. -/
structure RelativePower {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ) where
  carrier : RelativeScheme S
  projection : Fin d → (carrier ⟶ X)
  isPower : ∀ {T : RelativeScheme S} (f : Fin d → (T ⟶ X)),
    ∃! h : T ⟶ carrier, ∀ i, h ≫ projection i = f i
  permutation : Equiv.Perm (Fin d) → (carrier ⟶ carrier)
  permutation_one : permutation 1 = 𝟙 carrier
  permutation_mul : ∀ σ τ, permutation (σ * τ) = permutation σ ≫ permutation τ
  permutation_projection : ∀ (σ : Equiv.Perm (Fin d)) (i : Fin d),
    permutation σ ≫ projection i = projection (σ i)

theorem relativePower_exists {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ) :
    Nonempty (RelativePower X d) := by
  sorry

noncomputable def relativePower {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ) :
    RelativePower X d :=
  Classical.choice (relativePower_exists X d)

noncomputable def RelativePower.lift {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    (P : RelativePower X d) (f : Fin d → (T ⟶ X)) :
    T ⟶ P.carrier :=
  (P.isPower f).choose

@[simp]
theorem RelativePower.lift_projection {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    (P : RelativePower X d) (f : Fin d → (T ⟶ X)) (i : Fin d) :
    P.lift f ≫ P.projection i = f i :=
  by
    simpa [RelativePower.lift] using (P.isPower f).choose_spec.1 i

theorem RelativePower.lift_unique {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    (P : RelativePower X d) (f : Fin d → (T ⟶ X))
    (h : T ⟶ P.carrier)
    (hh : ∀ i, h ≫ P.projection i = f i) :
    h = P.lift f := by
  simpa [RelativePower.lift] using
    (P.isPower f).unique hh (P.isPower f).choose_spec.1

noncomputable def RelativePower.zero_power_iso {S : Scheme.{u}} (X : RelativeScheme S) :
    RelativeScheme.Iso (relativePower X 0).carrier (base S) := by
  sorry

noncomputable def RelativePower.one_power_iso {S : Scheme.{u}} (X : RelativeScheme S) :
    RelativeScheme.Iso (relativePower X 1).carrier X := by
  sorry

/-- A group action by automorphisms in the slice category. -/
structure RelativeAction {S : Scheme.{u}} (Y : RelativeScheme S) (G : Type v)
    [Group G] where
  hom : G → (Y ⟶ Y)
  one_hom : hom 1 = 𝟙 Y
  mul_hom : ∀ g h, hom (g * h) = hom g ≫ hom h
  isIso : ∀ g, IsIso (hom g)

def RelativeAction.baseChange {S : Scheme.{u}} {Y : RelativeScheme S} {G : Type v} [Group G]
    (act : RelativeAction Y G) (T : RelativeScheme S) :
    RelativeAction (RelativeScheme.baseChange Y T) G where
  hom := fun g => RelativeScheme.baseChangeHom (act.hom g) T
  one_hom := by
    apply RelativeScheme.Hom.ext
    sorry
  mul_hom := by
    intro g h
    apply RelativeScheme.Hom.ext
    sorry
  isIso := by
    intro g
    sorry

/-- The action is free when no nonidentity element fixes a relative point. -/
def RelativeAction.IsFree {S : Scheme.{u}} {Y : RelativeScheme S} {G : Type v} [Group G]
    (act : RelativeAction Y G) : Prop :=
  ∀ (T : RelativeScheme S), Nonempty T.carrier →
    ∀ (x : T ⟶ Y) (g : G),
    x ≫ act.hom g = x → g = 1

noncomputable def RelativePower.permutationAction {S : Scheme.{u}} {X : RelativeScheme S} {d : ℕ}
    (P : RelativePower X d) : RelativeAction P.carrier (Equiv.Perm (Fin d)) where
  hom := P.permutation
  one_hom := P.permutation_one
  mul_hom := P.permutation_mul
  isIso := by
    intro σ
    sorry

theorem RelativePower.permutationAction_projection {S : Scheme.{u}} {X : RelativeScheme S} {d : ℕ}
    (P : RelativePower X d)
    (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    (P.permutationAction.hom σ) ≫ P.projection i = P.projection (σ i) :=
  P.permutation_projection σ i

/-!
The quotient theorem consumes the canonical relative projective-bundle and
quasi-projective presentation supplied by Chapter 3.  The chapter-facing
class keeps the existing typeclass boundary while carrying that presentation
and the finiteness hypotheses used by the quotient construction.
-/

abbrev Chapter11RelativeProjectiveBundle (S : Scheme.{u}) (E : S.Modules) :=
  Chapter03RelativeProjectiveBundle S E

abbrev Chapter11QuasiProjectivePresentation {X S : Scheme.{u}} (f : X ⟶ S) :=
  Chapter03QuasiProjectivePresentation f

class Chapter11QuasiProjectiveOver {S : Scheme.{u}} (X : RelativeScheme S) where
  presentation : Chapter11QuasiProjectivePresentation X.structuralMap
  quasi_compact : QuasiCompact X.structuralMap
  finite_presentation : LocallyOfFinitePresentation X.structuralMap
  separated : IsSeparated X.structuralMap

/- A regular immersion is recorded by its closed-immersion structure and the
   regular-sequence description of its ideal in every source stalk. -/
def Chapter11FiberwiseCodimension {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ) : Prop :=
  ∀ x : X, ∃ rs : List (Y.presheaf.stalk (f x)),
    rs.length = r ∧
      RingTheory.Sequence.IsRegular (Y.presheaf.stalk (f x)) rs ∧
        RingHom.ker (f.stalkMap x).hom = Ideal.ofList rs

/-- Codimension by local ideal height, without asserting that the whole closed
    subscheme is a regular immersion.  This is the appropriate invariant for
    unions of pairwise diagonals, which can be singular at multiple collisions. -/
def Chapter11FiberwiseHeightCodimension {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ) : Prop :=
  ∀ x : X, (RingHom.ker (f.stalkMap x).hom).height = r

structure Chapter11RegularImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ) where
  closed : IsClosedImmersion f
  fiberwiseCodimension : Chapter11FiberwiseCodimension f r

/-- A categorical quotient in the slice, with its universal property. -/
structure RelativeCategoricalQuotient {S : Scheme.{u}} (Y : RelativeScheme S)
    (G : Type v) [Group G]
    (act : RelativeAction Y G) where
  carrier : RelativeScheme S
  quotientMap : Y ⟶ carrier
  invariant : ∀ g, act.hom g ≫ quotientMap = quotientMap
  universal : ∀ {Z : RelativeScheme S} (f : Y ⟶ Z),
    (∀ g, act.hom g ≫ f = f) →
      ∃! h : carrier ⟶ Z, quotientMap ≫ h = f

@[simp]
theorem RelativeCategoricalQuotient.quotientMap_invariant
    {S : Scheme.{u}} {Y : RelativeScheme S} {G : Type v} [Group G]
    {act : RelativeAction Y G}
    (Q : RelativeCategoricalQuotient Y G act) (g : G) :
    act.hom g ≫ Q.quotientMap = Q.quotientMap :=
  Q.invariant g

theorem RelativeCategoricalQuotient.factor_unique
    {S : Scheme.{u}} {Y : RelativeScheme S} {G : Type v} [Group G]
    {act : RelativeAction Y G}
    (Q : RelativeCategoricalQuotient Y G act)
    {Z : RelativeScheme S} (f : Y ⟶ Z)
    (hf : ∀ g, act.hom g ≫ f = f)
    (h k : Q.carrier ⟶ Z) (hh : Q.quotientMap ≫ h = f)
    (hk : Q.quotientMap ≫ k = f) : h = k := by
  exact (Q.universal f hf).unique hh hk

/-- The finite, integral, surjective quotient package used by this chapter. -/
structure RelativeFiniteGroupQuotient {S : Scheme.{u}} (Y : RelativeScheme S)
    (G : Type v) [Finite G] [Group G]
    (act : RelativeAction Y G) where
  quotient : RelativeCategoricalQuotient Y G act
  quasiProjective : Chapter11QuasiProjectiveOver quotient.carrier
  integral : IsIntegralHom quotient.quotientMap.hom
  finite : IsFinite quotient.quotientMap.hom
  surjective : Surjective quotient.quotientMap.hom
  flat_base_change :
    ∀ (T : RelativeScheme S), Flat T.structuralMap →
      ∃ QT : RelativeCategoricalQuotient
        (RelativeScheme.baseChange Y T) G (act.baseChange T),
        ∃ e : RelativeScheme.Iso (RelativeScheme.baseChange quotient.carrier T) QT.carrier,
          RelativeScheme.baseChangeHom quotient.quotientMap T ≫ e.hom = QT.quotientMap

abbrev RelativeFiniteGroupQuotient.carrier
    {S : Scheme.{u}} {Y : RelativeScheme S} {G : Type v} [Finite G] [Group G]
    {act : RelativeAction Y G}
    (Q : RelativeFiniteGroupQuotient Y G act) :
    RelativeScheme S :=
  Q.quotient.carrier

abbrev RelativeFiniteGroupQuotient.quotientMap
    {S : Scheme.{u}} {Y : RelativeScheme S} {G : Type v} [Finite G] [Group G]
    {act : RelativeAction Y G}
    (Q : RelativeFiniteGroupQuotient Y G act) :
    Y ⟶ Q.carrier :=
  Q.quotient.quotientMap

theorem finite_group_quotient_exists
    {S : Scheme.{u}} {Y : RelativeScheme S} {G : Type v} [Finite G] [Group G]
    (act : RelativeAction Y G)
    [Chapter11QuasiProjectiveOver Y] :
    Nonempty (RelativeFiniteGroupQuotient Y G act) := by
  sorry

noncomputable def finiteGroupQuotient
    {S : Scheme.{u}} {Y : RelativeScheme S} {G : Type v} [Finite G] [Group G]
    (act : RelativeAction Y G)
    [Chapter11QuasiProjectiveOver Y] :
    RelativeFiniteGroupQuotient Y G act :=
  Classical.choice (finite_group_quotient_exists act)

/-- The fppf condition used for a single scheme morphism. -/
def Chapter11Fppf {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  QuasiCompact f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧ Surjective f

/-- The finite-type package for a scheme morphism. -/
def Chapter11FiniteType {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  QuasiCompact f ∧ LocallyOfFiniteType f

/-- Finite locally free of constant rank, expressed through Mathlib's rank API. -/
def Chapter11FiniteLocallyFreeOfRank {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) : Prop :=
  IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
    ∀ y : Y, Scheme.Hom.finrank f y = d

/-- An ideal sheaf is effective Cartier when it is locally generated by a regular element. -/
def _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier {X : Scheme.{u}}
    (I : X.IdealSheafData) : Prop :=
  ∀ (U : X.affineOpens) (x : U.1),
    ∃ (V : X.affineOpens) (f : Γ(X, V.1)),
      x.1 ∈ V.1 ∧ V ≤ U ∧ I.ideal V = Ideal.span ({f} : Set Γ(X, V.1)) ∧
        f ∈ nonZeroDivisors Γ(X, V.1)

/-- An effective Cartier divisor represented by its ideal sheaf. -/
structure EffectiveCartierDivisor (X : Scheme.{u}) where
  ideal : X.IdealSheafData
  isEffectiveCartier : ideal.IsEffectiveCartier

namespace EffectiveCartierDivisor

abbrev subscheme {X : Scheme.{u}} (D : EffectiveCartierDivisor X) : Scheme :=
  D.ideal.subscheme

abbrev inclusion {X : Scheme.{u}} (D : EffectiveCartierDivisor X) : D.subscheme ⟶ X :=
  D.ideal.subschemeι

def add {X : Scheme.{u}} (D E : EffectiveCartierDivisor X) : EffectiveCartierDivisor X where
  ideal := D.ideal * E.ideal
  isEffectiveCartier := by
    sorry

def sum {X : Scheme.{u}} {d : ℕ} (D : Fin d → EffectiveCartierDivisor X) :
    EffectiveCartierDivisor X where
  ideal := ∏ i, (D i).ideal
  isEffectiveCartier := by
    sorry

@[simp]
theorem sum_zero {X : Scheme.{u}} :
    (sum (d := 0) (fun i => Fin.elim0 i)).ideal = (1 : X.IdealSheafData) := by
  simp [sum]

theorem support_add {X : Scheme.{u}} (D E : EffectiveCartierDivisor X) :
    (D.add E).ideal.support = D.ideal.support ⊔ E.ideal.support := by
  simp [add]

end EffectiveCartierDivisor

/-- A degree-`d` relative effective Cartier divisor on `C_T`. -/
structure RelativeEffectiveCartierDivisor {S : Scheme.{u}}
    (C T : RelativeScheme S) (d : ℕ) where
  divisor : EffectiveCartierDivisor (pullback C.structuralMap T.structuralMap)
  finite_flat_rank :
    Chapter11FiniteLocallyFreeOfRank
      (divisor.inclusion ≫ pullback.snd C.structuralMap T.structuralMap) d

/- Degree is additive for sums of finite-flat effective Cartier divisors. -/
theorem relativeEffectiveCartierDivisor_add_rank {S : Scheme.{u}}
    {C T : RelativeScheme S} (d e : ℕ)
    (D : RelativeEffectiveCartierDivisor C T d)
    (E : RelativeEffectiveCartierDivisor C T e) :
    Chapter11FiniteLocallyFreeOfRank
      ((D.divisor.add E.divisor).inclusion ≫
        pullback.snd C.structuralMap T.structuralMap) (d + e) := by
  sorry

/-- A finite étale degree-`d` subscheme of `X_T`. -/
def Chapter11FiniteEtaleOfDegree {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) : Prop :=
  IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧ Etale f ∧
    ∀ y : Y, Scheme.Hom.finrank f y = d

structure RelativeFiniteEtaleSubscheme {S : Scheme.{u}}
    (X T : RelativeScheme S) (d : ℕ) where
  /-- A finite étale family is represented by its ideal sheaf in `X_T`, not by
      an arbitrary presentation of the same closed subscheme.  This is the
      set-valued convention used by the Hilbert functor. -/
  ideal : (pullback X.structuralMap T.structuralMap).IdealSheafData
  finite_etale : Chapter11FiniteEtaleOfDegree
    (ideal.subschemeι ≫ pullback.snd X.structuralMap T.structuralMap) d

namespace RelativeFiniteEtaleSubscheme

abbrev carrier {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    (Z : RelativeFiniteEtaleSubscheme X T d) : Scheme.{u} :=
  Z.ideal.subscheme

abbrev mapToX {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    (Z : RelativeFiniteEtaleSubscheme X T d) :
    Z.carrier ⟶ pullback X.structuralMap T.structuralMap :=
  Z.ideal.subschemeι

abbrev mapToBase {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    (Z : RelativeFiniteEtaleSubscheme X T d) : Z.carrier ⟶ T.carrier :=
  Z.mapToX ≫ pullback.snd X.structuralMap T.structuralMap

@[simp]
theorem over_base {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    (Z : RelativeFiniteEtaleSubscheme X T d) :
    Z.mapToX ≫ pullback.snd X.structuralMap T.structuralMap = Z.mapToBase :=
  rfl

/- The subscheme attached to an ideal sheaf is a closed subscheme.  Keeping
   this as a theorem, rather than as data on a second presentation, prevents
   isomorphic copies of one family from becoming different functor values. -/
theorem closed {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    (Z : RelativeFiniteEtaleSubscheme X T d) : IsClosedImmersion Z.mapToX := by
  sorry

@[ext]
theorem ext {S : Scheme.{u}} {X T : RelativeScheme S} {d : ℕ}
    {Z W : RelativeFiniteEtaleSubscheme X T d} (h : Z.ideal = W.ideal) : Z = W := by
  cases Z with
  | mk ideal finite_etale =>
    cases W with
    | mk ideal' finite_etale' =>
      cases h
      rfl

end RelativeFiniteEtaleSubscheme

/-- An isomorphism of finite étale families over the same ambient relative scheme. -/
structure RelativeFiniteEtaleSubscheme.Isomorphism {S : Scheme.{u}}
    {X T : RelativeScheme S} {d : ℕ}
    (Z W : RelativeFiniteEtaleSubscheme X T d) where
  hom : Z.carrier ⟶ W.carrier
  inv : W.carrier ⟶ Z.carrier
  hom_inv_id : hom ≫ inv = 𝟙 Z.carrier
  inv_hom_id : inv ≫ hom = 𝟙 W.carrier
  over_base : hom ≫ W.mapToBase = Z.mapToBase
  over_X : hom ≫ W.mapToX = Z.mapToX

/-- Pullback of a finite étale family along a morphism of relative test schemes. -/
noncomputable def RelativeFiniteEtaleSubscheme.pullback {S : Scheme.{u}}
    {X T U : RelativeScheme S} {d : ℕ}
    (Z : RelativeFiniteEtaleSubscheme X T d) (u : U ⟶ T) :
    RelativeFiniteEtaleSubscheme X U d := by
  sorry

/-- Sections that split a finite étale family after an étale cover. -/
def Chapter11PairwiseDisjointSections {U Z : Scheme.{u}} {d : ℕ}
    (s : Fin d → (U ⟶ Z)) : Prop :=
  ∀ (V : Scheme.{u}) (v : V ⟶ U), Nonempty V →
    Pairwise (fun i j => v ≫ s i ≠ v ≫ s j)

def Chapter11SplitsAsDisjointSections {S : Scheme.{u}}
    {X T : RelativeScheme S} (d : ℕ)
    (Z : RelativeFiniteEtaleSubscheme X T d) : Prop :=
  ∃ (U : Scheme.{u}) (u : U ⟶ T.carrier),
      Etale u ∧ Surjective u ∧
      ∃ (s : Fin d → (U ⟶ Z.carrier)),
        Chapter11PairwiseDisjointSections s ∧
          ∀ i, s i ≫ Z.mapToBase = u

/-- Ordered tuples are collision-free after every nonempty base change. -/
def Chapter11PairwiseDistinctOrderedTuple {S : Scheme.{u}}
    {X T : RelativeScheme S} {d : ℕ} (x : Fin d → (T ⟶ X)) : Prop :=
  ∀ (U : RelativeScheme S) (u : U ⟶ T), Nonempty U.carrier →
    Pairwise (fun i j => u ≫ x i ≠ u ≫ x j)

/--
The reusable configuration-space package supplied to later synthesis chapters.
The open complement, action freeness, quotient universal property, and family
classification are data of the construction; none is inferred from an
arbitrary pair of maps.
-/
structure Chapter11ConfigurationSpaceData {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X] where
  orderedConfiguration : RelativeScheme S
  orderedToPower : orderedConfiguration ⟶ (relativePower X d).carrier
  orderedToPower_isOpen : IsOpenImmersion orderedToPower.hom
  bigDiagonal : RelativeScheme S
  bigDiagonalInclusion : bigDiagonal ⟶ (relativePower X d).carrier
  bigDiagonal_isClosed : IsClosedImmersion bigDiagonalInclusion.hom
  diagonal_complement :
    Set.range orderedToPower.hom = Set.univ \ Set.range bigDiagonalInclusion.hom
  /-- The underlying-point complement of the closed big diagonal.  The
      scheme-theoretic universal property is `open_characterizes` below. -/
  open_characterizes :
    ∀ (T : RelativeScheme S) (x : T ⟶ (relativePower X d).carrier),
      Chapter11PairwiseDistinctOrderedTuple
          (fun i => x ≫ (relativePower X d).projection i) ↔
        ∃! y : T ⟶ orderedConfiguration, y ≫ orderedToPower = x
  permutationAction :
    RelativeAction orderedConfiguration (Equiv.Perm (Fin d))
  permutation_compatible :
    ∀ σ : Equiv.Perm (Fin d),
      permutationAction.hom σ ≫ orderedToPower =
        orderedToPower ≫ (relativePower X d).permutation σ
  permutation_isFree : permutationAction.IsFree
  quotient :
    RelativeFiniteGroupQuotient orderedConfiguration
      (Equiv.Perm (Fin d)) permutationAction
  quotient_universal :
    ∀ {Z : RelativeScheme S} (f : orderedConfiguration ⟶ Z),
      (∀ σ, permutationAction.hom σ ≫ f = f) →
        ∃! h : quotient.carrier ⟶ Z,
          quotient.quotientMap ≫ h = f
  quotient_finite_etale :
    Chapter11FiniteEtaleOfDegree quotient.quotientMap.hom (Nat.factorial d)
  universalFamily :
    RelativeFiniteEtaleSubscheme X quotient.carrier d
  universalFamily_splits :
    Chapter11SplitsAsDisjointSections d universalFamily
  universalFamily_classifies :
    ∀ T : RelativeScheme S,
      (T ⟶ quotient.carrier) ≃
        {Z : RelativeFiniteEtaleSubscheme X T d //
          Chapter11SplitsAsDisjointSections d Z}
  universalFamily_classifies_pullback :
    ∀ (T : RelativeScheme S) (f : T ⟶ quotient.carrier),
      (universalFamily_classifies T f).1 =
        RelativeFiniteEtaleSubscheme.pullback universalFamily f
  universalFamily_classifies_natural :
    ∀ {T U : RelativeScheme S} (u : U ⟶ T) (f : T ⟶ quotient.carrier),
      RelativeFiniteEtaleSubscheme.pullback
          (universalFamily_classifies T f).1 u =
        (universalFamily_classifies U (u ≫ f)).1
  universalFamily_is_classifying_point :
    (universalFamily_classifies quotient.carrier (𝟙 quotient.carrier)).1 =
      universalFamily

/-- A local monic equation with the basis `1,z,…,z^(d-1)`. -/
structure MonicPolynomialChart (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (d : ℕ) where
  parameter : A
  polynomial : R[X]
  monic : polynomial.Monic
  degree : polynomial.natDegree = d
  equation : Polynomial.aeval parameter polynomial = 0
  basis : Module.Basis (Fin d) R A
  basis_eq_power : ∀ i, basis i = parameter ^ (i : ℕ)

theorem MonicPolynomialChart.ext {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] {d : ℕ} {P Q : MonicPolynomialChart R A d}
    (hparameter : P.parameter = Q.parameter) (hpolynomial : P.polynomial = Q.polynomial) :
    P = Q := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
