import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finsupp.Defs
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RepresentationTheory.Induced
import LastLib.Book05LocalClassFieldTheory.Chapter05.Section03ClassFormation

namespace LastLib.Book06GlobalClassFieldTheory.Chapter04

noncomputable section

open CategoryTheory
open scoped BigOperators

universe u v w

/-!
Shared interfaces for the global class-formation chapter.

The pinned Mathlib snapshot contains the finite-group Tate and group-cohomology complexes, the
number-field place and Dedekind-zeta APIs, and Shapiro's lemma.  It does not yet expose the
idele-class, Brauer-group, or compact-support Galois-cohomology constructions used by the book.
The small structures below are therefore book-facing dependency interfaces.  They record objects
and maps; where a canonical earlier API is still absent, conclusion-level input is isolated in a
named record rather than smuggled into an unrelated map or proposition.

DEPENDENCY_GUESS: `Chapter04BrauerContext`, `Chapter04CompactSupportAPI`, and the idele-class
presentation are temporary bridges for the missing Book 4--6 interfaces.  They should be replaced
by the canonical reconciled declarations when those chapters are available.
-/

/-! ### Canonical finite-group cohomology bridge -/

/-- An additive integral representation, used to expose the pinned Mathlib Tate complex. -/
structure Chapter04GModule (G : Type u) [Group G] where
  V : Type v
  [addCommGroupV : AddCommGroup V]
  [moduleV : Module ℤ V]
  ρ : Representation ℤ G V

attribute [instance] Chapter04GModule.addCommGroupV Chapter04GModule.moduleV

noncomputable instance chapter04SubgroupFintype
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- The canonical `Rep` object attached to a book-facing additive `G`-module. -/
def chapter04GModuleRep {G : Type u} [Group G]
    (M : Chapter04GModule.{u, v} G) :
    Rep.{v, 0, u} ℤ G :=
  letI := M.addCommGroupV
  letI := M.moduleV
  Rep.of M.ρ

/-- Restriction of a book-facing module to a subgroup. -/
def chapter04RestrictGModule {G : Type u} [Group G]
    (M : Chapter04GModule.{u, v} G) (H : Subgroup G) : Chapter04GModule.{u, v} H where
  V := M.V
  addCommGroupV := M.addCommGroupV
  moduleV := M.moduleV
  ρ := M.ρ.comp H.subtype

/-- The trivial integral representation on `ℤ`. -/
def chapter04TrivialGModule (G : Type u) [Group G] : Chapter04GModule.{u, 0} G where
  V := ℤ
  addCommGroupV := inferInstance
  moduleV := inferInstance
  ρ := Representation.trivial ℤ G ℤ

/-- The annihilation condition used for finite coefficient modules. -/
def chapter04NAnnihilates {G : Type u} [Group G]
    (n : ℕ) (M : Chapter04GModule.{u, v} G) : Prop :=
  letI := M.addCommGroupV
  letI := M.moduleV
  ∀ x : M.V, n • x = 0

/-- Tate cohomology through Mathlib's canonical finite-group complex. -/
abbrev chapter04TateH {G : Type} [Group G] [Fintype G]
    (M : Chapter04GModule.{0, 0} G) (r : ℤ) : ModuleCat ℤ :=
  (tateCohomologyFunctor (R := ℤ) (G := G) r).obj (chapter04GModuleRep M)

/-- Positive-degree group cohomology through Mathlib's canonical complex. -/
abbrev chapter04GroupH {G : Type} [Group G]
    (M : Chapter04GModule.{0, 0} G) (r : ℕ) : ModuleCat ℤ :=
  groupCohomology (k := ℤ) (G := G) (chapter04GModuleRep M) r

/-- The canonical restriction of an ordinary degree-two class to a subgroup. -/
def chapter04RestrictTwoClass
    {G : Type} [Group G] [Fintype G]
    (C : Chapter04GModule.{0, 0} G) (H : Subgroup G)
    (u : chapter04GroupH C 2) :
    chapter04GroupH (chapter04RestrictGModule C H) 2 :=
  groupCohomology.map H.subtype
    (𝟙 (Rep.res H.subtype (chapter04GModuleRep C))) 2 u

/-- A coefficient module together with its Tate-dual coefficient and evaluation target. -/
structure Chapter04DualCoefficientPair (G : Type u) [Group G] where
  n : ℕ
  positive_n : 0 < n
  M : Chapter04GModule.{u, v} G
  Mdual : Chapter04GModule.{u, v} G
  μn : Chapter04GModule.{u, v} G
  nM : chapter04NAnnihilates n M
  nMdual : chapter04NAnnihilates n Mdual
  nμn : chapter04NAnnihilates n μn
  dualEquiv : Mdual.V ≃+ (M.V →+ μn.V)
  /-- The evaluation pairing is equivariant for the three displayed actions. -/
  dualEquiv_galois_compatible : ∀ (g : G) (y : Mdual.V) (x : M.V),
    dualEquiv (Mdual.ρ g y) (M.ρ g x) = μn.ρ g (dualEquiv y x)

/-! ### Additive quotients and finite-support sums -/

/-- The additive quotient by the image of a norm map. -/
def chapter04AddNormQuotient {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]
    (N : A →+ B) : Type v :=
  B ⧸ AddMonoidHom.range N

instance chapter04AddNormQuotientAddCommGroup
    {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]
    (N : A →+ B) : AddCommGroup (chapter04AddNormQuotient N) := by
  change AddCommGroup (B ⧸ AddMonoidHom.range N)
  infer_instance

/-- The book's target `ℚ / ℤ`, represented by the canonical additive quotient. -/
abbrev chapter04QModZ : Type :=
  ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

/-- The canonical representative of a rational invariant in `ℚ / ℤ`. -/
def chapter04QModZOfRat (q : ℚ) : chapter04QModZ :=
  QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) q

/- The finite coefficient range inside `ℚ / ℤ`. -/
def chapter04QModZTorsion (n : ℕ) : AddSubgroup chapter04QModZ where
  carrier := {x | n • x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change n • (x + y) = 0
    change n • x = 0 at hx
    change n • y = 0 at hy
    simp [hx, hy]
  neg_mem' := by
    intro x hx
    simpa using congrArg Neg.neg hx

@[simp] theorem chapter04_mem_QModZTorsion_iff (n : ℕ) (x : chapter04QModZ) :
    x ∈ chapter04QModZTorsion n ↔ n • x = 0 :=
  Iff.rfl

/-- Local Brauer restriction/corestriction data, with invariant maps in the book's normalization. -/
structure Chapter04LocalBrauerMapData (B₀ B₁ : Type*)
    [AddCommGroup B₀] [AddCommGroup B₁] where
  degree : ℕ
  res : B₀ →+ B₁
  cor : B₁ →+ B₀
  inv₀ : B₀ →+ chapter04QModZ
  inv₁ : B₁ →+ chapter04QModZ

/-! The maps alone do not determine the invariant normalization.  The local-field
laws are kept in a separate dependency record so that arbitrary additive maps
cannot be used to prove restriction/corestriction formulas. -/
structure Chapter04LocalBrauerMapLaws {B₀ B₁ : Type*}
    [AddCommGroup B₀] [AddCommGroup B₁]
    (D : Chapter04LocalBrauerMapData B₀ B₁) where
  positive_degree : 0 < D.degree
  restriction_formula : ∀ α : B₀,
    D.inv₁ (D.res α) = D.degree • D.inv₀ α
  corestriction_formula : ∀ β : B₁,
    D.inv₀ (D.cor β) = D.inv₁ β
  projection_formula : ∀ α : B₀,
    D.cor (D.res α) = D.degree • α

/-- The direct sum of local additive groups. -/
abbrev chapter04LocalBrauerSum (ι : Type u) (B : ι → Type v)
    [∀ i, AddCommGroup (B i)] : Type (max u v) :=
  DFinsupp B

/-- A bilinear pairing is perfect when it identifies each side with the additive dual of the
other side. -/
def chapter04PerfectPairing {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (pairing : A → B → chapter04QModZ) : Prop :=
  (∃ eA : A ≃+ (B →+ chapter04QModZ),
      ∀ x y, eA x y = pairing x y) ∧
    (∃ eB : B ≃+ (A →+ chapter04QModZ),
      ∀ y x, eB y x = pairing x y)

/-! ### Places and the missing global Brauer interface -/

/-- Finite and infinite places in one source-order index type. -/
abbrev Chapter04Place (F : Type u) [Field F] [NumberField F] : Type u :=
  NumberField.FinitePlace F ⊕ NumberField.InfinitePlace F

/-- Data for the global Brauer groups and their local invariant maps. -/
structure Chapter04BrauerContext (F : Type u) [Field F] [NumberField F] where
  Br : Type v
  [brGroup : AddCommGroup Br]
  localBr : Chapter04Place F → Type v
  [localGroup : ∀ v, AddCommGroup (localBr v)]
  localization : Br →+ chapter04LocalBrauerSum (Chapter04Place F) localBr
  invariant : ∀ v, localBr v →+ chapter04QModZ

attribute [instance] Chapter04BrauerContext.brGroup Chapter04BrauerContext.localGroup

/- Local descriptions used by the Brauer invariant theorem.  The finite-place equivalence is
required to be the invariant map itself, and the real field records the nonsplit quaternion
normalization. -/
structure Chapter04LocalBrauerBehavior
    {F : Type u} [Field F] [NumberField F]
    (D : Chapter04BrauerContext.{u, v} F) where
  complex_zero : ∀ w : NumberField.InfinitePlace F,
    NumberField.InfinitePlace.IsComplex w →
    Subsingleton (D.localBr (Sum.inr w))
  real_two_torsion : ∀ w : NumberField.InfinitePlace F,
    NumberField.InfinitePlace.IsReal w →
    ∀ x : D.localBr (Sum.inr w), 2 • x = 0
  real_half_class : ∀ w : NumberField.InfinitePlace F,
    NumberField.InfinitePlace.IsReal w →
    ∃ x : D.localBr (Sum.inr w),
      D.invariant (Sum.inr w) x = chapter04QModZOfRat ((1 : ℚ) / 2)
  real_invariant_equiv : ∀ w : NumberField.InfinitePlace F,
    NumberField.InfinitePlace.IsReal w →
      D.localBr (Sum.inr w) ≃+ chapter04QModZTorsion 2
  real_invariant_is_equiv : ∀ (w : NumberField.InfinitePlace F)
    (hw : NumberField.InfinitePlace.IsReal w) (x : D.localBr (Sum.inr w)),
    (real_invariant_equiv w hw x : chapter04QModZ) = D.invariant (Sum.inr w) x
  finite_invariant_equiv : ∀ v : NumberField.FinitePlace F,
    D.localBr (Sum.inl v) ≃+ chapter04QModZ
  finite_invariant_is_equiv : ∀ v : NumberField.FinitePlace F,
    ∀ x, finite_invariant_equiv v x = D.invariant (Sum.inl v) x

/-- The finite-support sum of the local invariant maps. -/
def chapter04BrauerInvariantSum {F : Type u} [Field F] [NumberField F]
    (D : Chapter04BrauerContext.{u, v} F) :
    chapter04LocalBrauerSum (Chapter04Place F) D.localBr →+ chapter04QModZ :=
  by
    classical
    exact DFinsupp.sumAddHom (fun v => D.invariant v)

/-- The exactness predicate for the four-term Brauer invariant row. -/
def chapter04BrauerInvariantExact {F : Type u} [Field F] [NumberField F]
    (D : Chapter04BrauerContext.{u, v} F) : Prop :=
  Function.Injective D.localization ∧
    Function.Exact D.localization (chapter04BrauerInvariantSum D) ∧
    Function.Surjective (chapter04BrauerInvariantSum D)

/-! This is the missing global realization of the abstract row above.  It is
deliberately separate from local behavior: local descriptions do not imply the
global Brauer exactness statement without the global arithmetic construction. -/
structure Chapter04BrauerInvariantSequenceData
    {F : Type u} [Field F] [NumberField F]
    (D : Chapter04BrauerContext.{u, v} F) where
  local_behavior : Chapter04LocalBrauerBehavior D
  exact_sequence : chapter04BrauerInvariantExact D

/-! ### Ideles and idele classes -/

/-- The canonical quotient of an abstract idele group by diagonal principal ideles. -/
abbrev chapter04IdeleClassQuotient (I : Type u) [CommGroup I]
    {L : Type v} [Field L] (diagonal : Lˣ →* I) : Type u :=
  I ⧸ diagonal.range

/-- The quotient map from ideles to idele classes. -/
def chapter04IdeleClassQuotientMap (I : Type u) [CommGroup I]
    {L : Type v} [Field L] (diagonal : Lˣ →* I) :
    I →* chapter04IdeleClassQuotient I diagonal :=
  QuotientGroup.mk' diagonal.range

/-- Book-facing data for an idele-class quotient and its diagonal subgroup. -/
structure Chapter04IdeleClassPresentation (L : Type*) [Field L] where
  I : Type*
  [iGroup : CommGroup I]
  diagonal : Lˣ →* I
  diagonal_injective : Function.Injective diagonal

attribute [instance] Chapter04IdeleClassPresentation.iGroup

abbrev Chapter04IdeleClassPresentation.classQuotient
    {L : Type*} [Field L] (P : Chapter04IdeleClassPresentation L) : Type* :=
  chapter04IdeleClassQuotient P.I P.diagonal

def Chapter04IdeleClassPresentation.quotientMap
    {L : Type*} [Field L] (P : Chapter04IdeleClassPresentation L) :
    P.I →* P.classQuotient :=
  chapter04IdeleClassQuotientMap P.I P.diagonal

@[simp] theorem Chapter04IdeleClassPresentation.quotientMap_diagonal
    {L : Type*} [Field L] (P : Chapter04IdeleClassPresentation L) (a : Lˣ) :
    P.quotientMap (P.diagonal a) = 1 := by
  change QuotientGroup.mk' P.diagonal.range (P.diagonal a) = 1
  exact QuotientGroup.eq_one_iff.mpr ⟨a, rfl⟩

/-! ### Compact-support cohomology and local dependency interfaces -/

/-- A finite-level compact-support/global cohomology interface.

The degree shift is recorded by `compactH M 3`, whose trace lands in `ℚ / ℤ`; the actual cone and
absolute-Galois-group construction is intentionally left to the later global-cohomology chapter.
-/
structure Chapter04CompactSupportAPI (G : Type u) [Group G] where
  globalH : Chapter04GModule.{u, v} G → ℤ → Type v
  [globalHGroup : ∀ M r, AddCommGroup (globalH M r)]
  compactH : Chapter04GModule.{u, v} G → ℤ → Type v
  [compactHGroup : ∀ M r, AddCommGroup (compactH M r)]
  trace : ∀ (M : Chapter04GModule.{u, v} G), compactH M 3 →+ chapter04QModZ
  trace_torsion : ∀ (M : Chapter04GModule.{u, v} G) (n : ℕ),
    chapter04NAnnihilates n M →
      ∀ z : compactH M 3, trace M z ∈ chapter04QModZTorsion n

attribute [instance] Chapter04CompactSupportAPI.globalHGroup
  Chapter04CompactSupportAPI.compactHGroup

abbrev chapter04GlobalH {G : Type u} [Group G]
    (C : Chapter04CompactSupportAPI.{u, v} G)
    (M : Chapter04GModule.{u, v} G) (r : ℤ) : Type v :=
  C.globalH M r

abbrev chapter04CompactSupportH {G : Type u} [Group G]
    (C : Chapter04CompactSupportAPI.{u, v} G)
    (M : Chapter04GModule.{u, v} G) (r : ℤ) : Type v :=
  C.compactH M r

/-! ### Exact two-extensions and cohomological triviality -/

/-- Vanishing of Tate cohomology on every subgroup, the book's cohomological-triviality notion. -/
def chapter04CohomologicallyTrivial {G : Type} [Group G] [Fintype G]
    (M : Chapter04GModule.{0, 0} G) : Prop :=
  ∀ (H : Subgroup G) (r : ℤ),
    IsZero (chapter04TateH (chapter04RestrictGModule M H) r)

/-- A two-extension `0 → A → X₁ → X₀ → B → 0` with its exactness data. -/
structure Chapter04TwoExtension {G : Type} [Group G] [Fintype G]
    (A : Chapter04GModule.{0, 0} G) (B : Chapter04GModule.{0, 0} G) where
  X₁ : Chapter04GModule.{0, 0} G
  X₀ : Chapter04GModule.{0, 0} G
  i : A.V →+ X₁.V
  p : X₁.V →+ X₀.V
  q : X₀.V →+ B.V
  i_injective : Function.Injective i
  p_comp_i : p.comp i = 0
  q_comp_p : q.comp p = 0
  exact_X₁ : Function.Exact i p
  exact_X₀ : Function.Exact p q
  q_surjective : Function.Surjective q
  X₁_cohomologicallyTrivial : chapter04CohomologicallyTrivial X₁
  X₀_cohomologicallyTrivial : chapter04CohomologicallyTrivial X₀

/-- A book-facing cap-product operation for a finite group and an additive module. -/
abbrev Chapter04TateCapProductAPI
    {G : Type} [Group G] [Fintype G]
    (C : Chapter04GModule.{0, 0} G)
    (u : chapter04GroupH C 2) : Type _ :=
  LastLib.Book05LocalClassFieldTheory.Chapter05.Chapter05CapProduct
    G (chapter04GModuleRep C) u

/-- The source-order interface for a fundamental class and its subgroup restrictions. -/
structure Chapter04FundamentalClass
    {G : Type} [Group G] [Fintype G] where
  C : Chapter04GModule.{0, 0} G
  /-- The fundamental class is ordinary degree-two cohomology, not Tate degree two. -/
  u : chapter04GroupH C 2
  capAPI : Chapter04TateCapProductAPI C u
  invariant : ∀ (H : Subgroup G),
    chapter04GroupH (chapter04RestrictGModule C H) 2 →+ chapter04QModZ
  invariant_normalization : ∀ (H : Subgroup G),
    invariant H (chapter04RestrictTwoClass C H u) =
      chapter04QModZOfRat ((1 : ℚ) / Nat.card H)

/-! The class-formation hypotheses are imported from the canonical finite-group
Tate--Nakayama interface.  This keeps the cap product tied to its chosen
degree-two class instead of leaving an unrelated arbitrary family of maps. -/
abbrev Chapter04ClassFormationHypotheses
    {G : Type} [Group G] [Fintype G]
    (U : Chapter04FundamentalClass (G := G)) : Type _ :=
  LastLib.Book05LocalClassFieldTheory.Chapter05.Chapter05TateNakayamaHypotheses
    G (chapter04GModuleRep U.C) U.u

end

end LastLib.Book06GlobalClassFieldTheory.Chapter04
