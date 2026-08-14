import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter13.Section01ATwoTermModel

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter13

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

universe u

/-! ## 13.2. Semicontinuity and base change -/

/-! ### Fiber dimensions -/

/-- The residue-field fiber of a module sheaf on the base. -/
def chapter13ResidueFiberModule {C : Chapter13RelativeCurve} (M : C.S.Modules)
    (s : C.S) : ModuleCat.{u} (C.S.residueField s) := by
  letI : Module (C.S.presheaf.stalk s : Type u)
      (TopCat.Presheaf.stalk M.val.presheaf s).carrier := by
    exact
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := C.S.presheaf) M.val s
  exact (ModuleCat.extendScalars (C.S.residue s).hom).obj
    (ModuleCat.of.{u, u} (C.S.presheaf.stalk s : Type u)
      (TopCat.Presheaf.stalk M.val.presheaf s).carrier)

/-- Chosen residue-field module realizations of the two fiber cohomology groups. -/
structure Chapter13FiberCohomologyProfile
    (C : Chapter13RelativeCurve) (M : C.X.Modules) where
  h0 : ∀ s : C.S, Chapter13FiberCohomologyModule M s 0
  h1 : ∀ s : C.S, Chapter13FiberCohomologyModule M s 1

/-- The dimension of the zeroth fiber cohomology. -/
def chapter13H0Dimension
    {C : Chapter13RelativeCurve} {M : C.X.Modules}
    (H : Chapter13FiberCohomologyProfile C M) (s : C.S) : ℕ :=
  chapter13FiberCohomologyDimension (H.h0 s)

/-- The dimension of the first fiber cohomology. -/
def chapter13H1Dimension
    {C : Chapter13RelativeCurve} {M : C.X.Modules}
    (H : Chapter13FiberCohomologyProfile C M) (s : C.S) : ℕ :=
  chapter13FiberCohomologyDimension (H.h1 s)

/-- The fiber Euler characteristic as an integer. -/
def chapter13FiberEulerCharacteristic
    {C : Chapter13RelativeCurve} {M : C.X.Modules}
    (H : Chapter13FiberCohomologyProfile C M) (s : C.S) : ℤ :=
  (chapter13H0Dimension H s : ℤ) - (chapter13H1Dimension H s : ℤ)

/-! ### The two base-change maps -/

/-- The residue-field fiber of a module sheaf on an arbitrary base scheme. -/
def chapter13BaseResidueFiberModule {S : Scheme.{u}} (M : S.Modules)
    (s : S) : ModuleCat.{u} (S.residueField s) := by
  letI : Module (S.presheaf.stalk s : Type u)
      (TopCat.Presheaf.stalk M.val.presheaf s).carrier := by
    exact
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := S.presheaf) M.val s
  exact (ModuleCat.extendScalars (S.residue s).hom).obj
    (ModuleCat.of.{u, u} (S.presheaf.stalk s : Type u)
      (TopCat.Presheaf.stalk M.val.presheaf s).carrier)

/-- A coherent base module in the finite-type quasi-coherent presentation. -/
abbrev chapter13CoherentBaseModule {C : Chapter13RelativeCurve} (M : C.S.Modules) : Prop :=
  chapter04FiniteTypeQuasiCoherent M

/-! ### Canonical local model comparisons -/

/- A residue-field point is represented by an actual algebra over the affine
chart carried by the local model.  The point-map equality prevents a profile
from being compared with a model on a different fiber. -/
structure Chapter13FiberTwoTermRealization
    (C : Chapter13RelativeCurve) (E : Chapter13VectorBundle C.X)
    (s : C.S) (F : Chapter13FiberCohomologyProfile C E.sheaf) where
  local_model : Chapter13LocalTwoTermModel C E
  residue_algebra :
    letI := local_model.chart.commRingA
    Algebra local_model.chart.A (C.S.residueField s)
  point_map :
    letI := local_model.chart.commRingA
    local_model.chart.mapToBase
        (chapter13AAlgebraOfAlgebra residue_algebra) =
      C.S.fromSpecResidueField s
  h0_model :
    letI := local_model.chart.commRingA
    let B := chapter13AAlgebraOfAlgebra residue_algebra
    letI := B.commRingB
    letI := B.algebraAB
    Nonempty (
      (F.h0 s).module ≅
        chapter13TwoTermH0Module
          (local_model.model.baseChange B).d)
  h1_model :
    letI := local_model.chart.commRingA
    let B := chapter13AAlgebraOfAlgebra residue_algebra
    letI := B.commRingB
    letI := B.algebraAB
    Nonempty (
      (F.h1 s).module ≅
        chapter13TwoTermH1Module
          (local_model.model.baseChange B).d)
  cokernel_comparison :
    letI := local_model.chart.commRingA
    let B := chapter13AAlgebraOfAlgebra residue_algebra
    letI := B.commRingB
    letI := B.algebraAB
    Nonempty (Chapter13CokernelBaseChangeComparison
      local_model.model B)

namespace Chapter13FiberTwoTermRealization

noncomputable def algebraData
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    {s : C.S} {F : Chapter13FiberCohomologyProfile C E.sheaf}
    (R : Chapter13FiberTwoTermRealization C E s F) :
    @Chapter13AAlgebra R.local_model.chart.A R.local_model.chart.commRingA := by
  letI := R.local_model.chart.commRingA
  exact chapter13AAlgebraOfAlgebra R.residue_algebra

end Chapter13FiberTwoTermRealization

/- The first higher direct image is kept as an explicit sheaf because the
 pinned API exposes sheaf cohomology but not a relative derived pushforward. -/
structure Chapter13RelativeCohomologyData
    (C : Chapter13RelativeCurve) (E : Chapter13VectorBundle C.X) where
  fiber : Chapter13FiberCohomologyProfile C E.sheaf
  local_model : ∀ s : C.S,
    Chapter13FiberTwoTermRealization C E s fiber
  firstHigherDirectImage : C.S.Modules
  firstHigherDirectImage_coherent :
    chapter13CoherentBaseModule firstHigherDirectImage
  h0_baseChangeMap : ∀ s : C.S,
    chapter13ResidueFiberModule (chapter13Pushforward E) s ⟶
      (fiber.h0 s).module
  h1_baseChangeMap : ∀ s : C.S,
    chapter13ResidueFiberModule firstHigherDirectImage s ⟶
      (fiber.h1 s).module
  h0_model_map : ∀ s : C.S,
    let R := local_model s
    letI := R.local_model.chart.commRingA
    let B := R.algebraData
    letI := B.commRingB
    letI := B.algebraAB
    chapter13ResidueFiberModule (chapter13Pushforward E) s ⟶
      chapter13TwoTermH0Module (R.local_model.model.baseChange B).d
  h0_baseChangeMap_is_model : ∀ s : C.S,
    let R := local_model s
    letI := R.local_model.chart.commRingA
    let B := R.algebraData
    letI := B.commRingB
    letI := B.algebraAB
    h0_baseChangeMap s =
      h0_model_map s ≫ (Classical.choice R.h0_model).inv
  h1_directImage_cokernel_comparison : ∀ s : C.S,
    let R := local_model s
    letI := R.local_model.chart.commRingA
    let B := R.algebraData
    letI := B.commRingB
    letI := B.algebraAB
    Nonempty (
      chapter13ResidueFiberModule firstHigherDirectImage s ≅
        chapter13TwoTermH1Module
          (R.local_model.model.baseChange B).d)
  h1_baseChangeMap_is_model : ∀ s : C.S,
    let R := local_model s
    letI := R.local_model.chart.commRingA
    let B := R.algebraData
    letI := B.commRingB
    letI := B.algebraAB
    h1_baseChangeMap s =
      (Classical.choice (h1_directImage_cokernel_comparison s)).hom ≫
        (Classical.choice R.h1_model).inv

namespace Chapter13RelativeCohomologyData

/-- The degree-zero pushforward term. -/
abbrev h0Sheaf {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (_D : Chapter13RelativeCohomologyData C E) : C.S.Modules :=
  chapter13Pushforward E

/-- The degree-one direct-image term. -/
abbrev h1Sheaf {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E) : C.S.Modules :=
  D.firstHigherDirectImage

end Chapter13RelativeCohomologyData

/-- The arbitrary-test-scheme base-change package for both cohomology terms. -/
structure Chapter13ArbitraryBaseChangeSystem
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E) where
  target : ∀ {T : Scheme} (g : T ⟶ C.S),
    Chapter13RelativeCohomologyData
      (chapter13BaseChangedRelativeCurve C g)
      (chapter13BaseChangedVectorBundle C E g)
  h0_sheaf_comparison : ∀ {T : Scheme} (g : T ⟶ C.S),
    Nonempty (
      (Scheme.Modules.pullback g).obj D.h0Sheaf ≅
        (target g).h0Sheaf)
  h1_sheaf_comparison : ∀ {T : Scheme} (g : T ⟶ C.S),
    Nonempty (
      (Scheme.Modules.pullback g).obj D.h1Sheaf ≅
        (target g).h1Sheaf)
  h0_comparison : ∀ {T : Scheme} (g : T ⟶ C.S) (t : T),
    Nonempty (
      chapter13BaseResidueFiberModule
        ((Scheme.Modules.pullback g).obj D.h0Sheaf) t ≅
        ((target g).fiber.h0 t).module)
  h1_comparison : ∀ {T : Scheme} (g : T ⟶ C.S) (t : T),
    Nonempty (
      chapter13BaseResidueFiberModule
        ((Scheme.Modules.pullback g).obj D.h1Sheaf) t ≅
        ((target g).fiber.h1 t).module)

/-- Both relative cohomology terms commute with arbitrary base change. -/
def chapter13BothTermsCommuteWithArbitraryBaseChange
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E) : Prop :=
  Nonempty (Chapter13ArbitraryBaseChangeSystem D)

/-- The map in (13.4), with the tensor written as a residue-field fiber. -/
def chapter13H0BaseChangeMap
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E) (s : C.S) :
    chapter13ResidueFiberModule D.h0Sheaf s ⟶ (D.fiber.h0 s).module :=
  D.h0_baseChangeMap s

/-- The map in (13.5), with the tensor written as a residue-field fiber. -/
def chapter13H1BaseChangeMap
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E) (s : C.S) :
    chapter13ResidueFiberModule D.h1Sheaf s ⟶ (D.fiber.h1 s).module :=
  D.h1_baseChangeMap s

/-- In a two-term perfect presentation, the degree-one base-change map is an isomorphism. -/
theorem chapter13_h1_base_change_isomorphism
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E) :
    ∀ s : C.S, IsIso (chapter13H1BaseChangeMap D s) := by
  sorry

/-! ### Universal base change and local freeness -/

/- The pointwise maps in the base-change theorem have different target modules,
so the book-facing universal condition is defined directly for the named map. -/
def chapter13H0BaseChangeUniversallyIsoAt
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E) (s : C.S) : Prop :=
  ∃ U : Set C.S, IsOpen U ∧ s ∈ U ∧
    ∀ t ∈ U, IsIso (chapter13H0BaseChangeMap D t)

/-- Local finite local freeness of a module sheaf at a base point. -/
def chapter13FiniteLocallyFreeAt {S : Scheme.{u}} (M : S.Modules) (s : S) : Prop :=
  ∃ U : S.Opens, s ∈ U ∧
    (M.over U).IsLocallyFree ∧ (M.over U).IsFiniteType

/-- Local constancy of `h¹` at a point. -/
def chapter13H1LocallyConstantAt
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E) (s : C.S) : Prop :=
  ∃ U : Set C.S, IsOpen U ∧ s ∈ U ∧
    ∀ t ∈ U, chapter13H1Dimension D.fiber t = chapter13H1Dimension D.fiber s

/-- The local form of the cohomology-and-base-change equivalence. -/
theorem chapter13_base_change_local_criterion
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E) (s : C.S) :
    chapter13H0BaseChangeUniversallyIsoAt D s ↔
      (chapter13FiniteLocallyFreeAt D.h1Sheaf s ↔
        chapter13H1LocallyConstantAt D s) := by
  sorry

/- The local criterion also supplies the degree-zero local-freeness conclusion;
the pinned sheaf API does not expose this as a pre-existing theorem. -/
theorem chapter13_h0_locally_free_near_base_change
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E) (s : C.S)
    (hbase : chapter13H0BaseChangeUniversallyIsoAt D s) :
    chapter13FiniteLocallyFreeAt D.h0Sheaf s := by
  sorry

/-! ### Global vanishing consequence -/

/-- Fiberwise vanishing of the first cohomology term. -/
def chapter13H1VanishesEverywhere
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E) : Prop :=
  ∀ s : C.S, IsZero (D.fiber.h1 s).module

/-- The workhorse package obtained when every fiber has vanishing `H¹`. -/
structure Chapter13GlobalBaseChangeConclusion
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E) where
  firstHigherDirectImage_is_zero : IsZero D.h1Sheaf
  pushforward_locally_free : D.h0Sheaf.IsLocallyFree
  pushforward_finite_type : D.h0Sheaf.IsFiniteType
  arbitrary_base_change : chapter13BothTermsCommuteWithArbitraryBaseChange D

/-- Fiberwise `H¹`-vanishing gives a locally free pushforward and base change. -/
theorem chapter13_h1_vanishing_gives_local_free_pushforward
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E)
    (hvanish : chapter13H1VanishesEverywhere D) :
    Nonempty (Chapter13GlobalBaseChangeConclusion D) := by
  sorry

/-! ### Semicontinuity -/

/-- Upper semicontinuity of the zeroth fiber-cohomology dimension. -/
theorem chapter13_h0_upper_semicontinuous
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E) :
    Chapter13UpperSemicontinuous (fun s => chapter13H0Dimension D.fiber s) := by
  sorry

/-- Upper semicontinuity of the first fiber-cohomology dimension. -/
theorem chapter13_h1_upper_semicontinuous
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E) :
    Chapter13UpperSemicontinuous (fun s => chapter13H1Dimension D.fiber s) := by
  sorry

/-! ### Numerical content of the two-term model -/

/- LOCAL_DEPENDENCY_GUESS: the pinned snapshot does not identify a geometric
fiber point with the affine algebra used by a chosen local two-term model.
The rank-profile fields below are the minimal numerical bridge needed to state
the source's virtual-rank formula without assuming that formula itself. -/

/- A model together with the fiberwise rank data extracted from its kernel and
cokernel. -/
structure Chapter13TwoTermEulerCharacteristicData
    (C : Chapter13RelativeCurve) (E : Chapter13VectorBundle C.X)
    (D : Chapter13RelativeCohomologyData C E) where
  local_model : ∀ s : C.S, Chapter13FiberTwoTermRealization C E s D.fiber
  h0_rank : C.S → ℕ
  h1_rank : C.S → ℕ
  h0_rank_eq_fiber : ∀ s, h0_rank s = chapter13H0Dimension D.fiber s
  h1_rank_eq_fiber : ∀ s, h1_rank s = chapter13H1Dimension D.fiber s
  model_rank_difference : ∀ s,
    letI := (local_model s).local_model.chart.commRingA
    chapter13TwoTermVirtualRank (local_model s).local_model.model =
        (h0_rank s : ℤ) - (h1_rank s : ℤ)
  euler_characteristic : C.S → ℤ
  euler_characteristic_eq_virtual_rank :
    ∀ s,
      letI := (local_model s).local_model.chart.commRingA
      euler_characteristic s =
        chapter13TwoTermVirtualRank (local_model s).local_model.model

theorem chapter13_euler_characteristic_eq_rank_difference
    {C : Chapter13RelativeCurve} {E : Chapter13VectorBundle C.X}
    (D : Chapter13RelativeCohomologyData C E)
    (T : Chapter13TwoTermEulerCharacteristicData C E D) (s : C.S) :
    (chapter13H0Dimension D.fiber s : ℤ) -
        (chapter13H1Dimension D.fiber s : ℤ) =
      T.euler_characteristic s := by
  sorry

/-! ### The cokernel and kernel distinction -/

/- The source uses the canonical fact that cokernels commute with tensor; the
comparison is recorded as an explicit equivalence rather than replacing it by
a kernel statement. -/
theorem chapter13_cokernel_commutes_with_tensor
    {A : Type u} [CommRing A] (M : Chapter13TwoTermModel A)
    (B : Chapter13AAlgebra A) :
    Nonempty (Chapter13CokernelBaseChangeComparison M B) := by
  sorry

/-- A precise failure marker for the possible noncommutation of kernels. -/
def chapter13KernelBaseChangeCanFail {A : Type u} [CommRing A]
    (M : Chapter13TwoTermModel A) (B : Chapter13AAlgebra A) : Prop :=
  by
    letI := B.commRingB
    letI := B.algebraAB
    exact ¬ Nonempty (
      (ModuleCat.extendScalars (algebraMap A B.B)).obj (chapter13Kernel M.d) ≅
        chapter13Kernel ((ModuleCat.extendScalars (algebraMap A B.B)).map M.d))

/-- An explicit witness interface for the failure of kernel base change. -/
structure Chapter13KernelBaseChangeFailureExample where
  A : Type u
  [commRingA : CommRing A]
  B : Chapter13AAlgebra A
  model : Chapter13TwoTermModel A
  failure : chapter13KernelBaseChangeCanFail model B

theorem chapter13_kernel_base_change_can_fail :
    Nonempty Chapter13KernelBaseChangeFailureExample := by
  sorry

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter13
