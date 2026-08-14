import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter08.Section03EffectivityAndFullFaithfulness

namespace LastLib
namespace Book10FaithfullyFlatDescentInAlgebraicGeometry
namespace Chapter08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Bicategory
open scoped AlgebraicGeometry

noncomputable section

universe u

/-!
## 8.4 Coherence and exactness
-/

/-- Finite locally free means locally free of finite type, matching the
module-theoretic affine criterion. -/
def Chapter08FiniteLocallyFree {S : Scheme.{u}} (M : S.Modules) : Prop :=
  M.IsLocallyFree ∧ M.IsFiniteType

/-- The stalkwise notion of a module sheaf being flat over its structure
sheaf. -/
def chapter08StalkFlatOver
    {X : Scheme.{u}} (M : X.Modules) (x : X) : Prop :=
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk M.val.presheaf x)) := by
    exact PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      M.val x
  Module.Flat (X.presheaf.stalk x)
    (↑(TopCat.Presheaf.stalk M.val.presheaf x))

/-- Flatness of a module sheaf, in the stalkwise formulation used by the
chapter. -/
def Chapter08FlatOver
    {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ x : X, chapter08StalkFlatOver M x

/-- The intrinsic rank of a module sheaf at a point. -/
def chapter08RankAtPoint {X : Scheme.{u}} (M : X.Modules) (x : X) : Cardinal :=
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk M.val.presheaf x)) := by
    exact PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      M.val x
  Module.rank (X.presheaf.stalk x)
    (↑(TopCat.Presheaf.stalk M.val.presheaf x))

/-- Finite locally free rank is unchanged by a faithfully flat pullback. -/
theorem chapter08_rank_pullback
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter08FpqcMorphism p) (M : S.Modules)
    (hM : Chapter08FiniteLocallyFree M) (t : T) :
    chapter08RankAtPoint ((Scheme.Modules.pullback p).obj M) t =
      chapter08RankAtPoint M (p t) := by
  sorry

/-- Finite type is fpqc local for quasi-coherent module sheaves. -/
theorem chapter08_finiteType_fpqc_local
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter08FpqcMorphism p) (M : S.Modules)
    (hM : M.IsQuasicoherent) :
    M.IsFiniteType ↔ ((Scheme.Modules.pullback p).obj M).IsFiniteType := by
  sorry

/-- Finite presentation is fpqc local for quasi-coherent module sheaves. -/
theorem chapter08_finitePresentation_fpqc_local
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter08FpqcMorphism p) (M : S.Modules)
    (hM : M.IsQuasicoherent) :
    M.IsFinitePresentation ↔
      ((Scheme.Modules.pullback p).obj M).IsFinitePresentation := by
  sorry

/-- Flatness of a module sheaf is fpqc local. -/
theorem chapter08_flatOver_fpqc_local
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter08FpqcMorphism p) (M : S.Modules)
    (hM : M.IsQuasicoherent) :
    Chapter08FlatOver M ↔
      Chapter08FlatOver ((Scheme.Modules.pullback p).obj M) := by
  sorry

/-- Finite local freeness is fpqc local. -/
theorem chapter08_finiteLocallyFree_fpqc_local
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter08FpqcMorphism p) (M : S.Modules)
    (hM : M.IsQuasicoherent) :
    Chapter08FiniteLocallyFree M ↔
      Chapter08FiniteLocallyFree ((Scheme.Modules.pullback p).obj M) := by
  sorry

/-- Pullback of a short complex of module sheaves along a scheme map. -/
def chapter08PullbackShortComplex
    {X Y : Scheme.{u}} (f : X ⟶ Y) (C : ShortComplex Y.Modules) :
    ShortComplex X.Modules where
  f := (Scheme.Modules.pullback f).map C.f
  g := (Scheme.Modules.pullback f).map C.g
  zero := by
    sorry

/-- Exactness of a sequence of quasi-coherent sheaves is reflected by an fpqc
pullback. -/
theorem chapter08_exact_fpqc_local
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter08FpqcMorphism p) (C : ShortComplex S.Modules)
    (h₁ : C.X₁.IsQuasicoherent) (h₂ : C.X₂.IsQuasicoherent)
    (h₃ : C.X₃.IsQuasicoherent) :
    C.Exact ↔ (chapter08PullbackShortComplex p C).Exact := by
  sorry

/-- The finite-free-kernel convention for coherence on a general scheme. -/
def Chapter08FiniteFreeKernels {S : Scheme.{u}} (M : S.Modules) : Prop :=
  ∀ (I : Type u), Finite I →
    ∀ (φ : SheafOfModules.free (R := S.ringCatSheaf) I ⟶ M),
      (kernel φ).IsFiniteType

/-- A stronger variant, useful when the chosen definition tests all finite-type
source modules rather than only finite free ones. -/
def Chapter08FiniteTypeKernels {S : Scheme.{u}} (M : S.Modules) : Prop :=
  ∀ (N : S.Modules), N.IsFiniteType → ∀ (φ : N ⟶ M),
    (kernel φ).IsFiniteType

/-- The standard noetherian convention: quasi-coherent and finite type. -/
def Chapter08NoetherianCoherent {S : Scheme.{u}} (M : S.Modules) : Prop :=
  M.IsQuasicoherent ∧ M.IsFiniteType

/-- The locally finitely presented convention for coherent quasi-coherent
sheaves. -/
def Chapter08LocallyFinitelyPresented {S : Scheme.{u}} (M : S.Modules) : Prop :=
  M.IsQuasicoherent ∧ M.IsFinitePresentation

/- The locally finitely presented convention is transported directly by the
quasi-coherent finite-presentation criterion. -/
theorem chapter08_locallyFinitelyPresented_fpqc_local
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter08FpqcMorphism p) (M : S.Modules)
    (hM : M.IsQuasicoherent) :
    Chapter08LocallyFinitelyPresented M ↔
      Chapter08LocallyFinitelyPresented ((Scheme.Modules.pullback p).obj M) := by
  sorry

/-- The more general kernel-finite convention. -/
def Chapter08KernelFiniteCoherent {S : Scheme.{u}} (M : S.Modules) : Prop :=
  M.IsQuasicoherent ∧ Chapter08FiniteFreeKernels M

/-- The hypotheses under which the chapter uses coherence descent. -/
structure Chapter08CoherenceDescentHypotheses
    {T S : Scheme.{u}} (p : T ⟶ S) where
  fpqc : Chapter08FpqcMorphism p
  baseLocallyNoetherian : IsLocallyNoetherian S

/-- On a locally noetherian scheme, finite type and finite presentation agree
for quasi-coherent sheaves. -/
theorem chapter08_coherent_iff_locallyFinitePresentation_of_locallyNoetherian
    {S : Scheme.{u}} (hS : IsLocallyNoetherian S) (M : S.Modules) :
    Chapter08NoetherianCoherent M ↔ Chapter08LocallyFinitelyPresented M := by
  sorry

/-- Under the locally noetherian convention, finite type kernels give the same
coherent sheaves. -/
theorem chapter08_kernelFinite_coherent_of_locallyNoetherian
    {S : Scheme.{u}} (hS : IsLocallyNoetherian S) (M : S.Modules)
    (hM : Chapter08NoetherianCoherent M) :
    Chapter08KernelFiniteCoherent M := by
  sorry

/-- Kernel-finite coherence descends along the quasi-compact faithfully flat
cover used in the chapter. -/
theorem chapter08_kernelFinite_coherent_fpqc_local
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter08FpqcMorphism p) (M : S.Modules) :
    Chapter08KernelFiniteCoherent M ↔
      Chapter08KernelFiniteCoherent
        ((Scheme.Modules.pullback p).obj M) := by
  sorry

end
end Chapter08
end Book10FaithfullyFlatDescentInAlgebraicGeometry
end LastLib
