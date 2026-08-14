import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03.Dependencies
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03.Section01TensorProductsDetectExactness
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03.Section02TheAmitsurEqualizer

/-!
# 3.3 Purity and descent tests
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03

open scoped TensorProduct

local instance chapter03ZModTwoTrivSqZeroExtCommRing :
    CommRing (TrivSqZeroExt ℤ (ZMod 2)) :=
  by
    letI : Module ℤᵐᵒᵖ (ZMod 2) := chapter03ZModTwoOppositeModule
    letI : IsCentralScalar ℤ (ZMod 2) := ⟨fun _ _ => rfl⟩
    exact TrivSqZeroExt.commRing

def Chapter03PureAlgebraMap (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∀ (M : Type*) [AddCommGroup M] [Module A M],
    Function.Injective (chapter03TensorUnitMap A B M)

theorem chapter03_faithfullyFlat_pure
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
    Chapter03PureAlgebraMap A B := by
  intro M _ _
  exact Module.FaithfullyFlat.tensorProduct_mk_injective M

theorem chapter03_pure_does_not_imply_flat :
    Chapter03PureAlgebraMap ℤ (TrivSqZeroExt ℤ (ZMod 2)) ∧
      ¬ Module.Flat ℤ (TrivSqZeroExt ℤ (ZMod 2)) := by
  constructor
  · intro M _ _
    let p : TrivSqZeroExt ℤ (ZMod 2) →ₗ[ℤ] ℤ :=
      (TrivSqZeroExt.fstHom ℤ ℤ (ZMod 2)).toLinearMap
    let q : (TrivSqZeroExt ℤ (ZMod 2)) ⊗[ℤ] M →ₗ[ℤ] M :=
      (TensorProduct.lid ℤ M).toLinearMap ∘ₗ p.rTensor M
    have hleft : q.comp (chapter03TensorUnitMap ℤ (TrivSqZeroExt ℤ (ZMod 2)) M) =
        LinearMap.id := by
      ext m
      change TensorProduct.lid ℤ M
        (p.rTensor M ((1 : TrivSqZeroExt ℤ (ZMod 2)) ⊗ₜ[ℤ] m)) = m
      rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      simp only [p]
      rw [show p 1 = (1 : ℤ) by rfl]
      exact (Module.toDistribMulAction (R := ℤ) (M := M)).one_smul m
    intro x y hxy
    have hq := congrArg q hxy
    have hleftx := LinearMap.congr_fun hleft x
    have hlefty := LinearMap.congr_fun hleft y
    calc
      x = q (chapter03TensorUnitMap ℤ (TrivSqZeroExt ℤ (ZMod 2)) M x) := hleftx.symm
      _ = q (chapter03TensorUnitMap ℤ (TrivSqZeroExt ℤ (ZMod 2)) M y) := hq
      _ = y := hlefty
  · intro hflat
    have hzero : (2 : ℤ) •
        (TrivSqZeroExt.inr (1 : ZMod 2) : TrivSqZeroExt ℤ (ZMod 2)) = 0 := by
      rw [← TrivSqZeroExt.inr_smul]
      have htwo : (2 : ZMod 2) = 0 := by rfl
      simp [htwo]
    have htf : Module.IsTorsionFree ℤ (TrivSqZeroExt ℤ (ZMod 2)) :=
      @Module.Flat.isTorsionFree ℤ (TrivSqZeroExt ℤ (ZMod 2)) _ _ _ hflat
    rcases (Module.isTorsionFree_iff_smul_eq_zero.mp htf) 2
        (TrivSqZeroExt.inr (1 : ZMod 2)) hzero with h2 | hmem
    · norm_num at h2
    · exact one_ne_zero (TrivSqZeroExt.inr_injective hmem)

theorem chapter03_finite_generation_descends
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B]
    [Module.Finite B (B ⊗[A] M)] :
    Module.Finite A M :=
  Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

def Chapter03FiniteGeneratorFamily (R M : Type*) [CommSemiring R] [AddCommMonoid M]
    [Module R M] (n : ℕ) (m : Fin n → M) : Prop :=
  Submodule.span R (Set.range m) = ⊤

def chapter03TensorGeneratorFamily
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] {n : ℕ} (m : Fin n → M) :
    Fin n → B ⊗[A] M :=
  fun i => (1 : B) ⊗ₜ[A] m i

theorem chapter03_tensor_generator_family_descends
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B] {n : ℕ}
    (m : Fin n → M)
    (hm : Chapter03FiniteGeneratorFamily B (B ⊗[A] M) n
      (chapter03TensorGeneratorFamily (A := A) (B := B) (M := M) m)) :
    Chapter03FiniteGeneratorFamily A M n m := by
  change Submodule.span A (Set.range m) = ⊤
  have hgen : Set.range
      (chapter03TensorGeneratorFamily (A := A) (B := B) (M := M) m) =
      (TensorProduct.mk A B M 1) '' Set.range m := by
    change Set.range (fun i => (TensorProduct.mk A B M 1) (m i)) =
      (TensorProduct.mk A B M 1) '' Set.range m
    exact Set.range_comp' _ _
  apply le_antisymm le_top
  · apply (Submodule.baseChange_le_iff (p := (⊤ : Submodule A M))
        (q := Submodule.span A (Set.range m)) (A := B)).mp
    rw [Submodule.baseChange_top, Submodule.baseChange_span]
    have hm' : Submodule.span B
        ((TensorProduct.mk A B M 1) '' Set.range m) = ⊤ := by
      rw [← hgen]
      exact hm
    exact le_of_eq hm'.symm

/-- Provisional Chapter 6-facing interface for descent of finite presentations of modules. -/
theorem chapter03_finite_presentation_descends
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B]
    [Module.FinitePresentation B (B ⊗[A] M)] :
    Module.FinitePresentation A M := by
  have hfinite : Module.Finite A M :=
    chapter03_finite_generation_descends (A := A) (B := B) (M := M)
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  have inst := Module.finitePresentation_of_projective B
    (B ⊗[A] (Fin n → A))
  have hfB : Function.Surjective (f.baseChange B) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective B hf
  have h_exact :
      Function.Exact ((LinearMap.ker f).subtype.baseChange B) (f.baseChange B) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_exact B (LinearMap.exact_subtype_ker_map f))
  let u : B ⊗[A] LinearMap.ker f →ₗ[B] LinearMap.ker (f.baseChange B) :=
    LinearMap.codRestrict _ ((LinearMap.ker f).subtype.baseChange B)
      (fun x => h_exact.apply_apply_eq_zero x)
  have hu : Function.Bijective u := by
    constructor
    · intro x y hxy
      apply (show Function.Injective ((LinearMap.ker f).subtype.baseChange B) from by
        rw [LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_preserves_injective_linearMap _
          (Submodule.injective_subtype _))
      exact congrArg Subtype.val hxy
    · intro y
      have hy : (y : B ⊗[A] (Fin n → A)) ∈
          LinearMap.range ((LinearMap.ker f).subtype.baseChange B) := by
        exact Eq.mp
          (congrArg (fun K : Submodule B (B ⊗[A] (Fin n → A)) =>
            (y.1 : B ⊗[A] (Fin n → A)) ∈ K) (LinearMap.exact_iff.mp h_exact)) y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
  let e := LinearEquiv.ofBijective u hu
  have hker_fg : (LinearMap.ker (f.baseChange B)).FG :=
    Module.FinitePresentation.fg_ker (f.baseChange B) hfB
  have hker_finite : Module.Finite B (LinearMap.ker (f.baseChange B)) :=
    Module.Finite.of_fg hker_fg
  have hbase_finite : Module.Finite B (B ⊗[A] LinearMap.ker f) := by
    rw [Module.Finite.equiv_iff e]
    exact hker_finite
  have hfinite_ker : Module.Finite A (LinearMap.ker f) :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  apply Module.finitePresentation_of_surjective f hf
  rw [← Module.Finite.iff_fg]
  exact hfinite_ker

def Chapter03ProjectivityDescentHypotheses (A M : Type*) [CommRing A] [AddCommGroup M]
    [Module A M] : Prop :=
  Module.FinitePresentation A M ∧ Module.Flat A M

theorem chapter03_projective_of_finite_presentation_and_flat
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] [Module.Flat A M] :
    Module.Projective A M :=
  Module.Flat.projective_of_finitePresentation

def Chapter03LinearEquationSolution
    {A M N : Type*} [CommRing A] [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N] (f : M →ₗ[A] N) (b : N) (x : M) : Prop :=
  f x = b

theorem chapter03_finite_linear_system_solution_descends
    {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    [Module.Finite A N] [Module.FaithfullyFlat A B]
    (f : M →ₗ[A] N) (b : N) (x : B ⊗[A] M)
    (hsolve : (f.lTensor B) x = chapter03TensorUnitMap A B N b)
    (hinvariant : chapter03AmitsurInvariant A B M x) :
    ∃ y : M, Chapter03LinearEquationSolution f b y := by
  have hxrange : x ∈ Set.range (chapter03ModuleAmitsurAugmentation A B M) := by
    rw [← chapter03_module_amitsur_equalizer_eq_range]
    exact hinvariant
  rcases hxrange with ⟨y, rfl⟩
  refine ⟨y, ?_⟩
  apply (chapter03_module_amitsur_augmentation_injective (A := A) (B := B) (M := N))
  simpa [chapter03ModuleAmitsurAugmentation, chapter03TensorUnitMap] using hsolve

theorem chapter03_zero_test
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A B] :
    Subsingleton (B ⊗[A] M) ↔ Subsingleton M :=
  chapter03_tensor_vanishes_iff

theorem chapter03_injective_test
    {A B M M' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [AddCommGroup M'] [Module A M] [Module A M']
    [Module.FaithfullyFlat A B] (u : M →ₗ[A] M') :
    Function.Injective (u.lTensor B) ↔ Function.Injective u := by
  exact (chapter03_tensor_injective_iff u).symm

theorem chapter03_surjective_test
    {A B M M' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [AddCommGroup M'] [Module A M] [Module A M']
    [Module.FaithfullyFlat A B] (u : M →ₗ[A] M') :
    Function.Surjective (u.lTensor B) ↔ Function.Surjective u := by
  exact (chapter03_tensor_surjective_iff u).symm

theorem chapter03_zero_map_test
    {A B M M' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [AddCommGroup M'] [Module A M] [Module A M']
    [Module.FaithfullyFlat A B] (u : M →ₗ[A] M') :
    u.lTensor B = 0 ↔ u = 0 := by
  exact (chapter03_tensor_zero_iff u).symm

theorem chapter03_exactness_test
    {A B M' M M'' : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M'']
    [Module A M'] [Module A M] [Module A M''] [Module.FaithfullyFlat A B]
    (u : M' →ₗ[A] M) (v : M →ₗ[A] M'') :
    Function.Exact (u.lTensor B) (v.lTensor B) ↔ Function.Exact u v :=
  (chapter03_tensor_exact_iff u v).symm

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter03
