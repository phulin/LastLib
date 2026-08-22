import LastLib.Book04AdelesAndIdeles.Chapter04.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open Set Filter
open NumberField IsDedekindDomain
open Module
open LastLib.Book04AdelesAndIdeles.Chapter03
open scoped BigOperators TensorProduct Topology RestrictedProduct

/- The tensor products in this section use the finite-dimensional module
topology induced by a finite `K`-basis, as in the scalar-extension discussion
of Section 4.4; the lattice comparison theorem records independence of the
integral model. -/

/-! ### 4.7 Linear algebra over the adele ring -/

structure Chapter04Lattice
    (K V : Type*) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [Module.Finite K V] [IsScalarTower (𝓞 K) K V] where
  carrier : Submodule (𝓞 K) V
  finite : Module.Finite (𝓞 K) carrier
  full : ∀ v : V, ∃ a : 𝓞 K, a ≠ 0 ∧ (a : K) • v ∈ carrier

@[ext]
theorem chapter04Lattice_ext
    (K V : Type*) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [Module.Finite K V] [IsScalarTower (𝓞 K) K V]
    {M N : Chapter04Lattice K V}
    (hcarrier : M.carrier = N.carrier) :
    M = N := by
  cases M
  cases N
  simp_all

def chapter04IsLattice
    (K V : Type*) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [Module.Finite K V] [IsScalarTower (𝓞 K) K V]
    (M : Submodule (𝓞 K) V) : Prop :=
  Module.Finite (𝓞 K) M ∧
    ∀ v : V, ∃ a : 𝓞 K, a ≠ 0 ∧ (a : K) • v ∈ M

theorem chapter04Lattice.is_lattice
    (K V : Type*) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [Module.Finite K V] [IsScalarTower (𝓞 K) K V]
    (M : Chapter04Lattice K V) :
    chapter04IsLattice K V M.carrier :=
  ⟨M.finite, M.full⟩

local instance chapter04TensorRightModule
    (K B V : Type*) [Field K] [CommRing B] [Algebra K B]
    [AddCommGroup V] [Module K V] : Module B (V ⊗[K] B) where
  smul b x := TensorProduct.map
    (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B b) x
  one_smul := by
    intro z
    induction z with
    | zero =>
        change TensorProduct.map
          (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B 1) 0 = 0
        exact (TensorProduct.map
          (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B 1)).map_zero
    | tmul v b =>
        change v ⊗ₜ[K] (1 * b) = v ⊗ₜ[K] b
        rw [one_mul]
    | add z₁ z₂ ih₁ ih₂ =>
        change TensorProduct.map
          (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B 1) (z₁ + z₂) = z₁ + z₂
        have h₁ : TensorProduct.map
            (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B 1) z₁ = z₁ := ih₁
        have h₂ : TensorProduct.map
            (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B 1) z₂ = z₂ := ih₂
        rw [map_add, h₁, h₂]
  mul_smul := by
    intro x y z
    induction z with
    | zero =>
        change TensorProduct.map
          (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B (x * y)) 0 =
          TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B x)
            (TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B y) 0)
        simp only [map_zero]
    | tmul v b =>
        change v ⊗ₜ[K] ((x * y) * b) = v ⊗ₜ[K] (x * (y * b))
        rw [mul_assoc]
    | add z₁ z₂ ih₁ ih₂ =>
        change TensorProduct.map
          (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B (x * y)) (z₁ + z₂) =
          TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B x)
            (TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B y)
              (z₁ + z₂))
        have h₁ : TensorProduct.map
            (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B (x * y)) z₁ =
            TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B x)
              (TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B y) z₁) := ih₁
        have h₂ : TensorProduct.map
            (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B (x * y)) z₂ =
            TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B x)
              (TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B y) z₂) := ih₂
        rw [map_add, map_add, h₁, h₂]
        exact ((TensorProduct.map
          (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B x)).map_add _ _).symm
  smul_add := by
    intro b x y
    change TensorProduct.map
      (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B b) (x + y) =
      TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B b) x +
        TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B b) y
    exact (TensorProduct.map
      (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B b)).map_add x y
  smul_zero := by
    intro b
    change TensorProduct.map
      (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B b) 0 = 0
    exact (TensorProduct.map
      (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B b)).map_zero
  add_smul := by
    intro x y z
    induction z with
    | zero =>
        change TensorProduct.map
          (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B (x + y)) 0 =
          TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B x) 0 +
            TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B y) 0
        rw [map_zero, map_zero, map_zero, add_zero]
    | tmul v b =>
        change v ⊗ₜ[K] ((x + y) * b) = v ⊗ₜ[K] (x * b) + v ⊗ₜ[K] (y * b)
        rw [add_mul, TensorProduct.tmul_add]
    | add z₁ z₂ ih₁ ih₂ =>
        change TensorProduct.map
          (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B (x + y)) (z₁ + z₂) =
          TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B x)
              (z₁ + z₂) +
            TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B y)
              (z₁ + z₂)
        have h₁ : TensorProduct.map
            (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B (x + y)) z₁ =
            TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B x) z₁ +
              TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B y) z₁ := ih₁
        have h₂ : TensorProduct.map
            (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B (x + y)) z₂ =
            TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B x) z₂ +
              TensorProduct.map (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B y) z₂ := ih₂
        rw [map_add, h₁, h₂, map_add, map_add, add_add_add_comm]
  zero_smul := by
    intro z
    induction z with
    | zero =>
        change TensorProduct.map
          (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B 0) 0 = 0
        exact (TensorProduct.map
          (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B 0)).map_zero
    | tmul v b =>
        change v ⊗ₜ[K] (0 * b) = 0
        rw [zero_mul, TensorProduct.tmul_zero]
    | add z₁ z₂ ih₁ ih₂ =>
        change TensorProduct.map
          (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B 0) (z₁ + z₂) = 0
        have h₁ : TensorProduct.map
            (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B 0) z₁ = 0 := ih₁
        have h₂ : TensorProduct.map
            (LinearMap.id : V →ₗ[K] V) (Algebra.lmul K B 0) z₂ = 0 := ih₂
        rw [map_add, h₁, h₂, add_zero]

def chapter04LocalScalarExtensionMap
    (K V : Type*) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V]
    (v : Chapter04FinitePlace K) :
    V →ₗ[K] V ⊗[K] Chapter04FiniteLocalField K v :=
  (TensorProduct.mk K V (Chapter04FiniteLocalField K v)).flip 1

section Chapter04LatticeContext

variable {K V : Type*} [Field K] [NumberField K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [Module.Finite K V] [IsScalarTower (𝓞 K) K V]

def chapter04LocalLatticeGenerators
    (M : Chapter04Lattice K V) (v : Chapter04FinitePlace K) :
    Set (V ⊗[K] Chapter04FiniteLocalField K v) :=
  Set.range (fun z : M.carrier × Chapter04FiniteLocalIntegerRing K v =>
    TensorProduct.mk K V (Chapter04FiniteLocalField K v) z.1.1
      (z.2 : Chapter04FiniteLocalField K v))

def chapter04LocalLattice
    (M : Chapter04Lattice K V) (v : Chapter04FinitePlace K) :
    AddSubgroup (V ⊗[K] Chapter04FiniteLocalField K v) :=
  AddSubgroup.closure (chapter04LocalLatticeGenerators M v)

theorem chapter04_local_lattice_is_generated_by_the_global_lattice
    (M : Chapter04Lattice K V) (v : Chapter04FinitePlace K) :
    chapter04LocalLattice M v =
      AddSubgroup.closure (chapter04LocalLatticeGenerators M v) := by
  rfl

abbrev Chapter04AdelicVectorSpace
    (K V : Type*) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] :=
  V ⊗[K] Chapter04AdeleRing K

noncomputable instance chapter04AdelicVectorSpaceTopologicalSpace
    (K V : Type*) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module.Finite K V] :
    TopologicalSpace (Chapter04AdelicVectorSpace K V) :=
  chapter04TensorProductTopology K (Chapter04AdeleRing K) V

noncomputable instance chapter04FiniteTensorProductTopologicalSpace
    (K V : Type*) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (v : Chapter04FinitePlace K) :
    TopologicalSpace (V ⊗[K] Chapter04FiniteLocalField K v) :=
  chapter04TensorProductTopology K (Chapter04FiniteLocalField K v) V

noncomputable instance chapter04InfiniteTensorProductTopologicalSpace
    (K V : Type*) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] :
    TopologicalSpace (V ⊗[K] Chapter04InfiniteAdeleRing K) :=
  chapter04TensorProductTopology K (Chapter04InfiniteAdeleRing K) V

abbrev Chapter04AdelicVectorSpaceFiniteTail
    (M : Chapter04Lattice K V) :=
  Chapter03AdditiveRestrictedProduct
    (G := fun v : Chapter04FinitePlace K =>
      V ⊗[K] Chapter04FiniteLocalField K v)
    (fun v : Chapter04FinitePlace K =>
      chapter04LocalLattice M v)

abbrev Chapter04AdelicVectorSpaceRestrictedProduct
    (M : Chapter04Lattice K V) :=
  (V ⊗[K] Chapter04InfiniteAdeleRing K) ×
    Chapter04AdelicVectorSpaceFiniteTail M

theorem chapter04_adelic_vector_space_is_infinite_times_restricted_finite
    (M : Chapter04Lattice K V) :
    Nonempty (Chapter04AdelicVectorSpace K V ≃+
      Chapter04AdelicVectorSpaceRestrictedProduct M) := by
  sorry

theorem chapter04_adelic_vector_space_topology_is_the_restricted_product_topology
    (M : Chapter04Lattice K V) :
    ∃ e : Chapter04AdelicVectorSpace K V ≃+
        Chapter04AdelicVectorSpaceRestrictedProduct M,
      Continuous e ∧ Continuous e.symm := by
  sorry

def chapter04LatticeLocalAgreementOutside
    (M N : Chapter04Lattice K V) : Prop :=
  ∃ S : Set (Chapter04FinitePlace K), S.Finite ∧
    ∀ v, v ∉ S → chapter04LocalLattice M v = chapter04LocalLattice N v

theorem chapter04_two_lattices_agree_locally_outside_finitely_many_places
    (M N : Chapter04Lattice K V) :
    chapter04LatticeLocalAgreementOutside M N := by
  sorry

theorem chapter04_adelic_vector_space_topology_is_independent_of_the_lattice
    (M N : Chapter04Lattice K V) :
    ∃ e : Chapter04AdelicVectorSpaceRestrictedProduct M ≃+
        Chapter04AdelicVectorSpaceRestrictedProduct N,
      (∀ x, (e x).1 = x.1 ∧ (e x).2.1 = x.2.1) ∧
      Continuous e ∧ Continuous e.symm := by
  sorry

theorem chapter04_adelic_vector_space_is_coordinatewise_after_a_basis
    (M : Chapter04Lattice K V)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) :
    ∃ e : Chapter04AdelicVectorSpace K V ≃+
        (ι → Chapter04AdeleRing K),
      Continuous e ∧ Continuous e.symm := by
  sorry

end Chapter04LatticeContext

def chapter04AdelicLinearMap
    {V W : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
  (T : V →ₗ[K] W) :
    (V ⊗[K] Chapter04AdeleRing K) →ₗ[K]
      (W ⊗[K] Chapter04AdeleRing K) :=
  TensorProduct.map T
    (LinearMap.id : Chapter04AdeleRing K →ₗ[K] Chapter04AdeleRing K)

def chapter04LocalAdelicLinearMap
    {V W : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    (T : V →ₗ[K] W) (v : Chapter04FinitePlace K) :
    (V ⊗[K] Chapter04FiniteLocalField K v) →ₗ[K]
      (W ⊗[K] Chapter04FiniteLocalField K v) :=
  TensorProduct.map T
    (LinearMap.id : Chapter04FiniteLocalField K v →ₗ[K]
      Chapter04FiniteLocalField K v)

@[simp]
theorem chapter04AdelicLinearMap_apply_tmul
    {V W : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    (T : V →ₗ[K] W) (v : V) (a : Chapter04AdeleRing K) :
    chapter04AdelicLinearMap T (v ⊗ₜ[K] a) = T v ⊗ₜ[K] a := by
  sorry

theorem chapter04_adelic_linear_map_is_continuous
    {V W : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    [Module.Finite K V] [Module.Finite K W]
    (T : V →ₗ[K] W) :
    Continuous (chapter04AdelicLinearMap T) := by
  sorry

def chapter04AdelicLinearMapOverAdeleRing
    {V W : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    (T : V →ₗ[K] W) :
    (V ⊗[K] Chapter04AdeleRing K) →ₗ[Chapter04AdeleRing K]
      (W ⊗[K] Chapter04AdeleRing K) where
  toFun := chapter04AdelicLinearMap T
  map_add' := by
    intro x y
    exact map_add (chapter04AdelicLinearMap T) x y
  map_smul' := by
    sorry

def chapter04AdelicLinearMapPreservesLatticeAlmostAll
    {V W : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    [Module (𝓞 K) V] [Module (𝓞 K) W]
    [Module.Finite K V] [Module.Finite K W]
    [IsScalarTower (𝓞 K) K V] [IsScalarTower (𝓞 K) K W]
    (T : V →ₗ[K] W) (M : Chapter04Lattice K V) (N : Chapter04Lattice K W) : Prop :=
  ∃ d : 𝓞 K, d ≠ 0 ∧
    ∃ S : Set (Chapter04FinitePlace K), S.Finite ∧
      ∀ v, v ∉ S →
        ∀ x ∈ chapter04LocalLattice M v,
          chapter04LocalAdelicLinearMap T v ((d : K) • x) ∈
            chapter04LocalLattice N v

theorem chapter04_linear_maps_preserve_integral_models_after_a_common_denominator
    {V W : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    [Module (𝓞 K) V] [Module (𝓞 K) W]
    [Module.Finite K V] [Module.Finite K W]
    [IsScalarTower (𝓞 K) K V] [IsScalarTower (𝓞 K) K W]
    (T : V →ₗ[K] W) (M : Chapter04Lattice K V) (N : Chapter04Lattice K W) :
    chapter04AdelicLinearMapPreservesLatticeAlmostAll T M N := by
  sorry

def chapter04AdelicKernel
    {V W : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    (T : V →ₗ[K] W) :
    Submodule (Chapter04AdeleRing K)
      (V ⊗[K] Chapter04AdeleRing K) :=
  (chapter04AdelicLinearMapOverAdeleRing T).ker

theorem chapter04_adelic_kernel_commutes_with_scalar_extension
    {V W : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    (T : V →ₗ[K] W) :
    Nonempty ((LinearMap.ker T ⊗[K] Chapter04AdeleRing K) ≃ₗ[
      Chapter04AdeleRing K]
      chapter04AdelicKernel T) := by
  sorry

theorem chapter04_adelic_image_of_an_invertible_map_is_open_and_closed
    {V W : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    [Module.Finite K V] [Module.Finite K W]
    (e : V ≃ₗ[K] W) :
    IsOpen (Set.range (chapter04AdelicLinearMap e.toLinearMap)) ∧
      IsClosed (Set.range (chapter04AdelicLinearMap e.toLinearMap)) := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter04
