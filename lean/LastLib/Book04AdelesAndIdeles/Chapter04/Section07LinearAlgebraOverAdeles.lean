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
  classical
  have hcommon : ∃ a : 𝓞 K, a ≠ 0 ∧
      (∀ x : V, x ∈ M.carrier → (a : K) • x ∈ N.carrier) ∧
      (∀ x : V, x ∈ N.carrier → (a : K) • x ∈ M.carrier) := by
    rcases (Submodule.fg_def.mp M.finite.fg_top) with ⟨sM, hsM, hspanM⟩
    rcases (Submodule.fg_def.mp N.finite.fg_top) with ⟨sN, hsN, hspanN⟩
    let dM : M.carrier → 𝓞 K := fun x => Classical.choose (N.full x.1)
    let dN : N.carrier → 𝓞 K := fun x => Classical.choose (M.full x.1)
    have hdM : ∀ x : M.carrier, dM x ≠ 0 ∧
        ((dM x : K) • (x : V) ∈ N.carrier) := by
      intro x
      exact Classical.choose_spec (N.full x.1)
    have hdN : ∀ x : N.carrier, dN x ≠ 0 ∧
        ((dN x : K) • (x : V) ∈ M.carrier) := by
      intro x
      exact Classical.choose_spec (M.full x.1)
    let pM : 𝓞 K := ∏ x ∈ hsM.toFinset, dM x
    let pN : 𝓞 K := ∏ x ∈ hsN.toFinset, dN x
    have hpM : pM ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr (fun x hx => (hdM x).1)
    have hpN : pN ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr (fun x hx => (hdN x).1)
    have hM : ∀ x : V, x ∈ M.carrier →
        (pM : K) • x ∈ N.carrier := by
      intro x hx
      have hx' : (⟨x, hx⟩ : M.carrier) ∈ Submodule.span (𝓞 K) sM := by
        rw [hspanM]
        exact Submodule.mem_top
      refine Submodule.span_induction (R := 𝓞 K) (s := sM)
        (x := (⟨x, hx⟩ : M.carrier)) (p := fun y _ =>
          (pM : K) • (y : V) ∈ N.carrier) ?_ ?_ ?_ ?_ hx'
      · intro y hy
        obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem dM
          (hsM.mem_toFinset.mpr hy)
        rw [show pM = dM y * c by exact hc]
        have hmem := N.carrier.smul_mem c (hdM y).2
        rw [← smul_assoc] at hmem
        simpa [Algebra.smul_def, map_mul, mul_comm] using hmem
      · simpa using N.carrier.zero_mem
      · intro y z _ _ hy hz
        simpa [smul_add] using N.carrier.add_mem hy hz
      · intro c y _ hy
        simpa [smul_smul, mul_comm] using N.carrier.smul_mem c hy
    have hN : ∀ x : V, x ∈ N.carrier →
        (pN : K) • x ∈ M.carrier := by
      intro x hx
      have hx' : (⟨x, hx⟩ : N.carrier) ∈ Submodule.span (𝓞 K) sN := by
        rw [hspanN]
        exact Submodule.mem_top
      refine Submodule.span_induction (R := 𝓞 K) (s := sN)
        (x := (⟨x, hx⟩ : N.carrier)) (p := fun y _ =>
          (pN : K) • (y : V) ∈ M.carrier) ?_ ?_ ?_ ?_ hx'
      · intro y hy
        obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem dN
          (hsN.mem_toFinset.mpr hy)
        rw [show pN = dN y * c by exact hc]
        have hmem := M.carrier.smul_mem c (hdN y).2
        rw [← smul_assoc] at hmem
        simpa [Algebra.smul_def, map_mul, mul_comm] using hmem
      · simpa using M.carrier.zero_mem
      · intro y z _ _ hy hz
        simpa [smul_add] using M.carrier.add_mem hy hz
      · intro c y _ hy
        simpa [smul_smul, mul_comm] using M.carrier.smul_mem c hy
    refine ⟨pM * pN, mul_ne_zero hpM hpN, ?_, ?_⟩
    · intro x hx
      have hmem := N.carrier.smul_mem pN (hM x hx)
      rw [← smul_assoc] at hmem
      simpa [Algebra.smul_def, map_mul, mul_comm] using hmem
    · intro x hx
      have hmem := M.carrier.smul_mem pM (hN x hx)
      rw [← smul_assoc] at hmem
      simpa [Algebra.smul_def, map_mul, mul_comm] using hmem
  rcases hcommon with ⟨a, ha, hMN, hNM⟩
  let hlocal_inclusion : ∀ (P Q : Chapter04Lattice K V),
      (∀ x : V, x ∈ P.carrier → (a : K) • x ∈ Q.carrier) →
      ∀ v : Chapter04FinitePlace K,
        (a : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        ((a : v.adicCompletion K)⁻¹) ∈ v.adicCompletionIntegers K →
        chapter04LocalLattice P v ≤ chapter04LocalLattice Q v := by
    intro P Q hPQ v haint hainv
    change AddSubgroup.closure (chapter04LocalLatticeGenerators P v) ≤
      chapter04LocalLattice Q v
    apply (AddSubgroup.closure_le _).2
    intro z hz
    rcases hz with ⟨z, rfl⟩
    rcases z with ⟨x, o⟩
    rcases x with ⟨x, hx⟩
    apply AddSubgroup.subset_closure
    let o' : Chapter04FiniteLocalIntegerRing K v :=
      ⟨(a : v.adicCompletion K)⁻¹ * (o : v.adicCompletion K),
        (v.adicCompletionIntegers K).mul_mem _ _ hainv o.property⟩
    refine ⟨(⟨(a : K) • x, hPQ x hx⟩, o'), ?_⟩
    change ((a : K) • x) ⊗ₜ[K] (o' : v.adicCompletion K) =
      x ⊗ₜ[K] (o : v.adicCompletion K)
    rw [TensorProduct.smul_tmul]
    dsimp [o']
    have hK : (a : K) ≠ 0 := by
      intro h
      apply ha
      exact Subtype.ext h
    have hane : (a : v.adicCompletion K) ≠ 0 := by
      have hmapne : algebraMap K (v.adicCompletion K) (a : K) ≠ 0 := by
        exact (map_ne_zero_iff (algebraMap K (v.adicCompletion K))
          (FaithfulSMul.algebraMap_injective K (v.adicCompletion K))).2 hK
      simpa [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
        using hmapne
    have hcoe : (a : v.adicCompletion K) =
        algebraMap K (v.adicCompletion K) (a : K) := by
      simp [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    have hmapne : algebraMap K (v.adicCompletion K) (a : K) ≠ 0 := by
      exact (map_ne_zero_iff (algebraMap K (v.adicCompletion K))
        (FaithfulSMul.algebraMap_injective K (v.adicCompletion K))).2 hK
    rw [hcoe]
    congr 1
    simp [Algebra.smul_def, hmapne]
  let d : K →+* Chapter04FiniteAdeleRing K :=
    IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 K) K
  let da : Chapter04FiniteAdeleRing K := d (a : K)
  let dai : Chapter04FiniteAdeleRing K := d ((a : K)⁻¹)
  let S : Set (Chapter04FinitePlace K) :=
    chapter04FiniteAdeleExceptionalSet K da ∪
      chapter04FiniteAdeleExceptionalSet K dai
  have hS : S.Finite := by
    exact (chapter04_finiteAdele_exceptionalSet_finite K da).union
      (chapter04_finiteAdele_exceptionalSet_finite K dai)
  refine ⟨S, hS, ?_⟩
  intro v hv
  have hda : da v ∈ chapter04FiniteLocalIntegerSet K v := by
    have hv' : v ∉ chapter04FiniteAdeleExceptionalSet K da := by
      intro hv'
      exact hv (Or.inl hv')
    exact not_not.mp hv'
  have hdai : dai v ∈ chapter04FiniteLocalIntegerSet K v := by
    have hv' : v ∉ chapter04FiniteAdeleExceptionalSet K dai := by
      intro hv'
      exact hv (Or.inr hv')
    exact not_not.mp hv'
  have haint : (a : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    have hcoe : da v = (a : v.adicCompletion K) := by
      exact IsDedekindDomain.FiniteAdeleRing.algebraMap_apply (𝓞 K) K a v
    rw [hcoe] at hda
    exact hda
  have hainv : ((a : v.adicCompletion K)⁻¹) ∈ v.adicCompletionIntegers K := by
    have hcoe : dai v = ((a : v.adicCompletion K)⁻¹) := by
      change (algebraMap K (v.adicCompletion K) ((a : K)⁻¹)) =
        ((a : v.adicCompletion K)⁻¹)
      rw [map_inv₀]
      congr 1
    rw [hcoe] at hdai
    exact hdai
  apply le_antisymm
  · exact hlocal_inclusion M N hMN v haint hainv
  · exact hlocal_inclusion N M hNM v haint hainv

theorem chapter04_adelic_vector_space_topology_is_independent_of_the_lattice
    (M N : Chapter04Lattice K V) :
    ∃ e : Chapter04AdelicVectorSpaceRestrictedProduct M ≃+
        Chapter04AdelicVectorSpaceRestrictedProduct N,
      (∀ x, (e x).1 = x.1 ∧ (e x).2.1 = x.2.1) ∧
      Continuous e ∧ Continuous e.symm := by
  classical
  have hopen_lattice :
      ∀ P : Chapter04Lattice K V, ∀ v,
        IsOpen (chapter04LocalLattice P v : Set
          (V ⊗[K] Chapter04FiniteLocalField K v)) := by
    intro P v
    let c : Basis (Module.Free.ChooseBasisIndex K V) K V := Module.Free.chooseBasis K V
    let a : Module.Free.ChooseBasisIndex K V → 𝓞 K :=
      fun i => Classical.choose (P.full (c i))
    have ha : ∀ i, a i ≠ 0 ∧ (a i : K) • c i ∈ P.carrier := by
      intro i
      exact Classical.choose_spec (P.full (c i))
    have hai : ∀ (i : Module.Free.ChooseBasisIndex K V),
        (a i : Chapter04FiniteLocalField K v) ≠ 0 := by
      intro i
      have haiK : (a i : K) ≠ 0 := by
        intro h
        apply (ha i).1
        exact_mod_cast h
      change algebraMap K (Chapter04FiniteLocalField K v) (a i : K) ≠ 0
      exact (map_ne_zero (algebraMap K (Chapter04FiniteLocalField K v))).2 haiK
    have hswap :
        ∀ (i : Module.Free.ChooseBasisIndex K V)
          (oi : Chapter04FiniteLocalIntegerRing K v),
          c i ⊗ₜ[K] ((a i : Chapter04FiniteLocalField K v) *
            (oi : Chapter04FiniteLocalField K v)) =
            ((a i : K) • c i) ⊗ₜ[K] (oi : Chapter04FiniteLocalField K v) := by
      intro i oi
      rw [show (a i : Chapter04FiniteLocalField K v) *
          (oi : Chapter04FiniteLocalField K v) =
          (a i : K) • (oi : Chapter04FiniteLocalField K v) by
        rw [Algebra.smul_def]
        rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
        simp]
      rw [TensorProduct.tmul_smul]
      rfl
    have hformula :
        ∀ y : Module.Free.ChooseBasisIndex K V → Chapter04FiniteLocalField K v,
        (TensorProduct.comm K V (Chapter04FiniteLocalField K v)).symm
          ((Algebra.TensorProduct.equivPiOfFiniteBasis
            (Chapter04FiniteLocalField K v) c).symm y) =
          ∑ i, TensorProduct.mk K V (Chapter04FiniteLocalField K v) (c i) (y i) := by
      intro y
      change (TensorProduct.comm K V (Chapter04FiniteLocalField K v)).symm
        ((c.equivFun.baseChange K (Chapter04FiniteLocalField K v)).symm
          ((TensorProduct.piScalarRight K (Chapter04FiniteLocalField K v)
            (Chapter04FiniteLocalField K v) _).symm y)) = _
      have hy : y = ∑ i, Pi.single i (y i) := by
        ext j
        simp [Pi.single_apply]
      conv_lhs => rw [hy]
      rw [map_sum, map_sum, map_sum]
      simp only [TensorProduct.piScalarRight_symm_single,
        LinearEquiv.baseChange_symm_tmul]
      have hs : ∀ i, c.equivFun.symm (Pi.single i (1 : K)) = c i := by
        intro i
        rw [c.equivFun_symm_apply]
        simp [Pi.single_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hs i]
      rw [TensorProduct.comm_symm_tmul]
      rfl
    have hmem :
        ∀ (x : V ⊗[K] Chapter04FiniteLocalField K v),
          (∀ i, ((a i : Chapter04FiniteLocalField K v)⁻¹ *
            (chapter04TensorProductCoordinateMap K
              (Chapter04FiniteLocalField K v) V c x) i) ∈
              chapter04FiniteLocalIntegerSet K v) →
          x ∈ chapter04LocalLattice P v := by
      intro x hx
      have hrepr :
          x = ∑ i, TensorProduct.mk K V (Chapter04FiniteLocalField K v) (c i)
            ((chapter04TensorProductCoordinateMap K
              (Chapter04FiniteLocalField K v) V c x) i) := by
        simpa [chapter04TensorProductCoordinateMap] using
          (hformula (chapter04TensorProductCoordinateMap K
            (Chapter04FiniteLocalField K v) V c x))
      rw [hrepr]
      apply AddSubgroup.sum_mem
      intro i hi
      let oi : Chapter04FiniteLocalIntegerRing K v :=
        ⟨(a i : Chapter04FiniteLocalField K v)⁻¹ *
          (chapter04TensorProductCoordinateMap K
            (Chapter04FiniteLocalField K v) V c x) i, hx i⟩
      have hcoord :
          (chapter04TensorProductCoordinateMap K
            (Chapter04FiniteLocalField K v) V c x) i =
            (a i : Chapter04FiniteLocalField K v) * (oi : Chapter04FiniteLocalField K v) := by
        dsimp [oi]
        rw [← mul_assoc, mul_inv_cancel₀ (hai i), one_mul]
      have hgen :
          TensorProduct.mk K V (Chapter04FiniteLocalField K v)
              ((a i : K) • c i) (oi : Chapter04FiniteLocalIntegerRing K v) ∈
            chapter04LocalLattice P v := by
        exact AddSubgroup.subset_closure
          ⟨⟨⟨(a i : K) • c i, (ha i).2⟩, oi⟩, rfl⟩
      rw [hcoord]
      change c i ⊗ₜ[K]
        ((a i : Chapter04FiniteLocalField K v) *
          (oi : Chapter04FiniteLocalField K v)) ∈ _
      rw [hswap i oi]
      exact hgen
    have hsep : SeparatelyContinuousAdd
        (V ⊗[K] Chapter04FiniteLocalField K v) := by
      let f : (V ⊗[K] Chapter04FiniteLocalField K v) →+
          (Module.Free.ChooseBasisIndex K V → Chapter04FiniteLocalField K v) :=
        { toFun := chapter04TensorProductCoordinateMap K
            (Chapter04FiniteLocalField K v) V c
          map_zero' := by
            change Algebra.TensorProduct.equivPiOfFiniteBasis
                (Chapter04FiniteLocalField K v) c
              (TensorProduct.comm K V (Chapter04FiniteLocalField K v) 0) = 0
            simp
          map_add' := by
            intro x y
            change Algebra.TensorProduct.equivPiOfFiniteBasis
                (Chapter04FiniteLocalField K v) c
              (TensorProduct.comm K V (Chapter04FiniteLocalField K v) (x + y)) =
              Algebra.TensorProduct.equivPiOfFiniteBasis
                (Chapter04FiniteLocalField K v) c
                (TensorProduct.comm K V (Chapter04FiniteLocalField K v) x) +
              Algebra.TensorProduct.equivPiOfFiniteBasis
                (Chapter04FiniteLocalField K v) c
                (TensorProduct.comm K V (Chapter04FiniteLocalField K v) y)
            simp }
      have hca : ContinuousAdd (V ⊗[K] Chapter04FiniteLocalField K v) :=
        continuousAdd_induced f
      exact
        { continuous_const_add := hca.continuous_add.comp
            (continuous_const.prodMk continuous_id)
          continuous_add_const := hca.continuous_add.comp
            (continuous_id.prodMk continuous_const) }
    let U : Set (Module.Free.ChooseBasisIndex K V → Chapter04FiniteLocalField K v) :=
      {x | ∀ i, ((a i : Chapter04FiniteLocalField K v)⁻¹ * x i) ∈
        chapter04FiniteLocalIntegerSet K v}
    have hU : IsOpen U := by
      rw [show U =
          ⋂ i, (fun x : Module.Free.ChooseBasisIndex K V →
              Chapter04FiniteLocalField K v =>
            (a i : Chapter04FiniteLocalField K v)⁻¹ * x i) ⁻¹'
              (chapter04FiniteLocalIntegerSet K v) by
        ext x
        simp [U]]
      apply isOpen_iInter_of_finite
      intro i
      exact (Valued.isOpen_valuationSubring _).preimage
        (continuous_const.mul (continuous_apply i))
    have hW : IsOpen
        ((chapter04TensorProductCoordinateMap K
          (Chapter04FiniteLocalField K v) V c) ⁻¹' U) := by
      change IsOpen[
        TopologicalSpace.induced
          (chapter04TensorProductCoordinateMap K
            (Chapter04FiniteLocalField K v) V c)
          inferInstance]
        ((chapter04TensorProductCoordinateMap K
          (Chapter04FiniteLocalField K v) V c) ⁻¹' U)
      exact isOpen_induced_iff.mpr ⟨U, hU, rfl⟩
    refine @AddSubgroup.isOpen_of_mem_nhds _ _ _ hsep
      (chapter04LocalLattice P v) 0 ?_
    refine Filter.mem_of_superset (hW.mem_nhds ?_) ?_
    · show (chapter04TensorProductCoordinateMap K
        (Chapter04FiniteLocalField K v) V c 0) ∈ U
      intro i
      simp [chapter04TensorProductCoordinateMap]
      change (0 : Chapter04FiniteLocalField K v) ∈
        chapter04FiniteLocalIntegerSet K v
      exact ValuationSubring.zero_mem _
    · intro x hx
      exact hmem x hx
  have hchange :
      chapter03AdditiveFiniteChange
        (fun v : Chapter04FinitePlace K => chapter04LocalLattice M v)
        (fun v : Chapter04FinitePlace K => chapter04LocalLattice N v) := by
    rcases chapter04_two_lattices_agree_locally_outside_finitely_many_places M N
      with ⟨S, hSfin, hS⟩
    unfold chapter03AdditiveFiniteChange chapter03AdditiveFiniteChangeSet
    apply hSfin.subset
    intro v hv
    by_contra hne
    exact hv (hS v hne)
  have hMopen := hopen_lattice M
  have hNopen := hopen_lattice N
  rcases chapter03_additive_local_lattice_agreement_outside_finite_set
      (fun v : Chapter04FinitePlace K => chapter04LocalLattice M v)
      (fun v : Chapter04FinitePlace K => chapter04LocalLattice N v)
      hchange hMopen hNopen with ⟨etailEquiv, heq, hcont, hcontinv⟩
  let etail : Chapter04AdelicVectorSpaceFiniteTail M ≃+
      Chapter04AdelicVectorSpaceFiniteTail N :=
    { toEquiv := etailEquiv
      map_add' := by
        intro x y
        apply Subtype.ext
        funext v
        have hxy := congrFun (heq (x + y)) v
        have hx := congrFun (heq x) v
        have hy := congrFun (heq y) v
        change (etailEquiv (x + y) :
            ∀ v : Chapter04FinitePlace K,
              V ⊗[K] Chapter04FiniteLocalField K v) v =
          ((etailEquiv x : ∀ v : Chapter04FinitePlace K,
              V ⊗[K] Chapter04FiniteLocalField K v) v +
            (etailEquiv y : ∀ v : Chapter04FinitePlace K,
              V ⊗[K] Chapter04FiniteLocalField K v) v)
        rw [hxy, hx, hy]
        rfl }
  let eprod : Chapter04AdelicVectorSpaceRestrictedProduct M ≃+
      Chapter04AdelicVectorSpaceRestrictedProduct N :=
    (AddEquiv.refl (V ⊗[K] Chapter04InfiniteAdeleRing K)).prodCongr etail
  refine ⟨eprod, ?_, ?_, ?_⟩
  · intro x
    refine ⟨rfl, ?_⟩
    change (etailEquiv x.2 :
        ∀ v : Chapter04FinitePlace K,
          V ⊗[K] Chapter04FiniteLocalField K v) =
      (x.2 : ∀ v : Chapter04FinitePlace K,
          V ⊗[K] Chapter04FiniteLocalField K v)
    exact heq x.2
  · exact continuous_fst.prodMk (hcont.comp continuous_snd)
  · exact continuous_fst.prodMk (hcontinv.comp continuous_snd)

theorem chapter04_adelic_vector_space_is_coordinatewise_after_a_basis
    (M : Chapter04Lattice K V)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) :
    ∃ e : Chapter04AdelicVectorSpace K V ≃+
        (ι → Chapter04AdeleRing K),
      Continuous e ∧ Continuous e.symm := by
  classical
  have _hM : Chapter04Lattice K V := M
  let c : Basis (Module.Free.ChooseBasisIndex K V) K V := Module.Free.chooseBasis K V
  let ec0 : (V ⊗[K] Chapter04AdeleRing K) ≃ₗ[Chapter04AdeleRing K]
      (Chapter04AdeleRing K ⊗[K] V) :=
    { toFun := TensorProduct.comm K V (Chapter04AdeleRing K)
      invFun := (TensorProduct.comm K V (Chapter04AdeleRing K)).symm
      left_inv := (TensorProduct.comm K V (Chapter04AdeleRing K)).left_inv
      right_inv := (TensorProduct.comm K V (Chapter04AdeleRing K)).right_inv
      map_add' := (TensorProduct.comm K V (Chapter04AdeleRing K)).map_add
      map_smul' := by
        intro a x
        induction x with
        | zero => simp
        | tmul v b => rfl
        | add x y hx hy => simp [hx, hy] }
  let ec : (V ⊗[K] Chapter04AdeleRing K) ≃ₗ[Chapter04AdeleRing K]
      (Module.Free.ChooseBasisIndex K V → Chapter04AdeleRing K) :=
    ec0.trans
      (Algebra.TensorProduct.equivPiOfFiniteBasis (Chapter04AdeleRing K) c)
  let _ : ContinuousAdd (V ⊗[K] Chapter04AdeleRing K) :=
    continuousAdd_induced ec.toAddEquiv.toAddHom
  let ecL : (V ⊗[K] Chapter04AdeleRing K) ≃L[Chapter04AdeleRing K]
      (Module.Free.ChooseBasisIndex K V → Chapter04AdeleRing K) :=
    { __ := ec
      continuous_toFun := by
        change Continuous[
          TopologicalSpace.induced
            (chapter04TensorProductCoordinateMap K (Chapter04AdeleRing K) V c)
            inferInstance, inferInstance] ec
        exact continuous_induced_dom
      continuous_invFun := by
        apply continuous_induced_rng.mpr
        have hcomp :
            chapter04TensorProductCoordinateMap K (Chapter04AdeleRing K) V
                (Module.Free.chooseBasis K V) ∘ ec.invFun =
              id := by
          funext x
          change ec (ec.invFun x) = x
          exact ec.apply_symm_apply x
        rw [hcomp]
        exact continuous_id }
  let htop : IsModuleTopology (Chapter04AdeleRing K)
      (V ⊗[K] Chapter04AdeleRing K) :=
    IsModuleTopology.iso ecL.symm
  let _ : IsModuleTopology (Chapter04AdeleRing K)
      (V ⊗[K] Chapter04AdeleRing K) := htop
  let e := ec0.trans
    (Algebra.TensorProduct.equivPiOfFiniteBasis (Chapter04AdeleRing K) b)
  refine ⟨e.toAddEquiv, ?_, ?_⟩
  · exact IsModuleTopology.continuous_of_linearMap e.toLinearMap
  · exact IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

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
  simp [chapter04AdelicLinearMap]

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
