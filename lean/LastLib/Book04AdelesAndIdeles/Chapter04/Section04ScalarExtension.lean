import LastLib.Book04AdelesAndIdeles.Chapter04.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open Set Filter
open NumberField IsDedekindDomain
open Module
open LastLib.Book04AdelesAndIdeles.Chapter01
open scoped BigOperators TensorProduct Topology RestrictedProduct

/-! ### 4.4 Scalar extension -/

abbrev Chapter04FinitePlaceAbove
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsScalarTower ℚ K L]
    (v : Chapter04FinitePlace K) :=
  {w : Chapter04FinitePlace L //
    Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal = v.asIdeal}

def chapter04TensorFiniteExtensionIntegralModel
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (M : Submodule (𝓞 K) L) (v : Chapter04FinitePlace K) :
    Set (L ⊗[K] Chapter04FiniteLocalField K v) :=
  (AddSubgroup.closure (Set.range (fun z :
      M × Chapter04FiniteLocalIntegerRing K v =>
      TensorProduct.mk K L (Chapter04FiniteLocalField K v) z.1.1
        (z.2 : Chapter04FiniteLocalField K v)))).carrier

def chapter04BranchIntegralModel
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsScalarTower ℚ K L]
    (v : Chapter04FinitePlace K) :
    Set (∀ w : Chapter04FinitePlaceAbove K L v,
      Chapter04FiniteLocalField L w.1) :=
  {x | ∀ w, x w ∈ chapter04FiniteLocalIntegerSet L w.1}

def chapter04FiniteExtensionUnramifiedAt
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsScalarTower ℚ K L]
    (v : Chapter04FinitePlace K) : Prop :=
  ∀ w : Chapter04FinitePlaceAbove K L v,
    w.1.asIdeal.ramificationIdx (𝓞 K) = 1

structure Chapter04FiniteExtensionIntegralData
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsScalarTower ℚ K L] where
  badPlaces : Set (Chapter04FinitePlace K)
  badPlaces_finite : badPlaces.Finite
  localDecomposition :
    ∀ v : Chapter04FinitePlace K,
      Nonempty (L ⊗[K] Chapter04FiniteLocalField K v ≃+*
        (∀ w : Chapter04FinitePlaceAbove K L v,
          Chapter04FiniteLocalField L w.1))
  integralModel :
    ∀ v : Chapter04FinitePlace K,
      Set (L ⊗[K] Chapter04FiniteLocalField K v)
  chosenIntegralLattice : Submodule (𝓞 K) L
  chosenIntegralLattice_finite : Module.Finite (𝓞 K) chosenIntegralLattice
  chosenIntegralLattice_full :
    ∀ x : L, ∃ a : 𝓞 K, a ≠ 0 ∧ (a : K) • x ∈ chosenIntegralLattice
  integral_model_is_generated_by_chosen_lattice :
    ∀ v, integralModel v =
      chapter04TensorFiniteExtensionIntegralModel K L chosenIntegralLattice v
  unramified_outside_badPlaces :
    ∀ v, v ∉ badPlaces → chapter04FiniteExtensionUnramifiedAt K L v
  integral_model_transport :
    ∀ v, v ∉ badPlaces →
      ∃ e : L ⊗[K] Chapter04FiniteLocalField K v ≃+*
        (∀ w : Chapter04FinitePlaceAbove K L v,
          Chapter04FiniteLocalField L w.1),
        e '' integralModel v = chapter04BranchIntegralModel K L v

/- The global discriminant/different argument and the completed-product
theorem from the earlier chapters should instantiate this data without
assuming the adelic scalar-extension conclusion. -/
theorem chapter04_finite_extension_integral_data_exists
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsScalarTower ℚ K L] :
    Nonempty (Chapter04FiniteExtensionIntegralData K L) := by
  sorry

theorem chapter04_finite_extension_trace_discriminant_is_nonzero
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsScalarTower ℚ K L] :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (b : Basis ι K L), Algebra.discr K b ≠ 0 := by
  sorry

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsScalarTower ℚ K L]

local instance chapter04AdeleTensorRightAlgebra :
    Algebra (Chapter04AdeleRing K) (L ⊗[K] Chapter04AdeleRing K) :=
  Algebra.TensorProduct.rightAlgebra

def chapter04FiniteExtensionBasisDenominatorSupport
    (D : Chapter04FiniteExtensionIntegralData K L)
    {ι : Type*} (b : Basis ι K L) : Set (Chapter04FinitePlace K) :=
  {v | ∃ i : ι,
    TensorProduct.mk K L (Chapter04FiniteLocalField K v) (b i) 1 ∉ D.integralModel v}

theorem chapter04_finite_extension_basis_has_only_finitely_many_denominator_places
    (D : Chapter04FiniteExtensionIntegralData K L)
    {ι : Type*} (b : Basis ι K L) :
    (chapter04FiniteExtensionBasisDenominatorSupport D b).Finite := by
  sorry

theorem chapter04_finite_extension_bad_places_are_finite
    (D : Chapter04FiniteExtensionIntegralData K L) :
    D.badPlaces.Finite :=
  D.badPlaces_finite

theorem chapter04_local_tensor_product_retains_all_branches
    (D : Chapter04FiniteExtensionIntegralData K L)
    (v : Chapter04FinitePlace K) :
    Nonempty (L ⊗[K] Chapter04FiniteLocalField K v ≃+*
      (∀ w : Chapter04FinitePlaceAbove K L v,
        Chapter04FiniteLocalField L w.1)) :=
  D.localDecomposition v

theorem chapter04_integral_models_agree_with_all_branches_away_from_bad_places
    (D : Chapter04FiniteExtensionIntegralData K L)
    (v : Chapter04FinitePlace K) (hv : v ∉ D.badPlaces) :
    ∃ e : L ⊗[K] Chapter04FiniteLocalField K v ≃+*
        (∀ w : Chapter04FinitePlaceAbove K L v,
          Chapter04FiniteLocalField L w.1),
      e '' D.integralModel v = chapter04BranchIntegralModel K L v := by
  exact D.integral_model_transport v hv

theorem chapter04_scalar_extension_is_finite_over_the_base_adele_ring
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsScalarTower ℚ K L] :
    Module.Finite (Chapter04AdeleRing K)
      (L ⊗[K] Chapter04AdeleRing K) := by
  sorry

theorem chapter04_scalar_extension_has_a_finite_adelic_basis
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsScalarTower ℚ K L] :
    ∃ n : ℕ, Nonempty (Basis (Fin n) (Chapter04AdeleRing K)
      (L ⊗[K] Chapter04AdeleRing K)) := by
  sorry

/- The topology on the algebraic tensor product is the finite-dimensional
module topology induced by a finite `K`-basis; the comparison theorem below
records independence of that choice. -/
theorem chapter04_scalar_extension_adelic_topological_ring_equiv
    :
    ∃ e : L ⊗[K] Chapter04AdeleRing K ≃ₐ[K] Chapter04AdeleRing L,
      @Continuous (L ⊗[K] Chapter04AdeleRing K) (Chapter04AdeleRing L)
          (chapter04TensorProductTopology K (Chapter04AdeleRing K) L)
          inferInstance (e : L ⊗[K] Chapter04AdeleRing K → Chapter04AdeleRing L) ∧
        @Continuous (Chapter04AdeleRing L) (L ⊗[K] Chapter04AdeleRing K)
          inferInstance (chapter04TensorProductTopology K (Chapter04AdeleRing K) L)
          (e.symm : Chapter04AdeleRing L → L ⊗[K] Chapter04AdeleRing K) := by
  sorry

theorem chapter04_scalar_extension_commutes_with_completion
    (D : Chapter04FiniteExtensionIntegralData K L)
    (v : Chapter04FinitePlace K) :
    Nonempty (L ⊗[K] Chapter04FiniteLocalField K v ≃+*
      (∀ w : Chapter04FinitePlaceAbove K L v,
        Chapter04FiniteLocalField L w.1)) := by
  exact D.localDecomposition v

theorem chapter04_scalar_extension_local_integrality_is_eventual
    (D : Chapter04FiniteExtensionIntegralData K L) :
    ∀ᶠ v : Chapter04FinitePlace K in Filter.cofinite,
        ∃ e : L ⊗[K] Chapter04FiniteLocalField K v ≃+*
          (∀ w : Chapter04FinitePlaceAbove K L v,
            Chapter04FiniteLocalField L w.1),
        e '' D.integralModel v = chapter04BranchIntegralModel K L v := by
  filter_upwards [D.badPlaces_finite.compl_mem_cofinite] with v hv
  exact chapter04_integral_models_agree_with_all_branches_away_from_bad_places D v hv

end

end LastLib.Book04AdelesAndIdeles.Chapter04
