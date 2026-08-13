import LastLib.Book04AdelesAndIdeles.Chapter08.Section82
import Mathlib.Topology.Algebra.Group.Units

namespace LastLib.Book04AdelesAndIdeles.Chapter08

noncomputable section

open scoped BigOperators nonZeroDivisors RestrictedProduct

/-! ## 8.3 Finiteness revisited topologically -/

@[instance_reducible]
def chapter08IdeleClassTopology (K : Type*) [Field K] [NumberField K] :
    TopologicalSpace (Chapter08IdeleClassGroup K) :=
  TopologicalSpace.coinduced
    (QuotientGroup.mk' (chapter08PrincipalIdeles K))
    (chapter08IdelesTopology K)

@[instance_reducible]
def chapter08OrdinaryClassGroupTopology (K : Type*) [Field K] [NumberField K] :
    TopologicalSpace (Chapter08OrdinaryClassGroup K) :=
  ⊥

theorem chapter08_ideal_class_group_finite
    (K : Type*) [Field K] [NumberField K] :
    Finite (Chapter08OrdinaryClassGroup K) := by
  infer_instance

theorem chapter08_ideal_class_group_discrete
    (K : Type*) [Field K] [NumberField K] :
    @DiscreteTopology (Chapter08OrdinaryClassGroup K)
      (chapter08OrdinaryClassGroupTopology K) := by
  exact discreteTopology_bot _

theorem chapter08_idele_class_map_continuous
    (K : Type*) [Field K] [NumberField K] :
    letI : TopologicalSpace (Chapter08IdeleClassGroup K) :=
      chapter08IdeleClassTopology K
    letI : TopologicalSpace (Chapter08OrdinaryClassGroup K) :=
      chapter08OrdinaryClassGroupTopology K
    Continuous (chapter08IdeleClassMap K) := by
  have hfin : @Continuous (Chapter08FiniteIdeles K) (Chapter08IdealGroup K)
      (chapter08FiniteIdeleGraphTopology K) ⊥
      (chapter08FiniteIdeleIdealMap K) :=
    chapter08_finite_idele_ideal_continuous K
  have hsnd : @Continuous (Chapter08Ideles K) (Chapter08FiniteIdeles K)
      (chapter08IdelesTopology K) (chapter08FiniteIdeleGraphTopology K)
      Prod.snd :=
    letI : TopologicalSpace (Chapter08FiniteIdeles K) :=
      chapter08FiniteIdeleGraphTopology K
    letI : TopologicalSpace (Chapter08Ideles K) := chapter08IdelesTopology K
    continuous_snd
  have hideal : @Continuous (Chapter08Ideles K) (Chapter08IdealGroup K)
      (chapter08IdelesTopology K) ⊥ (chapter08IdeleIdealHom K) := by
    exact
      letI : TopologicalSpace (Chapter08FiniteIdeles K) :=
        chapter08FiniteIdeleGraphTopology K
      letI : TopologicalSpace (Chapter08Ideles K) := chapter08IdelesTopology K
      letI : TopologicalSpace (Chapter08IdealGroup K) := ⊥
      show @Continuous (Chapter08Ideles K) (Chapter08IdealGroup K)
        (chapter08IdelesTopology K) ⊥ (chapter08IdeleIdealHom K) from
        by
          change @Continuous (Chapter08Ideles K) (Chapter08IdealGroup K)
            (chapter08IdelesTopology K) ⊥
            (fun x : Chapter08Ideles K => chapter08FiniteIdeleIdealMap K x.2)
          exact hfin.comp hsnd
  have hmk : @Continuous (Chapter08IdealGroup K)
      (Chapter08OrdinaryClassGroup K) ⊥
      (chapter08OrdinaryClassGroupTopology K) (ClassGroup.mk K) := by
    exact
      letI : TopologicalSpace (Chapter08IdealGroup K) := ⊥
      letI : TopologicalSpace (Chapter08OrdinaryClassGroup K) :=
        chapter08OrdinaryClassGroupTopology K
      letI : DiscreteTopology (Chapter08IdealGroup K) := discreteTopology_bot _
      continuous_of_discreteTopology
  have hcomp : @Continuous (Chapter08Ideles K)
      (Chapter08OrdinaryClassGroup K) (chapter08IdelesTopology K)
      (chapter08OrdinaryClassGroupTopology K)
      ((ClassGroup.mk K).comp (chapter08IdeleIdealHom K)) :=
    letI : TopologicalSpace (Chapter08Ideles K) := chapter08IdelesTopology K
    letI : TopologicalSpace (Chapter08IdealGroup K) := ⊥
    letI : TopologicalSpace (Chapter08OrdinaryClassGroup K) :=
      chapter08OrdinaryClassGroupTopology K
    hmk.comp hideal
  change @Continuous (Chapter08IdeleClassGroup K)
    (Chapter08OrdinaryClassGroup K) (chapter08IdeleClassTopology K)
    (chapter08OrdinaryClassGroupTopology K) (chapter08IdeleClassMap K)
  apply (continuous_coinduced_dom).2
  simpa [chapter08IdeleClassTopology, chapter08IdeleClassMap,
    Function.comp_def] using hcomp

theorem chapter08_kernel_numerator_is_open
    (K : Type*) [Field K] [NumberField K] :
    letI : TopologicalSpace (Chapter08Ideles K) := chapter08IdelesTopology K
    IsOpen (Set.range (chapter08KernelNumeratorEmbedding K)) := by
  let B : ∀ v : IsDedekindDomain.HeightOneSpectrum (Chapter08Integers K),
      Set ((v.adicCompletion K)ˣ) :=
    fun v => (Submonoid.ofClass (v.adicCompletionIntegers K)).units
  let U : Set (Πʳ v : IsDedekindDomain.HeightOneSpectrum (Chapter08Integers K),
      [(v.adicCompletion K)ˣ, B v]) :=
    {z | ∀ v, z v ∈ B v}
  have hB : ∀ v : IsDedekindDomain.HeightOneSpectrum (Chapter08Integers K),
      IsOpen (B v) := by
    intro v
    exact Submonoid.isOpen_units
      (Valued.isOpen_valuationSubring (v.adicCompletion K))
  have hU : IsOpen U := by
    exact RestrictedProduct.isOpen_forall_mem hB
  have hfinite : @IsOpen (Chapter08FiniteIdeles K)
      (chapter08FiniteIdeleGraphTopology K)
      (chapter08FiniteIntegralUnits (K := K) : Set (Chapter08FiniteIdeles K)) := by
    have heq :
        (chapter08FiniteIntegralUnits (K := K) : Set (Chapter08FiniteIdeles K)) =
          (RestrictedProduct.unitsEquiv
            (𝓕 := Filter.cofinite)
            (B := fun v : IsDedekindDomain.HeightOneSpectrum (Chapter08Integers K) =>
              v.adicCompletionIntegers K)
            (fun v : IsDedekindDomain.HeightOneSpectrum (Chapter08Integers K) =>
              v.adicCompletion K)) ⁻¹' U := by
      ext z
      constructor
      · intro hz v
        change (RestrictedProduct.unitsEquiv
          (𝓕 := Filter.cofinite)
          (B := fun v : IsDedekindDomain.HeightOneSpectrum (Chapter08Integers K) =>
            v.adicCompletionIntegers K)
          (fun v : IsDedekindDomain.HeightOneSpectrum (Chapter08Integers K) =>
            v.adicCompletion K) z v) ∈
          (v.adicCompletionIntegers K).units
        apply IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.2
        have he := RestrictedProduct.unitsEquiv_apply
          (R := fun v : IsDedekindDomain.HeightOneSpectrum (Chapter08Integers K) =>
            v.adicCompletion K) v z
        rw [he]
        change Valued.v (chapter08FiniteIdeleComponent z v) = 1
        exact (chapter08_finite_integral_unit_iff_local_valued_eq_one z).1 hz v
      · intro hz
        refine (chapter08_finite_integral_unit_iff_local_valued_eq_one z).2 ?_
        intro v
        have hv := hz v
        change (RestrictedProduct.unitsEquiv
          (𝓕 := Filter.cofinite)
          (B := fun v : IsDedekindDomain.HeightOneSpectrum (Chapter08Integers K) =>
            v.adicCompletionIntegers K)
          (fun v : IsDedekindDomain.HeightOneSpectrum (Chapter08Integers K) =>
            v.adicCompletion K) z v) ∈
          (v.adicCompletionIntegers K).units at hv
        have hval :=
          IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.1 hv
        have he := RestrictedProduct.unitsEquiv_apply
          (R := fun v : IsDedekindDomain.HeightOneSpectrum (Chapter08Integers K) =>
            v.adicCompletion K) v z
        rw [he] at hval
        change Valued.v (chapter08FiniteIdeleComponent z v) = 1 at hval
        exact hval
    rw [heq]
    exact isOpen_induced hU
  have hrange :
      Set.range (chapter08KernelNumeratorEmbedding K) =
        (Set.univ : Set (Chapter08InfiniteIdeles K)) ×ˢ
          (chapter08FiniteIntegralUnits (K := K) : Set (Chapter08FiniteIdeles K)) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Set.mem_univ _, y.2.property⟩
    · rintro ⟨_, hz⟩
      exact ⟨(z.1, ⟨z.2, hz⟩), rfl⟩
  rw [hrange]
  apply @IsOpen.prod (Chapter08InfiniteIdeles K) (Chapter08FiniteIdeles K)
    _ (chapter08FiniteIdeleGraphTopology K)
  · exact isOpen_univ
  · exact hfinite

theorem chapter08_idele_class_map_kernel_is_open
    (K : Type*) [Field K] [NumberField K] :
    letI : TopologicalSpace (Chapter08IdeleClassGroup K) :=
      chapter08IdeleClassTopology K
    IsOpen (MonoidHom.ker (chapter08IdeleClassMap K) :
      Set (Chapter08IdeleClassGroup K)) := by
  exact
    letI : Fact (∀ v : IsDedekindDomain.HeightOneSpectrum (Chapter08Integers K),
        IsOpen ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
          Set ((v.adicCompletion K)ˣ))) := ⟨by
      intro v
      exact Submonoid.isOpen_units
        (Valued.isOpen_valuationSubring (v.adicCompletion K))⟩
    letI : TopologicalSpace (Chapter08FiniteIdeles K) :=
      chapter08FiniteIdeleGraphTopology K
    letI : IsTopologicalGroup (Chapter08FiniteIdeles K) :=
      topologicalGroup_induced
      (RestrictedProduct.unitsEquiv
        (𝓕 := Filter.cofinite)
        (B := fun v : IsDedekindDomain.HeightOneSpectrum (Chapter08Integers K) =>
          v.adicCompletionIntegers K)
        (fun v : IsDedekindDomain.HeightOneSpectrum (Chapter08Integers K) =>
          v.adicCompletion K))
    letI : TopologicalSpace (Chapter08Ideles K) := chapter08IdelesTopology K
    by
      rw [chapter08_idele_class_kernel_eq_kernel_numerator_range]
      have hq : IsOpenMap (QuotientGroup.mk' (chapter08PrincipalIdeles K) :
          Chapter08Ideles K → Chapter08IdeleClassGroup K) := by
        exact isOpenMap_quotient_mk'_mul
      have he : IsOpen (Set.range (chapter08KernelNumeratorEmbedding K)) := by
        exact chapter08_kernel_numerator_is_open K
      have himage := hq _ he
      have hrange :
          MonoidHom.range (chapter08KernelIntoIdeleClass K) =
            (QuotientGroup.mk' (chapter08PrincipalIdeles K)) ''
              Set.range (chapter08KernelNumeratorEmbedding K) := by
        ext q
        constructor
        · rintro ⟨z, rfl⟩
          exact ⟨chapter08KernelNumeratorEmbedding K z, ⟨z, rfl⟩, rfl⟩
        · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
          exact ⟨z, rfl⟩
      rw [hrange]
      exact himage

/-! This is the abstract compact-to-discrete bridge used by the converse observation in the text.
The chapter deliberately does not use it as an alternative proof of the class-number theorem. -/

theorem chapter08_finite_of_compact_surjective_discrete
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [DiscreteTopology Y]
    (f : X → Y) (hf : Continuous f) (hsurj : Function.Surjective f) :
    Finite Y := by
  apply Finite.of_finite_univ
  have hcompact : IsCompact (f '' (Set.univ : Set X)) :=
    isCompact_univ.image hf
  have hfinite : (f '' (Set.univ : Set X)).Finite := hcompact.finite_of_discrete
  simpa [Set.image_univ, Set.range_eq_univ.mpr hsurj] using hfinite

end

end LastLib.Book04AdelesAndIdeles.Chapter08
