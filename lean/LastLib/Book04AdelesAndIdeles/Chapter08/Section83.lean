import LastLib.Book04AdelesAndIdeles.Chapter08.Section82

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
  sorry

theorem chapter08_kernel_numerator_is_open
    (K : Type*) [Field K] [NumberField K] :
    letI : TopologicalSpace (Chapter08Ideles K) := chapter08IdelesTopology K
    IsOpen (Set.range (chapter08KernelNumeratorEmbedding K)) := by
  sorry

theorem chapter08_idele_class_map_kernel_is_open
    (K : Type*) [Field K] [NumberField K] :
    letI : TopologicalSpace (Chapter08IdeleClassGroup K) :=
      chapter08IdeleClassTopology K
    IsOpen (MonoidHom.ker (chapter08IdeleClassMap K) :
      Set (Chapter08IdeleClassGroup K)) := by
  sorry

/-! This is the abstract compact-to-discrete bridge used by the converse observation in the text.
The chapter deliberately does not use it as an alternative proof of the class-number theorem. -/

theorem chapter08_finite_of_compact_surjective_discrete
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [DiscreteTopology Y]
    (f : X → Y) (hf : Continuous f) (hsurj : Function.Surjective f) :
    Finite Y := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter08
