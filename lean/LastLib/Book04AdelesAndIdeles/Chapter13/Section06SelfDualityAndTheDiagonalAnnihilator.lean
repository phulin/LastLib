import Mathlib.Topology.Order
import Mathlib.Algebra.Group.TransferInstance
import LastLib.Book04AdelesAndIdeles.Chapter13.Section05TheStandardAdditiveCharacter

open scoped BigOperators NumberField NumberField.AdeleRing RestrictedProduct

namespace LastLib.Book04AdelesAndIdeles.Chapter13

noncomputable section

instance chapter13WithDiscreteTopologyCommGroup
    (G : Type*) [CommGroup G] :
    CommGroup (WithDiscreteTopology G) :=
  (WithTopology.equiv G (⊥ : TopologicalSpace G)).commGroup

instance chapter13WithDiscreteTopologyAddCommGroup
    (G : Type*) [AddCommGroup G] :
    AddCommGroup (WithDiscreteTopology G) :=
  (WithTopology.equiv G (⊥ : TopologicalSpace G)).addCommGroup

/-!
## 13.6 Self-duality and the diagonal annihilator
-/

def chapter13RightMultiplicationAddMonoidHom
    {A : Type*} [NonUnitalNonAssocRing A] (y : A) : A →+ A :=
  { toFun := fun x => x * y
    map_zero' := by sorry
    map_add' := by sorry }

def chapter13ContinuousAddCharToDual
    {A : Type*} [NonUnitalNonAssocRing A] [TopologicalSpace A]
    (ψ : AddChar A Circle) (hψ : Continuous ψ) : Chapter13AdditiveDual A :=
  Additive.ofMul
    { toMonoidHom := ψ.toMonoidHom
      continuous_toFun := hψ }

def chapter13PairingCharacter
    {A : Type*} [NonUnitalNonAssocRing A] [TopologicalSpace A] [ContinuousMul A]
    (ψ : AddChar A Circle) (hψ : Continuous ψ) (y : A) :
    Chapter13AdditiveDual A :=
  chapter13ContinuousAddCharToDual
    (ψ.compAddMonoidHom (chapter13RightMultiplicationAddMonoidHom y))
    (by sorry)

theorem chapter13PairingCharacter_apply
    {A : Type*} [NonUnitalNonAssocRing A] [TopologicalSpace A] [ContinuousMul A]
    (ψ : AddChar A Circle) (hψ : Continuous ψ) (y x : A) :
    chapter13PairingCharacter ψ hψ y x = ψ (x * y) :=
  rfl

def chapter13RealAdditiveCharacterAt (y : ℝ) : Chapter13AdditiveDual ℝ :=
  chapter13PairingCharacter Real.fourierChar Real.continuous_fourierChar y

theorem chapter13_real_additive_character_at_apply (x y : ℝ) :
    chapter13RealAdditiveCharacterAt y x = Real.fourierChar (x * y) :=
  rfl

theorem chapter13_real_continuous_additive_character_classification
    (χ : Chapter13AdditiveDual ℝ) :
    ∃! y : ℝ, χ = chapter13RealAdditiveCharacterAt y := by
  sorry

def chapter13ComplexPairingAddMonoidHom (y : ℂ) : ℂ →+ ℝ :=
  { toFun := fun x => chapter13ComplexTracePairing x y
    map_zero' := by sorry
    map_add' := by sorry }

def chapter13ComplexPairingAddChar (y : ℂ) : AddChar ℂ Circle :=
  Real.fourierChar.compAddMonoidHom (chapter13ComplexPairingAddMonoidHom y)

def chapter13ComplexAdditiveCharacterAt (y : ℂ) : Chapter13AdditiveDual ℂ :=
  chapter13ContinuousAddCharToDual (chapter13ComplexPairingAddChar y) (by sorry)

theorem chapter13_complex_additive_character_at_apply (x y : ℂ) :
    chapter13ComplexAdditiveCharacterAt y x =
      Circle.exp (2 * Real.pi * chapter13ComplexTracePairing x y) := by
  sorry

theorem chapter13_complex_continuous_additive_character_classification
    (χ : Chapter13AdditiveDual ℂ) :
    ∃! y : ℂ, χ = chapter13ComplexAdditiveCharacterAt y := by
  sorry

/- DEPENDENCY_GUESS: instantiate the local-field completeness and inverse-limit argument from the
earlier completion chapters for the concrete trace pairing.  The data structure records the
pairing map's surjectivity and openness separately from the elementary nondegeneracy facts. -/

theorem chapter13_local_additive_character_classification_from_data
    {F : Type*} [Field F] [TopologicalSpace F]
    (D : Chapter13LocalSelfDualityData F)
    (χ : AddChar F Circle) (hχ : Continuous χ) :
    ∃! y : F, ∀ x, χ x = D.pairing x y := by
  sorry

theorem chapter13_local_pairing_map_injective
    {F : Type*} [Field F] [TopologicalSpace F]
    (D : Chapter13LocalSelfDualityData F) :
    Function.Injective D.pairingMap := by
  sorry

theorem chapter13_local_self_duality_from_data
    {F : Type*} [Field F] [TopologicalSpace F]
    (D : Chapter13LocalSelfDualityData F) :
    Nonempty (F ≃ₜ+ Chapter13AdditiveDual F) := by
  sorry

def chapter13FinitePairingIsPerfect
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    (pair : A → B → Circle) : Prop :=
  (∀ x y z, pair (x + y) z = pair x z * pair y z) ∧
    (∀ x y z, pair x (y + z) = pair x y * pair x z) ∧
      (∀ a, (∀ b, pair a b = 1) → a = 0) ∧
        (∀ b, (∀ a, pair a b = 1) → b = 0) ∧
          Fintype.card A = Fintype.card B

theorem chapter13_finite_trace_pairing_perfect_from_nondegeneracy
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    (pair : A → B → Circle)
    (hadd_left : ∀ x y z, pair (x + y) z = pair x z * pair y z)
    (hadd_right : ∀ x y z, pair x (y + z) = pair x y * pair x z)
    (hleft : ∀ a, (∀ b, pair a b = 1) → a = 0)
    (hright : ∀ b, (∀ a, pair a b = 1) → b = 0)
    (hcard : Fintype.card A = Fintype.card B) :
    chapter13FinitePairingIsPerfect pair := by
  exact ⟨hadd_left, hadd_right, hleft, hright, hcard⟩

/-!
The preceding finite interface is the book's local statement for
`π⁻ʳ O / πᵐ O` paired with `π⁻ᵐ D⁻¹ / πʳ D⁻¹`; the later fixup pass can instantiate `A` and `B`
with the canonical valuation-ring quotients from Chapters 05--08.
-/

def chapter13DiagonalAdditiveSubgroup
    (K : Type*) [Field K] [NumberField K] : AddSubgroup (Chapter13Adele K) :=
  NumberField.AdeleRing.principalSubgroup (R := 𝓞 K) (K := K)

abbrev Chapter13AdditiveAdelicQuotient (K : Type*) [Field K] [NumberField K] :=
  Chapter13Adele K ⧸ chapter13DiagonalAdditiveSubgroup K

def chapter13AdelicDualMap
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) :
    Chapter13Adele K →ₜ+ Chapter13AdditiveDual (Chapter13Adele K) :=
  { toAddMonoidHom :=
      { toFun := fun y =>
          chapter13PairingCharacter
            (chapter13StandardAdditiveCharacter K D)
            (chapter13StandardAdditiveCharacter_continuous K D) y
        map_zero' := by sorry
        map_add' := by sorry }
    continuous_toFun := by sorry }

theorem chapter13_adelic_dual_map_apply
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) (x y : Chapter13Adele K) :
    chapter13AdelicDualMap K D y x =
      chapter13StandardAdditiveCharacter K D (x * y) :=
  rfl

structure Chapter13AdelicLocalParameterData
    (K : Type*) [Field K] [NumberField K] where
  inverseDifferent :
    ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      AddSubgroup (v.adicCompletion K)
  inverseDifferent_integral_tail :
    ∀ᶠ v in Filter.cofinite,
      (inverseDifferent v : Set (v.adicCompletion K)) =
        {x : v.adicCompletion K | x ∈ v.adicCompletionIntegers K}

/- DEPENDENCY_GUESS: the previous completion and restricted-product chapters must eventually
instantiate these bridge facts from the local character classifications and restricted-product
topology.  They are not consequences of `Chapter13AdelicTraceData`; recording the local inputs and
the compact-tail statement here keeps the global self-duality statements from assuming their own
conclusion. -/
structure Chapter13AdelicDualityData
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) where
  localData : Chapter13AdelicLocalParameterData K
  infinite_local_duality :
    ∀ v : NumberField.InfinitePlace K,
      Chapter13LocalSelfDualityData (v.Completion)
  finite_local_duality :
    ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Chapter13LocalSelfDualityData (v.adicCompletion K)
  infiniteLocalEmbedding :
    ∀ v : NumberField.InfinitePlace K, (v.Completion) →+ Chapter13Adele K
  infiniteLocalEmbedding_continuous :
    ∀ v : NumberField.InfinitePlace K, Continuous (infiniteLocalEmbedding v)
  infiniteLocalEmbedding_coordinate :
    ∀ (v : NumberField.InfinitePlace K) (x : v.Completion),
      (infiniteLocalEmbedding v x).1 v = x
  infiniteLocalEmbedding_coordinate_off :
    ∀ (v w : NumberField.InfinitePlace K) (x : v.Completion), w ≠ v →
      (infiniteLocalEmbedding v x).1 w = 0
  infiniteLocalEmbedding_finite :
    ∀ (v : NumberField.InfinitePlace K) (x : v.Completion),
      (infiniteLocalEmbedding v x).2 = 0
  finiteLocalEmbedding :
    ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (v.adicCompletion K) →+ Chapter13Adele K
  finiteLocalEmbedding_continuous :
    ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Continuous (finiteLocalEmbedding v)
  finiteLocalEmbedding_infinite :
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K),
      (finiteLocalEmbedding v x).1 = 0
  finiteLocalEmbedding_coordinate :
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K),
      (finiteLocalEmbedding v x).2 v = x
  finiteLocalEmbedding_coordinate_off :
    ∀ (v w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K),
      w ≠ v → (finiteLocalEmbedding v x).2 w = 0
  infinite_local_pairing_compatibility :
    ∀ (v : NumberField.InfinitePlace K) (x : v.Completion) (y : Chapter13Adele K),
      chapter13StandardAdditiveCharacter K D (infiniteLocalEmbedding v x * y) =
        (infinite_local_duality v).pairing x (y.1 v)
  finite_local_pairing_compatibility :
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (x : v.adicCompletion K) (y : Chapter13Adele K),
      chapter13StandardAdditiveCharacter K D (finiteLocalEmbedding v x * y) =
        (finite_local_duality v).pairing x (y.2 v)
  finite_local_inverseDifferent :
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (y : v.adicCompletion K),
      y ∈ localData.inverseDifferent v ↔
        ∀ x : v.adicCompletion K, x ∈ v.adicCompletionIntegers K →
          (finite_local_duality v).pairing x y = 1
  local_parameter_tail :
    ∀ y : Chapter13Adele K,
      ∀ᶠ v in Filter.cofinite, y.2 v ∈ localData.inverseDifferent v
  /- Continuity of a global character forces it to kill a full compact-open tail.  The finite
  exceptional set is allowed to depend on the character; this is the topological input used before
  local self-duality assembles the character parameters. -/
  character_tail_trivial :
    ∀ χ : Chapter13AdditiveDual (Chapter13Adele K),
      ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
        ∀ y : Chapter13Adele K,
          y.1 = 0 →
            (∀ v ∈ S, y.2 v = 0) →
              (∀ v ∉ S, y.2 v ∈ v.adicCompletionIntegers K) →
                (Additive.toMul χ) (Multiplicative.ofAdd y) = 1
  /- Local open-map data alone does not automatically assemble into an open map for the
  restricted product.  Record that global topological input explicitly before using the
  topological self-duality conclusions. -/
  adelic_dual_map_isOpen : IsOpenMap (chapter13AdelicDualMap K D)

theorem chapter13_global_character_parameters_are_adeles
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K)
    (S : Chapter13AdelicDualityData K D)
    (χ : Chapter13AdditiveDual (Chapter13Adele K)) :
    ∃ y : Chapter13Adele K,
      χ = chapter13AdelicDualMap K D y := by
  sorry

theorem chapter13_global_character_has_local_trace_dual_tail
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K)
    (S : Chapter13AdelicDualityData K D)
    (χ : Chapter13AdditiveDual (Chapter13Adele K)) :
    ∃ y : Chapter13Adele K,
      χ = chapter13AdelicDualMap K D y ∧
        ∀ᶠ v in Filter.cofinite, y.2 v ∈ S.localData.inverseDifferent v := by
  sorry

theorem chapter13_global_character_parameter_unique
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K)
    (S : Chapter13AdelicDualityData K D)
    {y z : Chapter13Adele K}
    (h : chapter13AdelicDualMap K D y = chapter13AdelicDualMap K D z) :
    y = z := by
  sorry

theorem chapter13_adelic_self_duality
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K)
    (S : Chapter13AdelicDualityData K D) :
    Nonempty
      (Chapter13Adele K ≃ₜ+ Chapter13AdditiveDual (Chapter13Adele K)) := by
  sorry

theorem chapter13_adelic_dual_map_is_topological_equivalence
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K)
    (S : Chapter13AdelicDualityData K D) :
    ∃ e : Chapter13Adele K ≃ₜ+ Chapter13AdditiveDual (Chapter13Adele K),
      ∀ y, e y = chapter13AdelicDualMap K D y := by
  sorry

def chapter13DiagonalAnnihilator
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) : AddSubgroup (Chapter13Adele K) :=
  chapter13AdditiveAnnihilator
    (chapter13StandardAdditiveCharacter K D) (chapter13DiagonalAdditiveSubgroup K)

/-! The reverse annihilator argument uses concrete interfaces beyond the existence of the global
character: principal-parts approximation for the local trace-dual lattices, the archimedean
trace-dual lattice, and a local trace-pairing test together with its nondegeneracy after the finite
and infinite corrections.  They are kept as proof-support data rather than being hidden in the
reverse theorem's conclusion. -/

structure Chapter13DiagonalAnnihilatorData
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) where
  localData : Chapter13AdelicLocalParameterData K
  global_inverseDifferent_local :
    ∀ c, c ∈ chapter13GlobalInverseDifferent K →
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        algebraMap K (v.adicCompletion K) c ∈ localData.inverseDifferent v
  finite_principal_parts :
    ∀ y : Chapter13Adele K, ∃ b : K,
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        y.2 v - algebraMap K (v.adicCompletion K) b ∈ localData.inverseDifferent v
  archimedean_trace_dual :
    ∀ y : Chapter13Adele K, ∀ b : K,
      y ∈ chapter13DiagonalAnnihilator K D →
        (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          y.2 v - algebraMap K (v.adicCompletion K) b ∈ localData.inverseDifferent v) →
        ∃ c : K, c ∈ chapter13GlobalInverseDifferent K ∧
          y.1 - algebraMap K (Chapter13InfiniteAdele K) b =
            algebraMap K (Chapter13InfiniteAdele K) c
  local_trace_pairing :
    ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      v.adicCompletion K → v.adicCompletion K → Circle
  local_nondegenerate :
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (z : v.adicCompletion K),
      (∀ t : v.adicCompletion K, local_trace_pairing v z t = 1) → z = 0
  finite_local_trace_test :
    ∀ y : Chapter13Adele K,
      y ∈ chapter13DiagonalAnnihilator K D →
        y.1 = 0 →
          (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            y.2 v ∈ localData.inverseDifferent v) →
            ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
              (t : v.adicCompletion K),
              local_trace_pairing v (y.2 v) t = 1

theorem chapter13_diagonal_annihilator_forward
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) :
    chapter13DiagonalAdditiveSubgroup K ≤ chapter13DiagonalAnnihilator K D := by
  sorry

theorem chapter13_diagonal_annihilator_reverse_by_approximation
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K)
    (A : Chapter13DiagonalAnnihilatorData K D) :
    chapter13DiagonalAnnihilator K D ≤ chapter13DiagonalAdditiveSubgroup K := by
  sorry

theorem chapter13_diagonal_annihilator_eq_diagonal
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K)
    (A : Chapter13DiagonalAnnihilatorData K D) :
    chapter13DiagonalAnnihilator K D = chapter13DiagonalAdditiveSubgroup K := by
  apply le_antisymm
  · exact chapter13_diagonal_annihilator_reverse_by_approximation K D A
  · exact chapter13_diagonal_annihilator_forward K D

theorem chapter13_adelic_quotient_is_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (Chapter13AdditiveAdelicQuotient K)) := by
  sorry

def chapter13DescendAdditiveCharacterToAdelicQuotient
    (K : Type*) [Field K] [NumberField K]
    (ψ : AddChar (Chapter13Adele K) Circle)
    (hψ : ∀ x : chapter13DiagonalAdditiveSubgroup K, ψ x = 1) :
    AddChar (Chapter13AdditiveAdelicQuotient K) Circle :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (chapter13DiagonalAdditiveSubgroup K)
      ψ.toAddMonoidHom (by
        intro x hx
        change ψ x = 1
        exact hψ ⟨x, hx⟩))

theorem chapter13DescendAdditiveCharacterToAdelicQuotient_apply
    (K : Type*) [Field K] [NumberField K]
    (ψ : AddChar (Chapter13Adele K) Circle)
    (hψ : ∀ x : chapter13DiagonalAdditiveSubgroup K, ψ x = 1)
    (x : Chapter13Adele K) :
    chapter13DescendAdditiveCharacterToAdelicQuotient K ψ hψ (x : Chapter13AdditiveAdelicQuotient K) =
      ψ x :=
  rfl

theorem chapter13_additive_quotient_character_iff_trivial_on_diagonal
    (K : Type*) [Field K] [NumberField K]
    (χ : AddChar (Chapter13Adele K) Circle) (hχ : Continuous χ) :
    (∃ ψ : AddChar (Chapter13AdditiveAdelicQuotient K) Circle,
      Continuous ψ ∧
        ∀ x : Chapter13Adele K,
          ψ (x : Chapter13AdditiveAdelicQuotient K) = χ x) ↔
      ∀ x : chapter13DiagonalAdditiveSubgroup K, χ x = 1 := by
  sorry

theorem chapter13_quotient_dual_is_the_diagonal_field
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K)
    (S : Chapter13AdelicDualityData K D)
    (A : Chapter13DiagonalAnnihilatorData K D) :
    Nonempty
      (Chapter13AdditiveDual (Chapter13AdditiveAdelicQuotient K) ≃ₜ+
        WithDiscreteTopology K) := by
  sorry

theorem chapter13_quotient_character_is_trivial_on_diagonal
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13AdditiveDual (Chapter13Adele K))
    (hχ : ∀ x : chapter13DiagonalAdditiveSubgroup K,
      (Additive.toMul χ) (Multiplicative.ofAdd (x : Chapter13Adele K)) = 1) :
    ∃ ψ : Chapter13AdditiveDual (Chapter13AdditiveAdelicQuotient K),
      ∀ x : Chapter13Adele K,
        ψ (x : Chapter13AdditiveAdelicQuotient K) = χ x := by
  sorry

end
end LastLib.Book04AdelesAndIdeles.Chapter13
