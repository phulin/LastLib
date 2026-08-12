import LastLib.Book06GlobalClassFieldTheory.Chapter11.Section08QuadraticInductionInterface

namespace LastLib.Book06GlobalClassFieldTheory.Chapter11

open scoped BigOperators DirectSum NumberField.AdeleRing RestrictedProduct
open NumberField

noncomputable section

/-! ## 11.9. Induction through a general finite extension -/

structure Chapter11FiniteSeparableExtensionData
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [Algebra.IsSeparable K M] where
  degree : ℕ
  degree_formula : Module.finrank K M = degree

structure Chapter11FiniteExtensionInductionData
    (E G H : Type*) [Field E] [Group G] [Fintype G] [Group H] [Fintype H] where
  inclusion : H →* G
  degree : ℕ
  degree_formula : Fintype.card G = degree * Fintype.card H
  theta : H →* Eˣ

def chapter11GeneralInducedRepresentation
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11FiniteExtensionInductionData E G H) :
    Representation E G (Chapter11InducedSpace E G H D.inclusion D.theta) :=
  chapter11InducedRepresentation E G H D.inclusion D.theta

theorem chapter11_general_induced_dimension
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11FiniteExtensionInductionData E G H) :
    Module.finrank E (Chapter11InducedSpace E G H D.inclusion D.theta) = D.degree := by
  sorry

theorem chapter11_general_norm_pullback_is_restriction
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M]
    (N : Chapter11NormData K M)
    {G H : Type*} [Group G] [Group H]
    (baseArtin : Chapter11IdeleClass K →* G)
    (extensionArtin : Chapter11IdeleClass M →* H)
    (restriction : H →* G)
    (compatibility : ∀ x,
      restriction (extensionArtin x) = baseArtin (N.classNorm x))
    (η : G →* ℂˣ) (x : Chapter11IdeleClass M) :
    η (baseArtin (N.classNorm x)) =
      (η.comp restriction) (extensionArtin x) := by
  rw [← compatibility x]
  rfl

def chapter11GeneralRepresentationTwist
    {E G V : Type*} [Field E] [Group G] [AddCommGroup V] [Module E V]
    (ρ : Representation E G V) (η : G →* Eˣ) : Representation E G V := by
  refine
    { toFun := fun g => (η g : E) • ρ g
      map_one' := by sorry
      map_mul' := by sorry }

def chapter11GeneralTwistedCharacter
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11FiniteExtensionInductionData E G H) (η : G →* Eˣ) : H →* Eˣ :=
  { toFun := fun h => D.theta h * η (D.inclusion h)
    map_one' := by sorry
    map_mul' := by sorry }

theorem chapter11_general_induction_tensor_identity
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11FiniteExtensionInductionData E G H) (η : G →* Eˣ) :
    Nonempty
      ((chapter11InducedRepresentation E G H D.inclusion
        (chapter11GeneralTwistedCharacter D η)).Equiv
        (chapter11GeneralRepresentationTwist
          (chapter11GeneralInducedRepresentation D) η)) := by
  sorry

structure Chapter11GaloisMackeyData
    (E G H Γ : Type*) [Field E] [Group G] [Fintype G] [Group H]
    [Fintype H] [Group Γ] [Fintype Γ] where
  inclusion : H →* G
  normality : ∀ g h, ∃ k, g * inclusion h * g⁻¹ = inclusion k
  theta : H →* Eˣ
  conjugate : Γ → H →* Eˣ
  conjugate_one : conjugate 1 = theta
  coset_index : Fintype.card G = Fintype.card Γ * Fintype.card H

def chapter11MackeyDirectSumRepresentation
    {E G H Γ : Type*} [Field E] [Group G] [Fintype G] [Group H]
    [Fintype H] [Group Γ] [Fintype Γ]
    (D : Chapter11GaloisMackeyData E G H Γ) :
    Representation E H (⨁ _σ : Γ, E) := by
  exact Representation.directSum
    (fun σ => chapter11CharacterRepresentation E H (D.conjugate σ))

theorem chapter11_galois_restriction_mackey_decomposition
    {E G H Γ : Type*} [Field E] [Group G] [Fintype G] [Group H]
    [Fintype H] [Group Γ] [Fintype Γ]
    (D : Chapter11GaloisMackeyData E G H Γ) :
    Nonempty
      ((chapter11RestrictRepresentation D.inclusion
        (chapter11InducedRepresentation E G H D.inclusion D.theta)).Equiv
        (chapter11MackeyDirectSumRepresentation D)) := by
  sorry

def chapter11ConjugateStabilizer
    {E H Γ : Type*} [Field E] [Group H] [Group Γ]
    (theta : H →* Eˣ) (conjugate : Γ → H →* Eˣ) : Subgroup Γ where
  carrier := {σ | conjugate σ = theta}
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry

def chapter11IntertwinerSpace
    {E G V : Type*} [Field E] [Group G] [AddCommGroup V] [Module E V]
    (ρ σ : Representation E G V) : Submodule E (Module.End E V) where
  carrier := {f | ∀ g, f.comp (ρ g) = (σ g).comp f}
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' := by sorry

theorem chapter11_induced_end_dimension_is_stabilizer_cardinality
    {E G H Γ : Type*} [Field E] [Group G] [Fintype G] [Group H]
    [Fintype H] [Group Γ] [Fintype Γ]
    (D : Chapter11GaloisMackeyData E G H Γ) :
  Module.finrank E
        (chapter11IntertwinerSpace
          (chapter11InducedRepresentation E G H D.inclusion D.theta)
          (chapter11InducedRepresentation E G H D.inclusion D.theta)) =
      Nat.card (chapter11ConjugateStabilizer D.theta D.conjugate) := by
  sorry

theorem chapter11_general_induced_irreducible_iff_trivial_stabilizer
    {E G H Γ : Type*} [Field E] [IsAlgClosed E] [CharZero E]
    [Group G] [Fintype G] [Group H] [Fintype H] [Group Γ] [Fintype Γ]
    (D : Chapter11GaloisMackeyData E G H Γ) :
    chapter11RepresentationIrreducible
        (chapter11InducedRepresentation E G H D.inclusion D.theta) ↔
      ∀ σ : Γ, σ ≠ 1 → D.conjugate σ ≠ D.theta := by
  sorry

structure Chapter11GeneralDeterminantData
    (E G H : Type*) [Field E] [Group G] [Group H] where
  transfer : G →* H
  permutationSign : G →* Eˣ

theorem chapter11_general_induced_determinant_formula
    {E G H : Type*} [Field E] [Group G] [Fintype G] [Group H] [Fintype H]
    (D : Chapter11FiniteExtensionInductionData E G H)
    (T : Chapter11GeneralDeterminantData E G H) :
    chapter11RepresentationDeterminant (chapter11GeneralInducedRepresentation D) =
      { toFun := fun g => T.permutationSign g * D.theta (T.transfer g)
        map_one' := by sorry
        map_mul' := by sorry } := by
  sorry

structure Chapter11GeneralLocalConductorData
    (K W : Type*) [Field K] [NumberField K] where
  inducedExponent : NumberField.FinitePlace K → ℕ
  differentExponent : NumberField.FinitePlace K → ℕ
  placesAbove : NumberField.FinitePlace K → Finset W
  residueDegreeWeight : NumberField.FinitePlace K → W → ℕ
  characterExponent : NumberField.FinitePlace K → W → ℕ
  local_formula : ∀ v,
    inducedExponent v = differentExponent v +
      Finset.sum (placesAbove v) (fun w => residueDegreeWeight v w * characterExponent v w)

theorem chapter11_general_local_induction_conductor_formula
    {K W : Type*} [Field K] [NumberField K]
    (D : Chapter11GeneralLocalConductorData K W)
    (v : NumberField.FinitePlace K) :
    D.inducedExponent v = D.differentExponent v +
      Finset.sum (D.placesAbove v)
        (fun w => D.residueDegreeWeight v w * D.characterExponent v w) := by
  exact D.local_formula v

structure Chapter11GeneralConductorIdealData
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] where
  inducedConductor : Ideal (𝓞 K)
  differentIdeal : Ideal (𝓞 K)
  characterConductor : Ideal (𝓞 M)
  formula : inducedConductor =
    differentIdeal * Ideal.relNorm (𝓞 K) characterConductor

theorem chapter11_general_induced_conductor_ideal_formula
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M]
    (D : Chapter11GeneralConductorIdealData K M) :
    D.inducedConductor =
      D.differentIdeal * Ideal.relNorm (𝓞 K) D.characterConductor := by
  exact D.formula

structure Chapter11GeneralFrobeniusData
    (E places : Type*) [Field E] [Fintype places] where
  totalDegree : ℕ
  residueDegree : places → ℕ
  localFrobeniusValue : places → Eˣ
  degree_formula : ∑ w, residueDegree w = totalDegree
  characteristicPolynomial : Polynomial E
  frobenius_formula : characteristicPolynomial =
    ∏ w, (Polynomial.X ^ residueDegree w -
      Polynomial.C (localFrobeniusValue w : E))

theorem chapter11_general_frobenius_characteristic_polynomial
    {E places : Type*} [Field E] [Fintype places]
    (D : Chapter11GeneralFrobeniusData E places) :
    D.characteristicPolynomial =
      ∏ w, (Polynomial.X ^ D.residueDegree w -
        Polynomial.C (D.localFrobeniusValue w : E)) := by
  exact D.frobenius_formula

structure Chapter11TowerInductionData
    (E G H L : Type*) [Field E] [Group G] [Fintype G] [Group H]
    [Fintype H] [Group L] [Fintype L] where
  LtoH : L →* H
  HtoG : H →* G
  LtoG : L →* G
  composition : HtoG.comp LtoH = LtoG

theorem chapter11_induction_transitivity
    {E G H L V : Type*} [Field E] [Group G] [Fintype G] [Group H]
    [Fintype H] [Group L] [Fintype L] [AddCommGroup V] [Module E V]
    (D : Chapter11TowerInductionData E G H L)
    (ρ : Representation E L V) :
    Nonempty
      ((Representation.ind D.HtoG (Representation.ind D.LtoH ρ)).Equiv
        (Representation.ind D.LtoG ρ)) := by
  sorry

theorem chapter11_norm_transitivity
    {K M L : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Field L] [NumberField L] [Algebra K M] [Algebra M L]
    [Algebra K L] [FiniteDimensional K M] [FiniteDimensional M L]
    [IsScalarTower K M L]
    (NKM : Chapter11NormData K M) (NML : Chapter11NormData M L)
    (NKL : Chapter11NormData K L)
    (hcompat : NKL.classNorm = NKM.classNorm.comp NML.classNorm) :
    NKL.classNorm = NKM.classNorm.comp NML.classNorm :=
  hcompat

abbrev Chapter11VirtualCharacter (G E : Type*) := G → E

structure Chapter11VirtualInductionData
    (ι G E : Type*) [Fintype ι] [Group G] [Field E] where
  coefficient : ι → ℤ
  term : ι → Chapter11VirtualCharacter G E

def chapter11VirtualInducedCombination
    {ι G E : Type*} [Fintype ι] [Group G] [Field E]
    (D : Chapter11VirtualInductionData ι G E) : Chapter11VirtualCharacter G E :=
  fun g => ∑ i, (D.coefficient i : E) * D.term i g

structure Chapter11VirtualEffectivityWitness
    (G E V : Type*) [Group G] [Field E] [AddCommGroup V] [Module E V]
    (v : Chapter11VirtualCharacter G E) where
  representation : Representation E G V
  character_formula : representation.character = v

def chapter11VirtualCombinationIsEffective
    {G E V : Type*} [Group G] [Field E] [AddCommGroup V] [Module E V]
    (v : Chapter11VirtualCharacter G E) : Prop :=
  Nonempty (Chapter11VirtualEffectivityWitness G E V v)

/- SOURCE_NOTE: the final virtual combination is intentionally not declared
effective.  Reciprocity supplies each one-dimensional term and the
norm--transfer identities transport its local data, but negative integer
coefficients require an independent cancellation/effectivity argument. -/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter11
