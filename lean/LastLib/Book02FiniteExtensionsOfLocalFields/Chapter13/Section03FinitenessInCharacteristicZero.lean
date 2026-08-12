import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13.Section02CompactFamiliesOfEisensteinPolynomials
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13.Section01TheFinitenessQuestionAndItsExactScope
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section02TheSeparabilityMap

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13

noncomputable section

universe u uK uL uGamma

open IntermediateField
open Polynomial
open scoped Polynomial

/-! ## 13.3. Finiteness in characteristic zero -/

/-- The finite set of numerical factorizations used for one fixed degree. -/
def chapter13DegreeFactorPairs (d : ℕ) : Set (ℕ × ℕ) :=
  {q | q.1 * q.2 = d}

theorem chapter13_degree_has_finitely_many_factor_pairs (d : ℕ) :
    Set.Finite (chapter13DegreeFactorPairs d) := by
  sorry

/-- The valuation data expressing that an intermediate field is unramified.
The residue separability field is retained explicitly because it is part of
the canonical unramified condition. -/
structure Chapter13UnramifiedIntermediateData
    {K : Type uK} {L : Type uL} {ΓK : Type uGamma} [Field K] [Field L]
    [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    (vK : Valuation K ΓK) (M : IntermediateField K L) where
  valueGroup : Type uL
  [valueGroupOrder : LinearOrderedCommGroupWithZero valueGroup]
  valuation : Valuation M valueGroup
  [extension : vK.HasExtension valuation]
  [discrete : Valuation.IsRankOneDiscrete valuation]
  [finite : FiniteDimensional K M]
  [residue_algebra :
    Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField valuation.valuationSubring)]
  residue_separable :
    Algebra.IsSeparable
      (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField valuation.valuationSubring)
  ramification_index_eq_one :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring valuation.valuationSubring
      (IsLocalRing.maximalIdeal valuation.valuationSubring) = 1

def chapter13IsUnramifiedIntermediate
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    (vK : Valuation K ΓK) (M : IntermediateField K L) : Prop :=
  Nonempty (Chapter13UnramifiedIntermediateData vK M)

def chapter13MaximalUnramifiedIntermediate
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    (vK : Valuation K ΓK) (Kf : IntermediateField K L) : Prop :=
  chapter13IsUnramifiedIntermediate vK Kf ∧
    ∀ M : IntermediateField K L,
      chapter13IsUnramifiedIntermediate vK M → M ≤ Kf

/-- Book-facing degree data for the maximal unramified stage and the
remaining totally ramified stage. -/
structure Chapter13UnramifiedTotallyRamifiedDegreeData
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (d : ℕ) where
  Kf : IntermediateField K L
  [finite_base : FiniteDimensional K Kf]
  [finite_remainder : FiniteDimensional Kf L]
  maximal_unramified : chapter13MaximalUnramifiedIntermediate vK Kf
  f : ℕ
  e : ℕ
  base_degree : Module.finrank K Kf = f
  remainder_degree : Module.finrank Kf L = e
  degree : Module.finrank K L = d
  degree_factorization : d = e * f
  e_eq_ramification_index :
    e = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring)
  f_eq_residue_degree :
    f = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring)
  factorization :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Chapter12UnramifiedTotallyRamifiedFactorization vK vL
  /-- The abstract middle field in Chapter 12 is the chosen intermediate
  field `Kf` after its canonical map into `L`. -/
  middle_range :
    letI : Field factorization.middle := factorization.field_middle
    letI : Algebra factorization.middle L := factorization.algebra_middle_L
    Set.range (algebraMap factorization.middle L) = (Kf : Set L)
  remainder_totally_ramified : factorization.fML = 1

/- DEPENDENCY_GUESS: This is the Chapter 13 presentation of the earlier
   valuation-factorization theorem.  The existing Chapter 12 package proves
   the same two-stage numerical endpoints, but does not expose the maximal
   intermediate field in the structure used by this chapter. -/
theorem chapter13_finite_residue_extension_has_unramified_then_totally_ramified_stages
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Finite (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (d : ℕ) (hdegree : Module.finrank K L = d) :
    Nonempty
      (Chapter13UnramifiedTotallyRamifiedDegreeData vK vL d) := by
  sorry

/-- A finite residue-field extension is separable. -/
theorem chapter13_finite_residue_extension_is_separable
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [Fintype k] :
    Algebra.IsSeparable k l := by
  infer_instance

theorem chapter13_finite_residue_field_is_perfect
    (k : Type*) [Field k] [Fintype k] : PerfectField k := by
  infer_instance

theorem chapter13_finite_extension_has_finite_residue_field
    {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    (vK : Valuation K ΓK) (vL : Valuation L ΓL)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Finite (IsLocalRing.ResidueField vK.valuationSubring)] :
    Finite (IsLocalRing.ResidueField vL.valuationSubring) := by
  sorry

def chapter13BoundedDegreeFactorPairs (N : ℕ) : Set (ℕ × ℕ) :=
  {q | q.1 * q.2 ≤ N}

theorem chapter13_bounded_degree_has_finitely_many_factor_pairs (N : ℕ) :
    Set.Finite (chapter13BoundedDegreeFactorPairs N) := by
  sorry

/-- The unique unramified base for a fixed residue degree, up to the
base-field isomorphism used in the source. -/
theorem chapter13_unique_unramified_base_of_fixed_degree
    {A K k : Type*} [CommRing A] [IsDomain A]
    [Field K] [Field k] [Fintype k]
    [Algebra A K] [IsFractionRing A K]
    [HenselianLocalRing A] [IsDiscreteValuationRing A]
    (res : A →+* k) (f : ℕ) (hf : 0 < f)
    (hres_surjective : Function.Surjective res)
    (hres_kernel : RingHom.ker res = IsLocalRing.maximalIdeal A)
    (hpoly : ∃ gbar : k[X],
      gbar.Monic ∧ Irreducible gbar ∧ gbar.Separable ∧ gbar.natDegree = f) :
    ∃ M : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Chapter07FiniteResidueUnramifiedModel A K k res,
      M.degree = f ∧
        ∀ M' : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Chapter07FiniteResidueUnramifiedModel A K k res,
          M'.degree = f →
          letI : Field M.carrier := M.carrierField
          letI : Field M'.carrier := M'.carrierField
          letI : Algebra K M.carrier := M.carrierAlgebra
          letI : Algebra K M'.carrier := M'.carrierAlgebra
          Nonempty (M.carrier ≃ₐ[K] M'.carrier) := by
  sorry

/-- A uniformizer in the totally ramified stage has an Eisenstein minimal
polynomial of the ramification degree. -/
theorem chapter13_totally_ramified_stage_has_eisenstein_minpoly
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hfinite : Module.Finite A (integralClosure A L))
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (hdiscreteL :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (htotal : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08TotallyRamified vK vL hval)
    (hintegralK : ∀ x : K, IsIntegral A x ↔ 0 ≤ vK x)
    (hintegralL : ∀ x : L, IsIntegral A x ↔ 0 ≤ vL x)
    (πK : A) (hπK : vK (algebraMap A K πK) = 1)
    (πL : L) (hπL : vL πL = 1) :
    ∃ g : A[X],
      g.Monic ∧
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt πK g ∧
      g.natDegree = Module.finrank K L ∧
      g.map (algebraMap A K) = minpoly K πL := by
  sorry

/-- The finite union over the finitely many degree factorizations is the
book's final characteristic-zero counting step. -/
theorem chapter13_char_zero_finiteness_is_finite_union_over_factor_pairs
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [CharZero K]
    [Valuation.IsRankOneDiscrete vK]
    [Finite (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (N : ℕ) (hN : 1 ≤ N) :
    chapter13BoundedDegreeFiniteness (K := K) N := by
  exact chapter13_theorem_13_1_bounded_degree_finiteness
    vK hcomplete N hN

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13
