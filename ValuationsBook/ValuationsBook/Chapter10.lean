import Mathlib

namespace ValuationsBook.Chapter10

open scoped BigOperators TensorProduct WithZero PowerSeries
open Polynomial

noncomputable section

/-!
# Chapter 10: Extensions of valuations

This file is a statement-generation formalization of Sections 10.1--10.7 of
Book 1.  The declarations deliberately keep the valuation-theoretic data
explicit: this makes the extension, residue, and ramification assertions
usable independently of the other generated chapters.
-/

/-! ## 10.1. The extension problem -/

/-- The valuation ring attached to a valuation. -/
def Chapter10ValuationRing {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) : Subring K :=
  v.valuationSubring.toSubring

/-- A valuation extension, expressed using Mathlib's equivalence notion. -/
def Chapter10ValuationExtension {K L Γ₀ Δ₀ : Type*}
    [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Δ₀]
    (v : Valuation K Γ₀) (w : Valuation L Δ₀) : Prop :=
  Valuation.HasExtension v w

/-! A valuation on an extension is allowed to use its own ordered value group. -/

structure Chapter10ValuationOnField (L : Type*) [Field L] where
  valueGroup : Type*
  [orderedValueGroup : LinearOrderedCommGroupWithZero valueGroup]
  valuation : Valuation L valueGroup

instance {L : Type*} [Field L] (w : Chapter10ValuationOnField L) :
    LinearOrderedCommGroupWithZero w.valueGroup := w.orderedValueGroup


/-- Contraction of a valuation ring on L to the prescribed ring on K. -/
def Chapter10ContractsTo {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : Subring K) (W : Subring L) : Prop :=
  ∀ x : K, algebraMap K L x ∈ W ↔ x ∈ V

/-- Elements bounded by every valuation in a specified family. -/
def Chapter10BoundedAtValuations {L : Type*} [Field L]
    (E : Set (Chapter10ValuationOnField L)) : Set L :=
  {x | ∀ w, w ∈ E → x ∈ w.valuation.valuationSubring}

/-- The integral closure, named locally for traceability. -/
def Chapter10IntegralClosure (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] : Subalgebra R S :=
  integralClosure R S

/-- The set of elements integral over a base ring. -/
def Chapter10IntegralElements (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] : Set S :=
  {x | IsIntegral R x}

/-- A valuation-ring criterion used in the maximal-domination argument. -/
def Chapter10ValuationRingCriterion {L : Type*} [Field L]
    (R : Subring L) : Prop :=
  ∀ x : L, x ≠ 0 → x ∈ R ∨ x⁻¹ ∈ R

/-!
The maximal-domination proof uses pairs consisting of an overring and a prime
whose contraction is the maximal ideal of the original valuation ring.
-/

structure Chapter10DominationPair {K L : Type*} [Field K] [Field L]
    [Algebra K L] (V : Subring K) [IsLocalRing V] where
  carrier : Subring L
  contains : ∀ x : K, x ∈ V → algebraMap K L x ∈ carrier
  prime : Ideal carrier
  isPrime : prime.IsPrime
  contracts : ∀ (x : K) (hx : x ∈ V),
    (⟨algebraMap K L x, contains x hx⟩ : carrier) ∈ prime ↔
      (⟨x, hx⟩ : V) ∈ IsLocalRing.maximalIdeal V

/-- Domination of one pair by another. -/
def Chapter10DominationPair.Dominates
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {V : Subring K} [IsLocalRing V]
    (P Q : Chapter10DominationPair (K := K) (L := L) V) : Prop :=
  ∃ h : P.carrier ≤ Q.carrier, ∀ x : P.carrier,
    (⟨(x : L), h x.property⟩ : Q.carrier) ∈ Q.prime ↔ x ∈ P.prime

/-- A set of domination pairs is a chain. -/
def Chapter10DominationChain
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {V : Subring K} [IsLocalRing V]
    (C : Set (Chapter10DominationPair (K := K) (L := L) V)) : Prop :=
  ∀ P ∈ C, ∀ Q ∈ C,
    Chapter10DominationPair.Dominates P Q ∨
      Chapter10DominationPair.Dominates Q P

/-- Zorn upper bound for a domination chain. -/
theorem chapter10_domination_chain_upper_bound
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {V : Subring K} [IsLocalRing V]
    (C : Set (Chapter10DominationPair (K := K) (L := L) V))
    (hC : Chapter10DominationChain C) :
    ∃ Q : Chapter10DominationPair (K := K) (L := L) V, ∀ P ∈ C,
      Chapter10DominationPair.Dominates P Q := by
  sorry

/-- Existence of a maximal domination pair. -/
theorem chapter10_maximal_domination_pair
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {V : Subring K} [IsLocalRing V] :
    ∃ P : Chapter10DominationPair (K := K) (L := L) V, ∀ Q,
      Chapter10DominationPair.Dominates P Q →
        Chapter10DominationPair.Dominates Q P := by
  sorry

/-- A maximal pair is local. -/
theorem chapter10_maximal_domination_pair_is_local
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {V : Subring K} [IsLocalRing V]
    (P : Chapter10DominationPair (K := K) (L := L) V)
    (hmax : ∀ Q, Chapter10DominationPair.Dominates P Q →
      Chapter10DominationPair.Dominates Q P) :
    IsLocalRing P.carrier := by
  sorry

/-- The prime in a maximal pair is maximal. -/
theorem chapter10_maximal_domination_pair_prime_maximal
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {V : Subring K} [IsLocalRing V]
    (P : Chapter10DominationPair (K := K) (L := L) V)
    (hmax : ∀ Q, Chapter10DominationPair.Dominates P Q →
      Chapter10DominationPair.Dominates Q P) :
    P.prime.IsMaximal := by
  sorry

/-- The intrinsic valuation-ring test obtained from maximality. -/
theorem chapter10_maximal_domination_pair_is_valuation_ring
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {V : Subring K} [IsLocalRing V]
    (P : Chapter10DominationPair (K := K) (L := L) V)
    (hmax : ∀ Q, Chapter10DominationPair.Dominates P Q →
      Chapter10DominationPair.Dominates Q P) :
    Chapter10ValuationRingCriterion P.carrier := by
  sorry

/-- Every valuation extends to an arbitrary field extension. -/
theorem chapter10_valuation_extension_exists
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) :
    ∃ W : ValuationSubring L,
      Chapter10ContractsTo v.valuationSubring.toSubring W.toSubring := by
  sorry

/-- The algebraic case of the extension theorem. -/
theorem chapter10_algebraic_valuation_extension_exists
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) :
    ∃ W : ValuationSubring L,
      Chapter10ContractsTo v.valuationSubring.toSubring W.toSubring := by
  sorry

/-! ## 10.2--10.3. Integral elements and boundedness -/

/-- An element integral over a valuation ring lies in every extending ring. -/
theorem chapter10_integral_elements_are_bounded
    {K L Γ₀ Δ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Δ₀]
    (v : Valuation K Γ₀) (w : Valuation L Δ₀)
    [h : Valuation.HasExtension v w]
    {x : L} (hx : IsIntegral v.valuationSubring x) :
    x ∈ w.valuationSubring := by
  sorry

/-- One inclusion in the valuative description of the integral closure. -/
theorem chapter10_integral_closure_subset_bounded
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (E : Set (Chapter10ValuationOnField L))
    [Algebra v.valuationSubring L]
    (hE : ∀ W, W ∈ E ↔ v.IsEquiv (W.valuation.comap (algebraMap K L))) :
    Chapter10IntegralElements v.valuationSubring L ⊆
      Chapter10BoundedAtValuations E := by
  sorry

/-- The valuative criterion: integral elements are bounded at every extension. -/
theorem chapter10_integral_closure_valuative_criterion
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) [Algebra v.valuationSubring L] :
    Chapter10IntegralElements v.valuationSubring L =
      {x : L | ∀ (W : Chapter10ValuationOnField L),
        v.IsEquiv (W.valuation.comap (algebraMap K L)) →
          x ∈ W.valuation.valuationSubring} := by
  sorry

/-- Equivalent set notation for the intersection of all extending valuation rings. -/
theorem chapter10_integral_closure_is_intersection
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) [Algebra v.valuationSubring L] :
    (Chapter10IntegralClosure v.valuationSubring L).toSubring =
      ⨅ (W : Chapter10ValuationOnField L)
        (_ : v.IsEquiv (W.valuation.comap (algebraMap K L))),
        W.valuation.valuationSubring.toSubring := by
  sorry

/-- If the extension is unique, the integral closure itself is a valuation ring. -/
theorem chapter10_unique_extension_makes_integral_closure_valuation_ring
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) [Algebra v.valuationSubring L]
    (hunique : ∀ (W₁ W₂ : Chapter10ValuationOnField L),
      v.IsEquiv (W₁.valuation.comap (algebraMap K L)) →
      v.IsEquiv (W₂.valuation.comap (algebraMap K L)) →
        W₁.valuation.IsEquiv W₂.valuation) :
    Chapter10ValuationRingCriterion
      (Chapter10IntegralClosure v.valuationSubring L).toSubring := by
  sorry

/-- All coefficients of the characteristic polynomial, trace, and norm are integral. -/
def Chapter10CharacteristicPolynomialIntegral
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L]
    (x : L) (R : Subring K) : Prop :=
  (∀ i, (LinearMap.charpoly (Algebra.lmul K L x)).coeff i ∈ R) ∧
    Algebra.trace K L x ∈ R ∧ Algebra.norm K x ∈ R

/-- Integral elements pass the finite discretely valued norm test. -/
theorem chapter10_integral_element_characteristic_data
    {K L A : Type*} [Field K] [Field L] [CommRing A]
    [Algebra K L] [Algebra A L] [Algebra A K]
    [FiniteDimensional K L]
    (R : Subring K)
    (hR : ∀ z : K, IsIntegral R z → z ∈ R)
    {x : L} (hx : IsIntegral A x)
    (hAtoR : ∀ z : K, IsIntegral A z → z ∈ R) :
    Chapter10CharacteristicPolynomialIntegral x R := by
  sorry

/-- A cancellation example witnessing that the norm alone is not a converse. -/
structure Chapter10NormCancellationExample
    (A K L : Type*) [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] where
  x : L
  norm_mem : ∃ a : A, Algebra.norm K x = algebraMap A K a
  not_integral : ¬ IsIntegral A x

theorem chapter10_norm_alone_is_not_a_converse
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L]
    (exampleData : Chapter10NormCancellationExample A K L) :
    ¬ (∀ x : L, (∃ a : A, Algebra.norm K x = algebraMap A K a) →
      IsIntegral A x) := by
  sorry

/-! ## 10.4. Ramification index and residue degree -/

/-- The multiplicative subgroup generated by the nonzero values of a valuation. -/
def Chapter10ValueGroup {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) : Subgroup Γ₀ˣ :=
  MonoidWithZeroHom.valueGroup v.toMonoidWithZeroHom

/-- The residue field associated with a valuation. -/
abbrev Chapter10ResidueField {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) :=
  IsLocalRing.ResidueField v.valuationSubring

/-- The finite index of the value groups, once the inclusion is supplied. -/
noncomputable def Chapter10RamificationIndex
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    (hΓ : Chapter10ValueGroup v ≤ Chapter10ValueGroup w) : ℕ :=
  Nat.card (Chapter10ValueGroup w ⧸
    (Chapter10ValueGroup v).subgroupOf (Chapter10ValueGroup w))

/-- The residue degree of an extension. -/
noncomputable def Chapter10ResidueDegree
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    [Valuation.HasExtension v w] : ℕ :=
  Module.finrank (Chapter10ResidueField v) (Chapter10ResidueField w)

/-- The residue homomorphism induced by an extending valuation. -/
def Chapter10ResidueFieldMap
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    [Valuation.HasExtension v w] :
    Chapter10ResidueField v →+* Chapter10ResidueField w :=
  IsLocalRing.ResidueField.map (algebraMap v.valuationSubring w.valuationSubring)

/-- The residue degree for an extension whose value group may differ. -/
noncomputable def Chapter10HeterogeneousResidueDegree
    {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    (v : Valuation K ΓK) (w : Valuation L ΓL)
    (h : v.IsEquiv (w.comap (algebraMap K L))) : ℕ := by
  letI : Valuation.HasExtension v w := ⟨h⟩
  exact Module.finrank (Chapter10ResidueField v) (Chapter10ResidueField w)

/--
The actual value-group and residue-field data of one finite branch.  The map
and its finite quotient are retained explicitly, rather than identifying
different ordered value groups with a fixed codomain.
-/
structure Chapter10HeterogeneousExtensionData
    {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    (v : Valuation K ΓK) (w : Valuation L ΓL)
    (h : v.IsEquiv (w.comap (algebraMap K L))) where
  valueGroupMap : Chapter10ValueGroup v →* Chapter10ValueGroup w
  valueGroupMap_injective : Function.Injective valueGroupMap
  finite_quotient : Finite (Chapter10ValueGroup w ⧸ valueGroupMap.range)
  ramificationIndex : ℕ

  ramificationIndex_eq :
    ramificationIndex = Nat.card (Chapter10ValueGroup w ⧸ valueGroupMap.range)
  residueDegree : ℕ
  residueDegree_eq :
    residueDegree = Chapter10HeterogeneousResidueDegree v w h
/-- Value-group inclusion for a valuation extension. -/
theorem chapter10_value_group_inclusion
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    (h : v.IsEquiv (w.comap (algebraMap K L))) :
    Chapter10ValueGroup v ≤ Chapter10ValueGroup w := by
  sorry

/-- Finiteness of the value-group quotient in a finite extension. -/
theorem chapter10_value_group_quotient_finite
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀] [FiniteDimensional K L]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    (h : v.IsEquiv (w.comap (algebraMap K L)))
    (hΓ : Chapter10ValueGroup v ≤ Chapter10ValueGroup w) :
    Finite (Chapter10ValueGroup w ⧸
      (Chapter10ValueGroup v).subgroupOf (Chapter10ValueGroup w)) := by
  sorry

/-- Finiteness of the induced residue-field extension. -/
theorem chapter10_residue_degree_finite
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀] [FiniteDimensional K L]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    [h : Valuation.HasExtension v w] :
    FiniteDimensional (Chapter10ResidueField v) (Chapter10ResidueField w) := by
  sorry

/-- The value-group and residue directions give independent vectors. -/
theorem chapter10_value_residue_product_independence
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    [Valuation.HasExtension v w]
    {r s : ℕ} (x : Fin r → L) (y : Fin s → L)
    (hvalues : Pairwise (fun i j => w (x i) ≠ w (x j)))
    (hunits : ∀ j, w (y j) = 1)
    (hresidues : ∀ i j, i ≠ j → w (y i - y j) = 1) :
    LinearIndependent K (fun ij : Fin r × Fin s => x ij.1 * y ij.2) := by
  sorry

/-- The single-extension fundamental inequality ef ≤ [L:K]. -/
theorem chapter10_single_extension_fundamental_inequality
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀] [FiniteDimensional K L]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    [h : Valuation.HasExtension v w]
    (hΓ : Chapter10ValueGroup v ≤ Chapter10ValueGroup w) :
    Chapter10RamificationIndex v w hΓ * Chapter10ResidueDegree v w ≤
      Module.finrank K L := by
  sorry

/-- Normalized discrete additive valuations. -/
def Chapter10DiscreteAddValuation {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Prop :=
  ∃ π : K, π ≠ 0 ∧ v π = 1 ∧
    ∀ x : K, x ≠ 0 → ∃ n : ℤ, v x = (n : WithTop ℤ)

/-- Units for an additive valuation. -/
def Chapter10AddValuationUnit {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (u : K) : Prop :=
  u ≠ 0 ∧ v u = 0

/-- Restriction of a normalized discrete valuation scales by the ramification index. -/
theorem chapter10_normalized_restriction_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AddValuation K (WithTop ℤ)) (w : AddValuation L (WithTop ℤ))
    (hcomap : v = w.comap (algebraMap K L))
    (hv : Chapter10DiscreteAddValuation v)
    (hw : Chapter10DiscreteAddValuation w) :
    ∃ e : ℕ, 0 < e ∧ ∀ x : K, x ≠ 0 →
      w (algebraMap K L x) = e • v x := by
  sorry

/-- Uniformizers are related by π = u Piᵉ. -/
theorem chapter10_uniformizer_relation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AddValuation K (WithTop ℤ)) (w : AddValuation L (WithTop ℤ))
    (π : K) (Pi : L) (e : ℕ)
    (he : 0 < e) (hπ : v π = 1) (hPi : w Pi = 1)
    (hv : Chapter10DiscreteAddValuation v)
    (hw : Chapter10DiscreteAddValuation w)
    (hscale : ∀ x : K, x ≠ 0 →
      w (algebraMap K L x) = e • v x) :
    ∃ u : L, Chapter10AddValuationUnit w u ∧
      algebraMap K L π = u * Pi ^ e := by
  sorry

/-- The residue-field injection is finite in the finite-extension setting. -/
theorem chapter10_ramification_residue_finite
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀] [FiniteDimensional K L]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    [Valuation.HasExtension v w] :
    FiniteDimensional (Chapter10ResidueField v) (Chapter10ResidueField w) := by
  sorry

/-! ## 10.5. Several extensions and the fundamental inequality -/

/-- The numerical data attached to one branch. -/
structure Chapter10BranchInvariant where
  degree : ℕ
  e : ℕ
  f : ℕ

/-- The contribution ef of one branch. -/
def Chapter10BranchContribution (p : Chapter10BranchInvariant) : ℕ :=
  p.e * p.f

/-- A valuation branch together with its numerical profile. -/
structure Chapter10ValuationBranch {K L ΓK : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero ΓK]
    (v : Valuation K ΓK) where
  valueGroup : Type*
  [orderedValueGroup : LinearOrderedCommGroupWithZero valueGroup]
  w : Valuation L valueGroup
  isExtension : v.IsEquiv (w.comap (algebraMap K L))
  extensionData : Chapter10HeterogeneousExtensionData v w isExtension
  profile : Chapter10BranchInvariant
  profile_e : profile.e = extensionData.ramificationIndex
  profile_f : profile.f = extensionData.residueDegree

/-- A finite list of branches containing every inequivalent extension. -/
def Chapter10CompleteBranchFamily
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    (v : Valuation K ΓK)
    (S : Finset (Chapter10ValuationBranch (K := K) (L := L) v)) : Prop :=
  ∀ (ΓL : Type*) [LinearOrderedCommGroupWithZero ΓL]
      (w : Valuation L ΓL),
    v.IsEquiv (w.comap (algebraMap K L)) ↔
      ∃ b, b ∈ S ∧
        (letI : LinearOrderedCommGroupWithZero b.valueGroup := b.orderedValueGroup
         b.w.IsEquiv w)

/-- A branch profile is its ramification index and residue degree. -/
def Chapter10BranchProfileCorrect
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    (v : Valuation K ΓK)
    (b : Chapter10ValuationBranch (K := K) (L := L) v) : Prop :=
  letI : LinearOrderedCommGroupWithZero b.valueGroup := b.orderedValueGroup
  b.profile.e = b.extensionData.ramificationIndex ∧
    b.profile.f = b.extensionData.residueDegree

/-- Residue degree as a function of the explicit extension equivalence. -/
noncomputable def Chapter10ResidueDegreeOfExtension
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    (h : v.IsEquiv (w.comap (algebraMap K L))) : ℕ := by
  letI : Valuation.HasExtension v w := ⟨h⟩
  exact Chapter10ResidueDegree v w

/-- There are only finitely many inequivalent extensions of a finite extension. -/
theorem chapter10_finitely_many_valuation_extensions
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] [FiniteDimensional K L]
    (v : Valuation K ΓK) :
    ∃ S : Finset (Chapter10ValuationBranch (K := K) (L := L) v),
      Chapter10CompleteBranchFamily v S := by
  sorry

/-- The sum of ef over all branches is bounded by the extension degree. -/
theorem chapter10_fundamental_inequality
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] [FiniteDimensional K L]
    (v : Valuation K ΓK) :
    ∃ S : Finset (Chapter10ValuationBranch (K := K) (L := L) v),
      Chapter10CompleteBranchFamily v S ∧
        Finset.sum S (fun b => Chapter10BranchContribution b.profile) ≤
          Module.finrank K L := by
  sorry

/-- A henselization is immediate: it does not change value group or residue field. -/
def Chapter10ImmediateValuationExtension
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀) : Prop :=
  Chapter10ValueGroup v = Chapter10ValueGroup w ∧
    Nonempty (Chapter10ResidueField v ≃+* Chapter10ResidueField w)

/-- A named interface for a henselization with its immediate-extension data. -/
structure Chapter10HenselizationData (K Kh Γ₀ : Type*) [Field K] [Field Kh]
    [Algebra K Kh] [LinearOrderedCommGroupWithZero Γ₀] where
  v : Valuation K Γ₀
  vh : Valuation Kh Γ₀
  immediate : Chapter10ImmediateValuationExtension v vh
  henselian : HenselianLocalRing vh.valuationSubring

/-- The henselization has the same value group and residue field. -/
theorem chapter10_henselization_is_immediate
    {K Kh Γ₀ : Type*} [Field K] [Field Kh] [Algebra K Kh]
    [LinearOrderedCommGroupWithZero Γ₀]
    (H : Chapter10HenselizationData K Kh Γ₀) :
    Chapter10ImmediateValuationExtension H.v H.vh := by
  sorry

/-- Tensoring a finite extension with a henselization preserves its dimension. -/
theorem chapter10_henselized_tensor_dimension
    {K L Kh : Type*} [Field K] [Field L] [Field Kh]
    [Algebra K L] [Algebra K Kh] [Algebra Kh (L ⊗[K] Kh)]
    [FiniteDimensional K L] :
    Module.finrank Kh (L ⊗[K] Kh) = Module.finrank K L := by
  sorry

/-- The henselized tensor product used to separate the branches. -/
abbrev Chapter10HenselizedTensor (K L Kh : Type*) [CommRing K] [CommRing L]
    [CommRing Kh] [Algebra K L] [Algebra K Kh] : Type _ := L ⊗[K] Kh

/-- Maximal ideals of an algebra are the local-factor indices. -/
def Chapter10TensorMaximalIdeals {C : Type*} [CommRing C] : Set (Ideal C) :=
  {P | P.IsMaximal}

/-- The tensor product has finitely many maximal local factors in the finite case. -/
theorem chapter10_henselized_tensor_has_finitely_many_factors
    {K L Kh : Type*} [Field K] [Field L] [Field Kh]
    [Algebra K L] [Algebra K Kh] [FiniteDimensional K L]
    : Set.Finite (Chapter10TensorMaximalIdeals (C := L ⊗[K] Kh)) := by
  sorry

/-- Dimensions of the local tensor factors account for the total dimension. -/
theorem chapter10_henselized_tensor_factor_dimensions
    {K L Kh : Type*} [Field K] [Field L] [Field Kh]
    [Algebra K L] [Algebra K Kh] [Algebra Kh (L ⊗[K] Kh)]
    [FiniteDimensional K L]
    (factors : Finset (Ideal (L ⊗[K] Kh)))
    (hmax : ∀ P ∈ factors, P.IsMaximal)
    (hexhaustive : ∀ P, P.IsMaximal ↔ P ∈ factors) :
    Finset.sum factors
        (fun P => Module.finrank Kh ((L ⊗[K] Kh) ⧸ P)) =
      Module.finrank K L := by
  sorry

/-- The defect records the possible loss in a local tensor factor. -/
def Chapter10Defect (degree e f : ℕ) : ℚ :=
  (degree : ℚ) / ((e * f : ℕ) : ℚ)

/-- Defect one is exactly equality in the fundamental inequality. -/
theorem chapter10_defect_eq_one_iff
    (degree e f : ℕ) (hpos : 0 < e * f) (hdiv : e * f ∣ degree) :
    Chapter10Defect degree e f = 1 ↔ degree = e * f := by
  sorry

/-- A numerical profile is defectless when its degree is ef. -/
def Chapter10DefectlessProfile (p : Chapter10BranchInvariant) : Prop :=
  p.degree = p.e * p.f

/-- The finite normalization hypothesis in the DVR equality theorem. -/
def Chapter10FiniteNormalization (A B : Type*) [Semiring A]
    [AddCommMonoid B] [Module A B] : Prop :=
  Module.Finite A B

/-- Finite normalization of a DVR gives equality in the sum formula. -/
theorem chapter10_finite_dvr_normalization_fundamental_equality
    {A B K L Γ₀ : Type*} [CommRing A] [CommRing B]
    [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀] [FiniteDimensional K L]
    [Module A B] [IsDomain A] [IsDiscreteValuationRing A]
    (hfinite : Chapter10FiniteNormalization A B)
    (v : Valuation K Γ₀)
    (S : Finset (Chapter10ValuationBranch (K := K) (L := L) v))
    (hcomplete : Chapter10CompleteBranchFamily v S)
    (hprofile : ∀ b ∈ S, Chapter10BranchProfileCorrect v b) :
    Finset.sum S (fun b => Chapter10BranchContribution b.profile) = Module.finrank K L := by
  sorry

/-- The normalization of a ring in an algebra, named for the Dedekind case. -/
noncomputable def Chapter10Normalization (A L : Type*) [CommRing A] [CommRing L]
    [Algebra A L] : Subalgebra A L :=
  integralClosure A L

/-- Finite separable extensions of Dedekind domains have finite normalization. -/
theorem chapter10_dedekind_separable_normalization_finite
    {A K L : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [FiniteDimensional K L]
    (hseparable : Algebra.IsSeparable K L) :
    Module.Finite A (Chapter10Normalization A L) := by
  sorry

/-- Complete discretely valued fields are defectless, without residue perfection. -/
theorem chapter10_complete_discrete_valuation_defectless
    {K L Γ₀ : Type*} [NormedField K] [NormedField L]
    [CompleteSpace K] [IsUltrametricDist K] [Algebra K L]
    [FiniteDimensional K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀)
    (S : Finset (Chapter10ValuationBranch (K := K) (L := L) v))
    (hcomplete : Chapter10CompleteBranchFamily v S)
    (hprofile : ∀ b ∈ S, Chapter10BranchProfileCorrect v b) :
    Finset.sum S (fun b => Chapter10BranchContribution b.profile) = Module.finrank K L := by
  sorry

/-- A convenient record for a nontrivial separable defect extension. -/
structure Chapter10SeparableDefectExample where
  K : Type*
  L : Type*
  [fieldK : Field K]
  [fieldL : Field L]
  [algebraKL : Algebra K L]
  Γ : Type*
  [orderedValueGroup : LinearOrderedCommGroupWithZero Γ]
  [finiteDegree : FiniteDimensional K L]
  v : Valuation K Γ
  w : Valuation L Γ
  extension : v.IsEquiv (w.comap (algebraMap K L))
  valueGroupInclusion : Chapter10ValueGroup v ≤ Chapter10ValueGroup w
  degree : ℕ
  e : ℕ
  f : ℕ
  defect : ℕ
  residueCharacteristic : ℕ
  residueCharacteristic_prime : Nat.Prime residueCharacteristic
  residueCharacteristic_is_residue_char :
    CharP (Chapter10ResidueField v) residueCharacteristic
  separable : Algebra.IsSeparable K L
  degree_eq_field_degree : degree = Module.finrank K L
  ramification_eq : e = Chapter10RamificationIndex v w valueGroupInclusion
  residueDegree_eq :
    f = Chapter10HeterogeneousResidueDegree v w extension
  degree_eq_defect_times_ef : degree = defect * (e * f)
  nontrivial : 1 < defect

/-- Separable defect extensions can occur in poorly controlled positive residue characteristic. -/
theorem chapter10_separable_defect_extensions_can_occur :
    ∃ E : Chapter10SeparableDefectExample,
      Nat.Prime E.residueCharacteristic ∧
        1 < E.defect := by
  sorry

/-- Henselian valuation rings have one branch over an algebraic extension. -/
theorem chapter10_henselian_valuation_has_unique_branch
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀] [Algebra.IsAlgebraic K L]
    (v : Valuation K Γ₀) [HenselianLocalRing v.valuationSubring]
    (w₁ w₂ : Valuation L Γ₀)
    (h₁ : v.IsEquiv (w₁.comap (algebraMap K L)))
    (h₂ : v.IsEquiv (w₂.comap (algebraMap K L))) :
    w₁.IsEquiv w₂ := by
  sorry

/-- Complete nonarchimedean fields are henselian. -/
theorem chapter10_complete_nonarchimedean_is_henselian
    (K : Type*) [NormedField K] [CompleteSpace K] [IsUltrametricDist K] :
    HenselianLocalRing K := by
  sorry

/-! ## 10.6. Finite extensions of complete fields -/

/-- Coordinate max norm attached to a finite basis. -/
def Chapter10CoordinateNorm {K L ι : Type*} [NormedField K]
    [AddCommGroup L] [Module K L] [Fintype ι] [Nonempty ι]
    (b : Module.Basis ι K L) : L → ℝ :=
  fun x => Finset.univ.sup' Finset.univ_nonempty (fun i => ‖b.repr x i‖)

/-- Two real-valued norms are equivalent up to positive constants. -/
def Chapter10EquivalentRealNorms {L : Type*} (N M : L → ℝ) : Prop :=
  ∃ c d : ℝ, 0 < c ∧ 0 < d ∧
    (∀ x, N x ≤ c * M x) ∧ (∀ x, M x ≤ d * N x)

/-- Coordinate Cauchy condition, stated without choosing a topology on L. -/
def Chapter10CauchyInNorm {L : Type*} [AddGroup L]
    (N : L → ℝ) (s : ℕ → L) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ m n : ℕ,
    N₀ ≤ m → N₀ ≤ n → N (s m - s n) < ε

/-- Convergence in a specified real-valued norm. -/
def Chapter10TendsToInNorm {L : Type*} [AddGroup L]
    (N : L → ℝ) (s : ℕ → L) (x : L) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n : ℕ,
    N₀ ≤ n → N (s n - x) < ε

/-- The coordinate max norm is complete when the base field is complete. -/
theorem chapter10_coordinate_norm_complete
    {K L ι : Type*} [NormedField K] [CompleteSpace K]
    [Field L] [Algebra K L] [Fintype ι] [Nonempty ι]
    (b : Module.Basis ι K L) (s : ℕ → L)
    (hs : Chapter10CauchyInNorm (Chapter10CoordinateNorm b) s) :
    ∃ x : L, Chapter10TendsToInNorm (Chapter10CoordinateNorm b) s x := by
  sorry

/-- Every K-linear endomorphism is bounded for a coordinate norm. -/
theorem chapter10_coordinate_norm_linear_map_bound
    {K L ι : Type*} [NormedField K] [Field L] [Algebra K L]
    [Fintype ι] [Nonempty ι] [FiniteDimensional K L]
    (b : Module.Basis ι K L) (T : L →ₗ[K] L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : L,
      Chapter10CoordinateNorm b (T x) ≤
        C * Chapter10CoordinateNorm b x := by
  sorry

/-- Coordinate norms from two bases are equivalent. -/
theorem chapter10_coordinate_norms_equivalent
    {K L ι κ : Type*} [NormedField K] [Field L] [Algebra K L]
    [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    [FiniteDimensional K L]
    (b : Module.Basis ι K L) (c : Module.Basis κ K L) :
    Chapter10EquivalentRealNorms (Chapter10CoordinateNorm b)
      (Chapter10CoordinateNorm c) := by
  sorry

/-- Multiplication is bounded by a constant times the product of coordinate norms. -/
theorem chapter10_coordinate_norm_multiplication_bound
    {K L ι : Type*} [NormedField K] [Field L] [Algebra K L]
    [Fintype ι] [Nonempty ι] [FiniteDimensional K L]
    (b : Module.Basis ι K L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : L,
      Chapter10CoordinateNorm b (x * y) ≤
        C * Chapter10CoordinateNorm b x * Chapter10CoordinateNorm b y := by
  sorry

/-- Nonarchimedean triangle inequality for a real-valued norm. -/
def Chapter10NonarchimedeanNorm {L : Type*} [Add L] (N : L → ℝ) : Prop :=
  ∀ x y : L, N (x + y) ≤ max (N x) (N y)

/-- Extension of the base-field norm. -/
def Chapter10ExtendsBaseNorm {K L : Type*} [NormedField K]
    [Field L] [Algebra K L] (N : L → ℝ) : Prop :=
  ∀ x : K, N (algebraMap K L x) = ‖x‖

/-- Power multiplicativity, including the norm formula's uniqueness condition. -/
def Chapter10PowerMultiplicative {L : Type*} [Pow L ℕ] (N : L → ℝ) : Prop :=
  ∀ (x : L) (n : ℕ), N (x ^ n) = N x ^ n

/-- The property characterizing the unique nonarchimedean extension norm. -/
def Chapter10UniqueExtensionNormProperty
    {K L : Type*} [NormedField K] [Field L] [Algebra K L]
    (N : AlgebraNorm K L) : Prop :=
  Chapter10NonarchimedeanNorm (N : L → ℝ) ∧
    Chapter10PowerMultiplicative (N : L → ℝ) ∧
    Chapter10ExtendsBaseNorm (K := K) (L := L) (N : L → ℝ)


/-- The actual absolute-value axioms for an algebraic extension. -/
def Chapter10AlgebraicExtensionNormProperty
    {K L : Type*} [NormedField K] [Field L] [Algebra K L]
    (N : L → ℝ) : Prop :=
  N 0 = 0 ∧ N 1 = 1 ∧
    (∀ x, 0 ≤ N x) ∧ (∀ x, N x = 0 ↔ x = 0) ∧
    (∀ x y, N (x * y) = N x * N y) ∧
    (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧
    Chapter10ExtendsBaseNorm (K := K) (L := L) N
/-- Any nonarchimedean norm on a finite extension is equivalent to a coordinate norm. -/
theorem chapter10_nonarchimedean_norm_equivalent_to_coordinate_norm
    {K L ι : Type*} [NormedField K] [CompleteSpace K]
    [Field L] [Algebra K L] [Fintype ι] [Nonempty ι]
    [FiniteDimensional K L]
    (b : Module.Basis ι K L) (N : AlgebraNorm K L)
    (hN : Chapter10NonarchimedeanNorm (N : L → ℝ)) :
    Chapter10EquivalentRealNorms (N : L → ℝ) (Chapter10CoordinateNorm b) := by
  sorry

/-- The reverse inequality in the finite-dimensional nonarchimedean norm lemma. -/
theorem chapter10_nonarchimedean_norm_reverse_coordinate_bound
    {K L ι : Type*} [NormedField K] [CompleteSpace K]
    [Field L] [Algebra K L] [Fintype ι] [Nonempty ι]
    [FiniteDimensional K L]
    (b : Module.Basis ι K L) (N : AlgebraNorm K L)
    (hN : Chapter10NonarchimedeanNorm (N : L → ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : L,
      c * Chapter10CoordinateNorm b x ≤ N x := by
  sorry

/-- The one-dimensional induction step uses a positive distance from a closed subspace. -/
theorem chapter10_closed_subspace_distance_step
    {K L : Type*} [NormedField K] [CompleteSpace K]
    [NormedField L] [Algebra K L] (W : Submodule K L) (e : L)
    (hclosed : IsClosed (W : Set L)) (he : e ∉ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : W, δ ≤ ‖e - w‖ := by
  sorry

/-- Every finite algebraic extension of a complete normed field is complete. -/
theorem chapter10_finite_extension_is_complete
    {K L : Type*} [NormedField K] [CompleteSpace K]
    [NormedField L] [NormedAlgebra K L] [FiniteDimensional K L] :
    CompleteSpace L := by
  sorry

/--
Uniqueness over an arbitrary algebraic extension.  The values are compared
as real absolute values, so this statement does not silently fix a value
group for the algebraic extension.
-/
theorem chapter10_unique_complete_extension_norm
    {K L : Type*} [NormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] :
    ∃ N : L → ℝ,
      Chapter10AlgebraicExtensionNormProperty (K := K) (L := L) N ∧
        ∀ N' : L → ℝ,
          Chapter10AlgebraicExtensionNormProperty (K := K) (L := L) N' →
            ∀ x, N' x = N x := by
  sorry

/-- K-automorphisms preserve the unique extension norm. -/
theorem chapter10_automorphism_preserves_unique_norm
    {K L : Type*} [NormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (N : AlgebraNorm K L)
    (hN : Chapter10UniqueExtensionNormProperty N)
    (σ : L ≃ₐ[K] L) :
    ∀ x : L, N (σ x) = N x := by
  sorry

/-- Norm/product formula for a finite extension. -/
def Chapter10NormProductFormula
    {K L : Type*} [NormedField K] [Field L] [Algebra K L]
    (N : L → ℝ) : Prop :=
  ∀ x : L,
    N x = Real.rpow ‖Algebra.norm K x‖
      ((Module.finrank K L : ℝ)⁻¹)

theorem chapter10_complete_extension_norm_product_formula
    {K L : Type*} [NormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (N : AlgebraNorm K L)
    (hN : Chapter10UniqueExtensionNormProperty N) :
    Chapter10NormProductFormula (K := K) (L := L) (N : L → ℝ) := by
  sorry

/-- Complete fields give the unique valuation extension in the exact henselian sense. -/
theorem chapter10_henselian_unique_extension
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀] [Algebra.IsAlgebraic K L]
    (v : Valuation K Γ₀) [HenselianLocalRing v.valuationSubring]
    (w₁ w₂ : Valuation L Γ₀)
    (h₁ : v.IsEquiv (w₁.comap (algebraMap K L)))
    (h₂ : v.IsEquiv (w₂.comap (algebraMap K L))) :
    w₁.IsEquiv w₂ := by
  sorry

/-- Every algebraic element lies in a finite intermediate extension. -/
theorem chapter10_algebraic_element_in_finite_subextension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {x : L} (hx : IsAlgebraic K x) :
    ∃ E : IntermediateField K L, x ∈ E ∧ FiniteDimensional K E := by
  sorry

/-- Compatible finite-extension norms glue over an infinite algebraic extension. -/
theorem chapter10_compatible_finite_values_glue
    {K L : Type*} [NormedField K] [CompleteSpace K]
    [Field L] [Algebra K L]
    (Nfin : ∀ E : IntermediateField K L, E → ℝ)
    (hfinite : ∀ x : L, ∃ E : IntermediateField K L,
      x ∈ E ∧ FiniteDimensional K E)
    (hcompat : ∀ (E F : IntermediateField K L) (hEF : E ≤ F) (x : E),
      Nfin E x = Nfin F ⟨x.1, hEF x.2⟩) :
    ∃ N : L → ℝ, ∀ (E : IntermediateField K L) (x : E),
      N (x : L) = Nfin E x := by
  sorry

/-! ## 10.7. Concrete finite extensions -/

/-- A compact profile for the examples in this section. -/
structure Chapter10FiniteExtensionProfile where
  degree : ℕ
  ramificationIndex : ℕ
  residueDegree : ℕ

/-- The profile of a totally ramified extension. -/
def Chapter10TotallyRamified (p : Chapter10FiniteExtensionProfile) : Prop :=
  p.residueDegree = 1

/-- The profile of an unramified extension. -/
def Chapter10Unramified (p : Chapter10FiniteExtensionProfile) : Prop :=
  p.ramificationIndex = 1

/-- The equal-characteristic relation t = uⁿ. -/
def Chapter10PowerParameterRelation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (t : K) (u : L) (n : ℕ) : Prop :=
  algebraMap K L t = u ^ n

/-- Scaling of the normalized value on the base field. -/
def Chapter10ValueScaling
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : K → ℤ) (vL : L → ℤ) (n : ℕ) : Prop :=
  ∀ x : K, x ≠ 0 → vL (algebraMap K L x) = n * vK x

/-- The Laurent-series valuation used in the equal-characteristic model. -/
def Chapter10LaurentSeriesValuation (k : Type*) [Field k] :
    Valuation (LaurentSeries k) ℤᵐ⁰ :=
  Valued.v

/-- Value of a power of the Laurent-series parameter. -/
theorem chapter10_laurent_series_parameter_value
    {k : Type*} [Field k] (n : ℕ) :
    Chapter10LaurentSeriesValuation k
        (((PowerSeries.X : PowerSeries k) : LaurentSeries k) ^ n) =
      WithZero.exp (-(n : ℤ)) := by
  sorry

/-- The extension k((u))/k((t)) with t = uⁿ has e = n and f = 1. -/
theorem chapter10_equal_characteristic_totally_ramified_profile
    {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L]
    [FiniteDimensional K L]
    (t : K) (u : L) (n : ℕ)
    (hn : 0 < n)
    (hparameter : Chapter10PowerParameterRelation t u n)
    (hirreducible : Irreducible (X ^ n - C t : K[X]))
    (hdegree : Module.finrank K L = n)
    (vK : K → ℤ) (vL : L → ℤ)
    (hscale : Chapter10ValueScaling vK vL n) :
    ∃ p : Chapter10FiniteExtensionProfile,
      p.degree = n ∧ p.ramificationIndex = n ∧ p.residueDegree = 1 ∧
        Chapter10TotallyRamified p := by
  sorry

/-- Constant-field extensions have e = 1 and residue degree equal to the field degree. -/
theorem chapter10_constant_field_extension_profile
    {k k' : Type*} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
    (n : ℕ) (hn : n = Module.finrank k k') :
    ∃ p : Chapter10FiniteExtensionProfile,
      p.degree = n ∧ p.ramificationIndex = 1 ∧
        p.residueDegree = Module.finrank k k' ∧ Chapter10Unramified p := by
  sorry

/-- Combining a constant extension and a totally ramified extension gives ef. -/
theorem chapter10_combined_equal_characteristic_profile
    {e f : ℕ} (he : 0 < e) (hf : 0 < f) :
    ∃ p : Chapter10FiniteExtensionProfile,
      p.degree = e * f ∧ p.ramificationIndex = e ∧
        p.residueDegree = f := by
  sorry

/-- A local polynomial criterion spelling out the Eisenstein coefficient conditions. -/
def Chapter10EisensteinAtUniformizer {A : Type*} [CommRing A]
    (P : A[X]) (π : A) : Prop :=
  P.Monic ∧ P.natDegree ≠ 0 ∧
    (∀ i < P.natDegree, π ∣ P.coeff i) ∧
    ¬ π ^ 2 ∣ P.constantCoeff

/-- Eisenstein irreducibility. -/
theorem chapter10_eisenstein_irreducible
    {A : Type*} [CommRing A] [IsDomain A]
    (P : A[X]) (π : A) (hπ : Prime π)
    (hE : Chapter10EisensteinAtUniformizer P π) :
    Irreducible P := by
  sorry

/-- The minimal-value comparison for an Eisenstein root. -/
theorem chapter10_eisenstein_root_value_comparison
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (P : K[X]) (π : K) (α : L) (n : ℕ)
    (hroot : Polynomial.eval₂ (algebraMap K L) α P = 0)
    (hdegree : P.natDegree = n)
    (hE : Chapter10EisensteinAtUniformizer P π)
    (hπ : vL (algebraMap K L π) = 1)
    (hscale : vL (algebraMap K L (P.leadingCoeff)) = 0) :
    vL α = n • vL (algebraMap K L π) := by
  sorry

/-- Eisenstein extensions are totally ramified of the polynomial degree. -/
theorem chapter10_eisenstein_totally_ramified_profile
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (P : K[X]) (π : K) (α : L)
    (hE : Chapter10EisensteinAtUniformizer P π)
    (hroot : Polynomial.eval₂ (algebraMap K L) α P = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hdegree : Module.finrank K L = P.natDegree) :
    ∃ p : Chapter10FiniteExtensionProfile,
      p.degree = P.natDegree ∧ p.ramificationIndex = P.natDegree ∧
        p.residueDegree = 1 ∧ Chapter10TotallyRamified p := by
  sorry

/-- A polynomial has irreducible separable reduction through a chosen residue map. -/
def Chapter10IrreducibleSeparableReduction
    {A k : Type*} [CommRing A] [Field k]
    (res : A →+* k) (P : A[X]) (f : ℕ) : Prop :=
  let Q := P.map res
  Q.Monic ∧ Q.natDegree = f ∧ Irreducible Q ∧ Q.Separable

/-- Irreducible separable reduction gives an unramified extension. -/
theorem chapter10_unramified_lift_profile
    {A K L k : Type*} [CommRing A] [Field K] [Field L] [Field k]
    [Algebra A K] [Algebra A L] [Algebra K L]
    [FiniteDimensional K L]
    (res : A →+* k) (P : A[X]) (f : ℕ)
    (hred : Chapter10IrreducibleSeparableReduction res P f)
    (α : L)
    (hroot : Polynomial.eval₂ (algebraMap A L) α P = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hdegree : Module.finrank K L = f) :
    ∃ p : Chapter10FiniteExtensionProfile,
      p.degree = f ∧ p.ramificationIndex = 1 ∧
        p.residueDegree = f ∧ Chapter10Unramified p := by
  sorry

/-- The p-adic uniformizer has normalized valuation one. -/
theorem chapter10_padic_uniformizer_value
    {p : ℕ} [Fact p.Prime] :
    Padic.valuation (p : ℚ_[p]) = 1 := by
  sorry

/-- The p-adic Eisenstein setup is the preceding theorem with π = p. -/
theorem chapter10_padic_eisenstein_profile
    {p : ℕ} [Fact p.Prime] {L : Type*} [Field L]
    [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (P : ℚ_[p][X]) (α : L)
    (hE : Chapter10EisensteinAtUniformizer P (p : ℚ_[p]))
    (hroot : Polynomial.eval₂ (algebraMap ℚ_[p] L) α P = 0)
    (hgen : Algebra.adjoin ℚ_[p] ({α} : Set L) = ⊤)
    (hdegree : Module.finrank ℚ_[p] L = P.natDegree) :
    ∃ q : Chapter10FiniteExtensionProfile,
      q.degree = P.natDegree ∧ q.ramificationIndex = P.natDegree ∧
        q.residueDegree = 1 := by
  sorry

end

end ValuationsBook.Chapter10
