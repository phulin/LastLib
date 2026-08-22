import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter15.Section04TheMultiplicativePicture
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section07UnramifiedAndTotallyRamifiedEndpoints
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section08AFinalSynthesis
import Mathlib.RingTheory.LaurentSeries

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter15
noncomputable section

open Polynomial
open scoped BigOperators WithZero Polynomial

/-! ## 15.5. Conclusion -/

/-- Book 2, §15.5: the finite flat degree is the sum of local `e f` blocks. -/
theorem coherent_sum_ramification_times_residue_degree
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] [IsDomain R]
    [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S,
        q.1.ramificationIdx R * q.1.inertiaDeg R = Module.finrank R S := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.final_sum_ramification_times_residue_degree p

/-- Book 2, §15.5: for fraction fields the same equality reads `∑ e f = [L : K]`. -/
theorem coherent_fraction_field_degree_formula
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] [IsDomain R]
    [Algebra (FractionRing R) (FractionRing S)]
    [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver S)]
    (hfrac : Module.finrank R S =
      Module.finrank (FractionRing R) (FractionRing S)) :
    ∑ q : p.primesOver S,
        q.1.ramificationIdx R * q.1.inertiaDeg R =
      Module.finrank (FractionRing R) (FractionRing S) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.final_fraction_field_degree_formula p hfrac

/-- Book 2, §15.5: completeness or henselian uniqueness leaves one branch upstairs. -/
theorem coherent_complete_or_henselian_base_has_one_branch
    {K Γ E : Type u} [Field K] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K E]
    (v : Valuation K Γ)
    (hbase :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.HenselianFactorizationProperty
        v.valuationSubring ∨
      IsAdicComplete (IsLocalRing.maximalIdeal v.valuationSubring)
        v.valuationSubring)
    [Algebra.IsAlgebraic K E] :
    ∃ W : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.HeterogeneousValuationExtension v E,
      ∀ W' : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.HeterogeneousValuationExtension v E,
        (letI : LinearOrderedCommGroupWithZero W.valueGroup := W.orderedValueGroup
         letI : LinearOrderedCommGroupWithZero W'.valueGroup := W'.orderedValueGroup
         W'.valuation.IsEquiv W.valuation) := by
  have hfactor :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.HenselianFactorizationProperty
        v.valuationSubring := by
    rcases hbase with hH | hcomplete
    · exact hH
    · exact
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.complete_separated_local_ring_is_henselian
          hcomplete
  exact
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.complete_or_henselian_base_has_one_branch
      v hfactor

/--
Book 2, §15.5: an Eisenstein root supplies coordinates for the totally
ramified direction, including the uniformizer, ramification index, and
residue degree.
-/
theorem coherent_eisenstein_coordinates_control_total_ramification
    {A K L Γ : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L]
    (vK : Valuation K Γ) (v : Valuation L Γ) [vK.HasExtension v]
    [Valuation.IsRankOneDiscrete vK] [Valuation.IsRankOneDiscrete v]
    {n : ℕ} (π : A) (f : A[X]) (Pi : L)
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π f)
    (hroot : aeval Pi f = 0) (hdegree : f.natDegree = n)
    (hgenerates : Algebra.adjoin K ({Pi} : Set L) = ⊤)
    (hbaseIntegers : vK.Integers A)
    (hbaseValuationRing :
      (vK.valuationSubring : Set K) = Set.range (algebraMap A K))
    (hupperIntegralClosure :
      (v.valuationSubring : Set L) = (integralClosure A L : Set L)) :
    v.IsUniformizer Pi ∧
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
          vK.valuationSubring v.valuationSubring
          (IsLocalRing.maximalIdeal v.valuationSubring) = n ∧
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
          vK.valuationSubring v.valuationSubring
          (IsLocalRing.maximalIdeal v.valuationSubring) = 1 := by
  have h :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisenstein_root_is_uniformizer_and_totally_ramified
      vK v π f Pi hf hroot hdegree hgenerates hbaseIntegers
      hbaseValuationRing hupperIntegralClosure
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Book 2, §15.5: Eisenstein coordinates leave the residue field unchanged. -/
theorem coherent_eisenstein_coordinates_preserve_residue_field
    {A K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    {n : ℕ} (π : A) (f : A[X]) (Pi : L)
    [IsLocalRing (Algebra.adjoin A ({Pi} : Set L))]
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π f)
    (hroot : aeval Pi f = 0) (hdegree : f.natDegree = n) :
    Nonempty
      ((A ⧸ IsLocalRing.maximalIdeal A) ≃+*
        (Algebra.adjoin A ({Pi} : Set L) ⧸
          IsLocalRing.maximalIdeal (Algebra.adjoin A ({Pi} : Set L)))) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisenstein_residue_field_is_unchanged
    (A := A) (K := K) (L := L) π f Pi hf hroot hdegree

/-- Book 2, §15.5: the integral closure is the Eisenstein root order. -/
theorem coherent_eisenstein_coordinates_generate_integral_closure
    {A K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    {n : ℕ} (π : A) (f : A[X]) (Pi : L)
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π f)
    (hroot : aeval Pi f = 0) (hdegree : f.natDegree = n)
    (hgenerates : Algebra.adjoin K ({Pi} : Set L) = ⊤) :
    (integralClosure A L : Set L) =
      (Algebra.adjoin A ({Pi} : Set L) : Set L) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisenstein_integral_closure_is_root_order
    (A := A) (K := K) (L := L) π f Pi hf hroot hdegree hgenerates

/-- Book 2, §15.5: the assembled valuation/ring/residue/branch dictionary. -/
theorem coherent_local_arithmetic_dictionary
    {A K B L : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
    [IsLocalRing A] [Algebra A K] [Algebra A B] [Algebra A L]
    [Algebra K L] [Algebra B L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (P : Ideal B) [P.IsPrime]
    (v : Valuation K ℤᵐ⁰) (w : Valuation L ℤᵐ⁰)
    (hext : v.IsEquiv (w.comap (algebraMap K L)))
    (hP : P.IsMaximal)
    (hP_liesOver : P.LiesOver (IsLocalRing.maximalIdeal A))
    (hcenter : ∀ x : B, x ∈ P ↔ w (algebraMap B L x) < 1) :
    Nonempty
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Chapter12LocalArithmeticDictionary
        (A := A) (K := K) (B := B) (L := L) P v w) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.local_arithmetic_dictionary
    P v w hext hP hP_liesOver hcenter

/-!
The final paragraphs recall the preceding Krasner, finiteness, and
equal-characteristic chapters.  These definitions make the precise
book-facing targets explicit without importing a chapter aggregator.
-/

/-- The intermediate field generated by one chosen root. -/
def chapter15GeneratedRootField
    {K E : Type*} [Field K] [Field E] [Algebra K E] (α : E) :
    IntermediateField K E :=
  IntermediateField.adjoin K ({α} : Set E)

/-- Equivalence of the fields generated by two matched roots. -/
def chapter15GeneratedRootFieldEquivalent
    {K E : Type*} [Field K] [Field E] [Algebra K E] (α β : E) : Prop :=
  Nonempty
    (↥(chapter15GeneratedRootField (K := K) α) ≃ₐ[K]
      ↥(chapter15GeneratedRootField (K := K) β))

/-- Local constancy of the generated field in coefficient space. -/
def chapter15GeneratedFieldLocallyConstant
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [TopologicalSpace (K[X])] (f : K[X]) (α : E)
    (root : K[X] → E) : Prop :=
  ∃ U : Set (K[X]), IsOpen U ∧ f ∈ U ∧ root f = α ∧
    ∀ g, g ∈ U →
      aeval (root g) g = 0 ∧
        chapter15GeneratedRootFieldEquivalent (K := K) (E := E) (root f) (root g)

/-
DEPENDENCY_GUESS: the preceding Krasner chapter supplies this package from a
monic separable irreducible polynomial and a simple root.  Keeping the
neighborhood, root selector, and field-equivalence conclusion together gives
the later compactness argument an explicit input.
-/
structure Chapter15KrasnerStabilityData
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [TopologicalSpace (K[X])] (f : K[X]) (α : E) where
  monic : f.Monic
  irreducible : Irreducible f
  separable : f.Separable
  root : K[X] → E
  root_at_f : root f = α
  polynomial_root : aeval α f = 0
  local_constancy : chapter15GeneratedFieldLocallyConstant f α root

/-- The subextensions of degree at most `N` inside a fixed algebraic closure. -/
def chapter15BoundedDegreeSubextensions
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (N : ℕ) :
    Set (IntermediateField K Ω) :=
  {L | Module.Finite K L ∧ Module.finrank K L ≤ N}

/-
DEPENDENCY_GUESS: this is the fixed-algebraic-closure form of the
Krasner/compactness finiteness theorem recalled in §15.5.
-/
theorem characteristic_zero_bounded_degree_subextensions_finite
    {K Ω Γ : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [Valuation.IsRankOneDiscrete vK]
    [CharZero K] [Fintype (IsLocalRing.ResidueField vK.valuationSubring)]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (N : ℕ) :
    Set.Finite (chapter15BoundedDegreeSubextensions (K := K) (Ω := Ω) N) := by
  sorry

/- DEPENDENCY_GUESS: this bridge converts the fixed-algebraic-closure form
back to the book's formulation by `K`-isomorphism classes. -/
theorem bounded_degree_extension_has_fixed_closure_representative
    {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [FiniteDimensional K L]
    [Algebra.IsAlgebraic K L] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (N : ℕ) (hdegree : Module.finrank K L ≤ N) :
    ∃ M : IntermediateField K Ω,
      M ∈ chapter15BoundedDegreeSubextensions (K := K) (Ω := Ω) N ∧
        Nonempty (L ≃ₐ[K] ↥M) := by
  sorry

/-- Tame bounded-degree subextensions, expressed through the actual normalized
ramification-scaling witness rather than an unconstrained auxiliary index. -/
def chapter15TameBoundedDegreeSubextensions
    {K Ω Γ : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (p N : ℕ) : Set (IntermediateField K Ω) :=
  {L | Module.Finite K L ∧ Module.finrank K L ≤ N ∧
    ∃ vL : Valuation L Γ,
        Valuation.IsRankOneDiscrete vL ∧
        vK.IsEquiv (vL.comap (algebraMap K L)) ∧
        ∃ e,
          tameRamification e p ∧
          normalizedValuationRestriction vK vL e}

/- DEPENDENCY_GUESS: the tame compactness theorem from the preceding
chapters should prove finiteness of this set over a finite-residue local field. -/
theorem tame_bounded_degree_subextensions_finite
    {K Ω Γ : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [Valuation.IsRankOneDiscrete vK]
    [Fintype (IsLocalRing.ResidueField vK.valuationSubring)]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (p N : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField vK.valuationSubring) p]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    Set.Finite (chapter15TameBoundedDegreeSubextensions
      (K := K) (Ω := Ω) (Γ := Γ) vK p N) := by
  sorry

/-- Infinitely many pairwise nonisomorphic degree-`p` subextensions. -/
def chapter15InfiniteDegreePSubextensionFamily
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (p : ℕ) : Prop :=
    ∃ ι : Type*, Infinite ι ∧
    ∃ L : ι → IntermediateField K Ω,
      (∀ i, Module.Finite K (L i) ∧ Module.finrank K (L i) = p ∧
        Algebra.IsSeparable K (L i)) ∧
      Pairwise (fun i j =>
        ¬ Nonempty (↥(L i) ≃ₐ[K] ↥(L j)))

/-- A concrete model for the equal-characteristic local field `k((t))`. -/
def chapter15LaurentSeriesModel (k K : Type*) [Field k] [Field K] : Prop :=
  Nonempty (K ≃+* LaurentSeries k)

/- DEPENDENCY_GUESS: this is the Artin--Schreier family recalled in §15.5;
the explicit pole-order construction belongs with the equal-characteristic
finiteness chapter. -/
theorem equal_characteristic_wild_extensions_have_infinite_fixed_degree
    {k K Ω : Type*} [Field k] [Field K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (hmodel : chapter15LaurentSeriesModel k K) :
    chapter15InfiniteDegreePSubextensionFamily (K := K) (Ω := Ω) p := by
  sorry

/-
The closing global-arithmetic sentence is a cross-chapter application
summary.  Its number-field prime, completion, Frobenius-conjugacy, and weak
approximation objects belong to the preceding global-arithmetic API, so this
local-field chapter does not duplicate them with an artificial interface.
-/

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter15
