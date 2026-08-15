import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.ModEq
import LastLib.Book06GlobalClassFieldTheory.Chapter01.Section03FourKindsOfNormAssertion
import LastLib.Book06GlobalClassFieldTheory.Chapter04.Section03ConstructionOfTheFundamentalClass
import LastLib.Book06GlobalClassFieldTheory.Chapter09.Section01TheKnotBetweenLocalAndGlobalNorms

namespace LastLib.Book06GlobalClassFieldTheory.Chapter09

noncomputable section

universe u

/-!
The cohomological obstruction uses the actual Mathlib group-cohomology object
with trivial integral coefficients.  A subgroup restriction is the canonical
map supplied by `groupCohomology.map`.
-/
abbrev chapter09H3 (G : Type) [Group G] :=
  groupCohomology (Rep.trivial ℤ G ℤ) 3

structure Chapter09DecompositionData (G : Type) [Group G] where
  places : Type*
  decompositionGroup : places → Subgroup G

noncomputable def chapter09TrivialRestriction
    {G : Type} [Group G] (D : Subgroup G) :
    Rep.res D.subtype (Rep.trivial ℤ G ℤ) ⟶ Rep.trivial ℤ D ℤ :=
  Rep.ofHom
    ((LinearMap.id : ℤ →ₗ[ℤ] ℤ).intertwiningMap_of_isIntertwiningMap
      (Rep.res D.subtype (Rep.trivial ℤ G ℤ)).ρ
      (Rep.trivial ℤ D ℤ).ρ
      (fun _ _ => by simp))

noncomputable def chapter09H3Restriction
    {G : Type} [Group G] (D : Subgroup G) :
    chapter09H3 G ⟶ chapter09H3 D :=
  groupCohomology.map D.subtype (chapter09TrivialRestriction D) 3

noncomputable def chapter09H3LocalizationMap
    {G : Type} [Group G] (P : Chapter09DecompositionData G) :
    chapter09H3 G →ₗ[ℤ] ∀ v, chapter09H3 (P.decompositionGroup v) :=
  { toFun := fun x v => chapter09H3Restriction (P.decompositionGroup v) x
    map_add' := by
      intro x y
      funext v
      simp [chapter09H3Restriction]
    map_smul' := by
      intro r x
      funext v
      simp [chapter09H3Restriction]
      exact Int.cast_smul_eq_zsmul ℤ r _ }

def chapter09H3LocalizationKernel
    {G : Type} [Group G] (P : Chapter09DecompositionData G) :
    Submodule ℤ (chapter09H3 G) :=
  LinearMap.ker (chapter09H3LocalizationMap P)

instance chapter09_hilbert90_degree_one
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    Unique (groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L)) :=
  inferInstance

noncomputable def chapter09_shapiro_lemma
    {G : Type} [Group G] {D : Subgroup G}
    (A : Rep ℤ D) (n : ℕ) :
    groupCohomology (Rep.coind D.subtype A) n ≅
      groupCohomology A n :=
  groupCohomology.coindIso A n

/-!
The fundamental class supplies the degree shift by two which turns the class
module into the degree-three cohomology appearing in the obstruction formula.
The concrete class module and its extension are supplied by the preceding
global class-field-theory chapters.
-/
structure Chapter09FundamentalClassShiftData
    (R G : Type u) [CommRing R] [Group G] [Fintype G] where
  classModule : Rep.{u} R G
  shiftedModule : Rep.{u} R G
  shift_by_two :
    tateCohomology classModule (1 : ℤ) ≅
      groupCohomology shiftedModule 3

noncomputable def chapter09_fundamental_class_shift_by_two
    {R G : Type u} [CommRing R] [Group G] [Fintype G]
    (F : Chapter09FundamentalClassShiftData R G) :
    tateCohomology F.classModule (1 : ℤ) ≅
      groupCohomology F.shiftedModule 3 :=
  F.shift_by_two

/-!
The cohomological formula is tied to the canonical norm interface and to a
global place system.  In particular, the decomposition groups come from the
global Galois action/decomposition interface, rather than an unrelated family
of subgroups.
`Chapter04PlaceSystem` is the earlier source-order interface for precisely
this action/decomposition data; the remaining comparison theorem is stated
below as a theorem, not smuggled in as an arbitrary field of the realization.
-/
structure Chapter09CanonicalKnotCohomologyData
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] [Fintype (Gal(L / K))] where
  normData :
    LastLib.Book06GlobalClassFieldTheory.Chapter01.GlobalNormInterface K L
  placeSystem :
    LastLib.Book06GlobalClassFieldTheory.Chapter04.Chapter04PlaceSystem
      (Gal(L / K))
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace L)
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace K)
  placeSystem_below : placeSystem.below = normData.below
  decomposition_cyclic_off_finite :
    Set.Finite {w : LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace L |
      ¬ IsCyclic (placeSystem.decomposition w)}

noncomputable def chapter09CanonicalIdeleNormData
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] [Fintype (Gal(L / K))]
    (R : Chapter09CanonicalKnotCohomologyData K L) :
    Chapter09IdeleNormData K L
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleGroup K)
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.BookIdeleGroup L) :=
  chapter09IdeleNormDataOfGlobalNormInterface R.normData

def chapter09CanonicalDecompositionData
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] [Fintype (Gal(L / K))]
    (R : Chapter09CanonicalKnotCohomologyData K L) :
  Chapter09DecompositionData (Gal(L / K)) :=
  { places := LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace L
    decompositionGroup := R.placeSystem.decomposition }

theorem chapter09KnotCohomologyFormula
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] [Fintype (Gal(L / K))]
    (R : Chapter09CanonicalKnotCohomologyData K L)
    [Finite (chapter09KnotGroup (chapter09CanonicalIdeleNormData R))]
    [TopologicalSpace (chapter09KnotGroup (chapter09CanonicalIdeleNormData R))]
    [IsTopologicalGroup (chapter09KnotGroup (chapter09CanonicalIdeleNormData R))]
    [DiscreteTopology (chapter09KnotGroup (chapter09CanonicalIdeleNormData R))] :
    Nonempty
      (Additive (PontryaginDual (chapter09KnotGroup
        (chapter09CanonicalIdeleNormData R))) ≃+
        chapter09H3LocalizationKernel (chapter09CanonicalDecompositionData R)) := by
  sorry

noncomputable def chapter09_knot_cohomology_formula_at
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] [Fintype (Gal(L / K))]
    (R : Chapter09CanonicalKnotCohomologyData K L)
    [Finite (chapter09KnotGroup (chapter09CanonicalIdeleNormData R))]
    [TopologicalSpace (chapter09KnotGroup (chapter09CanonicalIdeleNormData R))]
    [IsTopologicalGroup (chapter09KnotGroup (chapter09CanonicalIdeleNormData R))]
    [DiscreteTopology (chapter09KnotGroup (chapter09CanonicalIdeleNormData R))] :
    Additive (PontryaginDual (chapter09KnotGroup
      (chapter09CanonicalIdeleNormData R))) ≃+
      chapter09H3LocalizationKernel (chapter09CanonicalDecompositionData R) :=
  Classical.choice (chapter09KnotCohomologyFormula R)

theorem chapter09_h3_cyclic_subgroup_vanishes
    {C : Type} [Group C] [Fintype C] [IsCyclic C] :
    Subsingleton (chapter09H3 C) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  let _ : CommGroup C := IsCyclic.commGroup
  let A : Rep ℤ C := Rep.trivial ℤ C ℤ
  let S := Rep.FiniteCyclicGroup.subCompNormHom A g
  have hexact : S.Exact := by
    rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
    intro x hx
    refine ⟨0, ?_⟩
    change (Rep.norm A).hom x = 0 at hx
    rw [Rep.norm_apply] at hx
    simp [A, Representation.norm] at hx
    have hx' : (Fintype.card C : ℤ) * x = 0 := by
      simpa [Finset.sum_const, nsmul_eq_mul] using hx
    have hcard : (Fintype.card C : ℤ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card C ≠ 0)
    have hx0 : x = 0 := (mul_eq_zero.mp hx').resolve_left hcard
    simp [S, A, hx0]
  have hz : CategoryTheory.Limits.IsZero S.homology :=
    (S.exact_iff_isZero_homology).mp hexact
  have hz' : CategoryTheory.Limits.IsZero (groupCohomology A 3) :=
    hz.of_iso (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 3
      (by exact ⟨1, by norm_num⟩))
  change Subsingleton (groupCohomology A 3)
  exact ModuleCat.isZero_iff_subsingleton.mp hz'

abbrev chapter09KleinFour : Type :=
  Multiplicative (ZMod 2 × ZMod 2)

theorem chapter09_h3_klein_four :
    Nonempty (chapter09H3 chapter09KleinFour ≃+ ZMod 2) := by
  sorry

theorem chapter09_h3_localization_kernel_nontrivial
    (P : Chapter09DecompositionData chapter09KleinFour)
    (hcyclic : ∀ v, IsCyclic (P.decompositionGroup v)) :
    Nontrivial (chapter09H3LocalizationKernel P) := by
  sorry

theorem chapter09_h3_localization_kernel_card_two
    (P : Chapter09DecompositionData chapter09KleinFour)
    (hcyclic : ∀ v, IsCyclic (P.decompositionGroup v))
    [Finite (chapter09H3LocalizationKernel P)] :
    Nat.card (chapter09H3LocalizationKernel P) = 2 := by
  sorry

/-!
The two elementary congruences used to analyze the biquadratic example are
kept as reusable arithmetic facts, while the p-adic square conclusions are
left as the local Hensel/norm-interface lemmas used by the later proof pass.
-/
theorem chapter09_biquadratic_congruence_at_13 :
    Int.ModEq 13 17 4 := by
  norm_num

theorem chapter09_biquadratic_congruence_at_17 :
    Int.ModEq 17 (8 ^ 2) 13 := by
  norm_num

theorem chapter09_biquadratic_congruence_at_2 :
    Int.ModEq 8 17 1 := by
  norm_num

theorem chapter09_seventeen_is_square_in_13adic [Fact (Nat.Prime 13)] :
    IsSquare (17 : ℚ_[13]) := by
  let F : Polynomial (ℤ_[13]) := Polynomial.X ^ 2 - Polynomial.C (17 : ℤ_[13])
  have hF : F.aeval (2 : ℤ_[13]) = (-13 : ℤ_[13]) := by
    norm_num [F, Polynomial.aeval_def, Polynomial.eval₂_at_apply]
  have hFd : F.derivative.aeval (2 : ℤ_[13]) = (4 : ℤ_[13]) := by
    norm_num [F, Polynomial.aeval_def, Polynomial.eval₂_at_apply]
  have hnorm : ‖F.aeval (2 : ℤ_[13])‖ <
      ‖F.derivative.aeval (2 : ℤ_[13])‖ ^ 2 := by
    rw [hF, hFd]
    have h13 : ‖(13 : ℤ_[13])‖ = (13 : ℝ)⁻¹ := PadicInt.norm_p
    rw [norm_neg, h13]
    have h4 : ‖(4 : ℤ_[13])‖ = 1 :=
      (PadicInt.norm_natCast_eq_one_iff).2 (by norm_num)
    rw [h4]
    norm_num
  obtain ⟨z, hz, _, _, _⟩ :=
    hensels_lemma (p := 13) (F := F) (a := (2 : ℤ_[13])) hnorm
  refine ⟨(z : ℚ_[13]), ?_⟩
  have hz' := congrArg (fun x : ℤ_[13] => (x : ℚ_[13])) hz
  have h17 : ((17 : ℤ_[13]) : ℚ_[13]) = (17 : ℚ_[13]) :=
    PadicInt.coe_natCast 17
  have hz'' : (z : ℚ_[13]) ^ 2 - ((17 : ℤ_[13]) : ℚ_[13]) = 0 := by
    simpa [F, Polynomial.aeval_def, Polynomial.eval₂_at_apply] using hz'
  rw [h17] at hz''
  simpa [pow_two] using (sub_eq_zero.mp hz'').symm

theorem chapter09_thirteen_is_square_in_17adic [Fact (Nat.Prime 17)] :
    IsSquare (13 : ℚ_[17]) := by
  let F : Polynomial (ℤ_[17]) := Polynomial.X ^ 2 - Polynomial.C (13 : ℤ_[17])
  have hF : F.aeval (8 : ℤ_[17]) = (51 : ℤ_[17]) := by
    norm_num [F, Polynomial.aeval_def, Polynomial.eval₂_at_apply]
  have hFd : F.derivative.aeval (8 : ℤ_[17]) = (16 : ℤ_[17]) := by
    norm_num [F, Polynomial.aeval_def, Polynomial.eval₂_at_apply]
  have hnorm : ‖F.aeval (8 : ℤ_[17])‖ <
      ‖F.derivative.aeval (8 : ℤ_[17])‖ ^ 2 := by
    rw [hF, hFd]
    have h51 : ‖(51 : ℤ_[17])‖ < 1 :=
      (PadicInt.norm_intCast_lt_one_iff).2 (by norm_num)
    have h16 : ‖(16 : ℤ_[17])‖ = 1 :=
      (PadicInt.norm_natCast_eq_one_iff).2 (by norm_num)
    calc
      ‖(51 : ℤ_[17])‖ < 1 := h51
      _ = ‖(16 : ℤ_[17])‖ ^ 2 := by rw [h16]; norm_num
  obtain ⟨z, hz, _, _, _⟩ :=
    hensels_lemma (p := 17) (F := F) (a := (8 : ℤ_[17])) hnorm
  refine ⟨(z : ℚ_[17]), ?_⟩
  have hz' := congrArg (fun x : ℤ_[17] => (x : ℚ_[17])) hz
  have h13 : ((13 : ℤ_[17]) : ℚ_[17]) = (13 : ℚ_[17]) :=
    PadicInt.coe_natCast 13
  have hz'' : (z : ℚ_[17]) ^ 2 - ((13 : ℤ_[17]) : ℚ_[17]) = 0 := by
    simpa [F, Polynomial.aeval_def, Polynomial.eval₂_at_apply] using hz'
  rw [h13] at hz''
  simpa [pow_two] using (sub_eq_zero.mp hz'').symm

theorem chapter09_seventeen_is_square_in_2adic [Fact (Nat.Prime 2)] :
    IsSquare (17 : ℚ_[2]) := by
  let F : Polynomial (ℤ_[2]) := Polynomial.X ^ 2 - Polynomial.C (17 : ℤ_[2])
  have hF : F.aeval (1 : ℤ_[2]) = (-16 : ℤ_[2]) := by
    norm_num [F, Polynomial.aeval_def, Polynomial.eval₂_at_apply]
  have hFd : F.derivative.aeval (1 : ℤ_[2]) = (2 : ℤ_[2]) := by
    norm_num [F, Polynomial.aeval_def, Polynomial.eval₂_at_apply]
  have hnorm : ‖F.aeval (1 : ℤ_[2])‖ <
      ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hF, hFd]
    have h16 : (16 : ℤ_[2]) = (2 : ℤ_[2]) ^ 4 := by norm_num
    rw [norm_neg, h16, norm_pow]
    have hnorm2 : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p
    rw [hnorm2]
    norm_num
  obtain ⟨z, hz, _, _, _⟩ :=
    hensels_lemma (p := 2) (F := F) (a := (1 : ℤ_[2])) hnorm
  refine ⟨(z : ℚ_[2]), ?_⟩
  have hz' := congrArg (fun x : ℤ_[2] => (x : ℚ_[2])) hz
  have h17 : ((17 : ℤ_[2]) : ℚ_[2]) = (17 : ℚ_[2]) :=
    PadicInt.coe_natCast 17
  have hz'' : (z : ℚ_[2]) ^ 2 - ((17 : ℤ_[2]) : ℚ_[2]) = 0 := by
    simpa [F, Polynomial.aeval_def, Polynomial.eval₂_at_apply] using hz'
  rw [h17] at hz''
  simpa [pow_two] using (sub_eq_zero.mp hz'').symm

theorem chapter09_biquadratic_positive_at_infinity :
    0 < (13 : ℝ) ∧ 0 < (17 : ℝ) := by
  norm_num

/-!
This presentation records the meaning of `L = ℚ(√13, √17)` without inventing
a new field type.  The local analysis below is parameterized by the canonical
finite-place/decomposition data for this presentation.
-/
structure Chapter09BiquadraticPresentation
    (L : Type) [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L] where
  sqrt13 : L
  sqrt17 : L
  sqrt13_sq : sqrt13 ^ 2 = (13 : L)
  sqrt17_sq : sqrt17 ^ 2 = (17 : L)
  adjoin_eq_top :
    IntermediateField.adjoin ℚ ({sqrt13, sqrt17} : Set L) = ⊤
  galoisGroup_equiv : Gal(L / ℚ) ≃* chapter09KleinFour

def chapter09BiquadraticDiscriminants : Set ℤ :=
  {13, 17, 13 * 17}

def chapter09BiquadraticRamifiedPrimes : Set ℕ :=
  {13, 17}

/-!
`finitePlaces` and `primeBelow` are an abstract presentation of the finite
places used by the book, with `place` locating them in the decomposition data.
In the canonical instance, the ramification field
identifies ramified primes with the primes dividing the recorded quadratic
discriminants, and the decomposition-group field records that every local
degree is at most two.  The resulting cyclicity is proved separately below.
-/
structure Chapter09BiquadraticLocalAnalysis
    (L : Type) [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (E : Chapter09BiquadraticPresentation L)
    (P : Chapter09DecompositionData (Gal(L / ℚ)))
    [Fintype (Gal(L / ℚ))] where
  quadraticDiscriminants : Set ℤ
  quadraticDiscriminants_eq :
    quadraticDiscriminants = chapter09BiquadraticDiscriminants
  finitePlaces : Type*
  place : finitePlaces → P.places
  primeBelow : finitePlaces → ℕ
  primeBelow_prime : ∀ v, Nat.Prime (primeBelow v)
  ramified : finitePlaces → Prop
  ramified_iff_discriminant_support :
    ∀ v, ramified v ↔
      ∃ d ∈ quadraticDiscriminants, (primeBelow v : ℤ) ∣ d
  decomposition_groups_card_le_two :
    ∀ v : P.places, Nat.card (P.decompositionGroup v) ≤ 2

theorem chapter09_biquadratic_only_13_17_ramify
    {L : Type} [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (E : Chapter09BiquadraticPresentation L)
    (P : Chapter09DecompositionData (Gal(L / ℚ)))
    [Fintype (Gal(L / ℚ))]
    (A : Chapter09BiquadraticLocalAnalysis L E P) :
    ∀ v, A.ramified v ↔ A.primeBelow v = 13 ∨ A.primeBelow v = 17 := by
  intro v
  rw [A.ramified_iff_discriminant_support v, A.quadraticDiscriminants_eq]
  constructor
  · rintro ⟨d, hd, hdiv⟩
    simp only [chapter09BiquadraticDiscriminants, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    have hp := A.primeBelow_prime v
    rcases hd with rfl | rfl | rfl
    · left
      have hdiv' : A.primeBelow v ∣ 13 := by
        exact_mod_cast hdiv
      rcases (Nat.dvd_prime (by decide : Nat.Prime 13)).mp hdiv' with h | h
      · exact (hp.ne_one h).elim
      · exact h
    · right
      have hdiv' : A.primeBelow v ∣ 17 := by
        exact_mod_cast hdiv
      rcases (Nat.dvd_prime (by decide : Nat.Prime 17)).mp hdiv' with h | h
      · exact (hp.ne_one h).elim
      · exact h
    · have hdiv' : A.primeBelow v ∣ 13 * 17 := by
        exact_mod_cast hdiv
      rcases (hp.dvd_mul).mp hdiv' with h13 | h17
      · left
        rcases (Nat.dvd_prime (by decide : Nat.Prime 13)).mp h13 with h | h
        · exact (hp.ne_one h).elim
        · exact h
      · right
        rcases (Nat.dvd_prime (by decide : Nat.Prime 17)).mp h17 with h | h
        · exact (hp.ne_one h).elim
        · exact h
  · rintro (h | h)
    · refine ⟨13, by simp [chapter09BiquadraticDiscriminants], ?_⟩
      rw [h]
      norm_num
    · refine ⟨17, by simp [chapter09BiquadraticDiscriminants], ?_⟩
      rw [h]
      norm_num

theorem chapter09_biquadratic_ramified_iff_discriminant_support
    {L : Type} [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (E : Chapter09BiquadraticPresentation L)
    (P : Chapter09DecompositionData (Gal(L / ℚ)))
    [Fintype (Gal(L / ℚ))]
    (A : Chapter09BiquadraticLocalAnalysis L E P) :
    ∀ v, A.ramified v ↔
      ∃ d ∈ A.quadraticDiscriminants, (A.primeBelow v : ℤ) ∣ d :=
  A.ramified_iff_discriminant_support

theorem chapter09_biquadratic_quadratic_discriminants
    {L : Type} [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (E : Chapter09BiquadraticPresentation L)
    (P : Chapter09DecompositionData (Gal(L / ℚ)))
    [Fintype (Gal(L / ℚ))]
    (A : Chapter09BiquadraticLocalAnalysis L E P) :
    A.quadraticDiscriminants = chapter09BiquadraticDiscriminants :=
  A.quadraticDiscriminants_eq

theorem chapter09_biquadratic_decomposition_groups_are_cyclic
    {L : Type} [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (E : Chapter09BiquadraticPresentation L)
    (P : Chapter09DecompositionData (Gal(L / ℚ)))
    [Fintype (Gal(L / ℚ))]
    (A : Chapter09BiquadraticLocalAnalysis L E P) :
    ∀ v, IsCyclic (P.decompositionGroup v) := by
  intro v
  have hpos : 0 < Nat.card (P.decompositionGroup v) := Nat.card_pos
  have hle : Nat.card (P.decompositionGroup v) ≤ 2 :=
    A.decomposition_groups_card_le_two v
  have hcard : Nat.card (P.decompositionGroup v) = 1 ∨
      Nat.card (P.decompositionGroup v) = 2 := by
    omega
  rcases hcard with hcard | hcard
  · exact @isCyclic_of_subsingleton _ _
      (Nat.card_eq_one_iff_unique.mp hcard).1
  · exact isCyclic_of_prime_card hcard

theorem chapter09_biquadratic_decomposition_groups_card_le_two
    {L : Type} [Field L] [Algebra ℚ L] [NumberField L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (E : Chapter09BiquadraticPresentation L)
    (P : Chapter09DecompositionData (Gal(L / ℚ)))
    [Fintype (Gal(L / ℚ))]
    (A : Chapter09BiquadraticLocalAnalysis L E P) :
    ∀ v, Nat.card (P.decompositionGroup v) ≤ 2 :=
  A.decomposition_groups_card_le_two

/-!
The local algebra used by the displayed example is the canonical tensor
product from Chapter 1, not an arbitrary family of monoids.  The
decomposition-group/local-analysis package below records the remaining
finite-place bridge; the norm failure itself is stated using the canonical
element/local norm predicates from the same earlier interface.
-/
structure Chapter09CanonicalBiquadraticCounterexample where
  L : Type
  [field_L : Field L]
  [numberField_L : NumberField L]
  [algebra_L : Algebra ℚ L]
  [finiteDimensional_L : FiniteDimensional ℚ L]
  [galois_L : IsGalois ℚ L]
  [fintype_galois_L : Fintype (Gal(L / ℚ))]
  presentation : Chapter09BiquadraticPresentation L

attribute [instance] Chapter09CanonicalBiquadraticCounterexample.field_L
  Chapter09CanonicalBiquadraticCounterexample.numberField_L
  Chapter09CanonicalBiquadraticCounterexample.algebra_L
  Chapter09CanonicalBiquadraticCounterexample.finiteDimensional_L
  Chapter09CanonicalBiquadraticCounterexample.galois_L
  Chapter09CanonicalBiquadraticCounterexample.fintype_galois_L

theorem chapter09_canonical_biquadratic_local_products
    {L : Type} [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] :
    ∀ v : LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace ℚ,
      LastLib.Book06GlobalClassFieldTheory.Chapter01.IsLocalProductAlgebra ℚ L v :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.local_tensor_product_product_decomposition

/- LOCAL_DEPENDENCY_GUESS: this is the canonical realization of the displayed
biquadratic field presentation.  The finite-place decomposition analysis is
kept in the separate `Chapter09BiquadraticLocalAnalysis` interface below. -/
theorem chapter09_canonical_biquadratic_counterexample_data :
    Nonempty Chapter09CanonicalBiquadraticCounterexample := by
  sorry

noncomputable def chapter09CanonicalBiquadraticCounterexample :
    Chapter09CanonicalBiquadraticCounterexample :=
  Classical.choice chapter09_canonical_biquadratic_counterexample_data

theorem chapter09_biquadratic_exists_local_not_global_norm_unconditional :
    ∃ a : ℚ, a ≠ 0 ∧
      LastLib.Book06GlobalClassFieldTheory.Chapter01.IsLocalElementNorm ℚ
        chapter09CanonicalBiquadraticCounterexample.L a ∧
      ¬ LastLib.Book06GlobalClassFieldTheory.Chapter01.IsElementNorm ℚ
        chapter09CanonicalBiquadraticCounterexample.L a := by
  sorry

/-!
The realization structure expresses the canonical compatibility between the
idele norm and the family of local norms.  It is the missing bridge needed to
turn the order-two knot into an explicit local-but-not-global norm statement.
-/
structure Chapter09NormRealizationData
    (K L I_K I_L V : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [CommGroup I_K] [CommGroup I_L]
    (K_v A_v : V → Type*)
    [∀ v, Monoid (K_v v)] [∀ v, Monoid (A_v v)] where
  idele : Chapter09IdeleNormData K L I_K I_L
  localNormData : Chapter09LocalNormData K V K_v A_v
  everywhere_iff_principal :
    ∀ a, chapter09EverywhereLocalNorm localNormData a ↔
      a ∈ chapter09PrincipalNormSubgroup idele

/- LOCAL_DEPENDENCY_GUESS: instantiate the canonical norm/place-system data
with the idele and local completion data of the displayed biquadratic field.
The theorem above is the global idele/cohomology comparison; the theorem below
only consumes that canonical comparison together with the local decomposition
analysis.
-/
theorem chapter09_biquadratic_knot_has_order_two
    {L : Type} [Field L] [Algebra ℚ L]
    [NumberField L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [Fintype (Gal(L / ℚ))]
    (E : Chapter09BiquadraticPresentation L)
    (R : Chapter09CanonicalKnotCohomologyData ℚ L)
    [Finite (chapter09KnotGroup (chapter09CanonicalIdeleNormData R))]
    [TopologicalSpace (chapter09KnotGroup (chapter09CanonicalIdeleNormData R))]
    [IsTopologicalGroup (chapter09KnotGroup (chapter09CanonicalIdeleNormData R))]
    [DiscreteTopology (chapter09KnotGroup (chapter09CanonicalIdeleNormData R))]
    (A : Chapter09BiquadraticLocalAnalysis L E
      (chapter09CanonicalDecompositionData R)) :
    Nat.card (chapter09KnotGroup (chapter09CanonicalIdeleNormData R)) = 2 := by
  sorry

theorem chapter09_biquadratic_exists_local_not_global_norm
    {L : Type} {I_K I_L V : Type*} [Field L] [Algebra ℚ L]
    [NumberField L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [CommGroup I_K] [CommGroup I_L]
    {K_v A_v : V → Type*}
    [∀ v, Monoid (K_v v)] [∀ v, Monoid (A_v v)]
    (R : Chapter09NormRealizationData ℚ L I_K I_L V K_v A_v)
    [Finite (chapter09KnotGroup R.idele)]
    (hknot : Nat.card (chapter09KnotGroup R.idele) = 2) :
    ∃ a : ℚˣ,
      chapter09EverywhereLocalNorm R.localNormData a ∧
        a ∉ chapter09FieldNormSubgroup ℚ L := by
  have hne : chapter09PrincipalNormSubgroup R.idele ≠
      chapter09FieldNormSubgroup ℚ L := by
    intro heq
    have hsub : Subsingleton (chapter09KnotGroup R.idele) :=
      (chapter09_knot_trivial_iff R.idele).2 heq
    have hone : Nat.card (chapter09KnotGroup R.idele) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    omega
  obtain ⟨a, ha_principal, ha_not_field⟩ :
      ∃ a : ℚˣ, a ∈ chapter09PrincipalNormSubgroup R.idele ∧
        a ∉ chapter09FieldNormSubgroup ℚ L := by
    by_contra h
    push Not at h
    apply hne
    apply le_antisymm
    · intro a ha
      exact h a ha
    · exact chapter09_field_norm_le_principal_norm R.idele
  refine ⟨a, ?_, ha_not_field⟩
  exact (R.everywhere_iff_principal a).2 ha_principal

end

end LastLib.Book06GlobalClassFieldTheory.Chapter09
