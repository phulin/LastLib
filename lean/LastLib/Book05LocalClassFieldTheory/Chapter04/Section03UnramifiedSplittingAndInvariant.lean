import LastLib.Book05LocalClassFieldTheory.Chapter04.Section02ValuationsOnDivisionAlgebras
import LastLib.Book05LocalClassFieldTheory.Chapter03.Section04CyclicAlgebras
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section05NormsInTowers
import Mathlib.LinearAlgebra.TensorProduct.Basic

namespace LastLib.Book05LocalClassFieldTheory.Chapter04

noncomputable section

open scoped BigOperators TensorProduct
open LastLib.Book05LocalClassFieldTheory.Chapter03
open LastLib.Book05LocalClassFieldTheory.Chapter02

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ## 4.3. Unramified splitting and the invariant -/

structure Chapter04ScalarExtensionAction
    (K D E : Type*) [Field K] [Ring D] [Field E]
    [Algebra K D] [Algebra K E] [Module E D] [FiniteDimensional E D]
    (embedding : E →ₐ[K] D) where
  action : D ⊗[K] E →ₐ[E] Module.End E D
  module_smul_eq : ∀ b : E, ∀ x : D, b • x = x * embedding b
  action_on_tmul : ∀ a : D, ∀ b : E, ∀ x : D,
    action (TensorProduct.tmul K a b) x = a * x * embedding b
  action_isomorphism : Nonempty
    (D ⊗[K] E ≃ₐ[E] Module.End E D)

theorem chapter04_scalar_extension_action_exists
    {K D E : Type*} [Field K] [Ring D] [Field E]
    [Algebra K D] [Algebra K E] [Module E D] [FiniteDimensional E D]
    (φ : E →ₐ[K] D) (hsmul : ∀ b : E, ∀ x : D, b • x = x * φ b) (d : ℕ)
    (hdimension : Module.finrank E D = d) :
    Nonempty (Chapter04ScalarExtensionAction K D E φ) := by
  sorry

theorem chapter04_division_algebra_splits_over_unramified_maximal_subfield
    {K D E : Type*} [Field K] [Ring D] [Field E]
    [Algebra K D] [Algebra K E] [Module E D] [FiniteDimensional E D]
    (φ : E →ₐ[K] D) (d : ℕ)
    (hdimension : Module.finrank E D = d)
    (A : Chapter04ScalarExtensionAction K D E φ) :
    Nonempty (D ⊗[K] E ≃ₐ[E] Matrix (Fin d) (Fin d) E) := by
  classical
  let b₀ : Module.Basis (Module.Free.ChooseBasisIndex E D) E D :=
    Module.Free.chooseBasis E D
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex E D) = d := by
    rw [← Module.finrank_eq_card_basis b₀, hdimension]
  let e : Module.Free.ChooseBasisIndex E D ≃ Fin d :=
    (Fintype.equivFin _).trans (Equiv.cast (congrArg Fin hcard))
  let b : Module.Basis (Fin d) E D := b₀.reindex e
  exact ⟨A.action_isomorphism.some.trans (LinearMap.toMatrixAlgEquiv b)⟩

theorem chapter04_division_algebra_is_split_by_unramified_extension
    {K : Type*} [Field K] (P : Chapter04LocalFieldProfile K)
    (D : Chapter04DivisionAlgebraData K)
    (E : Chapter04UnramifiedMaximalSubfieldSpec K P D) :
    chapter04UnramifiedMaximalSubfieldSplits P D E := by
  exact E.split_over_unramified_field

theorem chapter04_unramified_extension_is_cyclic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) :
    chapter03CyclicExtension K L U.degree U.arithmeticFrobenius := by
  refine ⟨U.degree_eq, ?_⟩
  intro τ
  rw [U.frobenius_generates]
  exact Subgroup.mem_top τ

noncomputable def chapter04UnramifiedCyclicAlgebraPresentation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) :
    chapter03CyclicAlgebra K L U.degree U.arithmeticFrobenius
      (U.uniformizer ^ r) :=
  chapter03CyclicAlgebraChoice K L U.degree U.arithmeticFrobenius
    (U.uniformizer ^ r) (chapter04_unramified_extension_is_cyclic U)

def chapter04UnramifiedCyclicAlgebraSplits
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) : Prop :=
  chapter03CyclicAlgebraSplitsOverBase K L U.degree U.arithmeticFrobenius
    (U.uniformizer ^ r)
    (chapter04UnramifiedCyclicAlgebraPresentation U r)

def chapter04UnramifiedCyclicBrauerClass
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) :
    chapter04BrauerGroup K :=
  chapter03CyclicAlgebraBrauerClass K L U.degree U.arithmeticFrobenius
    (U.uniformizer ^ r) (chapter04UnramifiedCyclicAlgebraPresentation U r)

def chapter04CyclicTermValue
    {L : Type*} [Field L] (vL : L → WithTop ℚ) (r : ℤ) (d : ℕ)
    (i : Fin d) (x : L) : WithTop ℚ :=
  vL x +
    (((r : ℚ) * ((i : ℕ) : ℚ) / (d : ℚ)) : WithTop ℚ)

def chapter04CyclicValuationFormula
    {L A : Type*} [Field L] [Ring A]
    (embed : L → A) (vL : L → WithTop ℚ) (r : ℤ) (d : ℕ)
    (basis : Fin d → A) (w : A → WithTop ℚ) : Prop :=
  ∀ x, x ≠ 0 →
    ∃ c : Fin d → L,
      x = ∑ i, embed (c i) * basis i ∧
        ∃ i : Fin d,
          w x = chapter04CyclicTermValue vL r d i (c i) ∧
            ∀ j : Fin d,
              w x ≤ chapter04CyclicTermValue vL r d j (c j)

def chapter04UnramifiedInvariantFraction
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) :
    chapter04RationalResidue :=
  chapter04RationalResidueFraction r U.degree

theorem chapter04_unramified_cyclic_parameter_period
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) :
    chapter04UnramifiedCyclicBrauerClass U (r + U.degree) =
      chapter04UnramifiedCyclicBrauerClass U r := by
  have hparam :
      (U.uniformizer ^ (r + U.degree)) * (U.uniformizer ^ r)⁻¹ ∈
        chapter03NormSubgroup K L := by
    have hnorm := U.units_are_norms (U.uniformizer ^ U.degree)
    have hnorm' : U.uniformizer ^ U.degree ∈ chapter03NormSubgroup K L :=
      (chapter03_mem_norm_subgroup_iff K L (U.uniformizer ^ U.degree)).2 hnorm
    rw [zpow_add]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hnorm'
  unfold chapter04UnramifiedCyclicBrauerClass
  apply Quotient.sound
  rcases (chapter03_cyclic_algebra_parameter_classification K L U.degree
    U.arithmeticFrobenius (U.uniformizer ^ (r + U.degree)) (U.uniformizer ^ r)
    (chapter04_unramified_extension_is_cyclic U)).2 hparam with ⟨e⟩
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  exact ⟨e.mapMatrix⟩

theorem chapter04_unramified_cyclic_parameter_modulo_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r s : ℤ)
    (hmod : r ≡ s [ZMOD U.degree]) :
    chapter04UnramifiedCyclicBrauerClass U r =
      chapter04UnramifiedCyclicBrauerClass U s := by
  have hperiod : ∀ k : ℤ,
      chapter04UnramifiedCyclicBrauerClass U (r + k * U.degree) =
        chapter04UnramifiedCyclicBrauerClass U r := by
    intro k
    refine Int.induction_on k ?_ ?_ ?_
    · simp
    · intro i hi
      rw [show r + (i + 1) * U.degree =
        (r + i * U.degree) + U.degree by ring]
      rw [chapter04_unramified_cyclic_parameter_period]
      exact hi
    · intro i hi
      calc
        chapter04UnramifiedCyclicBrauerClass U (r + (-i - 1) * U.degree) =
            chapter04UnramifiedCyclicBrauerClass U
              ((r + (-i - 1) * U.degree) + U.degree) := by
                symm
                exact chapter04_unramified_cyclic_parameter_period U _
        _ = chapter04UnramifiedCyclicBrauerClass U (r + (-i) * U.degree) := by
          congr 1
          ring
        _ = chapter04UnramifiedCyclicBrauerClass U r := hi
  rcases hmod.dvd with ⟨k, hk⟩
  have hs : s = r + k * U.degree := by
    calc
      s = r + (s - r) := by ring
      _ = r + (U.degree * k) := by rw [hk]
      _ = r + k * U.degree := by ring
  rw [hs]
  exact (hperiod k).symm

theorem chapter04_unramified_invariant_fraction_periodic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) :
    chapter04UnramifiedInvariantFraction U (r + U.degree) =
      chapter04UnramifiedInvariantFraction U r := by
  change chapter04RationalResidueFraction (r + U.degree) U.degree =
    chapter04RationalResidueFraction r U.degree
  unfold chapter04RationalResidueFraction chapter04RationalResidueMk
  rw [QuotientAddGroup.mk'_eq_mk']
  refine ⟨-(1 : ℚ), ?_, ?_⟩
  · exact AddSubgroup.neg_mem (AddSubgroup.zmultiples (1 : ℚ))
      (AddSubgroup.mem_zmultiples (1 : ℚ))
  · have hdegree : (U.degree : ℚ) ≠ 0 := by
      exact_mod_cast U.degree_pos.ne'
    field_simp [hdegree]
    norm_num

theorem chapter04_unramified_fraction_denominator_change
    (r : ℤ) (d m : ℕ) (hm : 0 < m) (hd : 0 < d) :
    chapter04RationalResidueFraction r d =
      chapter04RationalResidueFraction (m * r) (m * d) := by
  unfold chapter04RationalResidueFraction chapter04RationalResidueMk
  rw [QuotientAddGroup.mk'_eq_mk']
  refine ⟨0, AddSubgroup.zero_mem _, ?_⟩
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp [hm', hd']
  push_cast
  ring

/- A denominator change is a tower calculation.  Merely having two
  unramified extensions of the required dimensions does not identify their
  crossed products, so the intermediate-field and Frobenius compatibilities
  are recorded explicitly here. -/
structure Chapter04UnramifiedTowerData
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    (U : Chapter04UnramifiedExtensionData K L)
    (U' : Chapter04UnramifiedExtensionData K M) (m : ℕ) where
  positive : 0 < m
  degree_factor : U'.degree = m * U.degree
  uniformizer_eq : U'.uniformizer = U.uniformizer
  frobenius_restricts : ∀ x : L,
    (U'.arithmeticFrobenius ^ m) (algebraMap L M x) =
      algebraMap L M (U.arithmeticFrobenius x)

theorem chapter04_unramified_cyclic_brauer_denominator_change
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    (U : Chapter04UnramifiedExtensionData K L)
    (U' : Chapter04UnramifiedExtensionData K M)
    (m : ℕ) (T : Chapter04UnramifiedTowerData U U' m) (r : ℤ) :
    chapter04UnramifiedCyclicBrauerClass U r =
      chapter04UnramifiedCyclicBrauerClass U' (m * r) := by
  sorry

theorem chapter04_rational_residue_multiplication_is_surjective
    (n : ℕ) (hn : 0 < n) :
    Function.Surjective (fun q : chapter04RationalResidue => n • q) := by
  intro q
  rcases QuotientAddGroup.mk'_surjective
      (AddSubgroup.zmultiples (1 : ℚ)) q with ⟨q, rfl⟩
  refine ⟨chapter04RationalResidueMk (q / n), ?_⟩
  change QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))
      (n • (q / (n : ℚ))) =
    QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) q
  congr 1
  change (n : ℚ) * (q / (n : ℚ)) = q
  field_simp [show (n : ℚ) ≠ 0 by exact_mod_cast hn.ne']

theorem chapter04_unramified_norm_of_base_uniformizer
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) :
    ∃ u : Kˣ,
      Units.map (Algebra.norm K (S := L))
          (Units.map (algebraMap K L).toMonoidHom U.uniformizer) =
        U.uniformizer ^ U.degree * u := by
  let a : Kˣ := Units.map (Algebra.norm K (S := L))
    (Units.map (algebraMap K L).toMonoidHom U.uniformizer)
  refine ⟨a * (U.uniformizer ^ U.degree)⁻¹, ?_⟩
  change a = U.uniformizer ^ U.degree *
    (a * (U.uniformizer ^ U.degree)⁻¹)
  simp [mul_comm]

def chapter04CoprimeParameter (r : ℤ) (d : ℕ) : Prop :=
  Nat.Coprime r.natAbs d

theorem chapter04_unramified_cyclic_split_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) :
    chapter04UnramifiedCyclicAlgebraSplits U r ↔
      U.degree ∣ r.natAbs := by
  sorry

theorem chapter04_unramified_cyclic_is_division_of_coprime_parameter
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ)
    (hcoprime : chapter04CoprimeParameter r U.degree) :
    ∃ w : (chapter04UnramifiedCyclicAlgebraPresentation U r).carrier → WithTop ℚ,
      w 0 = ⊤ ∧ w 1 = 0 ∧
      (∀ x y, x ≠ 0 → y ≠ 0 → w (x * y) = w x + w y) ∧
      (∀ x, x ≠ 0 → w x ≠ ⊤) ∧
      (∀ x y, x * y = 0 → x = 0 ∨ y = 0) := by
  sorry

theorem chapter04_unramified_cyclic_minimum_valuation_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ)
    (vL : AddValuation L (WithTop ℚ))
    (hπ : vL (algebraMap K L (U.uniformizer : K)) = (1 : WithTop ℚ))
    (hcoprime : chapter04CoprimeParameter r U.degree)
    (C : chapter03CyclicAlgebra K L U.degree U.arithmeticFrobenius
      (U.uniformizer ^ r)) :
    ∃ w : C.carrier → WithTop ℚ,
      chapter04CyclicValuationFormula
        (C.algebraL.algebraMap : L → C.carrier) vL r U.degree
        (fun i => C.symbol ^ (i : ℕ)) w ∧
      (∀ x y, x ≠ 0 → y ≠ 0 → w (x * y) = w x + w y) ∧
      (∀ x, x ≠ 0 → w x ≠ ⊤) ∧
      (∀ x y, x * y = 0 → x = 0 ∨ y = 0) := by
  sorry

theorem chapter04_finite_csa_without_zero_divisors_is_division
    {K : Type*} [Field K] (A : chapter04CentralSimpleAlgebra K)
    (hnozero : ∀ x y : A, x * y = 0 → x = 0 ∨ y = 0) :
    ∃ D : Chapter04DivisionAlgebraData K,
      Nonempty (A ≃ₐ[K] D.carrier) := by
  let W := (chapter04_wedderburn_decomposition_exists A).some
  have hsize : W.matrixSize = 1 := by
    by_contra hne
    have hpos : 0 < W.matrixSize := W.matrixSize_pos
    have htwo : 2 ≤ W.matrixSize := by
      omega
    let i : Fin W.matrixSize := ⟨0, by omega⟩
    let j : Fin W.matrixSize := ⟨1, by omega⟩
    have hij : i ≠ j := by
      simp [i, j]
    let e := W.equivalence.some
    let M : Matrix (Fin W.matrixSize) (Fin W.matrixSize) W.division.carrier :=
      Matrix.single i j 1
    have hM : M ≠ 0 := by
      intro h
      have hentry := congrArg (fun X => X i j) h
      simp [M] at hentry
    let x : A := e.symm M
    have hx : x ≠ 0 := by
      intro hx
      apply hM
      calc
        M = e (e.symm M) := (e.apply_symm_apply M).symm
        _ = e 0 := by rw [show e.symm M = x from rfl, hx]
        _ = 0 := map_zero e
    have hxx : x * x = 0 := by
      apply e.injective
      change e (e.symm M * e.symm M) = e 0
      simpa only [map_mul, e.apply_symm_apply, map_zero] using
        (Matrix.single_mul_single_of_ne (1 : W.division.carrier)
          i j i hij.symm 1)
    rcases hnozero x x hxx with hx0 | hx0
    · exact hx hx0
    · exact hx hx0
  have hdivision : ∀ x : A, x ≠ 0 →
      ∃ y : A, x * y = 1 ∧ y * x = 1 := by
    intro x hx
    have hinj : Function.Injective (LinearMap.mulLeft K x) := by
      intro y z h
      change x * y = x * z at h
      apply sub_eq_zero.mp
      have hzero : x * (y - z) = 0 := by
        rw [mul_sub, h, sub_self]
      rcases hnozero x (y - z) hzero with hzero | hzero
      · exact (hx hzero).elim
      · exact hzero
    have hsurj : Function.Surjective (LinearMap.mulLeft K x) :=
      (LinearMap.injective_iff_surjective).mp hinj
    obtain ⟨y, hy⟩ := hsurj 1
    change x * y = 1 at hy
    have hleft : y * x = 1 := by
      have hzero : x * (y * x - 1) = 0 := by
        rw [mul_sub, ← mul_assoc, hy, one_mul, mul_one, sub_self]
      rcases hnozero x (y * x - 1) hzero with hzero | hzero
      · exact (hx hzero).elim
      · exact sub_eq_zero.mp hzero
    exact ⟨y, hy, hleft⟩
  have hfinrank : Module.finrank K A = W.division.degree ^ 2 := by
    calc
      Module.finrank K A =
          W.matrixSize ^ 2 * Module.finrank K W.division.carrier :=
        chapter04_wedderburn_decomposition_matrix_dimension A W
      _ = W.division.degree ^ 2 := by
        rw [hsize, W.division.finrank_eq_degree_sq]
        simp
  let D : Chapter04DivisionAlgebraData K :=
    { carrier := A
      isDivision := hdivision
      degree := W.division.degree
      degree_pos := W.division.degree_pos
      finrank_eq_degree_sq := hfinrank }
  refine ⟨D, ?_⟩
  exact ⟨AlgEquiv.refl⟩

def chapter04ReducedCyclicDegree (r : ℤ) (d : ℕ) : ℕ :=
  d / Nat.gcd r.natAbs d

theorem chapter04_unramified_cyclic_underlying_division_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) :
    chapter04ReducedCyclicDegree r U.degree =
      U.degree / Nat.gcd r.natAbs U.degree := by
  rfl

theorem chapter04_unramified_cyclic_reduced_division_representative
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) :
    ∃ D : Chapter04DivisionAlgebraData K,
      D.degree = chapter04ReducedCyclicDegree r U.degree ∧
      chapter04BrauerEquivalent D.carrier
        (chapter04UnramifiedCyclicAlgebraPresentation U r).carrier := by
  sorry

structure Chapter04UnramifiedInvariantNormalization
    {K : Type*} [Field K] (I : Chapter04LocalInvariantData K)
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) where
  uniformizer_value :
    I.invariant (chapter04UnramifiedCyclicBrauerClass U 1) =
      chapter04RationalResidueOneOver U.degree
  zero_parameter :
    chapter04UnramifiedCyclicBrauerClass U 0 = I.brauerLaw.one
  tensor_parameter_add : ∀ r s : ℤ,
    I.brauerLaw.tensor
        (chapter04UnramifiedCyclicBrauerClass U r)
        (chapter04UnramifiedCyclicBrauerClass U s) =
      chapter04UnramifiedCyclicBrauerClass U (r + s)
  opposite_parameter_neg : ∀ r : ℤ,
    I.brauerLaw.opposite (chapter04UnramifiedCyclicBrauerClass U r) =
      chapter04UnramifiedCyclicBrauerClass U (-r)

theorem chapter04_unramified_cyclic_invariant_fraction
    {K : Type*} [Field K] (I : Chapter04LocalInvariantData K)
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L)
    (N : Chapter04UnramifiedInvariantNormalization I U) (r : ℤ) :
    I.invariant (chapter04UnramifiedCyclicBrauerClass U r) =
      chapter04RationalResidueFraction r U.degree := by
  have hdq : (U.degree : ℚ) ≠ 0 := by
    exact_mod_cast U.degree_pos.ne'
  have hfrac_add (a b : ℤ) :
      chapter04RationalResidueFraction a U.degree +
          chapter04RationalResidueFraction b U.degree =
        chapter04RationalResidueFraction (a + b) U.degree := by
    change (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)))
        ((a : ℚ) / (U.degree : ℚ)) +
          (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)))
            ((b : ℚ) / (U.degree : ℚ)) =
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)))
        (((a + b : ℤ) : ℚ) / (U.degree : ℚ))
    rw [← (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).map_add]
    congr 1
    push_cast
    field_simp [hdq]
  have hfrac_neg (a : ℤ) :
      -chapter04RationalResidueFraction a U.degree =
        chapter04RationalResidueFraction (-a) U.degree := by
    change -(QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)))
        ((a : ℚ) / (U.degree : ℚ)) =
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)))
        (((-a : ℤ) : ℚ) / (U.degree : ℚ))
    rw [← (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).map_neg]
    congr 1
    push_cast
    field_simp [hdq]
  have hzero :
      I.invariant (chapter04UnramifiedCyclicBrauerClass U 0) =
        chapter04RationalResidueFraction 0 U.degree := by
    rw [N.zero_parameter, I.invariant_one]
    simp [chapter04RationalResidueFraction, chapter04RationalResidueMk]
  have hone :
      I.invariant (chapter04UnramifiedCyclicBrauerClass U 1) =
        chapter04RationalResidueFraction 1 U.degree := by
    exact N.uniformizer_value
  have hminus_one :
      I.invariant (chapter04UnramifiedCyclicBrauerClass U (-1)) =
        chapter04RationalResidueFraction (-1) U.degree := by
    calc
      I.invariant (chapter04UnramifiedCyclicBrauerClass U (-1)) =
          I.invariant (I.brauerLaw.opposite
            (chapter04UnramifiedCyclicBrauerClass U 1)) := by
              rw [N.opposite_parameter_neg]
      _ = -I.invariant (chapter04UnramifiedCyclicBrauerClass U 1) :=
        I.invariant_opposite _
      _ = chapter04RationalResidueFraction (-1) U.degree := by
        rw [hone, hfrac_neg]
  refine Int.induction_on r hzero ?_ ?_
  · intro i hi
    calc
      I.invariant (chapter04UnramifiedCyclicBrauerClass U (i + 1)) =
          I.invariant (I.brauerLaw.tensor
            (chapter04UnramifiedCyclicBrauerClass U i)
            (chapter04UnramifiedCyclicBrauerClass U 1)) := by
              rw [N.tensor_parameter_add]
      _ = I.invariant (chapter04UnramifiedCyclicBrauerClass U i) +
            I.invariant (chapter04UnramifiedCyclicBrauerClass U 1) :=
          I.invariant_tensor _ _
      _ = chapter04RationalResidueFraction i U.degree +
            chapter04RationalResidueFraction 1 U.degree := by rw [hi, hone]
      _ = chapter04RationalResidueFraction (i + 1) U.degree := hfrac_add _ _
  · intro i hi
    calc
      I.invariant (chapter04UnramifiedCyclicBrauerClass U (-i - 1)) =
          I.invariant (I.brauerLaw.tensor
            (chapter04UnramifiedCyclicBrauerClass U (-i))
            (chapter04UnramifiedCyclicBrauerClass U (-1))) := by
              rw [N.tensor_parameter_add]
              ring_nf
      _ = I.invariant (chapter04UnramifiedCyclicBrauerClass U (-i)) +
            I.invariant (chapter04UnramifiedCyclicBrauerClass U (-1)) :=
          I.invariant_tensor _ _
      _ = chapter04RationalResidueFraction (-i) U.degree +
            chapter04RationalResidueFraction (-1) U.degree := by
              rw [hi, hminus_one]
      _ = chapter04RationalResidueFraction (-i - 1) U.degree := hfrac_add _ _

theorem chapter04_local_invariant_data_exists
    {K : Type*} [Field K] (P : Chapter04LocalFieldProfile K) :
    Nonempty {I : Chapter04LocalInvariantData K // I.localField = P} := by
  sorry

theorem chapter04_theorem_4_1_local_invariant
    {K : Type*} [Field K] (P : Chapter04LocalFieldProfile K) :
    Nonempty {I : Chapter04LocalInvariantData K // I.localField = P} := by
  exact chapter04_local_invariant_data_exists P

theorem chapter04_local_invariant_is_an_isomorphism
    {K : Type*} [Field K] (I : Chapter04LocalInvariantData K) :
    Function.Injective I.invariant ∧ Function.Surjective I.invariant := by
  exact ⟨I.invariant_injective, I.invariant_surjective⟩

noncomputable def chapter04LocalInvariantEquiv
    {K : Type*} [Field K] (I : Chapter04LocalInvariantData K) :
    chapter04BrauerGroup K ≃ chapter04RationalResidue :=
  Equiv.ofBijective I.invariant
    ⟨I.invariant_injective, I.invariant_surjective⟩

theorem chapter04LocalInvariantEquiv_apply
    {K : Type*} [Field K] (I : Chapter04LocalInvariantData K)
    (a : chapter04BrauerGroup K) :
    chapter04LocalInvariantEquiv I a = I.invariant a := by
  rfl

def chapter04BrauerNatPower
    {K : Type*} [Field K] (B : Chapter04BrauerGroupLaw K)
    (a : chapter04BrauerGroup K) : ℕ → chapter04BrauerGroup K
  | 0 => B.one
  | n + 1 => B.tensor (chapter04BrauerNatPower B a n) a

theorem chapter04_invariant_of_brauer_nat_power
    {K : Type*} [Field K] (I : Chapter04LocalInvariantData K)
    (a : chapter04BrauerGroup K) (n : ℕ) :
    I.invariant (chapter04BrauerNatPower I.brauerLaw a n) =
      n • I.invariant a := by
  induction n with
  | zero =>
      simpa [chapter04BrauerNatPower] using I.invariant_one
  | succ n ih =>
      rw [chapter04BrauerNatPower, I.invariant_tensor, ih, succ_nsmul]

theorem chapter04_local_invariant_restriction_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (I_K : Chapter04LocalInvariantData K)
    (I_L : Chapter04LocalInvariantData L)
    (R : Chapter04BrauerRestrictionData K L)
    (n : ℕ) (hdegree : Module.finrank K L = n)
    (α : chapter04BrauerGroup K) :
    I_L.invariant (R.restriction α) = n • I_K.invariant α := by
  sorry

/- The invariant theorem also covers finite extensions with a purely
   inseparable part; separability is therefore not part of the final
   restriction statement. -/
theorem chapter04_local_invariant_restriction_formula_finite_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (I_K : Chapter04LocalInvariantData K)
    (I_L : Chapter04LocalInvariantData L)
    (R : Chapter04BrauerRestrictionData K L)
    (n : ℕ) (hdegree : Module.finrank K L = n)
    (α : chapter04BrauerGroup K) :
    I_L.invariant (R.restriction α) = n • I_K.invariant α := by
  sorry

theorem chapter04_restriction_unramified_stage_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I_K : Chapter04LocalInvariantData K)
    (I_L : Chapter04LocalInvariantData L)
    (R : Chapter04BrauerRestrictionData K L)
    (U : Chapter04UnramifiedExtensionData K L)
    (hdegree : Module.finrank K L = U.degree)
    (α : chapter04BrauerGroup K) :
    I_L.invariant (R.restriction α) = U.degree • I_K.invariant α := by
  sorry

structure Chapter04TotallyRamifiedStageData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] where
  valuationK : AddValuation K (WithTop ℤ)
  valuationL : AddValuation L (WithTop ℤ)
  localK : Chapter02LocalField valuationK
  localL : Chapter02LocalField valuationL
  degree : ℕ
  degree_pos : 0 < degree
  degree_eq : Module.finrank K L = degree
  residue_agreement :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11TotallyRamifiedResidueAgreement
      valuationK valuationL
  uniformizerK : K
  uniformizerL : L
  unit_factor : Lˣ
  uniformizerK_spec : chapter02IsUniformizer valuationK uniformizerK
  uniformizerL_spec : chapter02IsUniformizer valuationL uniformizerL
  uniformizer_factor :
    algebraMap K L uniformizerK = (unit_factor : L) * uniformizerL ^ degree

theorem chapter04_restriction_totally_ramified_stage_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (I_K : Chapter04LocalInvariantData K)
    (I_L : Chapter04LocalInvariantData L)
    (R : Chapter04BrauerRestrictionData K L)
    (T : Chapter04TotallyRamifiedStageData K L)
    (α : chapter04BrauerGroup K) :
    I_L.invariant (R.restriction α) = T.degree • I_K.invariant α := by
  sorry

/- The stage formula takes an explicit factorization witness; the source's
  purely inseparable case is handled separately in the invariant theorem. -/
theorem chapter04_restriction_finite_extension_stage_formula
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vM : AddValuation M (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (eKM eML : ℕ)
    (hstage : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnramifiedThenTotallyRamifiedFactorization
      K M L vK vM vL eKM eML)
    (I_K : Chapter04LocalInvariantData K)
    (I_M : Chapter04LocalInvariantData M)
    (I_L : Chapter04LocalInvariantData L)
    (R_KM : Chapter04BrauerRestrictionData K M)
    (R_ML : Chapter04BrauerRestrictionData M L)
    (R : Chapter04BrauerRestrictionData K L)
    (hdegreeKM : Module.finrank K M = eKM)
    (hdegreeML : Module.finrank M L = eML)
    (hrestriction_trans : R.restriction = R_ML.restriction ∘ R_KM.restriction)
    (α : chapter04BrauerGroup K) :
    I_L.invariant (R.restriction α) = (eKM * eML) • I_K.invariant α := by
  sorry

theorem chapter04_local_invariant_corestriction_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (I_K : Chapter04LocalInvariantData K)
    (I_L : Chapter04LocalInvariantData L)
    (C : Chapter04BrauerCorestrictionData K L)
    (β : chapter04BrauerGroup L) :
    I_K.invariant (C.corestriction β) = I_L.invariant β := by
  sorry

theorem chapter04_restriction_is_surjective_on_brauer_groups
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (I_K : Chapter04LocalInvariantData K)
    (I_L : Chapter04LocalInvariantData L)
    (R : Chapter04BrauerRestrictionData K L)
    (n : ℕ) (hdegree : Module.finrank K L = n) :
    Function.Surjective R.restriction := by
  have hn : 0 < n := by
    rw [← hdegree]
    exact Module.finrank_pos
  intro β
  obtain ⟨q, hq⟩ :=
    chapter04_rational_residue_multiplication_is_surjective n hn (I_L.invariant β)
  obtain ⟨α, hα⟩ := I_K.invariant_surjective q
  refine ⟨α, I_L.invariant_injective ?_⟩
  rw [chapter04_local_invariant_restriction_formula_finite_extension
    I_K I_L R n hdegree α, hα]
  exact hq

theorem chapter04_corestriction_restriction_degree_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (I_K : Chapter04LocalInvariantData K)
    (I_L : Chapter04LocalInvariantData L)
    (R : Chapter04BrauerRestrictionData K L)
    (C : Chapter04BrauerCorestrictionData K L)
    (n : ℕ) (hdegree : Module.finrank K L = n)
    (α : chapter04BrauerGroup K) :
    C.corestriction (R.restriction α) =
      chapter04BrauerNatPower I_K.brauerLaw α n := by
  apply I_K.invariant_injective
  rw [chapter04_local_invariant_corestriction_formula I_K I_L C]
  rw [chapter04_local_invariant_restriction_formula_finite_extension
    I_K I_L R n hdegree α]
  rw [chapter04_invariant_of_brauer_nat_power]

end

end LastLib.Book05LocalClassFieldTheory.Chapter04
