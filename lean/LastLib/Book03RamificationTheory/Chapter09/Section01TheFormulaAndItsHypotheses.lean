import LastLib.Book03RamificationTheory.Chapter09.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter09

noncomputable section

open LastLib.Book03RamificationTheory.Chapter05
open LastLib.Book03RamificationTheory.Chapter03
open LastLib.Book03RamificationTheory.Chapter07
open LastLib.Book03RamificationTheory.Chapter08
open scoped BigOperators Polynomial

/-! ## 9.1. The formula and its hypotheses -/

def chapter09IsFierce
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)] : Prop :=
  ¬Algebra.IsSeparable (chapter09ResidueField vK) (chapter09ResidueField vL)

theorem chapter09_local_galois_data_is_not_fierce
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)]
    (D : Chapter09LocalGaloisData K L vK vL) :
    ¬chapter09IsFierce vK vL := by
  exact fun hfierce => hfierce D.residue_separable

theorem chapter09_displacement_sum_eq_group_count_sum
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) :
    chapter09DisplacementSum D = chapter09GroupCountSum D := by
  classical
  have hcard : ∀ H : Subgroup G,
      Finset.sum (Finset.univ.erase (1 : G))
        (fun σ => if σ ∈ H then 1 else 0) = Nat.card H - 1 := by
    intro H
    have hfull :
        Finset.sum (Finset.univ : Finset G)
            (fun σ => if σ ∈ H then 1 else 0) = Nat.card H := by
      rw [Finset.sum_boole]
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_of_subtype
        (Finset.univ.filter (fun σ : G => σ ∈ H)) (by simp)).symm
    have herase := Finset.sum_erase_add (s := (Finset.univ : Finset G))
      (f := fun σ : G => if σ ∈ H then 1 else 0)
      (Finset.mem_univ (1 : G))
    have hone : (if (1 : G) ∈ H then 1 else 0) = 1 := by simp
    rw [hone, hfull] at herase
    omega
  have hdisp : ∀ {σ : G}, σ ≠ 1 →
      D.displacement σ =
        Finset.sum (Finset.range (chapter09Cutoff D + 1))
          (fun i => if σ ∈ D.lowerGroup (i : ℝ) then 1 else 0) := by
    intro σ hσ
    have hbound : D.displacement σ ≤ chapter09Cutoff D := by
      by_contra hbound
      have hmem : σ ∈ D.lowerGroup (chapter09Cutoff D : ℝ) :=
        (D.lower_nat_mem_iff hσ (chapter09Cutoff D)).2 (by omega)
      rw [chapter09_lower_group_trivial_at_cutoff D (chapter09Cutoff D) le_rfl]
        at hmem
      exact hσ (by simpa using hmem)
    have hfilter :
        Finset.filter (fun i : ℕ => σ ∈ D.lowerGroup (i : ℝ))
            (Finset.range (chapter09Cutoff D + 1)) = Finset.range (D.displacement σ) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      rw [D.lower_nat_mem_iff hσ]
      omega
    rw [← Finset.card_range (D.displacement σ), ← hfilter]
    exact
      (Finset.sum_boole (R := ℕ)
        (fun i : ℕ => σ ∈ D.lowerGroup (i : ℝ))
        (Finset.range (chapter09Cutoff D + 1))).symm
  rw [chapter09DisplacementSum, chapter09GroupCountSum]
  calc
    Finset.sum (Finset.univ.erase (1 : G)) D.displacement =
        Finset.sum (Finset.univ.erase (1 : G))
          (fun σ => Finset.sum (Finset.range (chapter09Cutoff D + 1))
            (fun i => if σ ∈ D.lowerGroup (i : ℝ) then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact hdisp (Finset.mem_erase.mp hσ).1
    _ = Finset.sum (Finset.range (chapter09Cutoff D + 1))
          (fun i => Finset.sum (Finset.univ.erase (1 : G))
            (fun σ => if σ ∈ D.lowerGroup (i : ℝ) then 1 else 0)) := by
      exact Finset.sum_comm
    _ = Finset.sum (Finset.range (chapter09Cutoff D + 1))
          (fun i => Nat.card (D.lowerGroup (i : ℝ)) - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hcard (D.lowerGroup (i : ℝ))

theorem chapter09_hilbert_different_formula
    {A B K L : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)]
    (S : Chapter09HilbertFormulaSetup A B K L vK vL) :
    S.d = chapter09DisplacementSum S.profile ∧
      S.d = chapter09GroupCountSum S.profile := by
  classical
  let αL : L := algebraMap B L S.α
  have hroot :
      Polynomial.eval αL (Polynomial.derivative
        (Finset.prod (Finset.univ : Finset (Gal(L / K)))
          (fun σ => Polynomial.X - Polynomial.C (σ αL)))) =
        Finset.prod (Finset.univ.erase (1 : Gal(L / K)))
          (fun σ => αL - σ αL) := by
    have hd :
        Polynomial.derivative
            (Finset.prod (Finset.univ : Finset (Gal(L / K)))
              (fun σ => Polynomial.X - Polynomial.C (σ αL))) =
          Finset.sum (Finset.univ : Finset (Gal(L / K))) (fun σ =>
            Finset.prod (Finset.univ.erase σ)
                (fun τ => Polynomial.X - Polynomial.C (τ αL)) *
              (Polynomial.X - Polynomial.C (σ αL)).derivative) := by
      change Polynomial.derivative
          ((Multiset.map (fun σ => Polynomial.X - Polynomial.C (σ αL))
            (Finset.univ : Finset (Gal(L / K))).1).prod) = _
      rw [Polynomial.derivative_prod]
      rfl
    rw [hd, Polynomial.eval_finsetSum]
    have hsum := Finset.sum_erase_add
      (s := (Finset.univ : Finset (Gal(L / K))))
      (f := fun σ => Polynomial.eval αL
        (Finset.prod (Finset.univ.erase σ)
            (fun τ => Polynomial.X - Polynomial.C (τ αL)) *
          (Polynomial.X - Polynomial.C (σ αL)).derivative))
      (Finset.mem_univ (1 : Gal(L / K)))
    rw [← hsum]
    rw [Finset.sum_eq_zero]
    · simp only [zero_add]
      rw [Polynomial.eval_mul, Polynomial.eval_prod]
      simp
    · intro σ hσ
      rw [Polynomial.eval_mul, Polynomial.eval_prod]
      have hone : (1 : Gal(L / K)) ∈ Finset.univ.erase σ := by
        rw [Finset.mem_erase]
        exact ⟨Ne.symm (Finset.mem_erase.mp hσ |>.1), Finset.mem_univ _⟩
      have hzero :
          Polynomial.eval αL
              (Polynomial.X - Polynomial.C ((1 : Gal(L / K)) αL)) = 0 := by
        simp
      rw [Finset.prod_eq_zero hone hzero]
      simp
  have hmap_eval :
      algebraMap B L (chapter07DerivativeAt A B S.f S.α) =
        Polynomial.eval αL (S.f.derivative.map (algebraMap A L)) := by
    rw [chapter07DerivativeAt]
    rw [Polynomial.map_aeval_eq_aeval_map (φ := algebraMap A L)
      (ψ := algebraMap B L) (by
        ext x
        simp only [RingHom.comp_apply]
        simp [IsScalarTower.algebraMap_apply A B L])]
    simp [αL, Polynomial.aeval_def]
  have hfactor :
      Polynomial.derivative (S.f.map (algebraMap A L)) =
        Polynomial.derivative (chapter09ConjugateProductPolynomial
          (K := K) (L := L) αL) := by
    apply congrArg (fun p : Polynomial L => p.derivative)
    simpa [αL] using S.conjugate_factorization
  have hderiv_eval :
      algebraMap B L (chapter07DerivativeAt A B S.f S.α) =
        Finset.prod (Finset.univ.erase (1 : Gal(L / K)))
          (fun σ => αL - σ αL) := by
    calc
      algebraMap B L (chapter07DerivativeAt A B S.f S.α) =
          Polynomial.eval αL (S.f.derivative.map (algebraMap A L)) := hmap_eval
      _ = Polynomial.eval αL (Polynomial.derivative (S.f.map (algebraMap A L))) := by
        rw [Polynomial.derivative_map]
      _ = Polynomial.eval αL (Polynomial.derivative
          (chapter09ConjugateProductPolynomial (K := K) (L := L) αL)) := by
            rw [hfactor]
      _ = Finset.prod (Finset.univ.erase (1 : Gal(L / K)))
          (fun σ => αL - σ αL) := by
            simpa [chapter09ConjugateProductPolynomial] using hroot
  have hprod_val : ∀ s : Finset (Gal(L / K)),
      vL (Finset.prod s (fun σ => αL - σ αL)) =
        Finset.sum s (fun σ => vL (αL - σ αL)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert σ s hσ ih =>
        rw [Finset.prod_insert hσ, Finset.sum_insert hσ, vL.map_mul, ih]
  have hneg : ∀ {σ : Gal(L / K)}, σ ≠ 1 →
      vL (αL - σ αL) = (S.profile.displacement σ : WithTop ℤ) := by
    intro σ hσ
    rw [show αL - σ αL = -(σ αL - αL) by ring, vL.map_neg]
    simpa [αL] using S.displacement_formula (σ := σ) hσ
  have hderivval :
      vL (algebraMap B L (chapter07DerivativeAt A B S.f S.α)) =
        Finset.sum (Finset.univ.erase (1 : Gal(L / K)))
          (fun σ => (S.profile.displacement σ : WithTop ℤ)) := by
    calc
      vL (algebraMap B L (chapter07DerivativeAt A B S.f S.α)) =
          vL (Finset.prod (Finset.univ.erase (1 : Gal(L / K)))
            (fun σ => αL - σ αL)) := congrArg vL hderiv_eval
      _ = Finset.sum (Finset.univ.erase (1 : Gal(L / K)))
          (fun σ => vL (αL - σ αL)) := hprod_val _
      _ = Finset.sum (Finset.univ.erase (1 : Gal(L / K)))
          (fun σ => (S.profile.displacement σ : WithTop ℤ)) := by
            apply Finset.sum_congr rfl
            intro σ hσ
            exact hneg (Finset.mem_erase.mp hσ).1
  have hsum_cast :
      ((chapter09DisplacementSum S.profile : ℕ) : WithTop ℤ) =
        Finset.sum (Finset.univ.erase (1 : Gal(L / K)))
          (fun σ => (S.profile.displacement σ : WithTop ℤ)) := by
    unfold chapter09DisplacementSum
    norm_cast
  have hdcast :
      (S.d : WithTop ℤ) = (chapter09DisplacementSum S.profile : WithTop ℤ) := by
    calc
      (S.d : WithTop ℤ) =
          vL (algebraMap B L (chapter07DerivativeAt A B S.f S.α)) :=
        S.different_derivative_value.symm
      _ = Finset.sum (Finset.univ.erase (1 : Gal(L / K)))
          (fun σ => (S.profile.displacement σ : WithTop ℤ)) := hderivval
      _ = (chapter09DisplacementSum S.profile : WithTop ℤ) := hsum_cast.symm
  have hdisplacement : S.d = chapter09DisplacementSum S.profile := by
    exact_mod_cast hdcast
  refine ⟨hdisplacement, ?_⟩
  exact hdisplacement.trans
    (chapter09_displacement_sum_eq_group_count_sum S.profile)

theorem chapter09_hilbert_different_formula_displacement
    {A B K L : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)]
    (S : Chapter09HilbertFormulaSetup A B K L vK vL) :
    S.d = chapter09DisplacementSum S.profile := by
  exact (chapter09_hilbert_different_formula vK vL S).1

theorem chapter09_hilbert_different_formula_group_counts
    {A B K L : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)]
    (S : Chapter09HilbertFormulaSetup A B K L vK vL) :
    S.d = chapter09GroupCountSum S.profile := by
  exact (chapter09_hilbert_different_formula vK vL S).2

/- The mixed unramified--tame profile from Chapter 3 has only the tame
   inertia group at level zero.  Hilbert's formula therefore identifies the
   actual different exponent of the setup with the Chapter 3 numerical value. -/
theorem chapter09_mixed_unramified_tame_different_exponent
    {A B K L : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)]
    (S : Chapter09HilbertFormulaSetup A B K L vK vL)
    (e : ℕ)
    (hprofile : chapter09MixedUnramifiedTameProfile S.profile e) :
    S.d = chapter03MixedDifferentExponent e := by
  rw [chapter09_hilbert_different_formula_group_counts vK vL S]
  unfold chapter09GroupCountSum chapter03MixedDifferentExponent
  have hzero : Nat.card (S.profile.lowerGroup (0 : ℝ)) = e := by
    simpa [chapter09LowerGroup] using hprofile.1
  have hone : S.profile.lowerGroup (1 : ℝ) = (⊥ : Subgroup (Gal(L / K))) := by
    simpa [chapter09LowerGroup] using hprofile.2
  have htail : ∀ i : ℕ, 1 ≤ i →
      Nat.card (S.profile.lowerGroup (i : ℝ)) - 1 = 0 := by
    intro i hi
    have hle : S.profile.lowerGroup (i : ℝ) ≤
        S.profile.lowerGroup (1 : ℝ) := by
      apply S.profile.lower_antitone
      exact_mod_cast hi
    have hbot : S.profile.lowerGroup (i : ℝ) = ⊥ :=
      bot_unique (by simpa [hone] using hle)
    simp [hbot]
  have hsum : ∀ b : ℕ,
      Finset.sum (Finset.range (b + 1))
          (fun i => Nat.card (S.profile.lowerGroup (i : ℝ)) - 1) =
        Nat.card (S.profile.lowerGroup (0 : ℝ)) - 1 := by
    intro b
    induction b with
    | zero => simp
    | succ b ih =>
        rw [Finset.sum_range_succ]
        rw [htail (b + 1) (by omega), add_zero]
        exact ih
  calc
    Finset.sum (Finset.range (chapter09Cutoff S.profile + 1))
        (fun i => Nat.card (S.profile.lowerGroup (i : ℝ)) - 1) =
      Nat.card (S.profile.lowerGroup (0 : ℝ)) - 1 := hsum _
    _ = e - 1 := by rw [hzero]

theorem chapter09_setup_d_is_the_different_power
    {A B K L : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)]
    (S : Chapter09HilbertFormulaSetup A B K L vK vL) :
    chapter09DifferentPower (IsLocalRing.maximalIdeal B)
      (chapter08DifferentIdeal A B) S.d := by
  exact S.different_power

theorem chapter09_setup_d_eq_canonical_different_exponent
    {A B K L : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)]
    (S : Chapter09HilbertFormulaSetup A B K L vK vL)
    (hD : ∃! n : ℕ,
      chapter09DifferentPower (IsLocalRing.maximalIdeal B)
        (chapter08DifferentIdeal A B) n) :
    chapter09DifferentExponent (IsLocalRing.maximalIdeal B)
        (chapter08DifferentIdeal A B) hD = S.d := by
  exact (hD.unique S.different_power (Classical.choose_spec hD).1).symm

end

end LastLib.Book03RamificationTheory.Chapter09
