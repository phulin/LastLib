import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section04TheMultiplicativePicture

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12

noncomputable section

open Polynomial

/-! ## 12.5. Nearby polynomials define the same extension -/

/-- The degree comparison used after applying Krasner's lemma: the generated
field inclusion and the common polynomial degree force equality. -/
theorem chapter12_nearby_root_has_same_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f g : K[X]) (α β : L) (d : ℕ)
    (hf_monic : f.Monic) (hf_irreducible : Irreducible f)
    (hf_separable : f.Separable) (hf_degree : f.natDegree = d)
    (hαroot : aeval α f = 0)
    (hg_monic : g.Monic) (hg_degree : g.natDegree = d)
    (hβroot : aeval β g = 0)
    (hcontain : IntermediateField.adjoin K ({α} : Set L) ≤
      IntermediateField.adjoin K ({β} : Set L)) :
    Irreducible g ∧
        IntermediateField.adjoin K ({α} : Set L) =
        IntermediateField.adjoin K ({β} : Set L) := by
  have _ := hf_separable
  have hαint : IsIntegral K α := ⟨f, hf_monic, hαroot⟩
  have hβint : IsIntegral K β := ⟨g, hg_monic, hβroot⟩
  have hminα : f = minpoly K α :=
    minpoly.eq_of_irreducible_of_monic hf_irreducible hαroot hf_monic
  have hαdim : Module.finrank K (IntermediateField.adjoin K ({α} : Set L)) = d := by
    rw [IntermediateField.adjoin.finrank hαint, ← hminα, hf_degree]
  have hdivβ : minpoly K β ∣ g := minpoly.dvd K β hβroot
  have hminβle : (minpoly K β).natDegree ≤ d := by
    simpa [hg_degree] using natDegree_le_of_dvd hdivβ hg_monic.ne_zero
  let : FiniteDimensional K (IntermediateField.adjoin K ({β} : Set L)) :=
    IntermediateField.adjoin.finiteDimensional hβint
  have hdim_le : Module.finrank K (IntermediateField.adjoin K ({α} : Set L)) ≤
      Module.finrank K (IntermediateField.adjoin K ({β} : Set L)) :=
    IntermediateField.finrank_le_of_le_right hcontain
  have hminβge : d ≤ (minpoly K β).natDegree := by
    calc
      d = Module.finrank K (IntermediateField.adjoin K ({α} : Set L)) := hαdim.symm
      _ ≤ Module.finrank K (IntermediateField.adjoin K ({β} : Set L)) := hdim_le
      _ = (minpoly K β).natDegree := IntermediateField.adjoin.finrank hβint
  have hdim_eq : Module.finrank K (IntermediateField.adjoin K ({α} : Set L)) =
      Module.finrank K (IntermediateField.adjoin K ({β} : Set L)) := by
    apply le_antisymm hdim_le
    calc
      Module.finrank K (IntermediateField.adjoin K ({β} : Set L)) =
          (minpoly K β).natDegree := IntermediateField.adjoin.finrank hβint
      _ ≤ d := hminβle
      _ = Module.finrank K (IntermediateField.adjoin K ({α} : Set L)) := hαdim.symm
  have hfields : IntermediateField.adjoin K ({α} : Set L) =
      IntermediateField.adjoin K ({β} : Set L) :=
    IntermediateField.eq_of_le_of_finrank_eq hcontain hdim_eq
  have hminβ : g = minpoly K β :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβint)
      hg_monic hdivβ (by simpa [hg_degree] using hminβge)
  refine ⟨?_, hfields⟩
  rw [hminβ]
  exact minpoly.irreducible hβint

/-- Local constancy in the fixed-degree monic coefficient space.  The
conclusion is stated for every root available in the chosen algebraic
overfield; the matched-root argument gives the displayed field isomorphism. -/
theorem chapter12_local_constancy_of_generated_field
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [NormedField L] [NormedAlgebra K L]
    [FiniteDimensional K L]
    (f : K[X]) (α : L) (d : ℕ)
    (hf_monic : f.Monic) (hf_irreducible : Irreducible f)
    (hf_separable : f.Separable) (hf_degree : f.natDegree = d)
    (hroot : aeval α f = 0)
    (hsplits : (f.map (algebraMap K L)).Splits) :
    ∃ U : Set (Fin d → K), IsOpen U ∧
      chapter12CoefficientVector d f ∈ U ∧
      ∀ b : Fin d → K, b ∈ U →
        let g := chapter12MonicPolynomial d b
        Irreducible g ∧
          (g.map (algebraMap K L)).Splits ∧
          ∀ β : L, aeval β g = 0 →
            Nonempty
              (IntermediateField.adjoin K ({α} : Set L) ≃ₐ[K]
                IntermediateField.adjoin K ({β} : Set L)) := by
  classical
  have hdpos : 0 < d := by
    rw [← hf_degree]
    exact hf_irreducible.natDegree_pos
  have hαint : IsIntegral K α := ⟨f, hf_monic, hroot⟩
  have hminα : f = minpoly K α :=
    minpoly.eq_of_irreducible_of_monic hf_irreducible hroot hf_monic
  let hSfinite : (f.rootSet L).Finite := Polynomial.rootSet_finite f L
  let S : Finset L := hSfinite.toFinset
  have hS_card : S.card = d := by
    dsimp [S]
    rw [hSfinite.card_toFinset]
    exact (Polynomial.card_rootSet_eq_natDegree (p := f) hf_separable hsplits).trans hf_degree
  let e : S ≃ Fin d := Finset.equivFinOfCardEq hS_card
  let roots : Fin d → L := fun i => (e.symm i).1
  have hroot_roots : ∀ i, aeval (roots i) f = 0 := by
    intro i
    have hi : (e.symm i).1 ∈ f.rootSet L := by
      exact hSfinite.mem_toFinset.mp (e.symm i).2
    change aeval (e.symm i).1 f = 0
    exact (hf_monic.mem_rootSet).mp hi
  have hexhaustive : ∀ z : L, aeval z f = 0 → ∃ i, z = roots i := by
    intro z hz
    have hzS : z ∈ S := by
      exact hSfinite.mem_toFinset.mpr ((hf_monic.mem_rootSet).mpr hz)
    let zS : S := ⟨z, hzS⟩
    refine ⟨e zS, ?_⟩
    change z = (e.symm (e zS)).1
    rw [e.symm_apply_apply]
  have hinjective : Function.Injective roots := by
      intro i j hij
      apply e.symm.injective
      apply Subtype.ext
      exact hij
  let q : Fin d → Fin d → ℝ := fun i j =>
    if i = j then 1 else ‖roots i - roots j‖
  have hqpos : ∀ i j, 0 < q i j := by
    intro i j
    dsimp [q]
    split
    · norm_num
    · rename_i hij
      apply norm_pos_iff.mpr
      intro h
      exact hij (hinjective (sub_eq_zero.mp h))
  have huniv : (Finset.univ : Finset (Fin d)).Nonempty :=
    ⟨⟨0, hdpos⟩, Finset.mem_univ _⟩
  let δ : ℝ :=
    (Finset.univ : Finset (Fin d)).inf' huniv (fun i =>
      (Finset.univ : Finset (Fin d)).inf' huniv (q i))
  have hδpos : 0 < δ := by
    dsimp [δ]
    apply (Finset.lt_inf'_iff _).2
    intro i hi
    apply (Finset.lt_inf'_iff _).2
    intro j hj
    exact hqpos i j
  have hδle : ∀ i j, δ ≤ q i j := by
    intro i j
    dsimp [δ]
    exact (Finset.inf'_le _ (Finset.mem_univ i)).trans
      (Finset.inf'_le _ (Finset.mem_univ j))
  let r : Fin d → ℝ := fun _ => δ / 2
  have hr : ∀ i, 0 < r i := by
    intro i
    dsimp [r]
    exact div_pos hδpos (by norm_num)
  have hballs : ∀ i j, i ≠ j →
      Disjoint (Metric.ball (roots i) (r i)) (Metric.ball (roots j) (r j)) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hsum : r i + r j = δ := by
      dsimp [r]
      ring
    rw [hsum]
    simpa [q, hij, dist_eq_norm] using hδle i j
  obtain ⟨U, hUopen, hUcenter, hstable⟩ :=
    chapter12_simultaneous_stability_of_simple_roots f d hf_monic hf_degree
      hf_separable hsplits roots hroot_roots hexhaustive hinjective r hr hballs
  refine ⟨U, hUopen, hUcenter, ?_⟩
  intro b hb
  let g : K[X] := chapter12MonicPolynomial d b
  change Irreducible g ∧
    (g.map (algebraMap K L)).Splits ∧
      ∀ β : L, aeval β g = 0 →
        Nonempty
          (IntermediateField.adjoin K ({α} : Set L) ≃ₐ[K]
            IntermediateField.adjoin K ({β} : Set L))
  obtain ⟨βs, hβs, hβunique, hfactor⟩ := hstable b hb
  have hβs' : ∀ i, aeval (βs i) g = 0 ∧
      βs i ∈ Metric.ball (roots i) (r i) := by
    intro i
    simpa [g] using hβs i
  have hfactor' : g.map (algebraMap K L) =
      ∏ i : Fin d, ((X : L[X]) - C (βs i)) := by
    simpa [g] using hfactor
  have hg_monic : g.Monic := by
    dsimp [g, chapter12MonicPolynomial]
    apply monic_X_pow_add
    exact degree_sum_fin_lt _
  have hg_degree : g.natDegree = d := by
    dsimp [g, chapter12MonicPolynomial]
    have hdeg :
        (∑ i : Fin d, C (b i) * X ^ (i : ℕ)).degree <
          (X ^ d : K[X]).degree := by
      rw [degree_X_pow]
      exact degree_sum_fin_lt b
    rw [natDegree_add_eq_left_of_degree_lt hdeg]
    simp
  have hg_splits : (g.map (algebraMap K L)).Splits := by
    rw [hfactor']
    exact Polynomial.Splits.prod (fun i hi => Polynomial.Splits.X_sub_C _)
  have hsame_of_index : ∀ i : Fin d,
      Irreducible g ∧
        IntermediateField.adjoin K ({roots i} : Set L) =
          IntermediateField.adjoin K ({βs i} : Set L) := by
    intro i
    have hminri : f = minpoly K (roots i) :=
      minpoly.eq_of_irreducible_of_monic hf_irreducible (hroot_roots i) hf_monic
    have hri_sep : IsSeparable K (roots i) := by
      rw [IsSeparable, ← hminri]
      exact hf_separable
    have hminri_splits :
        ((minpoly K (roots i)).map (algebraMap K L)).Splits := by
      rw [← hminri]
      exact hsplits
    have hβint : IsIntegral K (βs i) := ⟨g, hg_monic, (hβs' i).1⟩
    have hclose : chapter12KrasnerProximity (K := K) (roots i) (βs i) := by
      intro z hzconj hzneq
      have hzroot : aeval z f = 0 := by
        rw [hminri]
        exact IsConjRoot.aeval_eq_zero hzconj
      obtain ⟨j, hj⟩ := hexhaustive z hzroot
      have hij : i ≠ j := by
        intro hij
        apply hzneq
        rw [hj, hij]
      have hsmall : ‖βs i - roots i‖ < δ := by
        have hball := Metric.mem_ball.mp (hβs' i).2
        rw [dist_eq_norm] at hball
        exact hball.trans (by dsimp [r]; linarith)
      calc
        ‖βs i - roots i‖ < δ := hsmall
        _ ≤ q i j := hδle i j
        _ = ‖z - roots i‖ := by
          simp [q, hij, hj, norm_sub_rev]
    have hcontain :
        IntermediateField.adjoin K ({roots i} : Set L) ≤
          IntermediateField.adjoin K ({βs i} : Set L) :=
      chapter12_krasner_lemma_over_complete_base hri_sep hminri_splits hβint hclose
    exact chapter12_nearby_root_has_same_degree f g (roots i) (βs i) d
      hf_monic hf_irreducible hf_separable hf_degree (hroot_roots i)
      hg_monic hg_degree (hβs' i).1 hcontain
  let i0 : Fin d := ⟨0, hdpos⟩
  have hsame0 := hsame_of_index i0
  refine ⟨hsame0.1, hg_splits, ?_⟩
  intro β hβ
  have hmaproot : (g.map (algebraMap K L)).eval β = 0 := by
    rw [eval_map_algebraMap]
    exact hβ
  rw [hfactor'] at hmaproot
  have hprod : ∏ i : Fin d, (β - βs i) = 0 := by
    simpa [eval_prod] using hmaproot
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hprod
  have hβeq : β = βs i := sub_eq_zero.mp hi
  have hsame := hsame_of_index i
  have hmp : minpoly K α = minpoly K (roots i) :=
    hminα.symm.trans (minpoly.eq_of_irreducible_of_monic hf_irreducible
      (hroot_roots i) hf_monic)
  have e₁ : IntermediateField.adjoin K ({α} : Set L) ≃ₐ[K]
      IntermediateField.adjoin K ({roots i} : Set L) :=
    minpoly.algEquiv hαint.isAlgebraic hmp
  have e₂ : IntermediateField.adjoin K ({roots i} : Set L) ≃ₐ[K]
      IntermediateField.adjoin K ({βs i} : Set L) :=
    IntermediateField.equivOfEq hsame.2
  subst β
  exact ⟨e₁.trans e₂⟩

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12
