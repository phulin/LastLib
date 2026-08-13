import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Dependencies
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Section01IdealsAndAbsoluteConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Summable

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03

noncomputable section

open NumberField IsDedekindDomain
open scoped BigOperators nonZeroDivisors

/-! ### 3.2 Euler products -/

private theorem chapter03_prime_base_norm_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Summable (fun P : Chapter03PrimeIdeal K =>
      ‖(chapter03PrimeIdealNorm P : ℂ) ^ (-s)‖) := by
  classical
  let e : Chapter03PrimeIdeal K ≃
      {I : Chapter03IntegralIdeal K // (I : Ideal (𝓞 K)).IsPrime} :=
    { toFun := fun P =>
          ⟨⟨P.asIdeal, mem_nonZeroDivisors_of_ne_zero P.ne_bot⟩, P.isPrime⟩
      invFun := fun I =>
          ⟨I.1.1, I.2, mem_nonZeroDivisors_iff_ne_zero.mp I.1.2⟩
      left_inv := by intro P; rfl
      right_inv := by intro I; cases I; rfl }
  have hsub : Summable (fun I :
      {I : Chapter03IntegralIdeal K // (I : Ideal (𝓞 K)).IsPrime} =>
      ‖chapter03IdealTerm s I.1‖) :=
    (chapter03_ideal_series_absolutely_summable K hs).subtype _
  have he : Summable (fun P : Chapter03PrimeIdeal K =>
      ‖chapter03IdealTerm s (e P).1‖) := by
    exact e.summable_iff.mpr hsub
  simpa [e, chapter03IdealTerm, chapter03IdealNorm,
    chapter03AbsoluteIdealNorm, chapter03PrimeIdealNorm] using he

theorem chapter03_euler_product_eq_dedekind_zeta
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    chapter03DedekindZeta K s = chapter03EulerProduct K s := by
  classical
  let φ : Chapter03PrimeIdeal K ↪ Ideal (𝓞 K) :=
    ⟨fun P => P.asIdeal, IsDedekindDomain.HeightOneSpectrum.asIdeal_injective⟩
  have hsupport (I : Chapter03IntegralIdeal K) :
      (↑(factorization (I : Ideal (𝓞 K))).support : Set (Ideal (𝓞 K))) ⊆
        Set.range φ := by
    intro Q hQ
    rw [support_factorization] at hQ
    have hQ' : Q ∈ UniqueFactorizationMonoid.normalizedFactors
        (I : Ideal (𝓞 K)) := by simpa using hQ
    have hprime : Prime Q :=
      UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ'
    exact ⟨IsDedekindDomain.HeightOneSpectrum.ofPrime hprime, rfl⟩
  let eI : Chapter03IntegralIdeal K → Chapter03PrimeIdeal K →₀ ℕ := fun I =>
    Finsupp.comapDomain φ (factorization (I : Ideal (𝓞 K))) φ.injective.injOn
  have hemb (I : Chapter03IntegralIdeal K) :
      Finsupp.embDomain φ (eI I) = factorization (I : Ideal (𝓞 K)) := by
    exact Finsupp.embDomain_comapDomain (hsupport I)
  let E : (Chapter03PrimeIdeal K →₀ ℕ) → Chapter03IntegralIdeal K := fun f =>
    ⟨f.prod (fun P n => P.asIdeal ^ n), by
      apply mem_nonZeroDivisors_of_ne_zero
      simp only [Finsupp.prod]
      exact Finset.prod_ne_zero_iff.mpr
        (fun (P : Chapter03PrimeIdeal K) hP => pow_ne_zero _ P.ne_bot)⟩
  have hunder (f : Chapter03PrimeIdeal K →₀ ℕ) :
      (E f : Ideal (𝓞 K)) = (Finsupp.embDomain φ f).toMultiset.prod := by
    change f.prod (fun P n => P.asIdeal ^ n) = _
    rw [Finsupp.prod_toMultiset, Finsupp.prod_embDomain]
    rfl
  have hnorm (f : Chapter03PrimeIdeal K →₀ ℕ) :
      UniqueFactorizationMonoid.normalizedFactors (E f : Ideal (𝓞 K)) =
        (Finsupp.embDomain φ f).toMultiset := by
    rw [hunder]
    apply UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
    intro Q hQ
    rw [Finsupp.mem_toMultiset] at hQ
    rw [Finsupp.support_embDomain] at hQ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_map.mp hQ
    exact P.prime
  have hfactorE (f : Chapter03PrimeIdeal K →₀ ℕ) :
      factorization (E f : Ideal (𝓞 K)) = Finsupp.embDomain φ f := by
    simp only [factorization, hnorm, Finsupp.toMultiset_toFinsupp]
  have heE (f : Chapter03PrimeIdeal K →₀ ℕ) : eI (E f) = f := by
    change Finsupp.comapDomain φ (factorization (E f : Ideal (𝓞 K))) _ = f
    rw [hfactorE]
    exact Finsupp.comapDomain_embDomain φ f
  have hEI (I : Chapter03IntegralIdeal K) : E (eI I) = I := by
    apply Subtype.ext
    rw [hunder, hemb]
    have hI0 : (I : Ideal (𝓞 K)) ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp I.2
    have hIbot : (I : Ideal (𝓞 K)) ≠ ⊥ := by
      change (I : Ideal (𝓞 K)) ≠ 0
      exact hI0
    simpa [factorization] using
      (Ideal.prod_normalizedFactors_eq_self (I := (I : Ideal (𝓞 K)))
        hIbot)
  let e : Chapter03IntegralIdeal K ≃ (Chapter03PrimeIdeal K →₀ ℕ) :=
    { toFun := eI
      invFun := E
      left_inv := hEI
      right_inv := heE }
  have hsum :
      ∑' I : Chapter03IntegralIdeal K, chapter03IdealTerm s I =
        ∑' f : Chapter03PrimeIdeal K →₀ ℕ, chapter03IdealTerm s (E f) := by
    simpa [e, hEI] using
      (e.tsum_eq
        (fun f : Chapter03PrimeIdeal K →₀ ℕ => chapter03IdealTerm s (E f)))
  have hnormE (f : Chapter03PrimeIdeal K →₀ ℕ) :
      chapter03IdealNorm (E f) =
        f.prod (fun P n => chapter03PrimeIdealNorm P ^ n) := by
    change Ideal.absNorm (E f : Ideal (𝓞 K)) = _
    change Ideal.absNorm (f.prod (fun P n => P.asIdeal ^ n)) = _
    simp only [Finsupp.prod, map_prod, map_pow, chapter03PrimeIdealNorm,
      chapter03AbsoluteIdealNorm]
  have hpow (P : Chapter03PrimeIdeal K) (n : ℕ) :
      (((chapter03PrimeIdealNorm P) ^ n : ℕ) : ℂ) ^ (-s) =
        ((chapter03PrimeIdealNorm P : ℂ) ^ (-s)) ^ n := by
    calc
      (((chapter03PrimeIdealNorm P) ^ n : ℕ) : ℂ) ^ (-s) =
          ((chapter03PrimeIdealNorm P : ℂ) ^ n) ^ (-s) := by
            rw [Nat.cast_pow]
      _ = (chapter03PrimeIdealNorm P : ℂ) ^ ((n : ℂ) * (-s)) := by
        symm
        apply Complex.cpow_nat_mul'
        · simp [Complex.natCast_arg, Real.pi_pos]
        · simpa [Complex.natCast_arg] using Real.pi_pos.le
      _ = ((chapter03PrimeIdealNorm P : ℂ) ^ (-s)) ^ n :=
        Complex.cpow_nat_mul _ n _
  have hcpow (T : Finset (Chapter03PrimeIdeal K))
      (f : Chapter03PrimeIdeal K →₀ ℕ) :
      (((∏ P ∈ T, chapter03PrimeIdealNorm P ^ f P : ℕ) : ℂ) ^ (-s)) =
        ∏ P ∈ T, ((chapter03PrimeIdealNorm P : ℂ) ^ (-s)) ^ f P := by
    induction T using Finset.induction with
    | empty => simp
    | @insert P T hPT ih =>
      calc
        (((∏ P ∈ insert P T, chapter03PrimeIdealNorm P ^ f P : ℕ) : ℂ) ^ (-s)) =
            (((chapter03PrimeIdealNorm P ^ f P) *
              (∏ x ∈ T, chapter03PrimeIdealNorm x ^ f x) : ℕ) : ℂ) ^ (-s) := by
                rw [Finset.prod_insert hPT]
        _ = ((chapter03PrimeIdealNorm P ^ f P : ℕ) : ℂ) ^ (-s) *
              ((∏ x ∈ T, chapter03PrimeIdealNorm x ^ f x : ℕ) : ℂ) ^ (-s) := by
                rw [Nat.cast_mul]
                exact Complex.natCast_mul_natCast_cpow _ _ _
        _ = ((chapter03PrimeIdealNorm P : ℂ) ^ (-s)) ^ f P *
              ∏ x ∈ T, ((chapter03PrimeIdealNorm x : ℂ) ^ (-s)) ^ f x := by
                rw [hpow, ih]
        _ = ∏ P ∈ insert P T, ((chapter03PrimeIdealNorm P : ℂ) ^ (-s)) ^ f P := by
                rw [Finset.prod_insert hPT]
  have hFabs : Summable (fun f : Chapter03PrimeIdeal K →₀ ℕ =>
      ‖chapter03IdealTerm s (E f)‖) := by
    apply e.summable_iff.mp
    change Summable (fun I : Chapter03IntegralIdeal K =>
      ‖chapter03IdealTerm s (E (e I))‖)
    simpa [e, hEI] using (chapter03_ideal_series_absolutely_summable K hs)
  have hFsum : Summable (fun f : Chapter03PrimeIdeal K →₀ ℕ =>
      chapter03IdealTerm s (E f)) := hFabs.of_norm
  let A := {n : ℕ // 0 < n}
  let mkFiber (S : Finset (Chapter03PrimeIdeal K))
      (q : ∀ a : S, A) : Chapter03PrimeIdeal K →₀ ℕ :=
    Finsupp.onFinset S
      (fun a => if h : a ∈ S then (q ⟨a, h⟩).1 else 0) (by
        intro a ha
        by_contra h
        simp [h] at ha)
  have hmkFiber_support (S : Finset (Chapter03PrimeIdeal K))
      (q : ∀ a : S, A) : (mkFiber S q).support = S := by
    ext a
    by_cases h : a ∈ S
    · have ha : (q ⟨a, h⟩).1 ≠ 0 := Nat.ne_of_gt (q ⟨a, h⟩).2
      simp [mkFiber, h, ha]
    · simp [mkFiber, h]
  let fiberEquiv (S : Finset (Chapter03PrimeIdeal K)) :
      {f : Chapter03PrimeIdeal K →₀ ℕ // f.support = S} ≃ (∀ a : S, A) :=
    { toFun := fun f a =>
        ⟨f.1 a, Nat.pos_of_ne_zero <| Finsupp.mem_support_iff.mp <| by
          rw [f.2]
          exact a.2⟩
      invFun := fun q => ⟨mkFiber S q, hmkFiber_support S q⟩
      left_inv := by
        intro f
        apply Subtype.ext
        ext a
        by_cases h : a ∈ S
        · have ha : f.1 a ≠ 0 := by
            apply Finsupp.mem_support_iff.mp
            rw [f.2]
            exact h
          simp [mkFiber, h]
        · have ha : f.1 a = 0 := by
            apply Finsupp.notMem_support_iff.mp
            rw [f.2]
            exact h
          simp [mkFiber, h, ha]
      right_inv := by
        intro q
        funext a
        simp [mkFiber] }
  let z : Chapter03PrimeIdeal K → ℂ := fun P =>
    (chapter03PrimeIdealNorm P : ℂ) ^ (-s)
  have hznorm (P : Chapter03PrimeIdeal K) : ‖z P‖ < 1 := by
    have hP : 0 < chapter03PrimeIdealNorm P :=
      Nat.zero_lt_of_lt (chapter03_prime_ideal_norm_gt_one P)
    rw [show z P = (chapter03PrimeIdealNorm P : ℂ) ^ (-s) by rfl,
      Complex.norm_natCast_cpow_of_pos hP]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast chapter03_prime_ideal_norm_gt_one P)
      (neg_lt_zero.mpr (lt_trans zero_lt_one hs))
  have hterm (f : Chapter03PrimeIdeal K →₀ ℕ) :
      chapter03IdealTerm s (E f) = f.prod (fun P n => z P ^ n) := by
    change (chapter03IdealNorm (E f) : ℂ) ^ (-s) = _
    rw [hnormE f]
    simpa [Finsupp.prod, z] using hcpow f.support f
  let hposEquiv : ℕ ≃ A :=
    { toFun := fun n => ⟨n + 1, Nat.succ_pos n⟩
      invFun := fun n => n.1 - 1
      left_inv := by intro n; simp
      right_inv := by
        intro n
        apply Subtype.ext
        simp [Nat.sub_add_cancel n.2] }
  have hpos_sum (P : Chapter03PrimeIdeal K) :
      (∑' n : A, z P ^ (n.1)) = (1 - z P)⁻¹ - 1 := by
    rw [← hposEquiv.tsum_eq (fun n : A => z P ^ n.1)]
    calc
      (∑' c : ℕ, z P ^ (hposEquiv c).1) =
          ∑' n : ℕ, z P ^ (n + 1) := by
            apply tsum_congr
            intro n
            change z P ^ (n + 1) = z P ^ (n + 1)
            rfl
      _ = (∑' n : ℕ, z P ^ n) - 1 :=
        geom_series_succ (z P) (hznorm P)
      _ = (1 - z P)⁻¹ - 1 := by
        rw [tsum_geometric_of_norm_lt_one (hznorm P)]
  let a : Chapter03PrimeIdeal K → ℝ := fun P => ‖z P‖
  have ha : Summable a := by
    simpa [a, z] using (chapter03_prime_base_norm_summable K hs)
  let r : ℝ := Real.rpow 2 (-s.re)
  have hr : 0 ≤ r := by
    dsimp [r]
    positivity
  have hrlt : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (neg_lt_zero.mpr (lt_trans zero_lt_one hs))
  have ha_le (P : Chapter03PrimeIdeal K) : a P ≤ r := by
    have hP : 0 < chapter03PrimeIdealNorm P :=
      Nat.zero_lt_of_lt (chapter03_prime_ideal_norm_gt_one P)
    have hP' : (2 : ℝ) ≤ chapter03PrimeIdealNorm P := by
      exact_mod_cast
        ((Nat.succ_le_iff).2 (chapter03_prime_ideal_norm_gt_one P))
    dsimp [a, z, r]
    rw [Complex.norm_natCast_cpow_of_pos hP]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hP'
      (neg_nonpos.mpr (lt_trans zero_lt_one hs).le)
  let b : Chapter03PrimeIdeal K → ℂ := fun P =>
    ∑' n : A, z P ^ n.1
  have hb_bound (P : Chapter03PrimeIdeal K) :
      ‖b P‖ ≤ a P * (1 - r)⁻¹ := by
    rw [show b P = (1 - z P)⁻¹ - 1 by exact hpos_sum P]
    have hden0 : 1 - z P ≠ 0 := by
      intro h
      have hz : z P = 1 := (sub_eq_zero.mp h).symm
      have : ‖z P‖ = 1 := by rw [hz, norm_one]
      linarith [hznorm P]
    have hden : 1 - r ≤ ‖1 - z P‖ := by
      have htri := norm_add_le (1 - z P) (z P)
      have hone : (1 - z P) + z P = (1 : ℂ) := by ring
      rw [hone, norm_one] at htri
      dsimp [a] at ha_le ⊢
      linarith [ha_le P]
    have hrewrite : (1 - z P)⁻¹ - 1 = z P / (1 - z P) := by
      field_simp [hden0]
      ring
    rw [hrewrite, norm_div]
    calc
      ‖z P‖ / ‖1 - z P‖ ≤ ‖z P‖ / (1 - r) := by
        exact div_le_div_of_nonneg_left (norm_nonneg _) (sub_pos.mpr hrlt) hden
      _ = a P * (1 - r)⁻¹ := by
        dsimp [a]
        rw [div_eq_mul_inv]
  have hC : Summable (fun P : Chapter03PrimeIdeal K =>
      a P * (1 - r)⁻¹) := ha.mul_right _
  have hb : Summable (fun P : Chapter03PrimeIdeal K => ‖b P‖) :=
    hC.of_nonneg_of_le (fun P => norm_nonneg (b P)) hb_bound
  have hprod : Summable (fun T : Finset (Chapter03PrimeIdeal K) =>
      ∏ P ∈ T, b P) :=
    summable_finsetProd_of_summable_norm hb
  have hfactor (P : Chapter03PrimeIdeal K) :
      chapter03EulerFactor P s = 1 + b P := by
    change (1 - z P)⁻¹ = 1 + b P
    rw [show b P = (1 - z P)⁻¹ - 1 by exact hpos_sum P]
    ring
  have hfiber_term (T : Finset (Chapter03PrimeIdeal K))
      (q : ∀ a : T, A) :
      chapter03IdealTerm s (E ((fiberEquiv T).symm q).1) =
        ∏ P : T, z P.1 ^ (q P).1 := by
    rw [hterm]
    simp [Finsupp.prod, fiberEquiv, mkFiber]
    rw [hmkFiber_support T q]
    refine Finset.prod_bij' (fun a ha => ⟨a, ha⟩)
      (fun b _ => b.1) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact Finset.mem_attach T ⟨a, ha⟩
    · intro b hb
      exact b.2
    · intro a ha
      rfl
    · intro b hb
      apply Subtype.ext
      rfl
    · intro a ha
      simp [ha]
  have hpi_abs (T : Finset (Chapter03PrimeIdeal K)) :
      Summable (fun q : ∀ a : T, A =>
        ‖∏ P : T, z P.1 ^ (q P).1‖) := by
    have hf : Summable (fun f : {f : Chapter03PrimeIdeal K →₀ ℕ //
        f.support = T} => ‖chapter03IdealTerm s (E f.1)‖) :=
      hFabs.subtype _
    have hq : Summable (fun q : ∀ a : T, A =>
        ‖chapter03IdealTerm s (E ((fiberEquiv T).symm q).1)‖) := by
      apply (fiberEquiv T).summable_iff.mp
      convert hf using 1
      funext f
      simp
    simpa only [hfiber_term] using hq
  let subPiEquiv (T : Finset (Chapter03PrimeIdeal K)) :
      (∀ a : T, A) ≃ (∀ i, i ∈ T → A) :=
    { toFun := fun q i hi => q ⟨i, hi⟩
      invFun := fun q i => q i i.2
      left_inv := by
        intro q
        funext i
        rfl
      right_inv := by
        intro q
        funext i hi
        rfl }
  let eInsert (a : Chapter03PrimeIdeal K)
      (T : Finset (Chapter03PrimeIdeal K)) (ha : a ∉ T) :
      A × (∀ i : T, A) ≃
        (∀ i : T.cons a ha, A) :=
    (((Equiv.refl A).prodCongr (subPiEquiv T)).trans
      ((Finset.consPiProdEquiv (fun _ : Chapter03PrimeIdeal K => A) ha).symm)).trans
        (subPiEquiv (T.cons a ha)).symm
  have hpi (T : Finset (Chapter03PrimeIdeal K)) :
      (∑' q : ∀ a : T, A, ∏ P : T, z P.1 ^ (q P).1) =
        ∏ P : T, ∑' n : A, z P.1 ^ n.1 := by
    induction T using Finset.induction with
    | empty =>
        simp
    | @insert a T ha ih =>
        rw [← Finset.cons_eq_insert a T ha]
        let hIndex : (T.cons a ha) ≃ Option T :=
          { toFun := fun P =>
              if h : P.1 = a then none
              else some ⟨P.1, (Finset.mem_cons.mp P.2).resolve_left h⟩
            invFun := fun o =>
              Option.elim o ⟨a, Finset.mem_cons_self a T⟩
                (fun P => ⟨P.1, Finset.mem_cons_of_mem P.2⟩)
            left_inv := by
              intro P
              by_cases h : P.1 = a
              · simp only [dif_pos h]
                apply Subtype.ext
                exact h.symm
              · simp only [h]
                apply Subtype.ext
                rfl
            right_inv := by
              intro o
              cases o with
              | none => simp
              | some P =>
                  have h : (P.1 : Chapter03PrimeIdeal K) ≠ a := by
                    intro hPa
                    apply ha
                    simpa [hPa] using P.2
                  simp [h] }
        have hgeomPos : Summable (fun n : ℕ => z a ^ (n + 1)) :=
          (summable_geometric_of_norm_lt_one (hznorm a)).comp_injective
            Nat.succ_injective
        have hfirst : Summable (fun n : A => z a ^ n.1) := by
          apply hposEquiv.summable_iff.mp
          refine hgeomPos.congr ?_
          intro n
          simp [hposEquiv, Function.comp_apply]
        have hfirstNorm : Summable (fun n : A => ‖z a ^ n.1‖) := hfirst.norm
        have hrestNorm : Summable (fun q : ∀ i : T, A =>
            ‖∏ P : T, z P.1 ^ (q P).1‖) := hpi_abs T
        have hrest : Summable (fun q : ∀ i : T, A =>
            ∏ P : T, z P.1 ^ (q P).1) := hrestNorm.of_norm
        have hpair : Summable (fun x : A × (∀ i : T, A) =>
            z a ^ x.1.1 * ∏ P : T, z P.1 ^ (x.2 P).1) :=
          (hfirstNorm.mul_norm hrestNorm).of_norm
        have hmul := hfirst.tsum_mul_tsum hrest hpair
        have hreindex :
            (∑' q : ∀ i : T.cons a ha, A,
              ∏ P : T.cons a ha, z P.1 ^ (q P).1) =
              ∑' x : A × (∀ i : T, A),
                z a ^ x.1.1 * ∏ P : T, z P.1 ^ (x.2 P).1 := by
          calc
            (∑' q : ∀ i : T.cons a ha, A,
                ∏ P : T.cons a ha, z P.1 ^ (q P).1) =
                ∑' x : A × (∀ i : T, A),
                  ∏ P : T.cons a ha,
                    z P.1 ^ ((eInsert a T ha x) P).1 := by
              symm
              exact (eInsert a T ha).tsum_eq (fun q =>
                ∏ P : T.cons a ha, z P.1 ^ (q P).1)
            _ = ∑' x : A × (∀ i : T, A),
                z a ^ x.1.1 * ∏ P : T, z P.1 ^ (x.2 P).1 := by
              apply tsum_congr
              intro x
              have hprod := Fintype.prod_equiv hIndex
                (fun P : T.cons a ha =>
                  z P.1 ^ ((eInsert a T ha x) P).1)
                (fun o : Option T =>
                  Option.elim o (z a ^ x.1.1)
                    (fun P => z P.1 ^ (x.2 P).1)) (by
                  intro P
                  by_cases hPa : (P : Chapter03PrimeIdeal K) = a
                  · have hP : P = ⟨a, Finset.mem_cons_self a T⟩ := by
                      apply Subtype.ext
                      exact hPa
                    subst P
                    simp [hIndex, eInsert, subPiEquiv, Finset.consPiProdEquiv,
                      Finset.prodPiCons]
                  · have hPT : (P : Chapter03PrimeIdeal K) ∈ T := by
                      exact (Finset.mem_cons.mp P.2).resolve_left hPa
                    simp [hIndex, hPa, eInsert, subPiEquiv,
                      Finset.consPiProdEquiv, Finset.prodPiCons])
              simpa [Fintype.prod_option] using hprod
        have hprod_split (g : Chapter03PrimeIdeal K → ℂ) :
            (∏ P : T.cons a ha, g P.1) =
              g a * ∏ P : T, g P.1 := by
          have hprod := Fintype.prod_equiv hIndex
            (fun P : T.cons a ha => g P.1)
            (fun o : Option T =>
              Option.elim o (g a) (fun P => g P.1)) (by
                intro P
                by_cases hPa : (P : Chapter03PrimeIdeal K) = a
                · have hP : P = ⟨a, Finset.mem_cons_self a T⟩ := by
                    apply Subtype.ext
                    exact hPa
                  subst P
                  simp [hIndex]
                · simp [hIndex, hPa])
          simpa [Fintype.prod_option] using hprod
        calc
          (∑' q : ∀ i : T.cons a ha, A,
              ∏ P : T.cons a ha, z P.1 ^ (q P).1) =
              (∑' n : A, z a ^ n.1) *
                (∑' q : ∀ i : T, A, ∏ P : T, z P.1 ^ (q P).1) := by
            rw [hreindex, hmul]
          _ = ∏ P : T.cons a ha, ∑' n : A, z P.1 ^ n.1 := by
            rw [ih]
            exact (hprod_split (fun P => ∑' n : A, z P ^ n.1)).symm
  let supportEquiv :
      (Σ T : Finset (Chapter03PrimeIdeal K),
        {f : Chapter03PrimeIdeal K →₀ ℕ // f.support = T}) ≃
        (Chapter03PrimeIdeal K →₀ ℕ) :=
    Equiv.sigmaFiberEquiv (fun f : Chapter03PrimeIdeal K →₀ ℕ => f.support)
  have hSigmaAbs :
      Summable (fun p : Σ T : Finset (Chapter03PrimeIdeal K),
        {f : Chapter03PrimeIdeal K →₀ ℕ // f.support = T} =>
          ‖chapter03IdealTerm s (E p.2.1)‖) := by
    convert supportEquiv.summable_iff.mpr hFabs using 1
    rfl
  have hSigmaSum :
      Summable (fun p : Σ T : Finset (Chapter03PrimeIdeal K),
        {f : Chapter03PrimeIdeal K →₀ ℕ // f.support = T} =>
          chapter03IdealTerm s (E p.2.1)) := hSigmaAbs.of_norm
  have hSigmaFiber (T : Finset (Chapter03PrimeIdeal K)) :
      Summable (fun f : {f : Chapter03PrimeIdeal K →₀ ℕ // f.support = T} =>
        chapter03IdealTerm s (E f.1)) :=
    (hFabs.subtype _).of_norm
  have hSupportSum :
      (∑' f : Chapter03PrimeIdeal K →₀ ℕ, chapter03IdealTerm s (E f)) =
        ∑' T : Finset (Chapter03PrimeIdeal K),
          ∑' f : {f : Chapter03PrimeIdeal K →₀ ℕ // f.support = T},
            chapter03IdealTerm s (E f.1) := by
    calc
      (∑' f : Chapter03PrimeIdeal K →₀ ℕ, chapter03IdealTerm s (E f)) =
          ∑' p : Σ T : Finset (Chapter03PrimeIdeal K),
            {f : Chapter03PrimeIdeal K →₀ ℕ // f.support = T},
            chapter03IdealTerm s (E p.2.1) := by
        symm
        simpa [supportEquiv] using
          (supportEquiv.tsum_eq
            (fun f : Chapter03PrimeIdeal K →₀ ℕ =>
              chapter03IdealTerm s (E f)))
      _ = ∑' T : Finset (Chapter03PrimeIdeal K),
          ∑' f : {f : Chapter03PrimeIdeal K →₀ ℕ // f.support = T},
            chapter03IdealTerm s (E f.1) :=
        hSigmaSum.tsum_sigma' hSigmaFiber
  have hFiberSum (T : Finset (Chapter03PrimeIdeal K)) :
      (∑' f : {f : Chapter03PrimeIdeal K →₀ ℕ // f.support = T},
        chapter03IdealTerm s (E f.1)) =
        ∑' q : ∀ a : T, A, ∏ P : T, z P.1 ^ (q P).1 := by
    calc
      (∑' f : {f : Chapter03PrimeIdeal K →₀ ℕ // f.support = T},
          chapter03IdealTerm s (E f.1)) =
          ∑' q : ∀ a : T, A,
            chapter03IdealTerm s (E ((fiberEquiv T).symm q).1) := by
        symm
        exact (fiberEquiv T).symm.tsum_eq
          (fun f : {f : Chapter03PrimeIdeal K →₀ ℕ // f.support = T} =>
            chapter03IdealTerm s (E f.1))
      _ = ∑' q : ∀ a : T, A, ∏ P : T, z P.1 ^ (q P).1 := by
        apply tsum_congr
        intro q
        exact hfiber_term T q
  have hSupportFiber :
      (∑' f : Chapter03PrimeIdeal K →₀ ℕ, chapter03IdealTerm s (E f)) =
        ∑' T : Finset (Chapter03PrimeIdeal K),
          ∑' q : ∀ a : T, A, ∏ P : T, z P.1 ^ (q P).1 := by
    calc
      (∑' f : Chapter03PrimeIdeal K →₀ ℕ, chapter03IdealTerm s (E f)) =
          ∑' T : Finset (Chapter03PrimeIdeal K),
            ∑' f : {f : Chapter03PrimeIdeal K →₀ ℕ // f.support = T},
              chapter03IdealTerm s (E f.1) := hSupportSum
      _ = ∑' T : Finset (Chapter03PrimeIdeal K),
            ∑' q : ∀ a : T, A, ∏ P : T, z P.1 ^ (q P).1 := by
        apply tsum_congr
        intro T
        exact hFiberSum T
  have hpi_b (T : Finset (Chapter03PrimeIdeal K)) :
      (∑' q : ∀ a : T, A, ∏ P : T, z P.1 ^ (q P).1) =
        ∏ P : T, b P.1 := by
    simpa [b] using hpi T
  have hprod_b (T : Finset (Chapter03PrimeIdeal K)) :
      (∏ P : T, b P.1) = ∏ P ∈ T, b P := by
    rw [Finset.prod_coe_sort]
  have hEulerSeries :
      (∑' T : Finset (Chapter03PrimeIdeal K), ∏ P ∈ T, b P) =
        ∑' T : Finset (Chapter03PrimeIdeal K),
          ∑' q : ∀ a : T, A, ∏ P : T, z P.1 ^ (q P).1 := by
    apply tsum_congr
    intro T
    calc
      (∏ P ∈ T, b P) = ∏ P : T, b P.1 := (hprod_b T).symm
      _ = ∑' q : ∀ a : T, A, ∏ P : T, z P.1 ^ (q P).1 :=
        (hpi_b T).symm
  have hEulerProductExpand :
      chapter03EulerProduct K s =
        ∑' T : Finset (Chapter03PrimeIdeal K), ∏ P ∈ T, b P := by
    change (∏' P : Chapter03PrimeIdeal K, chapter03EulerFactor P s) = _
    calc
      (∏' P : Chapter03PrimeIdeal K, chapter03EulerFactor P s) =
          ∏' P : Chapter03PrimeIdeal K, (1 + b P) := by
        apply tprod_congr
        intro P
        exact hfactor P
      _ = ∑' T : Finset (Chapter03PrimeIdeal K), ∏ P ∈ T, b P :=
        tprod_one_add hprod
  calc
    chapter03DedekindZeta K s = chapter03IdealSeries K s :=
      chapter03_ideal_series_eq_dedekind_zeta K hs
    _ = ∑' f : Chapter03PrimeIdeal K →₀ ℕ, chapter03IdealTerm s (E f) := by
      change (∑' I : Chapter03IntegralIdeal K, chapter03IdealTerm s I) = _
      exact hsum
    _ = ∑' T : Finset (Chapter03PrimeIdeal K),
          ∑' q : ∀ a : T, A, ∏ P : T, z P.1 ^ (q P).1 := hSupportFiber
    _ = ∑' T : Finset (Chapter03PrimeIdeal K), ∏ P ∈ T, b P :=
      hEulerSeries.symm
    _ = chapter03EulerProduct K s := hEulerProductExpand.symm

theorem chapter03_euler_factor_ne_zero
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter03PrimeIdeal K) {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    chapter03EulerFactor P s ≠ 0 := by
  change (1 - (chapter03PrimeIdealNorm P : ℂ) ^ (-s))⁻¹ ≠ 0
  refine inv_ne_zero ?_
  intro h
  have hsre : (1 : ℝ) < s.re := hs
  have hnorm : ‖(chapter03PrimeIdealNorm P : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos
      (Nat.zero_lt_of_lt (chapter03_prime_ideal_norm_gt_one P))]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast chapter03_prime_ideal_norm_gt_one P)
      (neg_lt_zero.mpr (lt_trans zero_lt_one hsre))
  have hx : (chapter03PrimeIdealNorm P : ℂ) ^ (-s) = 1 :=
    (sub_eq_zero.mp h).symm
  rw [hx] at hnorm
  norm_num at hnorm

theorem chapter03_euler_product_multipliable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Multipliable (fun P : Chapter03PrimeIdeal K => chapter03EulerFactor P s) := by
  classical
  have hsre : (1 : ℝ) < s.re := hs
  let z : Chapter03PrimeIdeal K → ℂ := fun P =>
    (chapter03PrimeIdealNorm P : ℂ) ^ (-s)
  let a : Chapter03PrimeIdeal K → ℝ := fun P => ‖z P‖
  have ha : Summable a := by
    simpa [a, z] using (chapter03_prime_base_norm_summable K hs)
  let r : ℝ := Real.rpow 2 (-s.re)
  have hr : 0 ≤ r := by
    dsimp [r]
    positivity
  have hrlt : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (neg_lt_zero.mpr (lt_trans zero_lt_one hsre))
  have ha_le (P : Chapter03PrimeIdeal K) : a P ≤ r := by
    have hP : 0 < chapter03PrimeIdealNorm P :=
      Nat.zero_lt_of_lt (chapter03_prime_ideal_norm_gt_one P)
    have hP' : (2 : ℝ) ≤ chapter03PrimeIdealNorm P := by
      exact_mod_cast
        ((Nat.succ_le_iff).2 (chapter03_prime_ideal_norm_gt_one P))
    dsimp [a, z, r]
    rw [Complex.norm_natCast_cpow_of_pos hP]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hP'
      (neg_nonpos.mpr (lt_trans zero_lt_one hsre).le)
  have hC : Summable (fun P => a P * (1 - r)⁻¹) :=
    ha.mul_right _
  have hbound (P : Chapter03PrimeIdeal K) :
      ‖chapter03EulerFactor P s - 1‖ ≤ a P * (1 - r)⁻¹ := by
    have hnorm : ‖z P‖ < 1 := lt_of_le_of_lt (ha_le P) hrlt
    have hden0 : 1 - z P ≠ 0 := by
      intro h
      have hz : z P = 1 := (sub_eq_zero.mp h).symm
      have : ‖z P‖ = 1 := by rw [hz, norm_one]
      linarith
    have hden : 1 - r ≤ ‖1 - z P‖ := by
      have htri := norm_add_le (1 - z P) (z P)
      have hone : (1 - z P) + z P = (1 : ℂ) := by ring
      rw [hone, norm_one] at htri
      dsimp [a] at ha_le ⊢
      linarith [ha_le P]
    have hrewrite : (1 - z P)⁻¹ - 1 = z P / (1 - z P) := by
      field_simp [hden0]
      ring
    change ‖(1 - z P)⁻¹ - 1‖ ≤ a P * (1 - r)⁻¹
    rw [hrewrite, norm_div]
    calc
      ‖z P‖ / ‖1 - z P‖ ≤ ‖z P‖ / (1 - r) := by
        exact div_le_div_of_nonneg_left (norm_nonneg _) (sub_pos.mpr hrlt) hden
      _ = a P * (1 - r)⁻¹ := by
        dsimp [a]
        rw [div_eq_mul_inv]
  have hdiff : Summable (fun P : Chapter03PrimeIdeal K =>
      ‖chapter03EulerFactor P s - 1‖) :=
    hC.of_nonneg_of_le (fun P => norm_nonneg _) hbound
  have hdiff' : Summable (fun P : Chapter03PrimeIdeal K =>
      chapter03EulerFactor P s - 1) := hdiff.of_norm
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (Complex.multipliable_one_add_of_summable hdiff')

theorem chapter03_euler_product_hasProd
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    HasProd (fun P : Chapter03PrimeIdeal K => chapter03EulerFactor P s)
      (chapter03DedekindZeta K s) := by
  rw [chapter03_euler_product_eq_dedekind_zeta K hs]
  exact (chapter03_euler_product_multipliable K hs).hasProd

theorem chapter03_euler_log_series_absolutely_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Summable (fun q : Chapter03PrimePower K =>
      ‖chapter03EulerLogTerm q.1 q.2 s‖) := by
  classical
  have hsre : (1 : ℝ) < s.re := hs
  let s₀ : ℂ := ((1 + s.re) / 2 : ℝ)
  have hs₀ : s₀ ∈ chapter03EulerHalfPlane := by
    change (1 : ℝ) < (1 + s.re) / 2
    linarith
  let r : ℝ := Real.rpow 2 (-s₀.re)
  have hr : 0 ≤ r := by
    dsimp [r]
    positivity
  have hrlt : r < 1 := by
    dsimp [r]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    exact neg_lt_zero.mpr (by change 0 < (1 + s.re) / 2; linarith)
  have hgeom : Summable (fun m : ℕ => r ^ m) :=
    summable_geometric_of_lt_one hr hrlt
  let a : Chapter03PrimeIdeal K → ℝ := fun P =>
    ‖(chapter03PrimeIdealNorm P : ℂ) ^ (-s₀)‖
  have ha : Summable a := by
    simpa [a] using (chapter03_prime_base_norm_summable K hs₀)
  have ha_le (P : Chapter03PrimeIdeal K) : a P ≤ r := by
    have hP : 0 < chapter03PrimeIdealNorm P :=
      Nat.zero_lt_of_lt (chapter03_prime_ideal_norm_gt_one P)
    have hP' : (2 : ℝ) ≤ chapter03PrimeIdealNorm P := by
      exact_mod_cast
        ((Nat.succ_le_iff).2 (chapter03_prime_ideal_norm_gt_one P))
    dsimp [a, r]
    rw [Complex.norm_natCast_cpow_of_pos hP]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hP'
      (by change -((1 + s.re) / 2) ≤ 0; linarith)
  have hmajor : Summable (fun q : Chapter03PrimePower K => a q.1 * r ^ q.2) :=
    ha.mul_of_nonneg hgeom (fun P => norm_nonneg _) (fun _ => by positivity)
  apply hmajor.of_nonneg_of_le (fun q => norm_nonneg _)
  intro q
  have hP : 0 < chapter03PrimeIdealNorm q.1 :=
    Nat.zero_lt_of_lt (chapter03_prime_ideal_norm_gt_one q.1)
  have hfirst :
      ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
          (-((q.2 + 1 : ℕ) : ℂ) * s)‖ ≤
        ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
          (-((q.2 + 1 : ℕ) : ℂ) * s₀)‖ := by
    apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos hP
    norm_num [Complex.mul_re]
    have hs₀' : (1 + s.re) / 2 ≤ s.re := by
      linarith [hsre]
    exact mul_le_mul_of_nonpos_left hs₀' (by linarith)
  have hpow :
      ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
          (-((q.2 + 1 : ℕ) : ℂ) * s₀)‖ = a q.1 ^ (q.2 + 1) := by
    rw [Complex.norm_natCast_cpow_of_pos hP]
    dsimp [a]
    rw [Complex.norm_natCast_cpow_of_pos hP]
    norm_num [Complex.mul_re]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    ring
  change ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
      (-((q.2 + 1 : ℕ) : ℂ) * s) /
        ((q.2 + 1 : ℕ) : ℂ)‖ ≤ a q.1 * r ^ q.2
  rw [norm_div]
  calc
    ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
        (-((q.2 + 1 : ℕ) : ℂ) * s)‖ /
        ‖((q.2 + 1 : ℕ) : ℂ)‖ ≤
        ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
          (-((q.2 + 1 : ℕ) : ℂ) * s)‖ := by
      apply div_le_self (norm_nonneg _)
      simp only [norm_natCast]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero q.2))
    _ ≤ ‖(chapter03PrimeIdealNorm q.1 : ℂ) ^
        (-((q.2 + 1 : ℕ) : ℂ) * s₀)‖ := hfirst
    _ = a q.1 ^ (q.2 + 1) := hpow
    _ = a q.1 * a q.1 ^ q.2 := by rw [pow_succ, mul_comm]
    _ ≤ a q.1 * r ^ q.2 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (ha_le q.1) _) (norm_nonneg _)

theorem chapter03_euler_log_series_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Summable (fun q : Chapter03PrimePower K =>
      chapter03EulerLogTerm q.1 q.2 s) := by
  exact (chapter03_euler_log_series_absolutely_summable K hs).of_norm

theorem chapter03_euler_log_nested_series_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Summable (fun P : Chapter03PrimeIdeal K =>
      ∑' m : ℕ, chapter03EulerLogTerm P m s) := by
  have hsum : Summable (fun q : Chapter03PrimePower K =>
      chapter03EulerLogTerm q.1 q.2 s) :=
    (chapter03_euler_log_series_absolutely_summable K hs).of_norm
  refine ⟨∑' q : Chapter03PrimePower K, chapter03EulerLogTerm q.1 q.2 s, ?_⟩
  exact hsum.hasSum.prod_fiberwise (fun P =>
    (hsum.prod_factor P).hasSum)

theorem chapter03_euler_log_series_norm_summable_uniformly_on
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    SummableUniformlyOn
      (fun q : Chapter03PrimePower K =>
        fun s : ℂ => ‖chapter03EulerLogTerm q.1 q.2 s‖)
      (chapter03EulerHalfPlaneClosed ε) := by
  let s₀ : ℂ := (1 + ε : ℝ)
  have hs₀ : s₀ ∈ chapter03EulerHalfPlane := by
    change (1 : ℝ) < 1 + ε
    linarith
  have hsum₀ : Summable (fun q : Chapter03PrimePower K =>
      ‖chapter03EulerLogTerm q.1 q.2 s₀‖) :=
    chapter03_euler_log_series_absolutely_summable K hs₀
  apply HasSumUniformlyOn.summableUniformlyOn
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  apply tendstoUniformlyOn_tsum hsum₀
  intro q s hs
  have hP0 : chapter03PrimeIdealNorm q.1 ≠ 0 := by
    exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero q.1
  have hP : 0 < chapter03PrimeIdealNorm q.1 := Nat.pos_of_ne_zero hP0
  change ‖‖((chapter03PrimeIdealNorm q.1 : ℂ) ^
      (-((q.2 + 1 : ℕ) : ℂ) * s) /
        ((q.2 + 1 : ℕ) : ℂ))‖‖ ≤
    ‖((chapter03PrimeIdealNorm q.1 : ℂ) ^
      (-((q.2 + 1 : ℕ) : ℂ) * s₀) /
        ((q.2 + 1 : ℕ) : ℂ))‖
  have hbound :
      ‖((chapter03PrimeIdealNorm q.1 : ℂ) ^
        (-((q.2 + 1 : ℕ) : ℂ) * s) /
          ((q.2 + 1 : ℕ) : ℂ))‖ ≤
        ‖((chapter03PrimeIdealNorm q.1 : ℂ) ^
        (-((q.2 + 1 : ℕ) : ℂ) * s₀) /
          ((q.2 + 1 : ℕ) : ℂ))‖ := by
    rw [norm_div, norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos hP
    norm_num [Complex.mul_re]
    change (1 : ℝ) + ε ≤ s.re at hs
    dsimp [s₀]
    exact mul_le_mul_of_nonpos_left hs (by linarith)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound

theorem chapter03_euler_log_series_eq_nested_sum
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter03EulerLogSeries K s =
      ∑' P : Chapter03PrimeIdeal K, ∑' m : ℕ, chapter03EulerLogTerm P m s := by
  rfl

theorem chapter03_euler_product_eq_exp_euler_log_series
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    chapter03EulerProduct K s = Complex.exp (chapter03EulerLogSeries K s) := by
  classical
  let z : Chapter03PrimeIdeal K → ℂ := fun P =>
    (chapter03PrimeIdealNorm P : ℂ) ^ (-s)
  have hnorm (P : Chapter03PrimeIdeal K) : ‖z P‖ < 1 := by
    have hP : 0 < chapter03PrimeIdealNorm P :=
      Nat.zero_lt_of_lt (chapter03_prime_ideal_norm_gt_one P)
    rw [show z P = (chapter03PrimeIdealNorm P : ℂ) ^ (-s) by rfl,
      Complex.norm_natCast_cpow_of_pos hP]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast chapter03_prime_ideal_norm_gt_one P)
      (neg_lt_zero.mpr (lt_trans zero_lt_one hs))
  have hden0 (P : Chapter03PrimeIdeal K) : 1 - z P ≠ 0 := by
    intro h
    have hz : z P = 1 := (sub_eq_zero.mp h).symm
    have : ‖z P‖ = 1 := by rw [hz, norm_one]
    linarith [hnorm P]
  have hinner (P : Chapter03PrimeIdeal K) :
      HasSum (fun m : ℕ => chapter03EulerLogTerm P m s)
        (-Complex.log (1 - z P)) := by
    have heq : (fun m : ℕ => chapter03EulerLogTerm P m s) =
        (fun m : ℕ => z P ^ (m + 1) / ((m : ℂ) + 1)) := by
      funext m
      dsimp [chapter03EulerLogTerm, z]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [← Complex.cpow_nat_mul]
      congr 1
      norm_num [Nat.cast_add, Nat.cast_one]
      ring_nf
    rw [heq]
    exact Complex.hasSum_taylorSeries_neg_log' (z := z P) (hnorm P)
  have hfactor (P : Chapter03PrimeIdeal K) :
      chapter03EulerFactor P s =
        Complex.exp (∑' m : ℕ, chapter03EulerLogTerm P m s) := by
    change (1 - z P)⁻¹ = _
    calc
      (1 - z P)⁻¹ = Complex.exp (-Complex.log (1 - z P)) := by
        rw [Complex.exp_neg, Complex.exp_log (hden0 P)]
      _ = Complex.exp (∑' m : ℕ, chapter03EulerLogTerm P m s) := by
        rw [hinner P |>.tsum_eq]
  have houter :=
    (chapter03_euler_log_nested_series_summable K hs).hasSum.cexp.tprod_eq
  calc
    chapter03EulerProduct K s =
        ∏' P : Chapter03PrimeIdeal K,
          Complex.exp (∑' m : ℕ, chapter03EulerLogTerm P m s) := by
      apply tprod_congr
      intro P
      exact hfactor P
    _ = Complex.exp (∑' P : Chapter03PrimeIdeal K,
        ∑' m : ℕ, chapter03EulerLogTerm P m s) := by
      simpa only [Function.comp_apply] using houter
    _ = Complex.exp (chapter03EulerLogSeries K s) := by rfl

theorem chapter03_euler_log_series_exponentiates_to_zeta
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Complex.exp (chapter03EulerLogSeries K s) = chapter03DedekindZeta K s := by
  rw [chapter03_euler_product_eq_dedekind_zeta K hs]
  exact (chapter03_euler_product_eq_exp_euler_log_series K hs).symm

theorem chapter03_dedekind_zeta_ne_zero
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    chapter03DedekindZeta K s ≠ 0 := by
  rw [← chapter03_euler_log_series_exponentiates_to_zeta K hs]
  exact Complex.exp_ne_zero _

theorem chapter03_euler_product_ne_zero
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    chapter03EulerProduct K s ≠ 0 := by
  rw [← chapter03_euler_product_eq_dedekind_zeta K hs]
  exact chapter03_dedekind_zeta_ne_zero K hs

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03
