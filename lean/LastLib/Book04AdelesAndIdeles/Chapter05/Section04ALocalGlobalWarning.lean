import LastLib.Book04AdelesAndIdeles.Chapter05.Dependencies
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.RingTheory.ZMod.UnitsCyclic

namespace LastLib.Book04AdelesAndIdeles.Chapter05

open LastLib.Book04AdelesAndIdeles.Chapter01
open LastLib.Book04AdelesAndIdeles.Chapter04
open NumberField

noncomputable section

open scoped Topology

/-! ## 5.4. A local--global warning -/

/-! The real conic is the elementary warning in the source.  The named Selmer
curve below is an optional concrete example strengthening that warning; the
source does not rely on this particular counterexample. -/

def chapter05RealConicEquation (x y : ℝ) : Prop :=
  x ^ 2 + y ^ 2 = (-1 : ℝ)

theorem chapter05_real_conic_has_no_real_point :
    ¬ ∃ x y : ℝ, chapter05RealConicEquation x y := by
  rintro ⟨x, y, hxy⟩
  change x ^ 2 + y ^ 2 = (-1 : ℝ) at hxy
  nlinarith [sq_nonneg x, sq_nonneg y]

def chapter05SelmerPlaneCubicEquation
    {F : Type*} [Ring F] (x : Fin 3 → F) : Prop :=
  3 * x 0 ^ 3 + 4 * x 1 ^ 3 + 5 * x 2 ^ 3 = 0

def chapter05SelmerPlaneCubic (x : Fin 3 → ℚ) : Prop :=
  chapter05SelmerPlaneCubicEquation x

def chapter05SelmerPlaneCubicLocalPoint
    (v : Chapter04Place ℚ) : Prop :=
  ∃ x : Fin 3 → chapter04LocalField ℚ v,
    chapter05SelmerPlaneCubicEquation x ∧ ∃ i, x i ≠ 0

def chapter05SelmerPlaneCubicGlobalPoint : Prop :=
  ∃ x : Fin 3 → ℚ,
    chapter05SelmerPlaneCubic x ∧ ∃ i, x i ≠ 0

private theorem chapter05_padic_root_of_cubic_residue
    {p : ℕ} [Fact p.Prime] (A B a : ℤ)
    (hdiv : (p : ℤ) ∣ A * a ^ 3 - B)
    (hunit : IsCoprime (3 * A * a ^ 2) (p : ℤ)) :
    ∃ x : ℚ_[p], A * x ^ 3 = B := by
  let F : Polynomial ℤ := Polynomial.C A * Polynomial.X ^ 3 - Polynomial.C B
  have hval : ‖((A * a ^ 3 - B : ℤ) : ℤ_[p])‖ < 1 :=
    (PadicInt.norm_intCast_lt_one_iff).2 hdiv
  have hderiv : ‖F.derivative.aeval (a : ℤ_[p])‖ = 1 := by
    have hunit' : ‖((3 * A * a ^ 2 : ℤ) : ℤ_[p])‖ = 1 :=
      (PadicInt.norm_intCast_eq_one_iff).2 hunit
    simpa [F, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_mul, Polynomial.aeval_def, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      mul_assoc, mul_left_comm, mul_comm] using hunit'
  have hnorm : ‖F.aeval (a : ℤ_[p])‖ <
      ‖F.derivative.aeval (a : ℤ_[p])‖ ^ 2 := by
    rw [hderiv]
    simpa [F, Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C] using hval
  obtain ⟨z, hz, _, _, _⟩ := hensels_lemma (F := F) (a := (a : ℤ_[p])) hnorm
  refine ⟨(z : ℚ_[p]), ?_⟩
  have hz0 := hz
  rw [Polynomial.aeval_def] at hz0
  dsimp [F] at hz0
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C] at hz0
  have hz'' : (A : ℤ_[p]) * z ^ 3 - (B : ℤ_[p]) = 0 := by
    simpa using hz0
  have hz''' : (A : ℤ_[p]) * z ^ 3 = (B : ℤ_[p]) := sub_eq_zero.mp hz''
  exact congrArg (algebraMap ℤ_[p] ℚ_[p]) hz'''

private theorem chapter05_padic_cube_root_of_zmod_root
    {p : ℕ} [Fact p.Prime] (A B : ℤ) (r : ZMod p)
    (hr : (A : ZMod p) * r ^ 3 = B)
    (hpA : ¬ (p : ℤ) ∣ A) (hpB : ¬ (p : ℤ) ∣ B)
    (hp3 : ¬ (p : ℤ) ∣ 3) :
    ∃ x : ℚ_[p], (A : ℚ_[p]) * x ^ 3 = B := by
  let a : ℤ := r.val
  have har : (a : ZMod p) = r := by
    simp [a]
  have hdiv : (p : ℤ) ∣ A * a ^ 3 - B := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (A * a ^ 3 - B) p).mp
    rw [Int.cast_sub, Int.cast_mul, Int.cast_pow, har]
    rw [hr]
    simp
  have hanot : ¬ (p : ℤ) ∣ a := by
    intro ha
    apply hpB
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd B p).mp
    have haz : (a : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr ha
    have hrzero : r = 0 := by
      rw [← har]
      exact haz
    rw [← hr, hrzero]
    simp
  have hpI : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hprod : ¬ (p : ℤ) ∣ 3 * A * a ^ 2 := by
    intro h
    rcases hpI.dvd_mul.mp h with h3A | ha2
    · rcases hpI.dvd_mul.mp h3A with h3 | hA
      · exact hp3 h3
      · exact hpA hA
    · exact hanot (hpI.dvd_of_dvd_pow ha2)
  exact chapter05_padic_root_of_cubic_residue A B a hdiv
    ((hpI.irreducible.coprime_iff_not_dvd).2 hprod).symm

private theorem chapter05_cyclic_field_cube_choice
    {F : Type*} [Field F] [IsCyclic Fˣ]
    (h3 : (3 : F) ≠ 0) (h5 : (5 : F) ≠ 0) :
    (∃ x : F, x ^ 3 = 3) ∨
      (∃ y : F, y ^ 3 = 5) ∨
      (∃ x : F, x ^ 3 = 5 / 3) ∨
      ∃ t : F, t ^ 3 = 15 := by
  classical
  by_cases h3cube : ∃ x : F, x ^ 3 = 3
  · exact Or.inl h3cube
  let u3 : Fˣ := Units.mk0 (3 : F) h3
  let u5 : Fˣ := Units.mk0 (5 : F) h5
  obtain ⟨g, hg⟩ := IsCyclic.exists_zpow_surjective (G := Fˣ)
  obtain ⟨n3, hn3⟩ := hg u3
  obtain ⟨n5, hn5⟩ := hg u5
  have hg0 : (g : F) ≠ 0 := Units.ne_zero g
  have hn3F : (g : F) ^ n3 = 3 := by
    have h := congrArg (fun u : Fˣ => (u : F)) hn3
    simpa [u3] using h
  have hn5F : (g : F) ^ n5 = 5 := by
    have h := congrArg (fun u : Fˣ => (u : F)) hn5
    simpa [u5] using h
  have hnotdiv : ¬ 3 ∣ n3 := by
    intro hdiv
    obtain ⟨k, hk⟩ := hdiv
    apply h3cube
    refine ⟨(g : F) ^ k, ?_⟩
    calc
      ((g : F) ^ k) ^ 3 = (g : F) ^ (k * 3) := by
        rw [zpow_mul]
        simp
      _ = (g : F) ^ n3 := by rw [hk]; congr 1; ring
      _ = 3 := hn3F
  have hn3mod : n3 % 3 = 1 ∨ n3 % 3 = 2 := by
    have hnonneg : 0 ≤ n3 % 3 := Int.emod_nonneg _ (by norm_num)
    have hlt : n3 % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    have hcases : n3 % 3 = 0 ∨ n3 % 3 = 1 ∨ n3 % 3 = 2 := by omega
    rcases hcases with hzero | hone | htwo
    · exact False.elim (hnotdiv ((Int.dvd_iff_emod_eq_zero).2 hzero))
    · exact Or.inl hone
    · exact Or.inr htwo
  have hroot_of_dvd {n : ℤ} (hdiv : 3 ∣ n) :
      ∃ y : F, (g : F) ^ n = y ^ 3 := by
    obtain ⟨k, hk⟩ := hdiv
    refine ⟨(g : F) ^ k, ?_⟩
    calc
      (g : F) ^ n = (g : F) ^ (k * 3) := by rw [hk]; congr 1; ring
      _ = ((g : F) ^ k) ^ 3 := by rw [zpow_mul]; simp
  have hn5mod : n5 % 3 = 0 ∨ n5 % 3 = 1 ∨ n5 % 3 = 2 := by
    have hnonneg : 0 ≤ n5 % 3 := Int.emod_nonneg _ (by norm_num)
    have hlt : n5 % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    omega
  rcases hn3mod with hn31 | hn32
  · rcases hn5mod with hn50 | hn51 | hn52
    · obtain ⟨y, hy⟩ := hroot_of_dvd ((Int.dvd_iff_emod_eq_zero).2 hn50)
      exact Or.inr (Or.inl ⟨y, hy.symm.trans hn5F⟩)
    · have hdiv : 3 ∣ n5 - n3 := by
        rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, hn51, hn31]
        norm_num
      obtain ⟨y, hy⟩ := hroot_of_dvd hdiv
      right; right; left
      refine ⟨y, hy.symm.trans ?_⟩
      rw [zpow_sub₀ hg0, hn5F, hn3F]
    · have hdiv : 3 ∣ n5 + n3 := by
        rw [Int.dvd_iff_emod_eq_zero, Int.add_emod, hn52, hn31]
        norm_num
      obtain ⟨t, ht⟩ := hroot_of_dvd hdiv
      right; right; right
      refine ⟨t, ht.symm.trans ?_⟩
      rw [zpow_add₀ hg0, hn5F, hn3F]
      norm_num
  · rcases hn5mod with hn50 | hn51 | hn52
    · obtain ⟨y, hy⟩ := hroot_of_dvd ((Int.dvd_iff_emod_eq_zero).2 hn50)
      exact Or.inr (Or.inl ⟨y, hy.symm.trans hn5F⟩)
    · have hdiv : 3 ∣ n5 + n3 := by
        rw [Int.dvd_iff_emod_eq_zero, Int.add_emod, hn51, hn32]
        norm_num
      obtain ⟨t, ht⟩ := hroot_of_dvd hdiv
      right; right; right
      refine ⟨t, ht.symm.trans ?_⟩
      rw [zpow_add₀ hg0, hn5F, hn3F]
      norm_num
    · have hdiv : 3 ∣ n5 - n3 := by
        rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, hn52, hn32]
        norm_num
      obtain ⟨y, hy⟩ := hroot_of_dvd hdiv
      right; right; left
      refine ⟨y, hy.symm.trans ?_⟩
      rw [zpow_sub₀ hg0, hn5F, hn3F]

private theorem chapter05_selmer_padic_point
    (p : ℕ) [Fact p.Prime] (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    ∃ x : Fin 3 → ℚ_[p],
      chapter05SelmerPlaneCubicEquation x ∧ ∃ i, x i ≠ 0 := by
  have hp3I : ¬ (p : ℤ) ∣ 3 := by
    intro h
    have hd : p ∣ 3 := (Int.natCast_dvd_natCast).mp h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hd with h1 | h3
    · exact ((show Nat.Prime p from Fact.out).ne_one h1).elim
    · exact hp3 h3
  have hp5I : ¬ (p : ℤ) ∣ 5 := by
    intro h
    have hd : p ∣ 5 := (Int.natCast_dvd_natCast).mp h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hd with h1 | h5
    · exact ((show Nat.Prime p from Fact.out).ne_one h1).elim
    · exact hp5 h5
  have h3z : (3 : ZMod p) ≠ 0 := by
    intro h
    apply hp3I
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd 3 p).mp
    simpa using h
  have h5z : (5 : ZMod p) ≠ 0 := by
    intro h
    apply hp5I
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd 5 p).mp
    simpa using h
  have hp15I : ¬ (p : ℤ) ∣ 15 := by
    intro h
    have hpI : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
    have h' : (p : ℤ) ∣ 3 * 5 := by simpa using h
    rcases hpI.dvd_mul.mp h' with h3 | h5
    · exact hp3I h3
    · exact hp5I h5
  have hp1I : ¬ (p : ℤ) ∣ 1 := by
    intro h
    have hd : p ∣ 1 := (Int.natCast_dvd_natCast).mp h
    exact (show Nat.Prime p from Fact.out).ne_one (Nat.dvd_one.mp hd)
  obtain hchoice := chapter05_cyclic_field_cube_choice (F := ZMod p) h3z h5z
  rcases hchoice with ⟨x0, hx0⟩ | ⟨y0, hy0⟩ | ⟨x0, hx0⟩ | ⟨t0, ht0⟩
  · obtain ⟨x, hx⟩ := chapter05_padic_cube_root_of_zmod_root 1 3 x0
      (by simpa using hx0) hp1I hp3I hp3I
    refine ⟨![x, -1, -1], ?_, ⟨0, ?_⟩⟩
    · change 3 * x ^ 3 + 4 * (-1 : ℚ_[p]) ^ 3 + 5 * (-1 : ℚ_[p]) ^ 3 = 0
      have hx' : x ^ 3 = 3 := by simpa using hx
      rw [hx']
      norm_num
    · intro hxzero
      have hx0 : x = 0 := by simpa using hxzero
      have hx' : x ^ 3 = 3 := by simpa using hx
      rw [hx0] at hx'
      norm_num at hx'
  · obtain ⟨y, hy⟩ := chapter05_padic_cube_root_of_zmod_root 1 5 y0
      (by simpa using hy0) hp1I hp5I hp3I
    refine ⟨![-y, y, -1], ?_, ⟨1, ?_⟩⟩
    · change 3 * (-y) ^ 3 + 4 * y ^ 3 + 5 * (-1 : ℚ_[p]) ^ 3 = 0
      have hy' : y ^ 3 = 5 := by simpa using hy
      ring_nf
      rw [hy']
      norm_num
    · intro hyzero
      have hy0 : y = 0 := by simpa using hyzero
      have hy' : y ^ 3 = 5 := by simpa using hy
      rw [hy0] at hy'
      norm_num at hy'
  · obtain ⟨x, hx⟩ := chapter05_padic_cube_root_of_zmod_root 3 5 x0
      (by
        rw [hx0]
        field_simp [h3z]
        norm_num) hp3I hp5I hp3I
    refine ⟨![x, 0, -1], ?_, ⟨0, ?_⟩⟩
    · change 3 * x ^ 3 + 4 * (0 : ℚ_[p]) ^ 3 + 5 * (-1 : ℚ_[p]) ^ 3 = 0
      have hx' : (3 : ℚ_[p]) * x ^ 3 = 5 := by simpa using hx
      rw [hx']
      norm_num
    · intro hxzero
      have hx0 : x = 0 := by simpa using hxzero
      have hx' : (3 : ℚ_[p]) * x ^ 3 = 5 := by simpa using hx
      rw [hx0] at hx'
      norm_num at hx'
  · obtain ⟨t, ht⟩ := chapter05_padic_cube_root_of_zmod_root 1 15 t0
      (by simpa using ht0) hp1I hp15I hp3I
    refine ⟨![3 * t, 5, -7], ?_, ⟨0, ?_⟩⟩
    · change 3 * (3 * t) ^ 3 + 4 * (5 : ℚ_[p]) ^ 3 +
        5 * (-7 : ℚ_[p]) ^ 3 = 0
      have ht' : t ^ 3 = 15 := by simpa using ht
      ring_nf
      rw [ht']
      norm_num
    · intro htzero
      have ht0 : t = 0 := by simpa using htzero
      have ht' : t ^ 3 = 15 := by simpa using ht
      rw [ht0] at ht'
      norm_num at ht'

private theorem chapter05_selmer_padic_three_point
    (p : ℕ) [Fact p.Prime] (hp : p = 3) :
    ∃ x : Fin 3 → ℚ_[p],
      chapter05SelmerPlaneCubicEquation x ∧ ∃ i, x i ≠ 0 := by
  subst p
  let F : Polynomial ℤ := Polynomial.C 4 * Polynomial.X ^ 3 - Polynomial.C 5
  have h27 : ‖(27 : ℤ_[3])‖ < 1 :=
    (PadicInt.norm_natCast_lt_one_iff).2 (by norm_num)
  have h3norm : ‖(3 : ℤ_[3])‖ = (3 : ℝ)⁻¹ := by
    change ‖((3 : ℤ) : ℤ_[3])‖ = (3 : ℝ)⁻¹
    rw [PadicInt.norm_intCast_eq_padic_norm]
    simpa using (Padic.norm_p (p := 3))
  have h16 : ‖(16 : ℤ_[3])‖ = 1 :=
    (PadicInt.norm_natCast_eq_one_iff).2 (by norm_num)
  have h48 : ‖(48 : ℤ_[3])‖ = (3 : ℝ)⁻¹ := by
    calc
      ‖(48 : ℤ_[3])‖ = ‖(3 : ℤ_[3]) * 16‖ := by norm_num
      _ = ‖(3 : ℤ_[3])‖ * ‖(16 : ℤ_[3])‖ := norm_mul _ _
      _ = (3 : ℝ)⁻¹ := by rw [h3norm, h16, mul_one]
  have hnorm : ‖F.aeval (2 : ℤ_[3])‖ <
      ‖F.derivative.aeval (2 : ℤ_[3])‖ ^ 2 := by
    have h27le : ‖(27 : ℤ_[3])‖ ≤ (3 : ℝ) ^ (-3 : ℤ) :=
      (PadicInt.norm_int_le_pow_iff_dvd).2 (by norm_num)
    have hcond : ‖(27 : ℤ_[3])‖ < ‖(48 : ℤ_[3])‖ ^ 2 := by
      calc
        ‖(27 : ℤ_[3])‖ ≤ (3 : ℝ) ^ (-3 : ℤ) := h27le
        _ < ((3 : ℝ)⁻¹) ^ 2 := by norm_num
        _ = ‖(48 : ℤ_[3])‖ ^ 2 := by rw [h48]
    simpa [F, Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_X_pow, mul_assoc, mul_left_comm, mul_comm] using hcond
  obtain ⟨y, hy, _, _, _⟩ := hensels_lemma (F := F) (a := (2 : ℤ_[3])) hnorm
  refine ⟨![0, (y : ℚ_[3]), -1], ?_, ⟨1, ?_⟩⟩
  · have hy0 := hy
    rw [Polynomial.aeval_def] at hy0
    dsimp [F] at hy0
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C] at hy0
    have hy' : (4 : ℚ_[3]) * (y : ℚ_[3]) ^ 3 = 5 := by
      have : (4 : ℤ_[3]) * y ^ 3 = 5 := sub_eq_zero.mp (by simpa using hy0)
      exact congrArg (algebraMap ℤ_[3] ℚ_[3]) this
    change 3 * (0 : ℚ_[3]) ^ 3 + 4 * (y : ℚ_[3]) ^ 3 +
      5 * (-1 : ℚ_[3]) ^ 3 = 0
    rw [show 4 * (y : ℚ_[3]) ^ 3 = 5 by simpa using hy']
    norm_num
  · intro hyzero
    have hy' : (4 : ℚ_[3]) * (y : ℚ_[3]) ^ 3 = 5 := by
      have hy0 := hy
      rw [Polynomial.aeval_def] at hy0
      dsimp [F] at hy0
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C] at hy0
      have : (4 : ℤ_[3]) * y ^ 3 = 5 := sub_eq_zero.mp (by simpa using hy0)
      exact congrArg (algebraMap ℤ_[3] ℚ_[3]) this
    have hyzero' : (y : ℚ_[3]) = 0 := by simpa using hyzero
    rw [hyzero'] at hy'
    norm_num at hy'

private theorem chapter05_selmer_padic_five_point
    (p : ℕ) [Fact p.Prime] (hp : p = 5) :
    ∃ x : Fin 3 → ℚ_[p],
      chapter05SelmerPlaneCubicEquation x ∧ ∃ i, x i ≠ 0 := by
  subst p
  obtain ⟨x, hx⟩ := chapter05_padic_root_of_cubic_residue (p := 5) 1 3 2
    (by norm_num) (by norm_num [Int.isCoprime_iff_gcd_eq_one])
  refine ⟨![x, -1, -1], ?_, ⟨0, ?_⟩⟩
  · have hx' : x ^ 3 = 3 := by simpa using hx
    change 3 * x ^ 3 + 4 * (-1 : ℚ_[5]) ^ 3 +
      5 * (-1 : ℚ_[5]) ^ 3 = 0
    rw [hx']
    norm_num
  · intro hxzero
    have hx0 : x = 0 := by simpa using hxzero
    have hx' : x ^ 3 = 3 := by simpa using hx
    rw [hx0] at hx'
    norm_num at hx'

private theorem chapter05_transport_selmer_point
    {F G : Type*} [Ring F] [Ring G] (e : F ≃+* G)
    (x : Fin 3 → G)
    (hx : chapter05SelmerPlaneCubicEquation x)
    (hne : ∃ i, x i ≠ 0) :
    ∃ y : Fin 3 → F,
      chapter05SelmerPlaneCubicEquation y ∧ ∃ i, y i ≠ 0 := by
  let y : Fin 3 → F := fun i => e.symm (x i)
  refine ⟨y, ?_, ?_⟩
  · apply e.injective
    have h3 : e (3 : F) = (3 : G) := map_natCast e 3
    have h4 : e (4 : F) = (4 : G) := map_natCast e 4
    have h5 : e (5 : F) = (5 : G) := map_natCast e 5
    simp only [y, map_add, map_mul, map_pow, map_zero, e.apply_symm_apply]
    rw [h3, h4, h5]
    exact hx
  · obtain ⟨i, hi⟩ := hne
    refine ⟨i, ?_⟩
    intro hzero
    apply hi
    have hzero' := congrArg e hzero
    simpa [y] using hzero'

theorem chapter05_selmer_plane_cubic_has_point_over_every_completion :
    ∀ v : Chapter04Place ℚ, chapter05SelmerPlaneCubicLocalPoint v := by
  intro v
  cases v with
  | inl v =>
      let p0 : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v
      let p : ℕ := p0.1
      have hp : p.Prime := by simpa [p, p0] using p0.2
      let : Fact p.Prime := ⟨hp⟩
      let e : v.adicCompletion ℚ ≃A[ℚ] ℚ_[p] := by
        simpa [p, p0] using Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
      by_cases hp3 : p = 3
      · have hsrc := chapter05_selmer_padic_three_point p hp3
        exact chapter05_transport_selmer_point e.toRingEquiv hsrc.choose
          hsrc.choose_spec.1 hsrc.choose_spec.2
      · by_cases hp5 : p = 5
        · have hsrc := chapter05_selmer_padic_five_point p hp5
          exact chapter05_transport_selmer_point e.toRingEquiv hsrc.choose
            hsrc.choose_spec.1 hsrc.choose_spec.2
        · have hsrc := chapter05_selmer_padic_point p hp3 hp5
          exact chapter05_transport_selmer_point e.toRingEquiv hsrc.choose
            hsrc.choose_spec.1 hsrc.choose_spec.2
  | inr v =>
      rcases v.isReal_or_isComplex with hv | hv
      · let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv
        change ∃ x : Fin 3 → v.Completion,
          chapter05SelmerPlaneCubicEquation x ∧ ∃ i, x i ≠ 0
        let c : ℝ := 5 / 3
        have hc : 0 ≤ c := by norm_num [c]
        have hcroot : (c ^ (3 : ℝ)⁻¹) ^ 3 = c := by
          simpa [c] using Real.rpow_inv_natCast_pow hc (by norm_num : (3 : ℕ) ≠ 0)
        have hsrc : ∃ x : Fin 3 → ℝ,
            chapter05SelmerPlaneCubicEquation x ∧ ∃ i, x i ≠ 0 := by
          refine ⟨![c ^ (3 : ℝ)⁻¹, 0, -1], ?_, ⟨0, ?_⟩⟩
          · change 3 * (c ^ (3 : ℝ)⁻¹) ^ 3 + 4 * (0 : ℝ) ^ 3 +
              5 * (-1 : ℝ) ^ 3 = 0
            rw [hcroot]
            norm_num [c]
          · exact ne_of_gt (Real.rpow_pos_of_pos (by norm_num [c]) _)
        exact chapter05_transport_selmer_point e hsrc.choose
          hsrc.choose_spec.1 hsrc.choose_spec.2
      · let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
        change ∃ x : Fin 3 → v.Completion,
          chapter05SelmerPlaneCubicEquation x ∧ ∃ i, x i ≠ 0
        obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (5 / 3 : ℂ)
          (by norm_num : 0 < (3 : ℕ))
        have hrne : r ≠ 0 := by
          intro hr0
          rw [hr0] at hr
          norm_num at hr
        have hsrc : ∃ x : Fin 3 → ℂ,
            chapter05SelmerPlaneCubicEquation x ∧ ∃ i, x i ≠ 0 := by
          refine ⟨![r, 0, -1], ?_, ⟨0, hrne⟩⟩
          change 3 * r ^ 3 + 4 * (0 : ℂ) ^ 3 + 5 * (-1 : ℂ) ^ 3 = 0
          rw [hr]
          norm_num
        exact chapter05_transport_selmer_point e hsrc.choose
          hsrc.choose_spec.1 hsrc.choose_spec.2

theorem chapter05_selmer_plane_cubic_has_no_global_point :
    ¬ chapter05SelmerPlaneCubicGlobalPoint := by
  sorry

def chapter05IntegralTailCondition
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04FinitePlace K)) (a : K) : Prop :=
  ∀ v : Chapter04FinitePlace K, v ∉ S →
    chapter05FiniteDiagonal K a v ∈
      chapter04FiniteLocalIntegerSet K v

theorem chapter05_global_elements_have_finite_nonintegral_tail
    (K : Type*) [Field K] [NumberField K] (a : K) :
    ({v : Chapter04FinitePlace K |
      chapter05FiniteDiagonal K a v ∉
        chapter04FiniteLocalIntegerSet K v}).Finite := by
  sorry

theorem chapter05_strong_tail_is_an_almost_everywhere_requirement
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04FinitePlace K)) (a : K)
    (hS : ∀ v : Chapter04FinitePlace K, v ∉ S →
      chapter05FiniteDiagonal K a v ∈
        chapter04FiniteLocalIntegerSet K v) :
    chapter05IntegralTailCondition K S a := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter05
