import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section04FactorizationOfTheMaximalIdeal
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.DedekindDomain.Different

universe u v

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter11

noncomputable section

open Ideal IsLocalRing
open Polynomial
open scoped BigOperators TensorProduct WithZero Polynomial nonZeroDivisors

/-! # Chapter 11: several places above one place

This file is a statement-only formalization of sections 11.1--11.9 of Book 1.
The declarations are intentionally local to this namespace because the chapters
are generated independently.
-/

/-! # Book 1, Chapter 11, Section 11.8: Trace and Boundedness
-/

/-! ## 11.8. Trace, norm, and boundedness -/

/-- The characteristic polynomial of multiplication by an element of a finite module. -/
def chapter11CharacteristicPolynomial
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (x : B) : A[X] :=
  LinearMap.charpoly (Algebra.lmul A B x)

/-- The characteristic polynomial annihilates the multiplication operator. -/
def chapter11RootOfPolynomial
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (f : A[X]) (x : B) : Prop :=
  Polynomial.eval x (Polynomial.map (algebraMap A B) f) = 0

/-- Cayley--Hamilton gives an integral equation for every element of a finite module. -/
theorem chapter11_characteristic_polynomial_annihilates
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (x : B) :
    chapter11RootOfPolynomial A B (chapter11CharacteristicPolynomial A B x) x := by
  change Polynomial.eval x
    (Polynomial.map (algebraMap A B)
      (LinearMap.charpoly (Algebra.lmul A B x))) = 0
  simpa [aeval_def] using (Algebra.aeval_self_charpoly_lmul (R := A) (M := B) x)

/-- Trace and norm of an integral element remain in the base ring. -/
theorem chapter11_integral_trace_and_norm_stay_integral
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.Finite A B]
    [Module.Free A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (x : B) :
    Algebra.trace K L (algebraMap B L x) ∈ Set.range (algebraMap A K) ∧
      Algebra.norm K (algebraMap B L x) ∈ Set.range (algebraMap A K) := by
  refine ⟨?_, ?_⟩
  · refine ⟨Algebra.intTrace A B x, ?_⟩
    exact Algebra.algebraMap_intTrace (L := L) x
  · refine ⟨Algebra.intNorm A B x, ?_⟩
    exact Algebra.algebraMap_intNorm (L := L) x

/-- The trace pairing on the field extension. -/
def chapter11TracePairing (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (x y : L) : K :=
  Algebra.trace K L (x * y)

/-- Separability makes the trace pairing nondegenerate. -/
theorem chapter11_separable_trace_pairing_nondegenerate
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] :
    Function.Injective (fun x : L => fun y : L => chapter11TracePairing K L x y) := by
  intro x₁ x₂ h
  have hz : ∀ y : L, Algebra.trace K L ((x₁ - x₂) * y) = 0 := by
    intro y
    have hy : Algebra.trace K L (x₁ * y) = Algebra.trace K L (x₂ * y) := by
      simpa [chapter11TracePairing] using congrFun h y
    rw [sub_mul, map_sub]
    exact sub_eq_zero.mpr hy
  have hzero : x₁ - x₂ = 0 := by
    exact (traceForm_nondegenerate K L).1 (x₁ - x₂) (by
      intro y
      simpa only [Algebra.traceForm_apply] using hz y)
  exact sub_eq_zero.mp hzero

/-- A common denominator embeds the integral trace pairing into the A-dual. -/
theorem chapter11_trace_pairing_has_common_denominator
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsFractionRing B L] [IsIntegralClosure B A L]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Module.Finite A B] (x : B) :
    ∃ d : A, d ≠ 0 ∧
      ∃ φ : B →ₗ[A] A, ∀ y : B,
        algebraMap A K (φ y) =
        algebraMap A K d *
            Algebra.trace K L (algebraMap B L x * algebraMap B L y) := by
  let hB : B →ₗ[A] L :=
    (IsScalarTower.toAlgHom A B L).toLinearMap.comp (LinearMap.mulLeft A x)
  let h : B →ₗ[A] K :=
    (Algebra.trace K L).restrictScalars A |>.comp hB
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := B)
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (M := A⁰)
    (fun i : Fin n => h (s i))
  have hgen : ∀ i : Fin n, h (s i) * algebraMap A K (d : A) ∈
      LinearMap.range (Algebra.linearMap A K) := by
    intro i
    rcases hd i with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [Algebra.smul_def, mul_comm] using ha
  let hscl : B →ₗ[A] K := (d : A) • h
  have hscl_gen : ∀ i : Fin n, hscl (s i) ∈ LinearMap.range (Algebra.linearMap A K) := by
    intro i
    simpa [hscl, LinearMap.smul_apply, Algebra.smul_def, mul_comm] using hgen i
  let q : Submodule A B :=
    (LinearMap.range (Algebra.linearMap A K)).comap hscl
  have hqgen : ∀ i : Fin n, s i ∈ q := by
    intro i
    exact hscl_gen i
  have hqtop : q = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Submodule.span_le.2 (fun z hz => by
      rcases hz with ⟨i, rfl⟩
      exact hqgen i)
  have hmem : ∀ y : B, hscl y ∈ LinearMap.range (Algebra.linearMap A K) := by
    intro y
    have : y ∈ q := by rw [hqtop]; exact Submodule.mem_top
    exact this
  let e : A ≃ₗ[A] LinearMap.range (Algebra.linearMap A K) :=
    LinearEquiv.ofBijective (Algebra.linearMap A K).rangeRestrict
      ⟨(Algebra.linearMap A K).injective_rangeRestrict_iff.mpr
          (IsFractionRing.injective A K),
        (Algebra.linearMap A K).surjective_rangeRestrict⟩
  let φ : B →ₗ[A] A :=
    e.symm.toLinearMap.comp (hscl.codRestrict _ hmem)
  have hφ (y : B) : algebraMap A K (φ y) = hscl y := by
    rw [show algebraMap A K (φ y) = (e (φ y) : K) by rfl]
    simp [φ, e]
  have hdne : (d : A) ≠ 0 := by
    exact mem_nonZeroDivisors_iff_ne_zero.mp d.prop
  refine ⟨d, hdne, φ, ?_⟩
  intro y
  rw [hφ]
  change (d : A) • h y = _
  simp only [Algebra.smul_def]
  change algebraMap A K (d : A) *
      Algebra.trace K L (algebraMap B L (x * y)) = _
  rw [map_mul]

/-- Mathlib's different ideal is the inverse of the trace dual. -/
def chapter11DifferentIdeal
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B] : Ideal B :=
  differentIdeal A B

/-- The quadratic equation T² - Tr(x) T + N(x) proves integrality from trace and norm. -/
def chapter11QuadraticTraceNormRelation
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (tr n : A) : Prop :=
  x ^ 2 - algebraMap A B tr * x + algebraMap A B n = 0

/-- A displayed monic quadratic relation is sufficient for integrality. -/
theorem chapter11_quadratic_trace_norm_implies_integral
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (tr n : A)
    (h : chapter11QuadraticTraceNormRelation A B x tr n) :
    IsIntegral A x := by
  have hdeg : (C (-tr) * X + C n : A[X]).degree < (2 : ℕ) := by
    exact (degree_add_le _ _).trans_lt (max_lt
      ((degree_C_mul_X_le _).trans_lt (by norm_num))
      (degree_C_le.trans_lt (by norm_num)))
  have hmonic : (X ^ 2 + (C (-tr) * X + C n) : A[X]).Monic :=
    monic_X_pow_add hdeg
  refine ⟨X ^ 2 - C tr * X + C n, ?_, ?_⟩
  · simpa only [map_neg, sub_eq_add_neg, neg_mul, add_assoc] using hmonic
  · simpa only [chapter11QuadraticTraceNormRelation, eval₂_sub, eval₂_add,
      eval₂_mul, eval₂_X, eval₂_X_pow, eval₂_C] using h

/-- For a genuine quadratic field extension, integral trace and norm values
give the monic characteristic equation and hence integrality. -/
theorem chapter11_quadratic_field_trace_norm_implies_integral
    (A K L : Type*) [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsFractionRing A K] [FiniteDimensional K L]
    (hdegree : Module.finrank K L = 2) (x : L)
    (htrace : ∃ tr : A, algebraMap A K tr = Algebra.trace K L x)
    (hnorm : ∃ n : A, algebraMap A K n = Algebra.norm K x) :
    IsIntegral A x := by
  classical
  rcases htrace with ⟨tr, htr⟩
  rcases hnorm with ⟨n, hn⟩
  let b := Module.Free.chooseBasis K L
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex K L) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex]
    exact hdegree
  let m := LinearMap.toMatrix b b (Algebra.lmul K L x)
  have hchar : LinearMap.charpoly (Algebra.lmul K L x) =
      X ^ 2 - C (Algebra.trace K L x) * X + C (Algebra.norm K x) := by
    rw [← LinearMap.charpoly_toMatrix (Algebra.lmul K L x) b]
    change m.charpoly = _
    rw [Matrix.charpoly_of_card_eq_two (M := m) hcard]
    have htr' : m.trace = Algebra.trace K L x := by
      simpa [m, Algebra.trace_apply] using
        (LinearMap.trace_eq_matrix_trace K b (Algebra.lmul K L x)).symm
    have hdet' : m.det = Algebra.norm K x := by
      simp [m, Algebra.norm_apply]
    rw [htr', hdet']
  have hroot := Algebra.aeval_self_charpoly_lmul (R := K) (M := L) x
  rw [hchar] at hroot
  have hrel : chapter11QuadraticTraceNormRelation A L x tr n := by
    rw [chapter11QuadraticTraceNormRelation]
    rw [← htr, ← hn] at hroot
    simpa [aeval_def, IsScalarTower.algebraMap_apply A K L] using hroot
  exact chapter11_quadratic_trace_norm_implies_integral A L x tr n hrel

/-- Higher-degree characteristic polynomials have intermediate coefficients. -/
def chapter11MonicCoefficientProfile (A : Type*) [CommRing A] (n : ℕ) :=
  Fin (n + 1) → A

/-- The endpoint coefficient data do not determine a monic coefficient profile. -/
theorem chapter11_higher_degree_trace_norm_omit_intermediate_coefficients
    (A : Type*) [CommRing A] [Nontrivial A] (n : ℕ) (hn : 3 ≤ n) :
    ∃ c d : chapter11MonicCoefficientProfile A n,
      c 0 = d 0 ∧ c ⟨n, Nat.lt_succ_self n⟩ =
        d ⟨n, Nat.lt_succ_self n⟩ ∧ c ≠ d := by
  classical
  let j : Fin (n + 1) := ⟨1, by omega⟩
  let c : chapter11MonicCoefficientProfile A n := fun _ => 0
  let d : chapter11MonicCoefficientProfile A n := fun i => if i = j then 1 else 0
  have hj0 : j ≠ (0 : Fin (n + 1)) := by
    intro h
    have := congrArg Fin.val h
    simp [j] at this
  have hjn : j ≠ (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) := by
    intro h
    have := congrArg Fin.val h
    simp [j] at this
    omega
  have hj0' : (0 : Fin (n + 1)) ≠ j := Ne.symm hj0
  have hjn' : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) ≠ j := Ne.symm hjn
  refine ⟨c, d, ?_, ?_, ?_⟩
  · simp [c, d, hj0']
  · simp [c, d, hjn']
  · intro hcd
    have hcdj := congrFun hcd j
    change (0 : A) = if j = j then 1 else 0 at hcdj
    rw [if_pos rfl] at hcdj
    have h01 : (0 : A) = 1 := hcdj
    exact zero_ne_one h01

/-- In degree at least three, distinct monic polynomials can have the same
constant and leading coefficients.  These are the intermediate coefficients
which trace and norm do not record. -/
theorem chapter11_monic_polynomials_with_same_endpoint_coefficients
    (A : Type*) [CommRing A] [Nontrivial A] (n : ℕ) (hn : 3 ≤ n) :
    ∃ f g : A[X], f.Monic ∧ g.Monic ∧ f.natDegree = n ∧ g.natDegree = n ∧
      f.coeff 0 = g.coeff 0 ∧ f.coeff n = g.coeff n ∧ f ≠ g := by
  let f : A[X] := X ^ n
  let g : A[X] := X ^ n + X
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hng : g.Monic := by
    apply monic_X_pow_add
    have hlt : (1 : WithBot ℕ) < n := by
      exact_mod_cast (show 1 < n by omega)
    simpa using hlt
  have hfn : f.natDegree = n := by simp [f]
  have hgn : g.natDegree = n := by
    change (X ^ n + X : A[X]).natDegree = n
    have hdeg : (X : A[X]).natDegree < (X ^ n : A[X]).natDegree := by
      simpa using (show 1 < n by omega)
    rw [natDegree_add_eq_left_of_natDegree_lt hdeg]
    simp
  have hneq : f ≠ g := by
    intro hfg
    have hc := congrArg (fun q : A[X] => q.coeff 1) hfg
    simp [f, g] at hc
  refine ⟨f, g, by simp [f], hng, hfn, hgn, ?_, ?_, hneq⟩
  · simp [f, g]
  · rw [coeff_add, coeff_X_pow, coeff_X]
    simp [show 1 ≠ n by omega]

/-- Thus endpoint trace/norm data alone do not determine the intermediate
coefficients in higher degree. -/
theorem chapter11_trace_norm_are_insufficient_in_higher_degree
    (A : Type*) [CommRing A] [Nontrivial A] (n : ℕ) (hn : 3 ≤ n) :
    ∃ c d : chapter11MonicCoefficientProfile A n, c ≠ d ∧ c 0 = d 0 := by
  rcases chapter11_higher_degree_trace_norm_omit_intermediate_coefficients A n hn with
    ⟨c, d, h0, _, hcd⟩
  exact ⟨c, d, hcd, h0⟩

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
