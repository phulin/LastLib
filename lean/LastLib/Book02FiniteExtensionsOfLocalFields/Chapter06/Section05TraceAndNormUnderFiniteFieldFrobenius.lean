import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section01WhyFrobeniusIsCanonical
import Mathlib.FieldTheory.Finite.Trace

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06

noncomputable section

open Polynomial
open scoped BigOperators

/-! ## 6.5. Trace and norm under finite-field Frobenius -/

/- The ordered list of Frobenius conjugates of an element. -/
def chapter06FrobeniusConjugates
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] (f : ℕ) (a : l) : Fin f → l :=
  fun i => (chapter06ArithmeticFrobeniusRingEquiv k l ^ i.1) a

/- The exponent occurring in the finite-field norm formula. -/
def chapter06FiniteFieldNormExponent
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l] : ℕ :=
  (Nat.card l - 1) / (Nat.card k - 1)

/- The cardinality of a finite residue extension is `q^f`. -/
theorem chapter06_finite_field_cardinality_from_degree
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] (f : ℕ) (hdegree : Module.finrank k l = f) :
    Nat.card l = Nat.card k ^ f := by
  simpa [hdegree] using (Module.natCard_eq_pow_finrank (K := k) (V := l))

/- The norm exponent is the geometric-sum exponent when the degree is `f`. -/
theorem chapter06_finite_field_norm_exponent_eq_geometric_sum
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] (f : ℕ) (hdegree : Module.finrank k l = f) :
    chapter06FiniteFieldNormExponent k l =
      (Nat.card k ^ f - 1) / (Nat.card k - 1) := by
  rw [chapter06FiniteFieldNormExponent,
    chapter06_finite_field_cardinality_from_degree k l f hdegree]

/- Every conjugate is a Frobenius power, with the displayed repetitions retained. -/
theorem chapter06_finite_field_conjugates_are_frobenius_powers
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] (f : ℕ)
    (hdegree : Module.finrank k l = f) (a : l) :
    (∀ i : Fin f,
      chapter06FrobeniusConjugates k l f a i =
        a ^ (Nat.card k ^ i.1)) ∧
      (∀ σ : Gal(l/k), ∃ i : Fin f,
        σ a = a ^ (Nat.card k ^ i.1)) := by
  constructor
  · intro i
    change (chapter06ArithmeticFrobeniusRingEquiv k l ^ i.1) a = _
    simp [chapter06ArithmeticFrobeniusRingEquiv, chapter06ArithmeticFrobenius,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
      Nat.card_eq_fintype_card]
  · intro σ
    obtain ⟨i, hi⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k l).2 σ
    change chapter06ArithmeticFrobenius k l ^ i.1 = σ at hi
    refine ⟨⟨i.1, ?_⟩, ?_⟩
    · simpa [hdegree] using i.isLt
    · rw [← hi]
      simp [chapter06ArithmeticFrobenius,
        FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]

/- The trace is the sum of the Frobenius conjugates. -/
theorem chapter06_finite_field_trace_frobenius_sum
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l]
    (f : ℕ) (hdegree : Module.finrank k l = f) (a : l) :
    algebraMap k l (Algebra.trace k l a) =
      ∑ i ∈ Finset.range f, a ^ (Nat.card k ^ i) := by
  simpa [hdegree] using (FiniteField.algebraMap_trace_eq_sum_pow k l a)

/- The norm is the product of the Frobenius conjugates. -/
theorem chapter06_finite_field_norm_frobenius_product
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l]
    (f : ℕ) (hdegree : Module.finrank k l = f) (a : l) :
    algebraMap k l (Algebra.norm k a) =
      ∏ i ∈ Finset.range f, a ^ (Nat.card k ^ i) := by
  simpa [hdegree] using (FiniteField.algebraMap_norm_eq_prod_pow k l a)

/- The norm exponent is the finite-field geometric-sum exponent. -/
theorem chapter06_finite_field_norm_geometric_sum
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l]
    (f : ℕ) (hdegree : Module.finrank k l = f) (a : l) :
    algebraMap k l (Algebra.norm k a) =
      a ^ ((Nat.card k ^ f - 1) / (Nat.card k - 1)) := by
  simp [chapter06_finite_field_cardinality_from_degree k l f hdegree,
    FiniteField.algebraMap_norm_eq_pow]

/- The trace map of a finite-field extension is surjective. -/
theorem chapter06_finite_field_trace_surjective
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] :
    Function.Surjective (Algebra.trace k l) := by
  exact Algebra.trace_surjective k l

/- The trace is a nonzero `k`-linear map to the one-dimensional space `k`. -/
theorem chapter06_finite_field_trace_nonzero_and_target_dimension
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] :
    (Algebra.trace k l : l →ₗ[k] k) ≠ 0 ∧ Module.finrank k k = 1 := by
  exact ⟨by
    intro hzero
    obtain ⟨x, hx⟩ := chapter06_finite_field_trace_surjective k l 1
    have hxzero : Algebra.trace k l x = 0 := by
      rw [hzero]
      rfl
    exact one_ne_zero (hx.symm.trans hxzero), by simp⟩

/- The multiplicative group of a finite field is cyclic. -/
theorem chapter06_finite_field_units_are_cyclic
    (l : Type*) [Field l] [Finite l] : IsCyclic lˣ := by
  exact inferInstance

/- A generator of `lˣ` maps under the norm exponent to an element of order `q-1`. -/
theorem chapter06_finite_field_norm_exponent_on_generator
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] :
    ∃ g : lˣ,
      (∀ x : lˣ, x ∈ Subgroup.zpowers g) ∧
        orderOf (g ^ chapter06FiniteFieldNormExponent k l) = Nat.card k - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := lˣ)
  refine ⟨g, hg, ?_⟩
  have horder : orderOf g = Nat.card l - 1 := by
    simpa [Nat.card_units] using
      (orderOf_eq_card_of_forall_mem_zpowers hg)
  have hcard : Nat.card l = Nat.card k ^ Module.finrank k l :=
    Module.natCard_eq_pow_finrank (K := k) (V := l)
  have hdiv : Nat.card k - 1 ∣ orderOf g := by
    rw [horder, hcard]
    exact Nat.sub_one_dvd_pow_sub_one _ _
  change orderOf (g ^ ((Nat.card l - 1) / (Nat.card k - 1))) = Nat.card k - 1
  rw [← horder]
  exact orderOf_pow_orderOf_div (orderOf_pos g).ne' hdiv

/- The norm map on finite fields is surjective. -/
theorem chapter06_finite_field_norm_surjective
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] :
    Function.Surjective (fun a : l => Algebra.norm k a) := by
  exact FiniteField.norm_surjective k l

/-
Mathlib has the finite-field trace and norm formulas, but it does not provide
the book's valuation-ring notation `[a]` as a single local-field object.  The
following structure records a multiplicative residue section together with
the Frobenius action that the complete unramified valuation-ring construction
supplies.
-/

/- A Teichmüller residue section equipped with its arithmetic Frobenius action. -/
structure Chapter06TeichmullerLiftData
    (k l K L B : Type*) [Field k] [Fintype k] [Field l] [Fintype l]
    [Field K] [Field L] [CommRing B] [Algebra k l] [Algebra K L]
    [Algebra B L] [FiniteDimensional K L] [IsGalois K L] where
  residue : B →+* l
  lift : l → B
  residue_lift : ∀ a, residue (lift a) = a
  lift_zero : lift 0 = 0
  lift_one : lift 1 = 1
  lift_mul : ∀ a b, lift (a * b) = lift a * lift b
  /- The exponent is prime to the residue characteristic in the model. -/
  lift_exponent_is_unit : IsUnit ((Nat.card l - 1 : ℕ) : B)
  /- The nonzero lift is a root of `T^(#l-1) - 1`. -/
  lift_root : ∀ {a : l}, a ≠ 0 → lift a ^ (Nat.card l - 1) = 1
  /- The residue condition and this equation characterize the lift. -/
  lift_root_unique : ∀ {a : l} {x : B}, a ≠ 0 → residue x = a →
    x ^ (Nat.card l - 1) = 1 → x = lift a
  frobenius : Gal(L/K)
  frobenius_generates : ∀ σ : Gal(L/K), ∃ n : ℤ, frobenius ^ n = σ
  frobenius_lift : ∀ a,
    frobenius (algebraMap B L (lift a)) =
      algebraMap B L (lift (a ^ Fintype.card k))

/- The field element represented by a Teichmüller lift. -/
def chapter06TeichmullerRepresentative
    {k l K L B : Type*} [Field k] [Fintype k] [Field l] [Fintype l]
    [Field K] [Field L] [CommRing B] [Algebra k l] [Algebra K L]
    [Algebra B L] [FiniteDimensional K L] [IsGalois K L]
    (T : Chapter06TeichmullerLiftData k l K L B) (a : l) : L :=
  algebraMap B L (T.lift a)

/- A Teichmüller representative reduces to the element it represents. -/
theorem chapter06_teichmuller_reduces_to_residue
    {k l K L B : Type*} [Field k] [Fintype k] [Field l] [Fintype l]
    [Field K] [Field L] [CommRing B] [Algebra k l] [Algebra K L]
    [Algebra B L] [FiniteDimensional K L] [IsGalois K L]
    (T : Chapter06TeichmullerLiftData k l K L B) (a : l) :
    T.residue (T.lift a) = a := by
  exact T.residue_lift a

/- The zero and unit Teichmüller representatives have their expected values. -/
theorem chapter06_teichmuller_zero_one
    {k l K L B : Type*} [Field k] [Fintype k] [Field l] [Fintype l]
    [Field K] [Field L] [CommRing B] [Algebra k l] [Algebra K L]
    [Algebra B L] [FiniteDimensional K L] [IsGalois K L]
    (T : Chapter06TeichmullerLiftData k l K L B) :
    T.lift 0 = 0 ∧ T.lift 1 = 1 := by
  exact ⟨T.lift_zero, T.lift_one⟩

/- The nonzero Teichmüller lift is the distinguished simple root. -/
theorem chapter06_teichmuller_root_and_uniqueness
    {k l K L B : Type*} [Field k] [Fintype k] [Field l] [Fintype l]
    [Field K] [Field L] [CommRing B] [Algebra k l] [Algebra K L]
    [Algebra B L] [FiniteDimensional K L] [IsGalois K L]
    (T : Chapter06TeichmullerLiftData k l K L B) {a : l} (ha : a ≠ 0) :
    T.lift a ^ (Nat.card l - 1) = 1 ∧
      ∀ {x : B}, T.residue x = a →
        x ^ (Nat.card l - 1) = 1 → x = T.lift a := by
  exact ⟨T.lift_root ha, fun hres hroot => T.lift_root_unique ha hres hroot⟩

/- Frobenius acts literally on Teichmüller representatives. -/
theorem chapter06_teichmuller_frobenius_formula
    {k l K L B : Type*} [Field k] [Fintype k] [Field l] [Fintype l]
    [Field K] [Field L] [CommRing B] [Algebra k l] [Algebra K L]
    [Algebra B L] [FiniteDimensional K L] [IsGalois K L]
    (T : Chapter06TeichmullerLiftData k l K L B) (a : l) :
    T.frobenius (chapter06TeichmullerRepresentative T a) =
      chapter06TeichmullerRepresentative T (a ^ Fintype.card k) := by
  exact T.frobenius_lift a

/- On Teichmüller representatives, Frobenius is literally the `q`th power. -/
theorem chapter06_teichmuller_frobenius_power_formula
    {k l K L B : Type*} [Field k] [Fintype k] [Field l] [Fintype l]
    [Field K] [Field L] [CommRing B] [Algebra k l] [Algebra K L]
    [Algebra B L] [FiniteDimensional K L] [IsGalois K L]
    (T : Chapter06TeichmullerLiftData k l K L B) (a : l) :
    T.frobenius (chapter06TeichmullerRepresentative T a) =
      (chapter06TeichmullerRepresentative T a) ^ Fintype.card k := by
  rw [chapter06_teichmuller_frobenius_formula]
  change algebraMap B L (T.lift (a ^ Fintype.card k)) =
    (algebraMap B L (T.lift a)) ^ Fintype.card k
  have hpow : ∀ n : ℕ, T.lift (a ^ n) = (T.lift a) ^ n := by
    intro n
    induction n with
    | zero => simp [T.lift_one]
    | succ n ih =>
        rw [pow_succ, pow_succ, T.lift_mul, ih]
  rw [hpow, map_pow]

/- The upstairs trace of a Teichmüller representative has the same pattern. -/
theorem chapter06_teichmuller_trace_formula
    {k l K L B : Type*} [Field k] [Fintype k] [Field l] [Fintype l]
    [Field K] [Field L] [CommRing B] [Algebra k l] [Algebra K L]
    [Algebra B L] [FiniteDimensional K L] [IsGalois K L]
    (T : Chapter06TeichmullerLiftData k l K L B) (f : ℕ)
    (hdegree : Module.finrank K L = f) (a : l) :
    algebraMap K L
        (Algebra.trace K L (chapter06TeichmullerRepresentative T a)) =
      ∑ i ∈ Finset.range f,
        (chapter06TeichmullerRepresentative T a) ^ (Nat.card k ^ i) := by
  let F : Gal(L/K) := T.frobenius
  have hgen : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers F := by
    intro σ
    exact (Subgroup.mem_zpowers_iff).2 (T.frobenius_generates σ)
  have horder : orderOf F = f := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen,
      IsGalois.card_aut_eq_finrank, hdegree]
  let φ : Fin f → Gal(L/K) := fun i => F ^ i.1
  have hφ : Function.Bijective φ := by
    apply (Fintype.bijective_iff_injective_and_card φ).2
    refine ⟨?_, ?_⟩
    · intro i j hij
      change F ^ i.1 = F ^ j.1 at hij
      have hmod := (isOfFinOrder_of_finite F).pow_inj_mod.mp hij
      rw [horder] at hmod
      apply Fin.ext
      calc
        i.1 = i.1 % f := (Nat.mod_eq_of_lt i.isLt).symm
        _ = j.1 % f := hmod
        _ = j.1 := Nat.mod_eq_of_lt j.isLt
    · rw [Fintype.card_fin, Fintype.card_eq_nat_card]
      exact (show Nat.card (Gal(L/K)) = f from by
        rw [← orderOf_eq_card_of_forall_mem_zpowers hgen, horder]).symm
  have hFpow : ∀ n : ℕ,
      (F ^ n) (chapter06TeichmullerRepresentative T a) =
        (chapter06TeichmullerRepresentative T a) ^ (Fintype.card k ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        change (F ^ n) (F (chapter06TeichmullerRepresentative T a)) = _
        rw [show F (chapter06TeichmullerRepresentative T a) =
            (chapter06TeichmullerRepresentative T a) ^ Fintype.card k by
              simpa [F] using chapter06_teichmuller_frobenius_power_formula T a]
        rw [map_pow, ih, ← pow_mul]
        simp [pow_succ, Nat.mul_comm]
  rw [trace_eq_sum_automorphisms]
  rw [← Fintype.sum_equiv (Equiv.ofBijective φ hφ)
    (fun i => (φ i) (chapter06TeichmullerRepresentative T a))
    (fun σ => σ (chapter06TeichmullerRepresentative T a)) (fun _ => rfl)]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simpa [φ, Nat.card_eq_fintype_card] using hFpow i

/- The upstairs norm of a Teichmüller representative has the same pattern. -/
theorem chapter06_teichmuller_norm_formula
    {k l K L B : Type*} [Field k] [Fintype k] [Field l] [Fintype l]
    [Field K] [Field L] [CommRing B] [Algebra k l] [Algebra K L]
    [Algebra B L] [FiniteDimensional K L] [IsGalois K L]
    (T : Chapter06TeichmullerLiftData k l K L B) (f : ℕ)
    (hdegree : Module.finrank K L = f) (a : l) :
    algebraMap K L
        (Algebra.norm K (chapter06TeichmullerRepresentative T a)) =
      (chapter06TeichmullerRepresentative T a) ^
        ((Nat.card k ^ f - 1) / (Nat.card k - 1)) := by
  let F : Gal(L/K) := T.frobenius
  have hgen : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers F := by
    intro σ
    exact (Subgroup.mem_zpowers_iff).2 (T.frobenius_generates σ)
  have horder : orderOf F = f := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen,
      IsGalois.card_aut_eq_finrank, hdegree]
  let φ : Fin f → Gal(L/K) := fun i => F ^ i.1
  have hφ : Function.Bijective φ := by
    apply (Fintype.bijective_iff_injective_and_card φ).2
    refine ⟨?_, ?_⟩
    · intro i j hij
      change F ^ i.1 = F ^ j.1 at hij
      have hmod := (isOfFinOrder_of_finite F).pow_inj_mod.mp hij
      rw [horder] at hmod
      apply Fin.ext
      calc
        i.1 = i.1 % f := (Nat.mod_eq_of_lt i.isLt).symm
        _ = j.1 % f := hmod
        _ = j.1 := Nat.mod_eq_of_lt j.isLt
    · rw [Fintype.card_fin, Fintype.card_eq_nat_card]
      exact (show Nat.card (Gal(L/K)) = f from by
        rw [← orderOf_eq_card_of_forall_mem_zpowers hgen, horder]).symm
  have hFpow : ∀ n : ℕ,
      (F ^ n) (chapter06TeichmullerRepresentative T a) =
        (chapter06TeichmullerRepresentative T a) ^ (Fintype.card k ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        change (F ^ n) (F (chapter06TeichmullerRepresentative T a)) = _
        rw [show F (chapter06TeichmullerRepresentative T a) =
            (chapter06TeichmullerRepresentative T a) ^ Fintype.card k by
              simpa [F] using chapter06_teichmuller_frobenius_power_formula T a]
        rw [map_pow, ih, ← pow_mul]
        simp [pow_succ, Nat.mul_comm]
  rw [Algebra.norm_eq_prod_automorphisms]
  calc
    (∏ σ : Gal(L/K), σ (chapter06TeichmullerRepresentative T a)) =
        ∏ i : Fin f, (φ i) (chapter06TeichmullerRepresentative T a) := by
      exact (Fintype.prod_equiv (Equiv.ofBijective φ hφ)
        (fun i => (φ i) (chapter06TeichmullerRepresentative T a))
        (fun σ => σ (chapter06TeichmullerRepresentative T a)) (fun _ => rfl)).symm
    _ = ∏ i : Fin f,
        (chapter06TeichmullerRepresentative T a) ^ (Nat.card k ^ i.1) := by
      apply Finset.prod_congr rfl
      intro i hi
      simpa [φ, Nat.card_eq_fintype_card] using hFpow i.1
    _ = (chapter06TeichmullerRepresentative T a) ^
        (∑ i : Fin f, Nat.card k ^ i.1) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ = (chapter06TeichmullerRepresentative T a) ^
        ((Nat.card k ^ f - 1) / (Nat.card k - 1)) := by
      have hgeom :
          (∑ i ∈ Finset.range f, Nat.card k ^ i) =
            (Nat.card k ^ f - 1) / (Nat.card k - 1) := by
        simpa only [Nat.card_eq_fintype_card] using
          (Nat.geomSum_eq (Fintype.one_lt_card : 2 ≤ Fintype.card k) f)
      rw [Fin.sum_univ_eq_sum_range, hgeom]

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06
