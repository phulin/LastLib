import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section04PolynomialPicture

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
  have hpow : ∀ n : ℕ,
      (chapter06ArithmeticFrobeniusRingEquiv k l ^ n) a =
        a ^ (Nat.card k ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', RingAut.mul_apply, ih, map_pow]
        have happly : chapter06ArithmeticFrobeniusRingEquiv k l a =
            a ^ Fintype.card k := by
          simpa [chapter06ArithmeticFrobeniusRingEquiv] using
            chapter06_arithmetic_frobenius_apply k l a
        rw [happly, Fintype.card_eq_nat_card, ← pow_mul,
          Nat.pow_succ', Nat.mul_comm]
  constructor
  · intro i
    change (chapter06ArithmeticFrobeniusRingEquiv k l ^ i.1) a = _
    exact hpow i.1
  · intro σ
    obtain ⟨i, hi⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k l).2 σ
    refine ⟨⟨i.1, ?_⟩, ?_⟩
    · simpa [hdegree] using i.isLt
    · calc
        σ a = (chapter06ArithmeticFrobenius k l ^ i.1) a := by
          change σ a =
            (FiniteField.frobeniusAlgEquivOfAlgebraic k l ^ i.1) a
          exact congrArg (fun τ : Gal(l / k) => τ a) hi.symm
        _ = a ^ (Nat.card k ^ i.1) := by
          simpa [chapter06ArithmeticFrobeniusRingEquiv,
            chapter06ArithmeticFrobenius, RingAut.coe_pow, AlgEquiv.coe_pow] using
            hpow i.1

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
  simpa [hdegree, Nat.geomSum_eq Fintype.one_lt_card] using
    (FiniteField.algebraMap_norm_eq_pow_sum k l a)

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
  exact ⟨Algebra.trace_ne_zero k l, by simp⟩

/- The multiplicative group of a finite field is cyclic. -/
theorem chapter06_finite_field_units_are_cyclic
    (l : Type*) [Field l] [Finite l] : IsCyclic lˣ := by
  infer_instance

/- A generator of `lˣ` maps under the norm exponent to an element of order `q-1`. -/
theorem chapter06_finite_field_norm_exponent_on_generator
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] :
    ∃ g : lˣ,
      (∀ x : lˣ, x ∈ Subgroup.zpowers g) ∧
        orderOf (g ^ chapter06FiniteFieldNormExponent k l) = Nat.card k - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := lˣ)
  have horder : orderOf g = Nat.card l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  have hcard : Nat.card l = Nat.card k ^ Module.finrank k l := by
    exact Module.natCard_eq_pow_finrank
  have hdiv : Nat.card k - 1 ∣ orderOf g := by
    rw [horder, hcard]
    simpa using
      (Nat.sub_dvd_pow_sub_pow (Nat.card k) 1 (Module.finrank k l))
  refine ⟨g, hg, ?_⟩
  simpa [chapter06FiniteFieldNormExponent, horder] using
    (orderOf_pow_orderOf_div (x := g) (orderOf_pos g).ne' hdiv)

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
  lift_mul : ∀ a b, lift (a * b) = lift a * lift b
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

/- Frobenius acts literally on Teichmüller representatives. -/
theorem chapter06_teichmuller_frobenius_formula
    {k l K L B : Type*} [Field k] [Fintype k] [Field l] [Fintype l]
    [Field K] [Field L] [CommRing B] [Algebra k l] [Algebra K L]
    [Algebra B L] [FiniteDimensional K L] [IsGalois K L]
    (T : Chapter06TeichmullerLiftData k l K L B) (a : l) :
    T.frobenius (chapter06TeichmullerRepresentative T a) =
      chapter06TeichmullerRepresentative T (a ^ Fintype.card k) := by
  exact T.frobenius_lift a

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
  have horder : orderOf T.frobenius = f := by
    calc
      orderOf T.frobenius = Nat.card (Gal(L / K)) :=
        orderOf_eq_card_of_forall_mem_zpowers (fun σ =>
          (Subgroup.mem_zpowers_iff).2 (T.frobenius_generates σ))
      _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
      _ = f := hdegree
  have hfinite : IsOfFinOrder T.frobenius :=
    isOfFinOrder_of_finite T.frobenius
  have hpowbij : Function.Bijective
      (fun i : Fin (orderOf T.frobenius) => T.frobenius ^ i.1) := by
    refine ⟨?_, ?_⟩
    · intro i j hij
      apply (finEquivZPowers hfinite).injective
      apply Subtype.ext
      simpa only [finEquivZPowers_apply] using hij
    · intro σ
      obtain ⟨n, hn⟩ :=
        (finEquivZPowers hfinite).surjective
          ⟨σ, (Subgroup.mem_zpowers_iff).2 (T.frobenius_generates σ)⟩
      refine ⟨n, ?_⟩
      simpa only [finEquivZPowers_apply, Subtype.coe_mk] using
        congrArg Subtype.val hn
  have hbij : Function.Bijective
      (fun i : Fin f => T.frobenius ^ i.1) := by
    simpa [Function.comp_def] using
      hpowbij.comp (finCongr horder.symm).bijective
  have hlift_pow (b : l) : ∀ n : ℕ, 0 < n →
      T.lift (b ^ n) = T.lift b ^ n := by
    intro n hn
    cases n with
    | zero => simp at hn
    | succ n =>
        induction n with
        | zero => simp
        | succ n ih =>
            calc
              T.lift (b ^ (Nat.succ (Nat.succ n))) =
                  T.lift (b ^ (Nat.succ n) * b) := by rw [pow_succ]
              _ = T.lift (b ^ (Nat.succ n)) * T.lift b := T.lift_mul _ _
              _ = (T.lift b ^ (Nat.succ n)) * T.lift b := by
                rw [ih (Nat.zero_lt_succ n)]
              _ = T.lift b ^ (Nat.succ (Nat.succ n)) := by
                symm
                exact pow_succ _ _
  have hrep_pow (n : ℕ) :
      (T.frobenius ^ n)
          (chapter06TeichmullerRepresentative T a) =
        chapter06TeichmullerRepresentative T
          (a ^ (Fintype.card k ^ n)) := by
    induction n with
    | zero => simp [chapter06TeichmullerRepresentative]
    | succ n ih =>
        rw [pow_succ', AlgEquiv.mul_apply, ih,
          chapter06_teichmuller_frobenius_formula]
        apply congrArg (chapter06TeichmullerRepresentative T)
        rw [← pow_mul, Nat.pow_succ', Nat.mul_comm]
  have hformula (i : Fin f) :
      (T.frobenius ^ i.1)
          (chapter06TeichmullerRepresentative T a) =
        (chapter06TeichmullerRepresentative T a) ^ (Nat.card k ^ i.1) := by
    rw [hrep_pow i.1]
    change algebraMap B L (T.lift (a ^ (Fintype.card k ^ i.1))) =
      (algebraMap B L (T.lift a)) ^ (Nat.card k ^ i.1)
    rw [hlift_pow a _ (pow_pos Fintype.card_pos _), map_pow]
    simp only [Fintype.card_eq_nat_card]
  rw [trace_eq_sum_automorphisms, Finset.sum_range]
  exact Eq.symm <| Fintype.sum_bijective _ hbij _ _ fun i =>
    (hformula i).symm

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
  have horder : orderOf T.frobenius = f := by
    calc
      orderOf T.frobenius = Nat.card (Gal(L / K)) :=
        orderOf_eq_card_of_forall_mem_zpowers (fun σ =>
          (Subgroup.mem_zpowers_iff).2 (T.frobenius_generates σ))
      _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
      _ = f := hdegree
  have hfinite : IsOfFinOrder T.frobenius :=
    isOfFinOrder_of_finite T.frobenius
  have hpowbij : Function.Bijective
      (fun i : Fin (orderOf T.frobenius) => T.frobenius ^ i.1) := by
    refine ⟨?_, ?_⟩
    · intro i j hij
      apply (finEquivZPowers hfinite).injective
      apply Subtype.ext
      simpa only [finEquivZPowers_apply] using hij
    · intro σ
      obtain ⟨n, hn⟩ :=
        (finEquivZPowers hfinite).surjective
          ⟨σ, (Subgroup.mem_zpowers_iff).2 (T.frobenius_generates σ)⟩
      refine ⟨n, ?_⟩
      simpa only [finEquivZPowers_apply, Subtype.coe_mk] using
        congrArg Subtype.val hn
  have hbij : Function.Bijective
      (fun i : Fin f => T.frobenius ^ i.1) := by
    simpa [Function.comp_def] using
      hpowbij.comp (finCongr horder.symm).bijective
  have hlift_pow (b : l) : ∀ n : ℕ, 0 < n →
      T.lift (b ^ n) = T.lift b ^ n := by
    intro n hn
    cases n with
    | zero => simp at hn
    | succ n =>
        induction n with
        | zero => simp
        | succ n ih =>
            calc
              T.lift (b ^ (Nat.succ (Nat.succ n))) =
                  T.lift (b ^ (Nat.succ n) * b) := by rw [pow_succ]
              _ = T.lift (b ^ (Nat.succ n)) * T.lift b := T.lift_mul _ _
              _ = (T.lift b ^ (Nat.succ n)) * T.lift b := by
                rw [ih (Nat.zero_lt_succ n)]
              _ = T.lift b ^ (Nat.succ (Nat.succ n)) := by
                symm
                exact pow_succ _ _
  have hrep_pow (n : ℕ) :
      (T.frobenius ^ n)
          (chapter06TeichmullerRepresentative T a) =
        chapter06TeichmullerRepresentative T
          (a ^ (Fintype.card k ^ n)) := by
    induction n with
    | zero => simp [chapter06TeichmullerRepresentative]
    | succ n ih =>
        rw [pow_succ', AlgEquiv.mul_apply, ih,
          chapter06_teichmuller_frobenius_formula]
        apply congrArg (chapter06TeichmullerRepresentative T)
        rw [← pow_mul, Nat.pow_succ', Nat.mul_comm]
  have hformula (i : Fin f) :
      (T.frobenius ^ i.1)
          (chapter06TeichmullerRepresentative T a) =
        (chapter06TeichmullerRepresentative T a) ^ (Nat.card k ^ i.1) := by
    rw [hrep_pow i.1]
    change algebraMap B L (T.lift (a ^ (Fintype.card k ^ i.1))) =
      (algebraMap B L (T.lift a)) ^ (Nat.card k ^ i.1)
    rw [hlift_pow a _ (pow_pos Fintype.card_pos _), map_pow]
    simp only [Fintype.card_eq_nat_card]
  rw [Algebra.norm_eq_prod_automorphisms]
  calc
    (∏ σ : Gal(L / K), σ (chapter06TeichmullerRepresentative T a)) =
        ∏ i : Fin f,
          (chapter06TeichmullerRepresentative T a) ^ (Nat.card k ^ i.1) := by
      exact Eq.symm <| Fintype.prod_bijective _ hbij _ _ fun i =>
        (hformula i).symm
    _ = (chapter06TeichmullerRepresentative T a) ^
        (∑ i : Fin f, Nat.card k ^ i.1) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ = (chapter06TeichmullerRepresentative T a) ^
        ((Nat.card k ^ f - 1) / (Nat.card k - 1)) := by
      have hk : 2 ≤ Nat.card k :=
        (Nat.succ_le_iff).2 <| by
          simpa only [Fintype.card_eq_nat_card] using
            (Fintype.one_lt_card : 1 < Fintype.card k)
      rw [Fin.sum_univ_eq_sum_range, Nat.geomSum_eq hk]

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06
