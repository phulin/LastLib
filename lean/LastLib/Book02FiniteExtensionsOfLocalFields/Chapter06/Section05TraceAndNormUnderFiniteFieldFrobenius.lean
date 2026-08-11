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
  sorry

/- The norm exponent is the geometric-sum exponent when the degree is `f`. -/
theorem chapter06_finite_field_norm_exponent_eq_geometric_sum
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] (f : ℕ) (hdegree : Module.finrank k l = f) :
    chapter06FiniteFieldNormExponent k l =
      (Nat.card k ^ f - 1) / (Nat.card k - 1) := by
  sorry

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
  sorry

/- The trace is the sum of the Frobenius conjugates. -/
theorem chapter06_finite_field_trace_frobenius_sum
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l]
    (f : ℕ) (hdegree : Module.finrank k l = f) (a : l) :
    algebraMap k l (Algebra.trace k l a) =
      ∑ i ∈ Finset.range f, a ^ (Nat.card k ^ i) := by
  sorry

/- The norm is the product of the Frobenius conjugates. -/
theorem chapter06_finite_field_norm_frobenius_product
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l]
    (f : ℕ) (hdegree : Module.finrank k l = f) (a : l) :
    algebraMap k l (Algebra.norm k a) =
      ∏ i ∈ Finset.range f, a ^ (Nat.card k ^ i) := by
  sorry

/- The norm exponent is the finite-field geometric-sum exponent. -/
theorem chapter06_finite_field_norm_geometric_sum
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l]
    (f : ℕ) (hdegree : Module.finrank k l = f) (a : l) :
    algebraMap k l (Algebra.norm k a) =
      a ^ ((Nat.card k ^ f - 1) / (Nat.card k - 1)) := by
  sorry

/- The trace map of a finite-field extension is surjective. -/
theorem chapter06_finite_field_trace_surjective
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] :
    Function.Surjective (Algebra.trace k l) := by
  sorry

/- The trace is a nonzero `k`-linear map to the one-dimensional space `k`. -/
theorem chapter06_finite_field_trace_nonzero_and_target_dimension
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] :
    (Algebra.trace k l : l →ₗ[k] k) ≠ 0 ∧ Module.finrank k k = 1 := by
  sorry

/- The multiplicative group of a finite field is cyclic. -/
theorem chapter06_finite_field_units_are_cyclic
    (l : Type*) [Field l] [Finite l] : IsCyclic lˣ := by
  sorry

/- A generator of `lˣ` maps under the norm exponent to an element of order `q-1`. -/
theorem chapter06_finite_field_norm_exponent_on_generator
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] :
    ∃ g : lˣ,
      (∀ x : lˣ, x ∈ Subgroup.zpowers g) ∧
        orderOf (g ^ chapter06FiniteFieldNormExponent k l) = Nat.card k - 1 := by
  sorry

/- The norm map on finite fields is surjective. -/
theorem chapter06_finite_field_norm_surjective
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] :
    Function.Surjective (fun a : l => Algebra.norm k a) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06
