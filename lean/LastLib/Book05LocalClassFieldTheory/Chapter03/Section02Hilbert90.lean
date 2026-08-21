import LastLib.Book05LocalClassFieldTheory.Chapter03.Core
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

namespace LastLib.Book05LocalClassFieldTheory.Chapter03

noncomputable section

open scoped BigOperators

/-! ## 3.2. Hilbert's Theorem 90 with proof -/

/-- The twisted partial product `x_i = x σ(x) ⋯ σ^(i-1)(x)`. -/
def chapter03Hilbert90PartialProduct
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (x : Lˣ) (i : ℕ) : Lˣ :=
  ∏ j ∈ Finset.range i,
    Units.map ((σ ^ j).toRingEquiv.toMonoidHom) x

theorem chapter03_hilbert90_partial_product_zero
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (x : Lˣ) :
    chapter03Hilbert90PartialProduct K L σ x 0 = 1 := by
  simp [chapter03Hilbert90PartialProduct]

theorem chapter03_hilbert90_partial_product_succ
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (x : Lˣ) (i : ℕ) :
    chapter03Hilbert90PartialProduct K L σ x (i + 1) =
      chapter03Hilbert90PartialProduct K L σ x i *
        Units.map ((σ ^ i).toRingEquiv.toMonoidHom) x := by
  simp [chapter03Hilbert90PartialProduct, Finset.prod_range_succ]

/-- The twisted averaging operator `a ↦ ∑ x_i σ^i(a)`. -/
def chapter03Hilbert90Averaging
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (x : Lˣ) (n : ℕ) (a : L) : L :=
  ∑ i ∈ Finset.range n,
    (chapter03Hilbert90PartialProduct K L σ x i : L) * (σ ^ i) a

theorem chapter03_hilbert90_averaging_zero
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (x : Lˣ) (n : ℕ) :
    chapter03Hilbert90Averaging K L σ x n 0 =
      ∑ i ∈ Finset.range n, (chapter03Hilbert90PartialProduct K L σ x i : L) * 0 := by
  simp [chapter03Hilbert90Averaging]

theorem chapter03_hilbert90_partial_product_coe
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (x : Lˣ) (i : ℕ) :
    (chapter03Hilbert90PartialProduct K L σ x i : L) =
      ∏ j ∈ Finset.range i, (σ ^ j) (x : L) := by
  simp [chapter03Hilbert90PartialProduct]

theorem chapter03_hilbert90_partial_product_norm_wrap
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) (x : Lˣ)
    (hx : chapter03NormUnit K L x = 1) :
    chapter03Hilbert90PartialProduct K L σ x n = 1 := by
  classical
  have hncard : Nat.card (Gal(L/K)) = n := by
    rw [IsGalois.card_aut_eq_finrank K L, hcyc.1]
  have himage : Finset.image (fun i : ℕ => σ ^ i) (Finset.range n) = Finset.univ := by
    rw [← hncard]
    exact IsCyclic.image_range_card hcyc.2
  let e : Fin n → Gal(L/K) := fun i => σ ^ (i : ℕ)
  have he_surj : Function.Surjective e := by
    intro τ
    have hτ : τ ∈ Finset.image (fun i : ℕ => σ ^ i) (Finset.range n) := by
      rw [himage]
      simp
    rcases Finset.mem_image.mp hτ with ⟨i, hi, rfl⟩
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
  have he : Function.Bijective e := by
    apply (Fintype.bijective_iff_surjective_and_card e).2
    have hcard : Fintype.card (Gal(L/K)) = n := by
      simpa only [Nat.card_eq_fintype_card] using hncard
    exact ⟨he_surj, (Fintype.card_fin n).trans hcard.symm⟩
  have hprod :
      (∏ j ∈ Finset.range n, (σ ^ j) (x : L)) =
        ∏ τ : Gal(L/K), τ (x : L) := by
    calc
      (∏ j ∈ Finset.range n, (σ ^ j) (x : L)) =
          ∏ j : Fin n, (σ ^ (j : ℕ)) (x : L) := by
        exact (Fin.prod_univ_eq_prod_range
          (fun j : ℕ => (σ ^ j) (x : L)) n).symm
      _ = ∏ τ : Gal(L/K), τ (x : L) :=
        Fintype.prod_bijective e he _ _ (fun _ => rfl)
  have hx' : Algebra.norm K (x : L) = 1 := by
    simpa [chapter03_norm_unit_apply] using congrArg (fun u : Kˣ => (u : K)) hx
  apply Units.ext
  rw [chapter03_hilbert90_partial_product_coe, hprod,
    ← Algebra.norm_eq_prod_automorphisms, hx', map_one]
  simp

/-- Dedekind independence supplies a nonzero value of the averaging operator. -/
theorem chapter03_hilbert90_averaging_exists_nonzero
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) (x : Lˣ)
    (hx : chapter03NormUnit K L x = 1) :
    ∃ a : L, chapter03Hilbert90Averaging K L σ x n a ≠ 0 := by
  classical
  have _ := hx
  have hncard : Nat.card (Gal(L/K)) = n := by
    rw [IsGalois.card_aut_eq_finrank K L, hcyc.1]
  have himage : Finset.image (fun i : ℕ => σ ^ i) (Finset.range n) = Finset.univ := by
    rw [← hncard]
    exact IsCyclic.image_range_card hcyc.2
  let e : Fin n → Gal(L/K) := fun i => σ ^ (i : ℕ)
  have he_surj : Function.Surjective e := by
    intro τ
    have hτ : τ ∈ Finset.image (fun i : ℕ => σ ^ i) (Finset.range n) := by
      rw [himage]
      simp
    rcases Finset.mem_image.mp hτ with ⟨i, hi, rfl⟩
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
  have he : Function.Bijective e := by
    apply (Fintype.bijective_iff_surjective_and_card e).2
    have hcard : Fintype.card (Gal(L/K)) = n := by
      simpa only [Nat.card_eq_fintype_card] using hncard
    exact ⟨he_surj, (Fintype.card_fin n).trans hcard.symm⟩
  let E : Fin n ≃ Gal(L/K) := Equiv.ofBijective e he
  let f : Gal(L/K) → Lˣ := fun τ =>
    chapter03Hilbert90PartialProduct K L σ x (E.symm τ).val
  obtain ⟨a, ha⟩ : ∃ a : L, groupCohomology.Hilbert90.aux f a ≠ 0 :=
    not_forall.1 (fun H => groupCohomology.Hilbert90.aux_ne_zero f <|
      funext <| fun y => H y)
  have haux : groupCohomology.Hilbert90.aux f a =
      ∑ τ : Gal(L/K), f τ * τ a := by
    simp [groupCohomology.Hilbert90.aux, Finsupp.linearCombination,
      Finsupp.sum_fintype]
  have hsum :
      (∑ j : Fin n, f (e j) * e j a) =
        ∑ τ : Gal(L/K), f τ * τ a :=
    Fintype.sum_bijective e he _ _ (fun _ => rfl)
  refine ⟨a, ?_⟩
  rw [show chapter03Hilbert90Averaging K L σ x n a =
      ∑ j : Fin n, f (e j) * e j a by
    rw [chapter03Hilbert90Averaging, ← Fin.sum_univ_eq_sum_range]
    simp [f, E, e], hsum, ← haux]
  exact ha

/-- The index shift in the Hilbert 90 averaging argument. -/
theorem chapter03_hilbert90_averaging_shift
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) (x : Lˣ)
    (hx : chapter03NormUnit K L x = 1) (a : L)
    (ha : chapter03Hilbert90Averaging K L σ x n a ≠ 0) :
    (x : L) * σ (chapter03Hilbert90Averaging K L σ x n a) =
      chapter03Hilbert90Averaging K L σ x n a := by
  sorry

/-- Hilbert 90 in the book's unit-valued convention. -/
theorem chapter03_hilbert90
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) (x : Lˣ) :
    chapter03NormUnit K L x = 1 ↔
      ∃ y : Lˣ, x = chapter03DifferenceUnit K L σ y := by
  sorry

/-- The kernel/image form of Hilbert 90, matching the displayed set equality. -/
theorem chapter03_hilbert90_kernel_eq_difference_range
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) :
    {x : Lˣ | chapter03NormUnit K L x = 1} =
      Set.range (chapter03DifferenceUnit K L σ) := by
  ext x
  constructor
  · intro hx
    rcases (chapter03_hilbert90 K L n σ hcyc x).mp hx with ⟨y, hy⟩
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, hy⟩
    exact (chapter03_hilbert90 K L n σ hcyc x).mpr ⟨y, hy.symm⟩

/- This is deliberately a separate predicate: Hilbert 90 identifies the norm kernel, whereas norm
   surjectivity concerns the image and is an additional local-field calculation. -/
def chapter03NormSurjectivity
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Prop :=
  ∀ u : Kˣ, ∃ x : Lˣ, chapter03NormUnit K L x = u

/-- Mathlib's canonical generator-oriented formulation, with the opposite quotient convention. -/
theorem chapter03_hilbert90_via_mathlib
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)] (σ : Gal(L/K))
    (hσ : ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ)
    {x : L} (hx : Algebra.norm K x = 1) :
    ∃ y : Lˣ, y / σ y = x := by
  sorry

/-- The group-cohomological vanishing supplied by Mathlib's Hilbert 90 API. -/
abbrev chapter03Hilbert90H1
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :=
  groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L)

instance chapter03_hilbert90_h1_unique
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    Unique (chapter03Hilbert90H1 K L) := by
  infer_instance

theorem chapter03_hilbert90_h1_subsingleton
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    Subsingleton (chapter03Hilbert90H1 K L) := by
  infer_instance

end

end LastLib.Book05LocalClassFieldTheory.Chapter03
