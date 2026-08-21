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
  classical
  have _ := ha
  have hncard : Nat.card (Gal(L/K)) = n := by
    rw [IsGalois.card_aut_eq_finrank K L, hcyc.1]
  have hσn : σ ^ n = 1 := by
    rw [← hncard]
    exact pow_card_eq_one'
  let p : ℕ → L := fun i =>
    (chapter03Hilbert90PartialProduct K L σ x i : L)
  have hp_succ (i : ℕ) :
      p (i + 1) = p i * (σ ^ i) (x : L) := by
    dsimp [p]
    rw [chapter03_hilbert90_partial_product_succ]
    simp [Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
  have hpow (i : ℕ) (z : L) :
      σ ((σ ^ i) z) = (σ ^ (i + 1)) z := by
    calc
      σ ((σ ^ i) z) = (σ * σ ^ i) z := rfl
      _ = (σ ^ i * σ) z := by rw [(Commute.self_pow σ i).eq]
      _ = (σ ^ (i + 1)) z := by rw [pow_succ]
  have hp_shift (i : ℕ) :
      (x : L) * σ (p i) = p (i + 1) := by
    induction i with
    | zero =>
        simp [p, chapter03Hilbert90PartialProduct]
    | succ i ih =>
        calc
          (x : L) * σ (p (i + 1)) =
              (x : L) * (σ (p i) * σ ((σ ^ i) (x : L))) := by
                rw [hp_succ i, map_mul]
          _ = ((x : L) * σ (p i)) * σ ((σ ^ i) (x : L)) := by ring
          _ = p (i + 1) * σ ((σ ^ i) (x : L)) := by rw [ih]
          _ = p (i + 1) * (σ ^ (i + 1)) (x : L) := by rw [hpow i]
          _ = p ((i + 1) + 1) := by rw [hp_succ (i + 1)]
  let s : ℕ → L := fun i => p i * (σ ^ i) a
  have hterm (i : ℕ) : (x : L) * σ (s i) = s (i + 1) := by
    dsimp [s]
    calc
      (x : L) * σ (p i * (σ ^ i) a) =
          ((x : L) * σ (p i)) * σ ((σ ^ i) a) := by
            rw [map_mul]
            ring
      _ = p (i + 1) * σ ((σ ^ i) a) := by rw [hp_shift i]
      _ = p (i + 1) * (σ ^ (i + 1)) a := by rw [hpow i]
  have hp_n : p n = 1 := by
    dsimp [p]
    exact congrArg (fun u : Lˣ => (u : L))
      (chapter03_hilbert90_partial_product_norm_wrap K L n σ hcyc x hx)
  have hp_zero : p 0 = 1 := by
    simp [p, chapter03Hilbert90PartialProduct]
  have hsn : s n = s 0 := by
    dsimp [s]
    rw [hp_n, hp_zero, hσn]
    simp
  have hsum_shift :
      (∑ i ∈ Finset.range n, s (i + 1)) =
        ∑ i ∈ Finset.range n, s i := by
    calc
      (∑ i ∈ Finset.range n, s (i + 1)) =
          (∑ i ∈ Finset.range (n + 1), s i) - s 0 := by
            rw [Finset.sum_range_succ' s n]
            abel
      _ = (∑ i ∈ Finset.range n, s i) + s n - s 0 := by
            rw [Finset.sum_range_succ]
      _ = ∑ i ∈ Finset.range n, s i := by
            rw [hsn]
            abel
  change (x : L) * σ (∑ i ∈ Finset.range n, s i) =
    ∑ i ∈ Finset.range n, s i
  calc
    (x : L) * σ (∑ i ∈ Finset.range n, s i) =
        ∑ i ∈ Finset.range n, (x : L) * σ (s i) := by
          rw [map_sum, Finset.mul_sum]
    _ = ∑ i ∈ Finset.range n, s (i + 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hterm i
    _ = ∑ i ∈ Finset.range n, s i := hsum_shift

/-- Hilbert 90 in the book's unit-valued convention. -/
theorem chapter03_hilbert90
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) (x : Lˣ) :
    chapter03NormUnit K L x = 1 ↔
      ∃ y : Lˣ, x = chapter03DifferenceUnit K L σ y := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := chapter03_hilbert90_averaging_exists_nonzero K L n σ hcyc x hx
    have hshift := chapter03_hilbert90_averaging_shift K L n σ hcyc x hx a ha
    let u : Lˣ := Units.mk0 (chapter03Hilbert90Averaging K L σ x n a) ha
    have hσa :
        σ (chapter03Hilbert90Averaging K L σ x n a) ≠ 0 := by
      exact (map_ne_zero σ).2 ha
    have hcalc :
        (x : L) =
          (σ (chapter03Hilbert90Averaging K L σ x n a))⁻¹ *
            chapter03Hilbert90Averaging K L σ x n a := by
      calc
        (x : L) =
            (x : L) * σ (chapter03Hilbert90Averaging K L σ x n a) /
              σ (chapter03Hilbert90Averaging K L σ x n a) := by
                field_simp
        _ =
            chapter03Hilbert90Averaging K L σ x n a /
              σ (chapter03Hilbert90Averaging K L σ x n a) := by
                rw [hshift]
        _ = (σ (chapter03Hilbert90Averaging K L σ x n a))⁻¹ *
              chapter03Hilbert90Averaging K L σ x n a := by
                field_simp
    refine ⟨u⁻¹, ?_⟩
    apply Units.ext
    rw [chapter03_difference_unit_apply]
    simpa [u] using hcalc
  · rintro ⟨y, rfl⟩
    apply Units.ext
    rw [chapter03_norm_unit_apply, chapter03_difference_unit_apply]
    have hnorm :
        Algebra.norm K (σ (y : L)) = Algebra.norm K (y : L) :=
      Algebra.norm_eq_of_algEquiv σ (y : L)
    have hnormi :
        Algebra.norm K ((y : L)⁻¹) = (Algebra.norm K (y : L))⁻¹ :=
      Algebra.norm_inv (K := K) (L := L) (y : L)
    calc
      Algebra.norm K (σ (y : L) / (y : L)) =
          Algebra.norm K (σ (y : L)) * Algebra.norm K ((y : L)⁻¹) := by
            rw [div_eq_mul_inv, map_mul]
      _ = 1 := by rw [hnorm, hnormi]; simp

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
  let n : ℕ := Module.finrank K L
  have hcyc : chapter03CyclicExtension K L n σ := ⟨rfl, hσ⟩
  have hx0 : x ≠ 0 := by
    intro hx0
    rw [hx0] at hx
    simp at hx
  let xu : Lˣ := hx0.isUnit.unit
  have hnorm : chapter03NormUnit K L xu = 1 := by
    apply Units.ext
    simpa [xu, chapter03_norm_unit_apply] using hx
  obtain ⟨y, hy⟩ :=
    (chapter03_hilbert90 K L n σ hcyc xu).mp hnorm
  have hyfield : (xu : L) = σ (y : L) / (y : L) := by
    rw [hy, chapter03_difference_unit_apply]
  refine ⟨y⁻¹, ?_⟩
  have hσinv : σ ((y : L)⁻¹) = (σ (y : L))⁻¹ := by
    exact map_inv₀ σ (y : L)
  calc
    (↑(y⁻¹) : L) / σ (↑(y⁻¹) : L) =
        σ (y : L) / (y : L) := by
          rw [Units.val_inv_eq_inv_val, hσinv]
          field_simp
    _ = (xu : L) := hyfield.symm
    _ = x := by
      exact hx0.isUnit.unit_spec.symm

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
