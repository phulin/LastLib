import LastLib.Book05LocalClassFieldTheory.Chapter07.Section03DensityAndSurjectivity

namespace LastLib.Book05LocalClassFieldTheory.Chapter07

noncomputable section

open CategoryTheory Opposite
open scoped BigOperators

/-- The kernel of the infinite map is the intersection of all finite norm
subgroups. -/
theorem chapter07_local_reciprocity_kernel_eq_norm_intersection
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb) :
    (chapter07LocalReciprocity S).ker =
      ⨅ L : Chapter07FiniteAbelianIndex K KAb,
        chapter07NormSubgroup (K := K) (L := L) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_iInf]
    intro L
    rw [← chapter07_finite_artin_kernel_eq_norm S L]
    change S.artin L x = 1
    rw [← chapter07_finite_artin_is_the_reciprocity_projection S L x]
    rw [hx]
    simp only [InfiniteGalois.proj, map_one]
  · intro hx
    change chapter07LocalReciprocity S x = 1
    rw [Subgroup.mem_iInf] at hx
    apply (chapter07AbelianGaloisLimitEquiv K KAb).injective
    ext L
    induction L with
    | _ L =>
      rw [map_one]
      change
        (InfiniteGalois.proj L
          ((chapter07AbelianGaloisLimitEquiv K KAb)
            (chapter07LocalReciprocity S x)) : Gal(L / K)) =
          (1 : Gal(L / K))
      have hproj :=
        chapter07_finite_artin_is_the_reciprocity_projection S L x
      have hxL := hx L
      rw [← chapter07_finite_artin_kernel_eq_norm S L] at hxL
      change S.artin L x = 1 at hxL
      simpa only [InfiniteGalois.proj, map_one] using hproj.trans hxL

/-- Membership in the kernel is forced into every explicit finite-precision
subgroup supplied by the local existence construction. -/
theorem chapter07_local_reciprocity_kernel_le_precision
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (D : Chapter07PrecisionData Kˣ)
    (hcofinal : chapter07KernelCofinality (KAb := KAb) D) :
    (chapter07LocalReciprocity S).ker ≤
      chapter07PrecisionIntersection D := by
  intro x hx
  change x ∈ ⨅ m : Chapter07PositiveNat, ⨅ n : Chapter07PositiveNat,
    chapter07PrecisionSubgroup D m n
  rw [Subgroup.mem_iInf]
  intro m
  rw [Subgroup.mem_iInf]
  intro n
  obtain ⟨L, hL⟩ := hcofinal m n
  have hxall : x ∈ ⨅ L' : Chapter07FiniteAbelianIndex K KAb,
      chapter07NormSubgroup (K := K) (L := L') := by
    rw [← chapter07_local_reciprocity_kernel_eq_norm_intersection S]
    exact hx
  rw [Subgroup.mem_iInf] at hxall
  exact hL (hxall L)

/-- The intersection of all positive precision subgroups is trivial. -/
theorem chapter07_precision_intersection_eq_bot
    {G : Type*} [CommGroup G] (D : Chapter07PrecisionData G) :
    chapter07PrecisionIntersection D = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hxmn : ∀ m n : Chapter07PositiveNat,
        x ∈ chapter07PrecisionSubgroup D m n := by
      intro m n
      exact (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx m)) n
    let v : ℤ := Multiplicative.toAdd (D.valuation x)
    let m : Chapter07PositiveNat :=
      ⟨Int.natAbs v + 1, Nat.succ_pos _⟩
    have hdiv : (m.1 : ℤ) ∣ v := by
      change (m.1 : ℤ) ∣ Multiplicative.toAdd (D.valuation x)
      exact D.valuation_precision (hxmn m ⟨1, Nat.zero_lt_succ 0⟩)
    have hdiv_nat : m.1 ∣ Int.natAbs v := Int.natCast_dvd.mp hdiv
    have hv : v = 0 := by
      by_contra hv
      apply (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hv) ?_) hdiv_nat
      exact Nat.lt_succ_self _
    apply D.units_separated
    intro n
    have hnorm := D.normalized_precision (hxmn ⟨1, Nat.zero_lt_succ 0⟩ n)
    change x * D.uniformizer ^ (-v) ∈ D.unitFiltration n.1 at hnorm
    simpa [hv] using hnorm
  · exact bot_le

/-- The infinite reciprocity map has trivial kernel once the cofinal
precision family is available. -/
theorem chapter07_local_reciprocity_kernel_eq_bot
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (D : Chapter07PrecisionData Kˣ)
    (hcofinal : chapter07KernelCofinality (KAb := KAb) D) :
    (chapter07LocalReciprocity S).ker = ⊥ := by
  apply le_antisymm
  · exact
      (chapter07_local_reciprocity_kernel_le_precision S D hcofinal).trans
        (le_of_eq (chapter07_precision_intersection_eq_bot D))
  · exact bot_le

/-- Injectivity is the kernel form of the infinite reciprocity statement. -/
theorem chapter07_local_reciprocity_injective
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (D : Chapter07PrecisionData Kˣ)
    (hcofinal : chapter07KernelCofinality (KAb := KAb) D) :
    Function.Injective (chapter07LocalReciprocity S) := by
  exact (MonoidHom.ker_eq_bot_iff _).mp
    (chapter07_local_reciprocity_kernel_eq_bot S D hcofinal)

/-- The finite quotient form retained in Theorem 7.2. -/
theorem chapter07_local_reciprocity_finite_quotient
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (L : Chapter07FiniteAbelianIndex K KAb) :
    Nonempty
      (Kˣ ⧸ chapter07NormSubgroup (K := K) (L := L) ≃*
        Gal(L / K)) :=
  ⟨chapter07FiniteReciprocityEquiv S L⟩

/-- The exact infinite local reciprocity theorem: continuous, injective,
dense, and an isomorphism on every finite abelian quotient. -/
theorem chapter07_local_reciprocity_theorem
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (D : Chapter07PrecisionData Kˣ)
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ))
    (hcofinal : chapter07KernelCofinality (KAb := KAb) D) :
    Continuous (chapter07LocalReciprocity S) ∧
      Function.Injective (chapter07LocalReciprocity S) ∧
      DenseRange (chapter07LocalReciprocity S) ∧
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        Nonempty
          (Kˣ ⧸ chapter07NormSubgroup (K := K) (L := L) ≃*
            Gal(L / K)) := by
  refine ⟨chapter07_local_reciprocity_continuous S hopen, ?_, ?_, ?_⟩
  · exact chapter07_local_reciprocity_injective S D hcofinal
  · exact chapter07_local_reciprocity_dense S
  · intro L
    exact chapter07_local_reciprocity_finite_quotient S L

end

end LastLib.Book05LocalClassFieldTheory.Chapter07
