import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section02FrobeniusInAnUnramifiedExtension
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section03CompatibilityInTowers

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06

noncomputable section

open Set

/-! ## 6.6. Frobenius and restriction -/

/- The unique intermediate finite field of each allowed degree. -/
theorem chapter06_unique_intermediate_field_of_degree
    (k Kf : Type*) [Field k] [Fintype k] [Field Kf] [Finite Kf]
    [Algebra k Kf] [FiniteDimensional k Kf]
    (f d : ℕ) (hdegree : Module.finrank k Kf = f) (hdvd : d ∣ f) :
    ∃! E : IntermediateField k Kf, Module.finrank k E = d := by
  let F : Gal(Kf / k) := chapter06ArithmeticFrobenius k Kf
  have hfpos : 0 < f := by
    rw [← hdegree]
    exact Module.finrank_pos
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hfpos
  have hdivpos : 0 < f / d := Nat.div_pos (Nat.le_of_dvd hfpos hdvd) hdpos
  have hForder : orderOf F = f := by
    simpa [F] using chapter06_arithmetic_frobenius_order k Kf f hdegree
  have hpoworder : orderOf (F ^ d) = f / d := by
    rw [orderOf_pow_of_dvd hdpos.ne' (by simpa [hForder] using hdvd), hForder]
  let H : Subgroup Gal(Kf / k) := Subgroup.zpowers (F ^ d)
  let E₀ : IntermediateField k Kf := IntermediateField.fixedField H
  have hHcard : Nat.card H = f / d := by
    change Nat.card (Subgroup.zpowers (F ^ d)) = f / d
    rw [Nat.card_zpowers, hpoworder]
  have hErel : Module.finrank E₀ Kf = Nat.card H :=
    IntermediateField.finrank_fixedField_eq_card H
  have hEdegree : Module.finrank k E₀ = d := by
    have hmul : Module.finrank k E₀ * (f / d) = f := by
      calc
        Module.finrank k E₀ * (f / d) =
            Module.finrank k E₀ * Module.finrank E₀ Kf := by
          rw [hErel, hHcard]
        _ = Module.finrank k Kf := Module.finrank_mul_finrank k E₀ Kf
        _ = f := hdegree
    apply Nat.mul_right_cancel hdivpos
    calc
      Module.finrank k E₀ * (f / d) = f := hmul
      _ = d * (f / d) := by
        rw [Nat.mul_comm, Nat.div_mul_cancel hdvd]
  refine ⟨E₀, hEdegree, ?_⟩
  intro E hEdegree'
  have hrel : Module.finrank E Kf = f / d := by
    calc
      Module.finrank E Kf =
          Module.finrank k Kf / Module.finrank k E :=
        (Module.finrank_div_finrank_cancel_left k E Kf
          (by rw [hEdegree']; exact hdpos.ne')).symm
      _ = f / d := by rw [hdegree, hEdegree']
  have hHEcard : Nat.card E.fixingSubgroup = f / d := by
    calc
      Nat.card E.fixingSubgroup = Module.finrank E Kf :=
        IsGalois.card_fixingSubgroup_eq_finrank E
      _ = f / d := hrel
  have hgen : ∀ σ : Gal(Kf / k), σ ∈ Subgroup.zpowers F := by
    intro σ
    exact (Subgroup.mem_zpowers_iff).2
      (chapter06_arithmetic_frobenius_generates k Kf σ)
  have hHEle : E.fixingSubgroup ≤ Subgroup.zpowers F := by
    intro σ hσ
    exact hgen σ
  obtain ⟨n, hEn⟩ :=
    (Subgroup.le_zpowers_iff F E.fixingSubgroup).1 hHEle
  have hquot : f / Nat.gcd f n = f / d := by
    calc
      f / Nat.gcd f n = orderOf (F ^ n) := by
        rw [orderOf_pow, hForder]
      _ = Nat.card (Subgroup.zpowers (F ^ n)) := (Nat.card_zpowers (F ^ n)).symm
      _ = Nat.card E.fixingSubgroup := by rw [hEn]
      _ = f / d := hHEcard
  have hgcd : Nat.gcd f n = d := by
    apply Nat.mul_left_cancel hdivpos
    calc
      (f / d) * Nat.gcd f n = (f / Nat.gcd f n) * Nat.gcd f n := by rw [hquot]
      _ = f := Nat.div_mul_cancel (Nat.gcd_dvd_left f n)
      _ = (f / d) * d := (Nat.div_mul_cancel hdvd).symm
  have hdn : d ∣ n := by
    rw [← hgcd]
    exact Nat.gcd_dvd_right f n
  have hle : E.fixingSubgroup ≤ H := by
    rw [hEn]
    apply Subgroup.zpowers_le_of_mem
    obtain ⟨m, rfl⟩ := hdn
    change F ^ (d * m) ∈ Subgroup.zpowers (F ^ d)
    rw [pow_mul]
    exact pow_mem (Subgroup.mem_zpowers _) m
  have hEq : E.fixingSubgroup = H := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hHcard, hHEcard]
  calc
    E = IntermediateField.fixedField E.fixingSubgroup :=
      (IsGalois.fixedField_fixingSubgroup E).symm
    _ = IntermediateField.fixedField H := by rw [hEq]
    _ = E₀ := rfl

/- The residue cardinality of the degree-`d` intermediate field is `q^d`. -/
theorem chapter06_intermediate_field_cardinality
    (k Kf : Type*) [Field k] [Fintype k] [Field Kf] [Finite Kf]
    [Algebra k Kf] [FiniteDimensional k Kf]
    (E : IntermediateField k Kf) (d : ℕ)
    (hdegree : Module.finrank k E = d) :
    Nat.card E = Nat.card k ^ d := by
  simpa [hdegree] using (Module.natCard_eq_pow_finrank (K := k) (V := E))

/- Arithmetic Frobenius restricts to arithmetic Frobenius on every intermediate field. -/
theorem chapter06_restriction_arithmetic_frobenius
    (k Kf : Type*) [Field k] [Fintype k] [Field Kf] [Finite Kf]
    [Algebra k Kf] [FiniteDimensional k Kf]
    (E : IntermediateField k Kf) [Normal k E] :
    AlgEquiv.restrictNormal (chapter06ArithmeticFrobenius k Kf) E =
      chapter06ArithmeticFrobenius k E := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E Kf).injective
  calc
    algebraMap E Kf
        (AlgEquiv.restrictNormal (chapter06ArithmeticFrobenius k Kf) E x) =
      chapter06ArithmeticFrobenius k Kf (algebraMap E Kf x) :=
        AlgEquiv.restrictNormal_commutes (chapter06ArithmeticFrobenius k Kf) E x
    _ = (algebraMap E Kf x) ^ Fintype.card k :=
      chapter06_arithmetic_frobenius_apply k Kf (algebraMap E Kf x)
    _ = algebraMap E Kf (x ^ Fintype.card k) := by
      rw [map_pow]
    _ = algebraMap E Kf (chapter06ArithmeticFrobenius k E x) := by
      rw [chapter06_arithmetic_frobenius_apply k E x]

/- In the tower `Kf / E / k`, relative arithmetic Frobenius is the `k`-Frobenius power
    determined by the intermediate residue degree. -/
theorem chapter06_relative_arithmetic_frobenius_is_degree_power
    (k Kf : Type*) [Field k] [Fintype k] [Field Kf] [Finite Kf]
    [Algebra k Kf] [FiniteDimensional k Kf]
    (E : IntermediateField k Kf) [Fintype E]
    (d : ℕ) (hdegree : Module.finrank k E = d) :
    chapter06ArithmeticFrobeniusRingEquiv E Kf =
      (chapter06ArithmeticFrobeniusRingEquiv k Kf) ^ d := by
  exact chapter06_arithmetic_frobenius_tower_power_relation k E Kf d hdegree

/- The corresponding geometric Frobenius identity is obtained by inversion. -/
theorem chapter06_relative_geometric_frobenius_is_degree_power
    (k Kf : Type*) [Field k] [Fintype k] [Field Kf] [Finite Kf]
    [Algebra k Kf] [FiniteDimensional k Kf]
    (E : IntermediateField k Kf) [Fintype E]
    (d : ℕ) (hdegree : Module.finrank k E = d) :
    chapter06GeometricFrobeniusRingEquiv E Kf =
      (chapter06GeometricFrobeniusRingEquiv k Kf) ^ d := by
  exact chapter06_geometric_frobenius_tower_power_relation k E Kf d hdegree

/- A compatible map of Galois quotients carries the Frobenius coset to the
    corresponding Frobenius coset.  This models restriction to a subextension
    and passage to a ramified quotient without choosing compatible lifts. -/
theorem chapter06_quotient_map_carries_frobenius_coset
    {G H G' H' : Type*} [Group G] [Group H] [Group G'] [Group H']
    (I : Subgroup G) (I' : Subgroup G') [I.Normal] [I'.Normal]
    (D : Chapter06RamifiedGaloisReduction G H I)
    (D' : Chapter06RamifiedGaloisReduction G' H' I')
    (φ : G →* G') (ψ : H →* H') (α : H) (α' : H')
    (hcompat : ∀ g : G,
      D'.quotientEquiv (QuotientGroup.mk' I' (φ g)) =
        ψ (D.quotientEquiv (QuotientGroup.mk' I g)))
    (hfrob : ψ α = α') (g : G) :
    g ∈ chapter06ArithmeticFrobeniusCoset I D α →
      φ g ∈ chapter06ArithmeticFrobeniusCoset I' D' α' := by
  intro hg
  change D.quotientEquiv (QuotientGroup.mk' I g) = α at hg
  change D'.quotientEquiv (QuotientGroup.mk' I' (φ g)) = α'
  exact (hcompat g).trans ((congrArg ψ hg).trans hfrob)

/- The compatible map carries the entire Frobenius coset downstairs. -/
theorem chapter06_quotient_map_carries_frobenius_coset_set
    {G H G' H' : Type*} [Group G] [Group H] [Group G'] [Group H']
    (I : Subgroup G) (I' : Subgroup G') [I.Normal] [I'.Normal]
    (D : Chapter06RamifiedGaloisReduction G H I)
    (D' : Chapter06RamifiedGaloisReduction G' H' I')
    (φ : G →* G') (ψ : H →* H') (α : H) (α' : H')
    (hcompat : ∀ g : G,
      D'.quotientEquiv (QuotientGroup.mk' I' (φ g)) =
        ψ (D.quotientEquiv (QuotientGroup.mk' I g)))
    (hfrob : ψ α = α') :
    φ '' chapter06ArithmeticFrobeniusCoset I D α ⊆
      chapter06ArithmeticFrobeniusCoset I' D' α' := by
  rintro _ ⟨g, hg, rfl⟩
  exact chapter06_quotient_map_carries_frobenius_coset I I' D D' φ ψ α α'
    hcompat hfrob g hg

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06
