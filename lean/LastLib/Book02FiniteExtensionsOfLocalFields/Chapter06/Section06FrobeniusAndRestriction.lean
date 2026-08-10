import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section05TraceAndNormUnderFiniteFieldFrobenius

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
  have hForder : orderOf F = f := by
    simpa [F] using chapter06_arithmetic_frobenius_order k Kf f hdegree
  have hdpos : 0 < d :=
    Nat.pos_of_dvd_of_pos hdvd (hdegree ▸ Module.finrank_pos)
  have hdiv : d ∣ orderOf F := by
    rw [hForder]
    exact hdvd
  let H : Subgroup (Gal(Kf / k)) := Subgroup.zpowers (F ^ d)
  let E₀ : IntermediateField k Kf := IntermediateField.fixedField H
  have hHcard : Nat.card H = f / d := by
    change Nat.card (Subgroup.zpowers (F ^ d)) = f / d
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hdpos.ne' hdiv, hForder]
  have hrel₀ : Module.finrank E₀ Kf = f / d := by
    change Module.finrank (IntermediateField.fixedField H) Kf = f / d
    rw [IntermediateField.finrank_fixedField_eq_card, hHcard]
  have hprod₀ : Module.finrank k E₀ * Module.finrank E₀ Kf = f := by
    rw [← hdegree]
    exact Module.finrank_mul_finrank k E₀ Kf
  have hprod₀' : Module.finrank k E₀ * (f / d) = d * (f / d) := by
    calc
      Module.finrank k E₀ * (f / d) = f := by rw [← hrel₀]; exact hprod₀
      _ = d * (f / d) := (Nat.mul_div_cancel' hdvd).symm
  have hfdpos : 0 < f / d :=
    Nat.div_pos (Nat.le_of_dvd (hdegree ▸ Module.finrank_pos) hdvd) hdpos
  have hdim₀ : Module.finrank k E₀ = d :=
    Nat.eq_of_mul_eq_mul_right hfdpos hprod₀'
  refine ⟨E₀, hdim₀, ?_⟩
  intro E hE
  have hrel : Module.finrank E Kf = f / d := by
    have hprod := Module.finrank_mul_finrank k E Kf
    rw [hE, hdegree] at hprod
    exact Nat.eq_div_of_mul_eq_right hdpos.ne' hprod
  have hgen : F ^ d ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    letI : Fintype E := Fintype.ofFinite E
    have hcardE : Fintype.card E = Fintype.card k ^ d := by
      rw [Module.card_eq_pow_finrank (K := k) (V := E), hE]
    have hxe : (⟨x, hx⟩ : E) ^ (Fintype.card k ^ d) = ⟨x, hx⟩ := by
      rw [← hcardE]
      exact FiniteField.pow_card _
    have hpow : (F ^ d) (x : Kf) =
        (x : Kf) ^ (Fintype.card k ^ d) := by
      simp [F, chapter06ArithmeticFrobenius, AlgEquiv.coe_pow,
        FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    rw [hpow]
    exact congrArg (fun y : E => (y : Kf)) hxe
  have hsub : H ≤ E.fixingSubgroup := by
    change Subgroup.zpowers (F ^ d) ≤ E.fixingSubgroup
    exact Subgroup.zpowers_le.mpr hgen
  have hcardHfix : Nat.card E.fixingSubgroup = f / d := by
    rw [IsGalois.card_fixingSubgroup_eq_finrank E, hrel]
  have hsubeq : H = E.fixingSubgroup := by
    exact Subgroup.eq_of_le_of_card_ge hsub (hcardHfix.trans hHcard.symm).le
  have hfix : IntermediateField.fixedField H = E := by
    rw [← IsGalois.fixedField_fixingSubgroup E, hsubeq]
  exact hfix.symm

/- The residue cardinality of the degree-`d` intermediate field is `q^d`. -/
theorem chapter06_intermediate_field_cardinality
    (k Kf : Type*) [Field k] [Fintype k] [Field Kf] [Finite Kf]
    [Algebra k Kf] [FiniteDimensional k Kf]
    (E : IntermediateField k Kf) (d : ℕ)
    (hdegree : Module.finrank k E = d) :
    Nat.card E = Nat.card k ^ d := by
  rw [Module.natCard_eq_pow_finrank (K := k) (V := E), hdegree]

/- Arithmetic Frobenius restricts to arithmetic Frobenius on every intermediate field. -/
theorem chapter06_restriction_arithmetic_frobenius
    (k Kf : Type*) [Field k] [Fintype k] [Field Kf] [Finite Kf]
    [Algebra k Kf] [FiniteDimensional k Kf]
    (E : IntermediateField k Kf) [Normal k E] :
    AlgEquiv.restrictNormal (chapter06ArithmeticFrobenius k Kf) E =
      chapter06ArithmeticFrobenius k E := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  rw [AlgEquiv.restrictNormal_apply]
  simp only [chapter06_arithmetic_frobenius_apply, IntermediateField.coe_pow]

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
  rw [hcompat g, hg, hfrob]

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06
