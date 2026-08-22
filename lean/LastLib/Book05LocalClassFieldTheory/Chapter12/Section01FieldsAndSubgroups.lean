import LastLib.Book05LocalClassFieldTheory.Chapter12.Core
import LastLib.Book05LocalClassFieldTheory.Chapter06.Section07TheExistenceTheorem

namespace LastLib.Book05LocalClassFieldTheory.Chapter12

noncomputable section

/-! ## 12.1. Fields and subgroups -/

/-- Finite reciprocity identifies the norm quotient with the Galois group. -/
theorem chapter12_subextension_artin_quotient_equiv
    {K : Type*} [Field K]
    (P : Chapter12LocalFieldProfile K)
    (E : Chapter12FiniteAbelianSubextension K) :
    Nonempty
      (Kˣ ⧸ E.normSubgroup ≃* Gal(E.field / K)) := by
  let _ : FiniteDimensional K E.field := E.finite
  let _ : IsGalois K E.field := E.galois
  let _ : Fintype (Gal(E.field / K)) := E.galois_group_finite
  obtain ⟨A⟩ :=
    LastLib.Book05LocalClassFieldTheory.Chapter06.chapter06_finite_artin_map_exists_for_subextension E
  have hmap : chapter12MultiplicativeNormMap K E.field =
      LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormMap K E.field := by
    rfl
  have hsub :
      LastLib.Book05LocalClassFieldTheory.Chapter06.chapter06NormSubgroup K E.field =
        chapter12NormSubgroup K E.field := by
    ext x
    rw [LastLib.Book05LocalClassFieldTheory.Chapter06.chapter06_mem_normSubgroup_iff,
      chapter12_mem_normSubgroup_iff, hmap]
  have hnorm : E.normSubgroup = chapter12NormSubgroup K E.field := by
    rw [LastLib.Book05LocalClassFieldTheory.Chapter06.chapter06FiniteAbelianSubextension_normSubgroup_coe E,
      hsub]
  let A' : LastLib.Book05LocalClassFieldTheory.Chapter10.Chapter10FiniteArtinMap
      K E.field := {
    reciprocity := A.reciprocity
    kernel_eq_norm := by
      rw [A.kernel_eq_norm, hsub]
    surjective := A.surjective }
  rw [hnorm]
  exact ⟨LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10ArtinQuotientEquiv
    K E.field A'⟩

/-- The index of the norm subgroup is the extension degree. -/
theorem chapter12_subextension_norm_index_eq_degree
    {K : Type*} [Field K]
    (P : Chapter12LocalFieldProfile K)
    (E : Chapter12FiniteAbelianSubextension K) :
    Nat.card (Kˣ ⧸ E.normSubgroup) = E.degree := by
  let _ : FiniteDimensional K E.field := E.finite
  let _ : IsGalois K E.field := E.galois
  let _ : Fintype (Gal(E.field / K)) := E.galois_group_finite
  obtain ⟨e⟩ := chapter12_subextension_artin_quotient_equiv P E
  calc
    Nat.card (Kˣ ⧸ E.normSubgroup) = Nat.card (Gal(E.field / K)) :=
      Nat.card_congr e.toEquiv
    _ = Module.finrank K E.field :=
      LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05_galois_group_card_eq_degree
        K E.field
    _ = E.degree := rfl

 /-- Every open finite-index subgroup is realized by a unique finite abelian
subextension of the fixed algebraic closure. -/
theorem chapter12_open_subgroup_correspondence
    {K : Type*} [Field K] [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (P : Chapter12LocalFieldProfile K)
    (H : Subgroup Kˣ) (hH : chapter12OpenFiniteIndex H) :
    ∃! E : Chapter12FiniteAbelianSubextension K,
      E.normSubgroup = H := by
  sorry

private theorem chapter12_normSubgroup_eq_chapter10
    {K : Type*} [Field K]
    (E : Chapter12FiniteAbelianSubextension K) :
    E.normSubgroup =
      @LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup
        K E.field _ _ _ E.finite := by
  let _ : FiniteDimensional K E.field := E.finite
  rw [LastLib.Book05LocalClassFieldTheory.Chapter06.chapter06FiniteAbelianSubextension_normSubgroup_coe E]
  ext u
  rw [LastLib.Book05LocalClassFieldTheory.Chapter06.chapter06_mem_normSubgroup_iff,
    LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10_mem_normSubgroup_iff]
  rfl

private theorem chapter12_chapter10_norm_subgroup_algEquiv
    {K L₁ L₂ : Type*} [Field K] [Field L₁] [Field L₂]
    [Algebra K L₁] [Algebra K L₂]
    (e : L₁ ≃ₐ[K] L₂) [FiniteDimensional K L₁] [FiniteDimensional K L₂] :
    LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K L₁ =
      LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K L₂ := by
  ext u
  rw [LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10_mem_normSubgroup_iff,
    LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10_mem_normSubgroup_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Units.map e.toMonoidHom y, ?_⟩
    apply Units.ext
    rw [← hy]
    change Algebra.norm K (e (y : L₁)) = Algebra.norm K (y : L₁)
    rw [Algebra.norm_eq_of_equiv_equiv (RingEquiv.refl K) e.toRingEquiv]
    · rfl
    · apply RingHom.ext
      intro x
      exact (e.commutes x).symm
  · rintro ⟨y, hy⟩
    refine ⟨Units.map e.symm.toMonoidHom y, ?_⟩
    apply Units.ext
    rw [← hy]
    change Algebra.norm K (e.symm (y : L₂)) = Algebra.norm K (y : L₂)
    rw [Algebra.norm_eq_of_equiv_equiv (RingEquiv.refl K) e.symm.toRingEquiv]
    · rfl
    · apply RingHom.ext
      intro x
      exact (e.symm.commutes x).symm

private theorem chapter12_compositum_is_abelian
    {K : Type*} [Field K]
    (E₁ E₂ : Chapter12FiniteAbelianSubextension K) :
    IsAbelianGalois K
      (E₁.field ⊔ E₂.field : IntermediateField K (AlgebraicClosure K)) := by
  let _ : FiniteDimensional K E₁.field := E₁.finite
  let _ : FiniteDimensional K E₂.field := E₂.finite
  let _ : IsGalois K E₁.field := E₁.galois
  let _ : IsGalois K E₂.field := E₂.galois
  let _ : IsAbelianGalois K E₁.field :=
    { toIsGalois := E₁.galois, is_comm := ⟨E₁.abelian⟩ }
  let _ : IsAbelianGalois K E₂.field :=
    { toIsGalois := E₂.galois, is_comm := ⟨E₂.abelian⟩ }
  let F : IntermediateField K (AlgebraicClosure K) := E₁.field ⊔ E₂.field
  let _ : FiniteDimensional K F := by infer_instance
  let A : IntermediateField K F := E₁.field.restrict le_sup_left
  let B : IntermediateField K F := E₂.field.restrict le_sup_right
  let eA : E₁.field ≃ₐ[K] A := E₁.field.restrictAlgEquiv le_sup_left
  let eB : E₂.field ≃ₐ[K] B := E₂.field.restrictAlgEquiv le_sup_right
  let _ : IsAbelianGalois K A := IsAbelianGalois.of_algHom eA.symm.toAlgHom
  let _ : IsAbelianGalois K B := IsAbelianGalois.of_algHom eB.symm.toAlgHom
  have hsup : A ⊔ B = (⊤ : IntermediateField K F) := by
    apply IntermediateField.lift_injective F
    rw [IntermediateField.lift_sup, IntermediateField.lift_top,
      IntermediateField.lift_restrict, IntermediateField.lift_restrict]
  have hAF : IsGalois A F :=
    IsGalois.sup_right B A (by rw [sup_comm]; exact hsup)
  let _ : IsGalois A F := hAF
  have hsepF : Algebra.IsSeparable K F := Algebra.IsSeparable.trans K A F
  let _ : Normal K (⊤ : IntermediateField K F) := by
    rw [← hsup]
    infer_instance
  have hnormF : Normal K F :=
    Normal.of_algEquiv (IntermediateField.topEquiv :
      (⊤ : IntermediateField K F) ≃ₐ[K] F)
  have hFgal : IsGalois K F :=
    { to_isSeparable := hsepF, to_normal := hnormF }
  let _ : IsGalois K F := hFgal
  let rA : Gal(F / K) →* Gal(A / K) := AlgEquiv.restrictNormalHom A
  let rB : Gal(F / K) →* Gal(B / K) := AlgEquiv.restrictNormalHom B
  let dA : Gal(A / K) →* Gal(E₁.field / K) :=
    { toFun := fun q => eA.trans (q.trans eA.symm)
      map_one' := by
        ext x
        simp only [AlgEquiv.trans_apply, AlgEquiv.one_apply, AlgEquiv.symm_apply_apply]
      map_mul' := by
        intro q r
        ext x
        simp only [AlgEquiv.trans_apply, AlgEquiv.mul_apply, AlgEquiv.apply_symm_apply] }
  let dB : Gal(B / K) →* Gal(E₂.field / K) :=
    { toFun := fun q => eB.trans (q.trans eB.symm)
      map_one' := by
        ext x
        simp only [AlgEquiv.trans_apply, AlgEquiv.one_apply, AlgEquiv.symm_apply_apply]
      map_mul' := by
        intro q r
        ext x
        simp only [AlgEquiv.trans_apply, AlgEquiv.mul_apply, AlgEquiv.apply_symm_apply] }
  have hdA : Function.Injective dA := by
    intro q r h
    apply AlgEquiv.ext
    intro y
    have h' := congrArg (fun s : Gal(E₁.field / K) => s (eA.symm y)) h
    have h'' := congrArg eA h'
    change eA (eA.symm (q (eA (eA.symm y)))) =
      eA (eA.symm (r (eA (eA.symm y)))) at h''
    simpa only [AlgEquiv.apply_symm_apply] using h''
  have hdB : Function.Injective dB := by
    intro q r h
    apply AlgEquiv.ext
    intro y
    have h' := congrArg (fun s : Gal(E₂.field / K) => s (eB.symm y)) h
    have h'' := congrArg eB h'
    change eB (eB.symm (q (eB (eB.symm y)))) =
      eB (eB.symm (r (eB (eB.symm y)))) at h''
    simpa only [AlgEquiv.apply_symm_apply] using h''
  have hcommA (σ τ : Gal(F / K)) : rA σ * rA τ = rA τ * rA σ := by
    apply hdA
    simpa only [map_mul] using E₁.abelian (dA (rA σ)) (dA (rA τ))
  have hcommB (σ τ : Gal(F / K)) : rB σ * rB τ = rB τ * rB σ := by
    apply hdB
    simpa only [map_mul] using E₂.abelian (dB (rB σ)) (dB (rB τ))
  have hcomm (σ τ : Gal(F / K)) : σ * τ = τ * σ := by
    let c : Gal(F / K) := (σ * τ) * (τ * σ)⁻¹
    have hresA : rA c = 1 := by
      simp only [c, map_mul, map_inv, hcommA, mul_inv_cancel]
    have hresB : rB c = 1 := by
      simp only [c, map_mul, map_inv, hcommB, mul_inv_cancel]
    have hfixA : c ∈ A.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hxres := congrArg (fun ρ : Gal(A / K) => ρ ⟨x, hx⟩) hresA
      have hxres' := congrArg (fun z : A => (z : F)) hxres
      calc
        c x = (rA c ⟨x, hx⟩ : F) :=
          (AlgEquiv.restrictNormalHom_apply A c ⟨x, hx⟩).symm
        _ = ((1 : Gal(A / K)) ⟨x, hx⟩ : F) := hxres'
        _ = x := rfl
    have hfixB : c ∈ B.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hxres := congrArg (fun ρ : Gal(B / K) => ρ ⟨x, hx⟩) hresB
      have hxres' := congrArg (fun z : B => (z : F)) hxres
      calc
        c x = (rB c ⟨x, hx⟩ : F) :=
          (AlgEquiv.restrictNormalHom_apply B c ⟨x, hx⟩).symm
        _ = ((1 : Gal(B / K)) ⟨x, hx⟩ : F) := hxres'
        _ = x := rfl
    have hfix : c ∈ (A ⊔ B).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hfixA, hfixB⟩
    rw [hsup, IntermediateField.fixingSubgroup_top] at hfix
    have hc : (σ * τ) * (τ * σ)⁻¹ = 1 := by
      simpa [c] using Subgroup.mem_bot.mp hfix
    calc
      σ * τ = (σ * τ) * 1 := by simp
      _ = (σ * τ) * ((τ * σ)⁻¹ * (τ * σ)) := by simp
      _ = ((σ * τ) * (τ * σ)⁻¹) * (τ * σ) := by simp only [mul_assoc]
      _ = 1 * (τ * σ) := by rw [hc]
      _ = τ * σ := by simp
  exact { toIsGalois := hFgal, is_comm := ⟨hcomm⟩ }

private theorem chapter12_intersection_is_abelian
    {K : Type*} [Field K]
    (E₁ E₂ : Chapter12FiniteAbelianSubextension K) :
    IsAbelianGalois K
      (E₁.field ⊓ E₂.field : IntermediateField K (AlgebraicClosure K)) := by
  let _ : FiniteDimensional K E₁.field := E₁.finite
  let _ : FiniteDimensional K E₂.field := E₂.finite
  let _ : IsGalois K E₁.field := E₁.galois
  let _ : IsGalois K E₂.field := E₂.galois
  let _ : IsAbelianGalois K E₁.field :=
    { toIsGalois := E₁.galois, is_comm := ⟨E₁.abelian⟩ }
  let _ : IsAbelianGalois K E₂.field :=
    { toIsGalois := E₂.galois, is_comm := ⟨E₂.abelian⟩ }
  let I : IntermediateField K (AlgebraicClosure K) := E₁.field ⊓ E₂.field
  let _ : Normal K E₁.field := E₁.galois.to_normal
  let _ : Normal K E₂.field := E₂.galois.to_normal
  let _ : FiniteDimensional K I := by infer_instance
  have hsepI : Algebra.IsSeparable K I :=
    Algebra.IsSeparable.of_algHom K E₁.field
      (IntermediateField.inclusion inf_le_left)
  let _ : Normal K I := by infer_instance
  have hIgal : IsGalois K I :=
    { to_isSeparable := hsepI, to_normal := inferInstance }
  let _ : IsGalois K I := hIgal
  exact IsAbelianGalois.of_algHom (IntermediateField.inclusion inf_le_left)

/-- The compositum/intersection rule for norm groups. -/
theorem chapter12_norm_group_of_compositum
    {K : Type*} [Field K]
    (P : Chapter12LocalFieldProfile K)
    (E₁ E₂ : Chapter12FiniteAbelianSubextension K) :
    ∃ E₁₂ : Chapter12FiniteAbelianSubextension K,
        E₁₂.field = E₁.field ⊔ E₂.field ∧
        E₁₂.normSubgroup = E₁.normSubgroup ⊓ E₂.normSubgroup := by
  let _P := P
  let _ : FiniteDimensional K E₁.field := E₁.finite
  let _ : FiniteDimensional K E₂.field := E₂.finite
  let F : IntermediateField K (AlgebraicClosure K) := E₁.field ⊔ E₂.field
  let hFabelian : IsAbelianGalois K F := chapter12_compositum_is_abelian E₁ E₂
  let _ : IsAbelianGalois K F := hFabelian
  let _ : FiniteDimensional K F := by infer_instance
  let A : IntermediateField K F := E₁.field.restrict le_sup_left
  let B : IntermediateField K F := E₂.field.restrict le_sup_right
  let eA : E₁.field ≃ₐ[K] A := E₁.field.restrictAlgEquiv le_sup_left
  let eB : E₂.field ≃ₐ[K] B := E₂.field.restrictAlgEquiv le_sup_right
  let _ : FiniteDimensional K A := by infer_instance
  let _ : FiniteDimensional K B := by infer_instance
  have hsup : A ⊔ B = (⊤ : IntermediateField K F) := by
    apply IntermediateField.lift_injective F
    rw [IntermediateField.lift_sup, IntermediateField.lift_top,
      IntermediateField.lift_restrict, IntermediateField.lift_restrict]
  let E₁₂ : Chapter12FiniteAbelianSubextension K :=
    { field := F
      finite := by infer_instance
      galois := hFabelian.toIsGalois
      galois_group_finite := by infer_instance
      abelian := hFabelian.is_comm.comm }
  have hcomp := LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10_compositum_norm_subgroup_eq_intersection
    (K := K) (Ω := F) A B
  have hcomp' :
      LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K
          (⊤ : IntermediateField K F) =
        LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K A ⊓
          LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K B := by
    exact hsup ▸ hcomp
  have hE₁ := chapter12_normSubgroup_eq_chapter10 E₁
  have hE₂ := chapter12_normSubgroup_eq_chapter10 E₂
  have hE₁₂ := chapter12_normSubgroup_eq_chapter10 E₁₂
  have hA := chapter12_chapter10_norm_subgroup_algEquiv eA
  have hB := chapter12_chapter10_norm_subgroup_algEquiv eB
  have htop := chapter12_chapter10_norm_subgroup_algEquiv
    (IntermediateField.topEquiv :
      (⊤ : IntermediateField K F) ≃ₐ[K] F)
  refine ⟨E₁₂, rfl, ?_⟩
  calc
    E₁₂.normSubgroup =
        LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K F := hE₁₂
    _ = LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K
        (⊤ : IntermediateField K F) := htop.symm
    _ = LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K A ⊓
        LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K B := hcomp'
    _ = LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K E₁.field ⊓
        LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K E₂.field := by
      rw [hA, hB]
    _ = E₁.normSubgroup ⊓ E₂.normSubgroup := by
      rw [← hE₁, ← hE₂]

/-- Inclusion of finite abelian fields reverses inclusion of norm groups. -/
theorem chapter12_field_inclusion_iff_norm_inclusion
    {K : Type*} [Field K]
    (P : Chapter12LocalFieldProfile K)
    (E₁ E₂ : Chapter12FiniteAbelianSubextension K) :
    E₁.field ≤ E₂.field ↔ E₂.normSubgroup ≤ E₁.normSubgroup := by
  constructor
  · intro hfield
    let _ : FiniteDimensional K E₁.field := E₁.finite
    let _ : FiniteDimensional K E₂.field := E₂.finite
    let _ : Algebra E₁.field E₂.field :=
      RingHom.toAlgebra (IntermediateField.inclusion hfield).toRingHom
    let _ : IsScalarTower K E₁.field E₂.field :=
      IsScalarTower.of_algebraMap_eq (congrFun rfl)
    let _ : FiniteDimensional E₁.field E₂.field :=
      Module.Finite.of_restrictScalars_finite K E₁.field E₂.field
    exact
      LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05_norm_subgroup_mono_of_tower
        K E₁.field E₂.field
  · intro hnorm
    obtain ⟨E₁₂, hfield, hnorm₁₂⟩ := chapter12_norm_group_of_compositum P E₁ E₂
    have hnorm_eq : E₁₂.normSubgroup = E₂.normSubgroup := by
      calc
        E₁₂.normSubgroup = E₁.normSubgroup ⊓ E₂.normSubgroup := hnorm₁₂
        _ = E₂.normSubgroup := inf_eq_right.mpr hnorm
    let _ : FiniteDimensional K E₁₂.field := E₁₂.finite
    let _ : FiniteDimensional K E₂.field := E₂.finite
    have hdeg : E₁₂.degree = E₂.degree := by
      calc
        E₁₂.degree = Nat.card (Kˣ ⧸ E₁₂.normSubgroup) :=
          (chapter12_subextension_norm_index_eq_degree P E₁₂).symm
        _ = Nat.card (Kˣ ⧸ E₂.normSubgroup) := by
          exact congrArg (fun H : Subgroup Kˣ => Nat.card (Kˣ ⧸ H)) hnorm_eq
        _ = E₂.degree := chapter12_subextension_norm_index_eq_degree P E₂
    change Module.finrank K E₁₂.field = Module.finrank K E₂.field at hdeg
    have hle₂ : E₂.field ≤ E₁₂.field := by
      rw [hfield]
      exact le_sup_right
    have heq : E₂.field = E₁₂.field :=
      IntermediateField.eq_of_le_of_finrank_eq hle₂ hdeg.symm
    have hle₁ : E₁.field ≤ E₁₂.field := by
      rw [hfield]
      exact le_sup_left
    exact hle₁.trans (heq.symm ▸ le_rfl)

/-- The intersection/product rule for norm groups. -/
theorem chapter12_norm_group_of_intersection
    {K : Type*} [Field K]
    (P : Chapter12LocalFieldProfile K)
    (E₁ E₂ : Chapter12FiniteAbelianSubextension K) :
    ∃ E₁₂ : Chapter12FiniteAbelianSubextension K,
        E₁₂.field = E₁.field ⊓ E₂.field ∧
        E₁₂.normSubgroup =
          chapter12NormSubgroupProduct E₁.normSubgroup E₂.normSubgroup := by
  let _P := P
  let _ : FiniteDimensional K E₁.field := E₁.finite
  let _ : FiniteDimensional K E₂.field := E₂.finite
  let F : IntermediateField K (AlgebraicClosure K) := E₁.field ⊔ E₂.field
  let _ : IsAbelianGalois K F := chapter12_compositum_is_abelian E₁ E₂
  let _ : FiniteDimensional K F := by infer_instance
  let A : IntermediateField K F := E₁.field.restrict le_sup_left
  let B : IntermediateField K F := E₂.field.restrict le_sup_right
  let I' : IntermediateField K F := A ⊓ B
  let I : IntermediateField K (AlgebraicClosure K) := E₁.field ⊓ E₂.field
  let eA : E₁.field ≃ₐ[K] A := E₁.field.restrictAlgEquiv le_sup_left
  let eB : E₂.field ≃ₐ[K] B := E₂.field.restrictAlgEquiv le_sup_right
  let _ : FiniteDimensional K A := by infer_instance
  let _ : FiniteDimensional K B := by infer_instance
  let _ : FiniteDimensional K I' := by infer_instance
  have hlift : IntermediateField.lift I' = I := by
    dsimp [I', I]
    rw [IntermediateField.lift_inf, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict]
  let eI : I' ≃ₐ[K] I := by
    rw [← hlift]
    exact IntermediateField.liftAlgEquiv I'
  let hIabelian : IsAbelianGalois K I := chapter12_intersection_is_abelian E₁ E₂
  let E₁₂ : Chapter12FiniteAbelianSubextension K :=
    { field := I
      finite := by infer_instance
      galois := hIabelian.toIsGalois
      galois_group_finite := by infer_instance
      abelian := hIabelian.is_comm.comm }
  have hcomp := LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10_intersection_norm_subgroup_eq_product
    (K := K) (Ω := F) A B
  have hE₁ := chapter12_normSubgroup_eq_chapter10 E₁
  have hE₂ := chapter12_normSubgroup_eq_chapter10 E₂
  have hE₁₂ := chapter12_normSubgroup_eq_chapter10 E₁₂
  have hA := chapter12_chapter10_norm_subgroup_algEquiv eA
  have hB := chapter12_chapter10_norm_subgroup_algEquiv eB
  have hI := chapter12_chapter10_norm_subgroup_algEquiv eI
  refine ⟨E₁₂, rfl, ?_⟩
  calc
    E₁₂.normSubgroup =
        LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K I := hE₁₂
    _ = LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K I' := hI.symm
    _ = LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K A ⊔
        LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K B := hcomp
    _ = LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K E₁.field ⊔
        LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K E₂.field := by
      rw [hA, hB]
    _ = chapter12NormSubgroupProduct E₁.normSubgroup E₂.normSubgroup := by
      rw [← hE₁, ← hE₂]
      rfl

/-- A finite abelian extension is cyclic exactly when its norm quotient is. -/
theorem chapter12_cyclic_extension_iff_cyclic_norm_quotient
    {K : Type*} [Field K]
    (P : Chapter12LocalFieldProfile K)
    (E : Chapter12FiniteAbelianSubextension K) :
    (∃ g : Gal(E.field / K),
      ∀ σ : Gal(E.field / K), ∃ n : ℤ, g ^ n = σ) ↔
      chapter12CyclicQuotient E.normSubgroup := by
  let _ : FiniteDimensional K E.field := E.finite
  let _ : IsGalois K E.field := E.galois
  let _ : Fintype (Gal(E.field / K)) := E.galois_group_finite
  obtain ⟨e⟩ := chapter12_subextension_artin_quotient_equiv P E
  have hcyc_gal :
      (∃ g : Gal(E.field / K),
        ∀ σ : Gal(E.field / K), ∃ n : ℤ, g ^ n = σ) ↔
        IsCyclic (Gal(E.field / K)) := by
    constructor
    · rintro ⟨g, hg⟩
      apply
        (LastLib.Book05LocalClassFieldTheory.Chapter03.chapter03_cyclic_generator_exists_iff
          K E.field).mp
      refine ⟨g, ?_⟩
      intro σ
      exact Subgroup.mem_zpowers_iff.mpr (hg σ)
    · intro hcyc
      obtain ⟨g, hg⟩ := hcyc.exists_zpow_surjective
      exact ⟨g, hg⟩
  exact hcyc_gal.trans (MulEquiv.isCyclic e).symm

/-- The book-facing unramified norm profile is exactly
`π^(mℤ) · Oˣ`, represented by the subgroup generated by `π^m` and units. -/
def chapter12UnramifiedNormProfile
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (H : Subgroup Kˣ) (m : ℕ) : Prop :=
  H = chapter12UnramifiedNormSubgroup C m ∧
    Finite (Kˣ ⧸ H) ∧ Nat.card (Kˣ ⧸ H) = m

theorem chapter12_unramified_norm_profile_iff
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (H : Subgroup Kˣ) (m : ℕ)
    (_hm : 0 < m) :
    chapter12UnramifiedNormProfile C H m ↔
      H = chapter12UnramifiedNormSubgroup C m ∧
        Finite (Kˣ ⧸ H) ∧ Nat.card (Kˣ ⧸ H) = m := by
  rfl

/-- A total norm subgroup has unrestricted valuation coordinate. -/
theorem chapter12_totally_ramified_norm_has_all_valuation_coordinates
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (H : Subgroup Kˣ)
    (hH : chapter12TotallyRamifiedNormSubgroup C H) :
    ∀ z : ℤ, ∃ x : H, C.valuation x.1 = z := by
  intro z
  exact hH z

/-- In the total-ramified case the valuation-one norm is only determined up to
a unit; the chosen uniformizer itself is not part of the statement. -/
theorem chapter12_totally_ramified_norm_has_unit_times_uniformizer
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (H : Subgroup Kˣ)
    (hH : chapter12TotallyRamifiedNormSubgroup C H) :
    chapter12ValuationOneNormForm C H := by
  rcases hH 1 with ⟨x, hx⟩
  refine ⟨x, hx, x.1 * C.uniformizer⁻¹, ?_, ?_⟩
  · rw [C.valuation_mul, C.valuation_inv, C.uniformizer_value]
    rw [show C.valuation x.1 = 1 from hx]
    norm_num
  · simp [mul_assoc]

end

end LastLib.Book05LocalClassFieldTheory.Chapter12
