import LastLib.Book05LocalClassFieldTheory.Chapter07.Section05ProfiniteCompletion
import LastLib.Book05LocalClassFieldTheory.Chapter06.Section07TheExistenceTheorem

namespace LastLib.Book05LocalClassFieldTheory.Chapter07

noncomputable section

open CategoryTheory Opposite

/-- The maximal abelian subextension supplied by Chapter 5. -/
abbrev chapter07MaximalAbelianSubextension
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] :
    IntermediateField K E :=
  LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05MaximalAbelianSubextension K E

/-- The commutator fixed field is Galois over the base. -/
theorem chapter07_maximal_abelian_subextension_is_galois
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] :
    IsGalois K
      (chapter07MaximalAbelianSubextension (K := K) (E := E)) := by
  exact inferInstance

/- LOCAL_DEPENDENCY_GUESS: the quotient of Gal(E/K) by its commutator is
abelian, and the fixed-field quotient API supplies the corresponding
abelian-Galois instance. -/
theorem chapter07_maximal_abelian_subextension_is_abelian
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] :
    IsAbelianGalois K
      (chapter07MaximalAbelianSubextension (K := K) (E := E)) := by
  exact inferInstance

/-- Every abelian intermediate field of E/K lies in the commutator fixed
field. -/
theorem chapter07_maximal_abelian_subextension_is_maximal
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    (L : IntermediateField K E) [IsAbelianGalois K L] :
    L ≤ chapter07MaximalAbelianSubextension (K := K) (E := E) := by
  change L ≤ IntermediateField.fixedField (commutator (Gal(E / K)))
  rw [IntermediateField.le_iff_le]
  let f : Gal(E / K) →* Gal(L / K) :=
    { toFun := AlgEquiv.restrictNormalHom L
      map_one' := map_one _
      map_mul' := map_mul _ }
  have hcomm : commutator (Gal(E / K)) ≤ f.ker := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro x ⟨p, q, rfl⟩
    change f (p * q * p⁻¹ * q⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [IsMulCommutative.is_comm.comm (f p) (f q)]
    simp
  have hfker : f.ker = L.fixingSubgroup := by
    change (AlgEquiv.restrictNormalHom L).ker = L.fixingSubgroup
    exact IntermediateField.restrictNormalHom_ker L
  rw [← hfker]
  exact hcomm

/-- The fixing subgroup of the maximal abelian subextension is the
commutator subgroup. -/
theorem chapter07_maximal_abelian_subextension_fixing_subgroup
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] :
    (chapter07MaximalAbelianSubextension (K := K) (E := E)).fixingSubgroup =
      commutator (Gal(E / K)) := by
  change (IntermediateField.fixedField (commutator (Gal(E / K)))).fixingSubgroup =
    commutator (Gal(E / K))
  exact IntermediateField.fixingSubgroup_fixedField _

/-! The explicit construction in Chapter 6 is the existence input used by
Chapter 7.  Keep its finite-precision realization visible here rather than
silently replacing it by the abstract existence property below. -/
theorem chapter07_chapter06_precision_subgroup_is_realized
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (D : LastLib.Book05LocalClassFieldTheory.Chapter06.Chapter06LocalFieldData K)
    (hmax :
      LastLib.Book05LocalClassFieldTheory.Chapter06.Chapter06IsMaximalAbelianExtension
        K KAb)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ L :
        LastLib.Book05LocalClassFieldTheory.Chapter06.Chapter06FiniteAbelianSubextension
          K KAb,
      L.normSubgroup =
        LastLib.Book05LocalClassFieldTheory.Chapter06.chapter06PrecisionSubgroup D m n := by
  exact
    LastLib.Book05LocalClassFieldTheory.Chapter06.chapter06_precision_subgroup_is_realized
      D hmax m n hm hn

/-- The unique finite abelian level attached by the local existence theorem
to an open finite-index subgroup. -/
/- LOCAL_DEPENDENCY_GUESS: the direct construction and uniqueness proof are
the local-existence theorem supplied by the preceding chapters. -/
theorem chapter07_local_existence_theorem
    {K : Type*} [Field K]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (vK : AddValuation K (WithTop ℤ))
    (hKlocal :
      LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01LocalField vK)
    (hbasis :
      LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01FieldUnitFiltrationNeighborhoodBasis
        vK)
    (D :
      LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01MaximalAbelianExtensionData K)
    [IsAbelianGalois K D.extension]
    (H : Chapter07OpenFiniteIndexSubgroup Kˣ) :
    ∃! L : Chapter07FiniteAbelianIndex K D.extension,
      chapter07NormSubgroup (K := K) (L := L) = H.1 := by
  exact
    LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01_local_existence_theorem
      vK hKlocal hbasis D H

/-- The pointwise local-existence theorem is the chapter's existence
property used by the completion and correspondence APIs. -/
theorem chapter07_local_existence_gives_existence_property
    {K : Type*} [Field K]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (vK : AddValuation K (WithTop ℤ))
    (hKlocal :
      LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01LocalField vK)
    (hbasis :
      LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01FieldUnitFiltrationNeighborhoodBasis
        vK)
    (D :
      LastLib.Book05LocalClassFieldTheory.Chapter01.Chapter01MaximalAbelianExtensionData K)
    [IsAbelianGalois K D.extension] :
    chapter07ExistenceProperty K D.extension := by
  intro H
  exact chapter07_local_existence_theorem vK hKlocal hbasis D H

/-- The unique finite abelian level attached by the local existence theorem
to an open finite-index subgroup. -/
noncomputable def chapter07ExtensionOfOpenSubgroup
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (hExist : chapter07ExistenceProperty K KAb)
    (H : Chapter07OpenFiniteIndexSubgroup Kˣ) :
    Chapter07FiniteAbelianIndex K KAb :=
  (hExist H).choose

/-- The norm group of the extension chosen from H is H. -/
theorem chapter07_norm_of_extension_of_open_subgroup
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (hExist : chapter07ExistenceProperty K KAb)
    (H : Chapter07OpenFiniteIndexSubgroup Kˣ) :
    chapter07NormSubgroup (K := K)
        (L := chapter07ExtensionOfOpenSubgroup hExist H) = H.1 :=
  ((hExist H).choose_spec).1

/-- Uniqueness in the local existence theorem. -/
theorem chapter07_extension_of_open_subgroup_unique
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (hExist : chapter07ExistenceProperty K KAb)
    (H : Chapter07OpenFiniteIndexSubgroup Kˣ)
    (L : Chapter07FiniteAbelianIndex K KAb)
    (hL : chapter07NormSubgroup (K := K) (L := L) = H.1) :
    L = chapter07ExtensionOfOpenSubgroup hExist H :=
  (hExist H).unique hL ((hExist H).choose_spec).1

/-- The degree/index formula in the local existence theorem. -/
theorem chapter07_local_existence_degree
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (S : Chapter07FiniteArtinSystem K KAb)
    (hExist : chapter07ExistenceProperty K KAb)
    (H : Chapter07OpenFiniteIndexSubgroup Kˣ) :
    Module.finrank K (chapter07ExtensionOfOpenSubgroup hExist H) =
      H.1.index := by
  change Module.finrank K (chapter07ExtensionOfOpenSubgroup hExist H) =
    Nat.card (Kˣ ⧸ H.1)
  rw [← chapter07_norm_of_extension_of_open_subgroup hExist H]
  rw [Nat.card_congr (chapter07FiniteReciprocityEquiv S
    (chapter07ExtensionOfOpenSubgroup hExist H)).toEquiv]
  exact (IsGalois.card_aut_eq_finrank K
    (chapter07ExtensionOfOpenSubgroup hExist H)).symm

/-- Finite reciprocity at the level selected by an open subgroup. -/
noncomputable def chapter07LocalExistenceFiniteReciprocityEquiv
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (S : Chapter07FiniteArtinSystem K KAb)
    (hExist : chapter07ExistenceProperty K KAb)
    (H : Chapter07OpenFiniteIndexSubgroup Kˣ) :
    Kˣ ⧸ H.1 ≃* Gal(chapter07ExtensionOfOpenSubgroup hExist H / K) := by
  rw [← chapter07_norm_of_extension_of_open_subgroup hExist H]
  exact chapter07FiniteReciprocityEquiv S
    (chapter07ExtensionOfOpenSubgroup hExist H)

/-- Finite reciprocity at the level selected by an open subgroup. -/
theorem chapter07_local_existence_finite_reciprocity
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (S : Chapter07FiniteArtinSystem K KAb)
    (hExist : chapter07ExistenceProperty K KAb)
    (H : Chapter07OpenFiniteIndexSubgroup Kˣ) :
    Nonempty
      (Kˣ ⧸ H.1 ≃*
        Gal(chapter07ExtensionOfOpenSubgroup hExist H / K)) :=
  ⟨chapter07LocalExistenceFiniteReciprocityEquiv S hExist H⟩

/-- Under the existence theorem, the norm-subgroup assignment lands in the
open finite-index subgroup API. -/
noncomputable def chapter07NormSubgroupAsOpenFiniteIndex
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (S : Chapter07FiniteArtinSystem K KAb)
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ))
    (L : Chapter07FiniteAbelianIndex K KAb) :
    Chapter07OpenFiniteIndexSubgroup Kˣ where
  val := chapter07NormSubgroup (K := K) (L := L)
  property := by
    constructor
    · exact hopen L
    · have hker : (S.artin L).ker =
          chapter07NormSubgroup (K := K) (L := L) := by
        simpa only [chapter07NormSubgroup] using S.kernel_eq_norm L
      exact hker ▸ (inferInstance : (S.artin L).ker.FiniteIndex)

/-- Inclusion of finite abelian levels reverses inclusion of norm groups. -/
theorem chapter07_norm_subgroup_antitone
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb]
    (L₁ L₂ : Chapter07FiniteAbelianIndex K KAb)
    (hL : L₁ ≤ L₂) :
    chapter07NormSubgroup (K := K) (L := L₂) ≤
      chapter07NormSubgroup (K := K) (L := L₁) := by
  let _ : Algebra L₁ L₂ := RingHom.toAlgebra
    (Subsemiring.inclusion ((FiniteGaloisIntermediateField.le_iff L₁ L₂).mp hL))
  let _ : IsScalarTower K L₁ L₂ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  let _ : FiniteDimensional L₁ L₂ :=
    Module.Finite.of_restrictScalars_finite K L₁ L₂
  have hnorm₁ : chapter07NormSubgroup (K := K) (L := L₁) =
      LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormSubgroup K L₁ := by
    ext x
    rw [chapter07_mem_norm_subgroup_iff,
      LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05_mem_normSubgroup_iff]
    rfl
  have hnorm₂ : chapter07NormSubgroup (K := K) (L := L₂) =
      LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormSubgroup K L₂ := by
    ext x
    rw [chapter07_mem_norm_subgroup_iff,
      LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05_mem_normSubgroup_iff]
    rfl
  rw [hnorm₂, hnorm₁]
  exact LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05_norm_subgroup_mono_of_tower
    K L₁ L₂

/-- Equality of norm groups determines the finite abelian level. -/
theorem chapter07_norm_subgroup_injective
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (hExist : chapter07ExistenceProperty K KAb)
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ))
    {L₁ L₂ : Chapter07FiniteAbelianIndex K KAb}
    (hL : chapter07NormSubgroup (K := K) (L := L₁) =
      chapter07NormSubgroup (K := K) (L := L₂)) :
    L₁ = L₂ := by
  sorry

private theorem chapter07_norm_subgroup_le_of_norm_le
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (S : Chapter07FiniteArtinSystem K KAb)
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ))
    (hExist : chapter07ExistenceProperty K KAb)
    {L₁ L₂ : Chapter07FiniteAbelianIndex K KAb}
    (hN : chapter07NormSubgroup (K := K) (L := L₂) ≤
      chapter07NormSubgroup (K := K) (L := L₁)) :
    L₁ ≤ L₂ := by
  let M : Chapter07FiniteAbelianIndex K KAb := L₁ ⊔ L₂
  have hL₁M : L₁.toIntermediateField ≤ M.toIntermediateField := le_sup_left
  have hL₂M : L₂.toIntermediateField ≤ M.toIntermediateField := le_sup_right
  let L₁' : IntermediateField K M := IntermediateField.restrict hL₁M
  let L₂' : IntermediateField K M := IntermediateField.restrict hL₂M
  have hsup : L₁' ⊔ L₂' = (⊤ : IntermediateField K M) := by
    apply IntermediateField.lift_injective M.toIntermediateField
    rw [IntermediateField.lift_sup, IntermediateField.lift_top,
      IntermediateField.lift_restrict, IntermediateField.lift_restrict]
    rfl
  let f₁ : Opposite.op M ⟶ Opposite.op L₁ :=
    CategoryTheory.opHomOfLE (x := Opposite.op L₁) (y := Opposite.op M)
      ((FiniteGaloisIntermediateField.le_iff L₁ M).2 hL₁M)
  let f₂ : Opposite.op M ⟶ Opposite.op L₂ :=
    CategoryTheory.opHomOfLE (x := Opposite.op L₂) (y := Opposite.op M)
      ((FiniteGaloisIntermediateField.le_iff L₂ M).2 hL₂M)
  let _ : Algebra L₁ M := RingHom.toAlgebra (Subsemiring.inclusion hL₁M)
  let _ : IsScalarTower K L₁ M :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  let _ : Algebra L₂ M := RingHom.toAlgebra (Subsemiring.inclusion hL₂M)
  let _ : IsScalarTower K L₂ M :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  have hnorm_le :
      chapter07NormSubgroup (K := K) (L := L₂) ≤
        chapter07NormSubgroup (K := K) (L := M) := by
    intro x hx
    have hx₁ : x ∈ chapter07NormSubgroup (K := K) (L := L₁) := hN hx
    have hxker₁ : x ∈ (S.artin L₁).ker := by
      rw [S.kernel_eq_norm L₁]
      exact hx₁
    have hxker₂ : x ∈ (S.artin L₂).ker := by
      rw [S.kernel_eq_norm L₂]
      exact hx
    have hres₁ :
        (finGaloisGroupMap f₁).hom.hom
            (S.artin M x) = 1 := by
      rw [S.compatible f₁ x]
      exact MonoidHom.mem_ker.mp hxker₁
    have hres₂ :
        (finGaloisGroupMap f₂).hom.hom
            (S.artin M x) = 1 := by
      rw [S.compatible f₂ x]
      exact MonoidHom.mem_ker.mp hxker₂
    have hz₁ (y : M) (hy : y ∈ L₁') :
        (S.artin M x) y = y := by
      have hy₁ : y.1 ∈ L₁.toIntermediateField :=
        (IntermediateField.mem_restrict hL₁M y).mp hy
      let z : L₁ := ⟨y.1, hy₁⟩
      let r : Gal(L₁ / K) := (finGaloisGroupMap f₁).hom.hom (S.artin M x)
      have hz : r z = z := by
        have h := congrArg (fun τ : Gal(L₁ / K) => τ z) hres₁
        change r z = (1 : Gal(L₁ / K)) z at h
        exact h.trans (by rfl)
      have hcomm :
          algebraMap L₁ M (r z) =
            (S.artin M x) (algebraMap L₁ M z) := by
        change algebraMap L₁ M ((S.artin M x).restrictNormal L₁ z) =
          (S.artin M x) (algebraMap L₁ M z)
        exact AlgEquiv.restrictNormal_commutes (S.artin M x) L₁ z
      apply Subtype.ext
      have hcomm' := congrArg (fun w : M => (w : KAb)) hcomm
      have hz' := congrArg (algebraMap L₁ M) hz
      have hzM' := congrArg (fun w : M => (w : KAb)) hz'
      have hyalg : algebraMap L₁ M z = y := by
        apply Subtype.ext
        rfl
      rw [hyalg] at hcomm' hzM'
      exact hcomm'.symm.trans hzM'
    have hz₂ (y : M) (hy : y ∈ L₂') :
        (S.artin M x) y = y := by
      have hy₂ : y.1 ∈ L₂.toIntermediateField :=
        (IntermediateField.mem_restrict hL₂M y).mp hy
      let z : L₂ := ⟨y.1, hy₂⟩
      let r : Gal(L₂ / K) := (finGaloisGroupMap f₂).hom.hom (S.artin M x)
      have hz : r z = z := by
        have h := congrArg (fun τ : Gal(L₂ / K) => τ z) hres₂
        change r z = (1 : Gal(L₂ / K)) z at h
        exact h.trans (by rfl)
      have hcomm :
          algebraMap L₂ M (r z) =
            (S.artin M x) (algebraMap L₂ M z) := by
        change algebraMap L₂ M ((S.artin M x).restrictNormal L₂ z) =
          (S.artin M x) (algebraMap L₂ M z)
        exact AlgEquiv.restrictNormal_commutes (S.artin M x) L₂ z
      apply Subtype.ext
      have hcomm' := congrArg (fun w : M => (w : KAb)) hcomm
      have hz' := congrArg (algebraMap L₂ M) hz
      have hzM' := congrArg (fun w : M => (w : KAb)) hz'
      have hyalg : algebraMap L₂ M z = y := by
        apply Subtype.ext
        rfl
      rw [hyalg] at hcomm' hzM'
      exact hcomm'.symm.trans hzM'
    have hfix₁ : (S.artin M x) ∈ L₁'.fixingSubgroup := by
      exact (IntermediateField.mem_fixingSubgroup_iff L₁' (S.artin M x)).2 hz₁
    have hfix₂ : (S.artin M x) ∈ L₂'.fixingSubgroup := by
      exact (IntermediateField.mem_fixingSubgroup_iff L₂' (S.artin M x)).2 hz₂
    have hfix : (S.artin M x) ∈ (L₁' ⊔ L₂').fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hfix₁, hfix₂⟩
    rw [hsup, IntermediateField.fixingSubgroup_top] at hfix
    have htriv : S.artin M x = 1 := Subgroup.mem_bot.mp hfix
    have hxkerM : x ∈ (S.artin M).ker := MonoidHom.mem_ker.mpr htriv
    have hnormM : x ∈
        LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01NormSubgroup K M :=
      S.kernel_eq_norm M ▸ hxkerM
    simpa only [chapter07NormSubgroup] using hnormM
  have hnorm_ge :
      chapter07NormSubgroup (K := K) (L := M) ≤
        chapter07NormSubgroup (K := K) (L := L₂) := by
    exact chapter07_norm_subgroup_antitone L₂ M
      ((FiniteGaloisIntermediateField.le_iff L₂ M).2 hL₂M)
  have hnorm_eq :
      chapter07NormSubgroup (K := K) (L := M) =
        chapter07NormSubgroup (K := K) (L := L₂) := by
    exact le_antisymm hnorm_ge hnorm_le
  let H₂ : Chapter07OpenFiniteIndexSubgroup Kˣ :=
    chapter07NormSubgroupAsOpenFiniteIndex S hopen L₂
  have hM : M = L₂ := by
    apply (hExist H₂).unique
    · exact hnorm_eq.trans rfl
    · rfl
  exact hM ▸ le_sup_left

private theorem chapter07_norm_subgroup_order_iso_exists
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (S : Chapter07FiniteArtinSystem K KAb)
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ))
    (hExist : chapter07ExistenceProperty K KAb) :
    ∃ e : Chapter07FiniteAbelianIndex K KAb ≃o
        OrderDual (Chapter07OpenFiniteIndexSubgroup Kˣ),
      ∀ L, e L = chapter07NormSubgroupAsOpenFiniteIndex S hopen L := by
  let f : Chapter07FiniteAbelianIndex K KAb →
      OrderDual (Chapter07OpenFiniteIndexSubgroup Kˣ) :=
    fun L => chapter07NormSubgroupAsOpenFiniteIndex S hopen L
  have hf : Monotone f := by
    intro L₁ L₂ hL
    exact chapter07_norm_subgroup_antitone L₁ L₂ hL
  have hf_injective : Function.Injective f := by
    intro L₁ L₂ hL
    let H : Chapter07OpenFiniteIndexSubgroup Kˣ :=
      chapter07NormSubgroupAsOpenFiniteIndex S hopen L₁
    have hnorm :
        chapter07NormSubgroup (K := K) (L := L₁) =
          chapter07NormSubgroup (K := K) (L := L₂) := by
      exact congrArg (fun H : Chapter07OpenFiniteIndexSubgroup Kˣ => H.1) hL
    apply (hExist H).unique
    · rfl
    · change chapter07NormSubgroup (K := K) (L := L₂) =
        chapter07NormSubgroup (K := K) (L := L₁)
      exact hnorm.symm
  have hf_surjective : Function.Surjective f := by
    intro H
    obtain ⟨L, hL, _⟩ := hExist H
    refine ⟨L, ?_⟩
    apply Subtype.ext
    exact hL
  let e : Chapter07FiniteAbelianIndex K KAb ≃
      OrderDual (Chapter07OpenFiniteIndexSubgroup Kˣ) :=
    Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩
  have he_inv : Monotone e.symm := by
    intro H₁ H₂ hH
    have hH' : H₂.1 ≤ H₁.1 := hH
    have hnorm₁ :
        chapter07NormSubgroup (K := K) (L := e.symm H₁) = H₁.1 := by
      exact congrArg (fun H : OrderDual (Chapter07OpenFiniteIndexSubgroup Kˣ) => H.1)
        (e.apply_symm_apply H₁)
    have hnorm₂ :
        chapter07NormSubgroup (K := K) (L := e.symm H₂) = H₂.1 := by
      exact congrArg (fun H : OrderDual (Chapter07OpenFiniteIndexSubgroup Kˣ) => H.1)
        (e.apply_symm_apply H₂)
    apply chapter07_norm_subgroup_le_of_norm_le S hopen hExist
    rw [hnorm₂, hnorm₁]
    exact hH'
  let e' : Chapter07FiniteAbelianIndex K KAb ≃o
      OrderDual (Chapter07OpenFiniteIndexSubgroup Kˣ) :=
    Equiv.toOrderIso e hf he_inv
  refine ⟨e', ?_⟩
  intro L
  rfl

/- LOCAL_DEPENDENCY_GUESS: the finite reciprocity, local existence, and norm
limitation interfaces together assemble into the inclusion-reversing
correspondence stated by the chapter. -/
theorem chapter07_norm_subgroup_inclusion_reversing_bijection
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (S : Chapter07FiniteArtinSystem K KAb)
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ))
    (hExist : chapter07ExistenceProperty K KAb) :
    Nonempty
      (Chapter07FiniteAbelianIndex K KAb ≃o
        OrderDual (Chapter07OpenFiniteIndexSubgroup Kˣ)) := by
  obtain ⟨e, _⟩ :=
    chapter07_norm_subgroup_order_iso_exists S hopen hExist
  exact ⟨e⟩

/-- The order equivalence sends a finite level to its norm subgroup. -/
theorem chapter07_norm_subgroup_correspondence_is_norm
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (S : Chapter07FiniteArtinSystem K KAb)
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ))
    (hExist : chapter07ExistenceProperty K KAb) :
    ∃ e : Chapter07FiniteAbelianIndex K KAb ≃o
        OrderDual (Chapter07OpenFiniteIndexSubgroup Kˣ),
      ∀ L, e L = chapter07NormSubgroupAsOpenFiniteIndex S hopen L := by
  exact chapter07_norm_subgroup_order_iso_exists S hopen hExist

/- LOCAL_DEPENDENCY_GUESS: this is the norm-limitation theorem proved at
finite level and reused by the final Chapter 7 synthesis. -/
/-- Norm limitation for a finite Galois extension. -/
theorem chapter07_norm_limitation
    {K E : Type} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    [Fintype (Gal(E / K))]
    [Fintype (Gal(chapter07MaximalAbelianSubextension (K := K) (E := E) / K))]
    (D :
      LastLib.Book05LocalClassFieldTheory.Chapter05.Chapter05LocalClassFormationData K E)
    (DM :
      LastLib.Book05LocalClassFieldTheory.Chapter05.Chapter05LocalClassFormationData K
      (chapter07MaximalAbelianSubextension (K := K) (E := E))) :
    chapter07NormSubgroup (K := K) (L := E) =
      chapter07NormSubgroup (K := K)
        (L := chapter07MaximalAbelianSubextension (K := K) (E := E)) := by
  sorry

/-- The norm-limitation assertion for all finite Galois extensions of a base
field.  Naming this proposition keeps the final three-theorem package at one
universe-polymorphic interface. -/
def chapter07NormLimitationProperty (K : Type*) [Field K] : Prop :=
  ∀ (E : Type) [Field E] [Algebra K E] [FiniteDimensional K E]
    [IsGalois K E],
    chapter07NormSubgroup (K := K) (L := E) =
      chapter07NormSubgroup (K := K)
        (L := chapter07MaximalAbelianSubextension (K := K) (E := E))

/- LOCAL_DEPENDENCY_GUESS: this packages the three named theorems as a
single source-facing declaration; the finite Artin system and the selected
maximal abelian model are supplied by earlier chapters. -/
theorem chapter07_reciprocity_existence_and_norm_theorems
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ] [IsAbelianGalois K KAb]
    (S : Chapter07FiniteArtinSystem K KAb)
    (hExist : chapter07ExistenceProperty K KAb)
    (hNorm : chapter07NormLimitationProperty K) :
    (∀ L : Chapter07FiniteAbelianIndex K KAb,
      Nonempty
        (Kˣ ⧸ chapter07NormSubgroup (K := K) (L := L) ≃*
      Gal(L / K))) ∧
      chapter07ExistenceProperty K KAb ∧ chapter07NormLimitationProperty K := by
  exact ⟨fun L => ⟨chapter07FiniteReciprocityEquiv S L⟩, hExist, hNorm⟩

end

end LastLib.Book05LocalClassFieldTheory.Chapter07
