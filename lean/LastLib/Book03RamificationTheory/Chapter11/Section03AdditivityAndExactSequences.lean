import LastLib.Book03RamificationTheory.Chapter11.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter11

noncomputable section

open CategoryTheory

/-! ## 11.3. Additivity and exact sequences -/

/-- The same conductor API on Mathlib's finite-dimensional representation object. -/
abbrev chapter11ArtinConductorFD
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (V : FDRep k G) : ℚ :=
  chapter11ArtinConductor D V.ρ

abbrev chapter11TameConductorFD
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (V : FDRep k G) : ℚ :=
  chapter11TameConductor D V.ρ

abbrev chapter11SwanConductorFD
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (V : FDRep k G) : ℚ :=
  chapter11SwanConductor D V.ρ

/-- The product model of a direct sum of two representations. -/
noncomputable def chapter11DirectSumRepresentation
    {k G V W : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k G W) :
    Representation k G (V × W) :=
  Representation.prod ρ σ

/-- The categorical direct sum of two finite-dimensional representations. -/
abbrev chapter11DirectSumFDRep
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (V W : FDRep k G) : FDRep k G := V ⊞ W

/-- Twist a representation by a one-dimensional character. -/
def chapter11Twist
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (χ : G →* kˣ) (ρ : Representation k G V) : Representation k G V where
  toFun g := (χ g : k) • ρ g
  map_one' := by
    simp
  map_mul' g h := by
    ext
    simp [MonoidHom.map_mul, smul_smul, mul_comm]

/-- A character is unramified when it is trivial on inertia. -/
def chapter11UnramifiedCharacter
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (χ : G →* kˣ) : Prop :=
  ∀ σ : D.inertia, χ σ = 1

/-- A short exact sequence in the finite-dimensional representation category. -/
structure Chapter11ShortExactRepresentation
    (k G : Type*) [Field k] [CharZero k] [Fintype G] [Group G] where
  sequence : ShortComplex (FDRep k G)
  short_exact : sequence.ShortExact

/-- A splitting datum for a short exact representation sequence. -/
def Chapter11SplitShortExact
    {k G : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    (S : ShortComplex (FDRep k G)) : Prop :=
  ∃ (r : S.X₂ ⟶ S.X₁) (s : S.X₃ ⟶ S.X₂),
    S.f ≫ r = 𝟙 S.X₁ ∧
      s ≫ S.g = 𝟙 S.X₃ ∧
      r ≫ S.f + S.g ≫ s = 𝟙 S.X₂

private theorem chapter11_fixed_space_codim_direct_sum
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (V W : FDRep k G) (H : Subgroup G) :
    LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
        (V ⊞ W).ρ H =
      LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim V.ρ H +
        LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim W.ρ H := by
  let iV : V →ₗ[k] (V ⊞ W).V :=
    ((CategoryTheory.Limits.biprod.inl :
      (V : FDRep k G) ⟶ (V ⊞ W : FDRep k G)).hom.hom.hom)
  let iW : W →ₗ[k] (V ⊞ W).V :=
    ((CategoryTheory.Limits.biprod.inr :
      (W : FDRep k G) ⟶ (V ⊞ W : FDRep k G)).hom.hom.hom)
  let pV : (V ⊞ W).V →ₗ[k] V :=
    ((CategoryTheory.Limits.biprod.fst :
      (V ⊞ W : FDRep k G) ⟶ (V : FDRep k G)).hom.hom.hom)
  let pW : (V ⊞ W).V →ₗ[k] W :=
    ((CategoryTheory.Limits.biprod.snd :
      (V ⊞ W : FDRep k G) ⟶ (W : FDRep k G)).hom.hom.hom)
  let e : (V × W) ≃ₗ[k] (V ⊞ W).V :=
    { toFun := fun x => iV x.1 + iW x.2
      invFun := fun x => (pV x, pW x)
      left_inv := by
        intro x
        have hVV := congrArg (fun f => f.hom.hom.hom x.1)
          (CategoryTheory.Limits.biprod.inl_fst
            (X := (V : FDRep k G)) (Y := (W : FDRep k G)))
        have hWV := congrArg (fun f => f.hom.hom.hom x.2)
          (CategoryTheory.Limits.biprod.inr_fst
            (X := (V : FDRep k G)) (Y := (W : FDRep k G)))
        have hVW := congrArg (fun f => f.hom.hom.hom x.1)
          (CategoryTheory.Limits.biprod.inl_snd
            (X := (V : FDRep k G)) (Y := (W : FDRep k G)))
        have hWW := congrArg (fun f => f.hom.hom.hom x.2)
          (CategoryTheory.Limits.biprod.inr_snd
            (X := (V : FDRep k G)) (Y := (W : FDRep k G)))
        change pV (iV x.1) = x.1 at hVV
        change pV (iW x.2) = 0 at hWV
        change pW (iV x.1) = 0 at hVW
        change pW (iW x.2) = x.2 at hWW
        change (pV (iV x.1 + iW x.2), pW (iV x.1 + iW x.2)) = x
        simp only [map_add]
        rw [hVV, hWV, hVW, hWW]
        simp only [add_zero, zero_add]
      right_inv := by
        intro x
        have htotal := CategoryTheory.Limits.biprod.total
          (X := (V : FDRep k G)) (Y := (W : FDRep k G))
        have hx := congrArg (fun f => f.hom.hom.hom x) htotal
        change iV (pV x) + iW (pW x) = x at hx
        exact hx
      map_add' := by
        intro x y
        change iV (x.1 + y.1) + iW (x.2 + y.2) =
          (iV x.1 + iW x.2) + (iV y.1 + iW y.2)
        simp only [map_add]
        abel
      map_smul' := by
        intro a x
        simp [iV, iW] }
  have he_comm (g : G) :
      (V ⊞ W).ρ g ∘ₗ e.toLinearMap =
        e.toLinearMap ∘ₗ (V.ρ g).prodMap (W.ρ g) := by
    apply LinearMap.prod_ext <;> ext x
    · have hV := congrArg (fun f => f.hom.hom x)
        ((CategoryTheory.Limits.biprod.inl :
          (V : FDRep k G) ⟶ (V ⊞ W : FDRep k G)).comm g)
      simpa [e, iV] using hV.symm
    · have hW := congrArg (fun f => f.hom.hom x)
        ((CategoryTheory.Limits.biprod.inr :
          (W : FDRep k G) ⟶ (V ⊞ W : FDRep k G)).comm g)
      simpa [e, iW] using hW.symm
  let ρprod := chapter11DirectSumRepresentation V.ρ W.ρ
  have hfixed_prod :
      LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρprod H =
        (LastLib.Book03RamificationTheory.Chapter10.fixedSpace V.ρ H).prod
          (LastLib.Book03RamificationTheory.Chapter10.fixedSpace W.ρ H) := by
    ext x
    constructor
    · intro hx
      rw [LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff] at hx
      have hxV : x.1 ∈ LastLib.Book03RamificationTheory.Chapter10.fixedSpace V.ρ H := by
        rw [LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff]
        intro h
        have hx' := congrArg Prod.fst (hx h)
        simpa [ρprod, chapter11DirectSumRepresentation] using hx'
      have hxW : x.2 ∈ LastLib.Book03RamificationTheory.Chapter10.fixedSpace W.ρ H := by
        rw [LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff]
        intro h
        have hx' := congrArg Prod.snd (hx h)
        simpa [ρprod, chapter11DirectSumRepresentation] using hx'
      exact ⟨hxV, hxW⟩
    · intro hx
      have hxV :=
        (LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff V.ρ H x.1).mp hx.1
      have hxW :=
        (LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff W.ρ H x.2).mp hx.2
      rw [LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff]
      intro h
      apply Prod.ext
      · simpa [ρprod, chapter11DirectSumRepresentation] using hxV h
      · simpa [ρprod, chapter11DirectSumRepresentation] using hxW h
  have hfixed_map :
      LastLib.Book03RamificationTheory.Chapter10.fixedSpace (V ⊞ W).ρ H =
        (LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρprod H).map
          e.toLinearMap := by
    apply le_antisymm
    · intro y hy
      have hy' :=
        (LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff
          (V ⊞ W).ρ H y).mp hy
      let x := e.symm y
      have hx : x ∈ LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρprod H := by
        rw [LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff]
        intro h
        have hcomm := LinearMap.congr_fun (he_comm h) x
        apply e.injective
        rw [e.apply_symm_apply]
        simpa [x, ρprod, chapter11DirectSumRepresentation, LinearMap.comp_apply, hy' h]
          using hcomm.symm
      exact ⟨x, hx, by simp [x]⟩
    · rintro y ⟨x, hx, rfl⟩
      have hx' :=
        (LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff ρprod H x).mp hx
      rw [LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff]
      intro h
      have hx'' : (V.ρ (h : G) x.1, W.ρ (h : G) x.2) = x := by
        simpa [ρprod, chapter11DirectSumRepresentation] using hx' h
      have hcomm := LinearMap.congr_fun (he_comm h) x
      change (V ⊞ W).ρ (h : G) (e x) =
        e ((V.ρ (h : G) x.1, W.ρ (h : G) x.2)) at hcomm
      rw [hx''] at hcomm
      exact hcomm
  have he_fixed_dim :
      Module.finrank k
          (LastLib.Book03RamificationTheory.Chapter10.fixedSpace (V ⊞ W).ρ H) =
        Module.finrank k
          (LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρprod H) := by
    rw [hfixed_map, e.finrank_map_eq]
  let p := LastLib.Book03RamificationTheory.Chapter10.fixedSpace V.ρ H
  let q := LastLib.Book03RamificationTheory.Chapter10.fixedSpace W.ρ H
  let epq : (p × q) ≃ₗ[k] (p.prod q) :=
    { toFun := fun x => ⟨(x.1.1, x.2.1), ⟨x.1.2, x.2.2⟩⟩
      invFun := fun x => (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  have hprod_fixed_dim :
      Module.finrank k (LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρprod H) =
        Module.finrank k p + Module.finrank k q := by
    rw [hfixed_prod]
    calc
      Module.finrank k (p.prod q) = Module.finrank k (p × q) :=
        (LinearEquiv.finrank_eq epq).symm
      _ = Module.finrank k p + Module.finrank k q := Module.finrank_prod
  change Module.finrank k ((V ⊞ W).V ⧸
      LastLib.Book03RamificationTheory.Chapter10.fixedSpace (V ⊞ W).ρ H) =
    Module.finrank k (V.V ⧸ LastLib.Book03RamificationTheory.Chapter10.fixedSpace V.ρ H) +
      Module.finrank k (W.V ⧸ LastLib.Book03RamificationTheory.Chapter10.fixedSpace W.ρ H)
  rw [Submodule.finrank_quotient, Submodule.finrank_quotient,
    Submodule.finrank_quotient, he_fixed_dim, hprod_fixed_dim]
  rw [← e.finrank_eq, Module.finrank_prod]
  have hp : Module.finrank k p ≤ Module.finrank k V.V := Submodule.finrank_le p
  have hq : Module.finrank k q ≤ Module.finrank k W.V := Submodule.finrank_le q
  change Module.finrank k V.V + Module.finrank k W.V -
      (Module.finrank k p + Module.finrank k q) =
    (Module.finrank k V.V - Module.finrank k p) +
      (Module.finrank k W.V - Module.finrank k q)
  rw [Nat.sub_eq_iff_eq_add (Nat.add_le_add hp hq)]
  omega

private theorem chapter11_fixed_space_codim_iso
    {k G : Type*} [Field k] [Fintype G] [Group G]
    {V W : FDRep k G} (e : V ≅ W) (H : Subgroup G) :
    LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim V.ρ H =
      LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim W.ρ H := by
  let l := FDRep.isoToLinearEquiv e
  have hl (g : G) : W.ρ g ∘ₗ l.toLinearMap = l.toLinearMap ∘ₗ V.ρ g := by
    rw [FDRep.Iso.conj_ρ e g]
    ext x
    simp [l, LinearEquiv.conj_apply]
  have hfixed :
      LastLib.Book03RamificationTheory.Chapter10.fixedSpace W.ρ H =
        (LastLib.Book03RamificationTheory.Chapter10.fixedSpace V.ρ H).map
          l.toLinearMap := by
    apply le_antisymm
    · intro y hy
      have hy' :=
        (LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff W.ρ H y).mp hy
      let x := l.symm y
      have hx : x ∈ LastLib.Book03RamificationTheory.Chapter10.fixedSpace V.ρ H := by
        rw [LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff]
        intro g
        have hcomm := LinearMap.congr_fun (hl g) x
        apply l.injective
        rw [l.apply_symm_apply]
        simpa [x, LinearMap.comp_apply, hy' g] using hcomm.symm
      exact ⟨x, hx, by simp [x]⟩
    · rintro y ⟨x, hx, rfl⟩
      have hx' :=
        (LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff V.ρ H x).mp hx
      rw [LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff]
      intro g
      have hcomm := LinearMap.congr_fun (hl g) x
      have hx'' := hx' g
      change W.ρ (g : G) (l x) = l (V.ρ (g : G) x) at hcomm
      rw [hx''] at hcomm
      exact hcomm
  unfold LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
  rw [Submodule.finrank_quotient, Submodule.finrank_quotient,
    hfixed, l.finrank_map_eq, ← l.finrank_eq]

private theorem chapter11_artin_conductor_iso
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) {V W : FDRep k G} (e : V ≅ W) :
    chapter11ArtinConductor D V.ρ = chapter11ArtinConductor D W.ρ := by
  unfold chapter11ArtinConductor
  simp_rw [chapter11_fixed_space_codim_iso e]

theorem chapter11_short_exact_representation_splits
    {k G : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    (S : Chapter11ShortExactRepresentation k G) :
    Chapter11SplitShortExact S.sequence := by
  letI : NeZero (Nat.card G : k) := by
    have hcard : (Nat.card G : k) ≠ 0 := by
      rw [← Fintype.card_eq_nat_card]
      exact (Nat.cast_ne_zero (R := k)).mpr
        (Fintype.card_ne_zero : Fintype.card G ≠ 0)
    exact ⟨hcard⟩
  letI : Injective S.sequence.X₁ := by
    constructor
    intro X Y g f hf
    letI : Mono f := hf
    let F := forget₂ (FDRep k G) (Rep k G)
    let T := Rep.toModuleMonoidAlgebra (k := k) (G := G)
    let fR := F.map f
    let gR := F.map g
    let fM := T.map fR
    let gM := T.map gR
    letI : Mono fR := F.map_mono f
    have hfM : Function.Injective fM.hom := by
      apply (ModuleCat.mono_iff_injective fM).mp
      exact T.map_mono fR
    haveI : IsSemisimpleRing (MonoidAlgebra k G) := by infer_instance
    haveI : Module.Injective (MonoidAlgebra k G) (T.obj (F.obj S.sequence.X₁)) :=
      Module.injective_of_isSemisimpleRing _ _
    obtain ⟨hM, hhM⟩ := Module.Injective.out fM.hom hfM gM.hom
    obtain ⟨hR, hTR⟩ := T.map_surjective (ModuleCat.ofHom hM)
    obtain ⟨hFD, hF⟩ := F.map_surjective hR
    refine ⟨hFD, ?_⟩
    apply F.map_injective
    rw [F.map_comp, hF]
    apply T.map_injective
    rw [T.map_comp, hTR]
    apply ModuleCat.hom_ext
    ext x
    exact hhM x
  let hsplit := S.short_exact.splittingOfInjective
  exact ⟨hsplit.r, hsplit.s, hsplit.f_r, hsplit.s_g, hsplit.id⟩

theorem chapter11_artin_conductor_direct_sum
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (V W : FDRep k G) :
    chapter11ArtinConductorFD D (chapter11DirectSumFDRep V W) =
      chapter11ArtinConductorFD D V + chapter11ArtinConductorFD D W := by
  change chapter11ArtinConductor D (V ⊞ W).ρ =
    chapter11ArtinConductor D V.ρ + chapter11ArtinConductor D W.ρ
  unfold chapter11ArtinConductor
  simp_rw [chapter11_fixed_space_codim_direct_sum]
  simp only [Nat.cast_add, mul_add]
  rw [Finset.sum_add_distrib]

theorem chapter11_swan_conductor_direct_sum
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (V W : FDRep k G) :
    chapter11SwanConductorFD D (chapter11DirectSumFDRep V W) =
      chapter11SwanConductorFD D V + chapter11SwanConductorFD D W := by
  change chapter11SwanConductor D (V ⊞ W).ρ =
    chapter11SwanConductor D V.ρ + chapter11SwanConductor D W.ρ
  unfold chapter11SwanConductor
  simp_rw [chapter11_fixed_space_codim_direct_sum]
  simp only [Nat.cast_add, mul_add]
  rw [Finset.sum_add_distrib]

/-- Artin conductors are additive in a short exact sequence of finite-dimensional representations. -/
theorem chapter11_artin_conductor_short_exact_additive
    {k G : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G)
    (S : Chapter11ShortExactRepresentation k G) :
    chapter11ArtinConductorFD D S.sequence.X₂ =
      chapter11ArtinConductorFD D S.sequence.X₁ +
        chapter11ArtinConductorFD D S.sequence.X₃ := by
  rcases chapter11_short_exact_representation_splits S with
    ⟨r, s, hr, hs, hid⟩
  let hsplit : S.sequence.Splitting :=
    { r := r
      s := s
      f_r := hr
      s_g := hs
      id := hid }
  let e := hsplit.isoBinaryBiproduct
  change chapter11ArtinConductor D S.sequence.X₂.ρ =
    chapter11ArtinConductor D S.sequence.X₁.ρ +
      chapter11ArtinConductor D S.sequence.X₃.ρ
  rw [chapter11_artin_conductor_iso D e]
  exact chapter11_artin_conductor_direct_sum D S.sequence.X₁ S.sequence.X₃

theorem chapter11_swan_conductor_short_exact_additive
    {k G : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G)
    (S : Chapter11ShortExactRepresentation k G) :
    chapter11SwanConductorFD D S.sequence.X₂ =
      chapter11SwanConductorFD D S.sequence.X₁ +
        chapter11SwanConductorFD D S.sequence.X₃ := by
  rcases chapter11_short_exact_representation_splits S with
    ⟨r, s, hr, hs, hid⟩
  let hsplit : S.sequence.Splitting :=
    { r := r
      s := s
      f_r := hr
      s_g := hs
      id := hid }
  let e := hsplit.isoBinaryBiproduct
  change chapter11SwanConductor D S.sequence.X₂.ρ =
    chapter11SwanConductor D S.sequence.X₁.ρ +
      chapter11SwanConductor D S.sequence.X₃.ρ
  unfold chapter11SwanConductor
  simp_rw [chapter11_fixed_space_codim_iso e,
    chapter11_fixed_space_codim_direct_sum]
  simp only [Nat.cast_add, mul_add]
  rw [Finset.sum_add_distrib]

/-- Duality preserves the codimension of every finite-group fixed space. -/
theorem chapter11_fixed_space_codimension_dual
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V)
    (H : Subgroup G) :
    LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ.dual H =
      LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ H := by
  classical
  let _ : Invertible (Fintype.card H : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  let ρH : Representation k H V := ρ.comp H.subtype
  have hsum_inv :
      (∑ h : H, ρH.character h⁻¹) =
        ∑ h : H, ρH.character h := by
    exact Fintype.sum_bijective (fun h : H => h⁻¹)
      (inv_bijective : Function.Bijective (fun h : H => h⁻¹)) _ _ (fun _ => rfl)
  have hsum :
      (∑ h : H, ρH.dual.character h) =
        ∑ h : H, ρH.character h := by
    calc
      (∑ h : H, ρH.dual.character h) =
          ∑ h : H, ρH.character h⁻¹ := by
            apply Finset.sum_congr rfl
            intro h _hh
            rw [Representation.char_dual]
      _ = ∑ h : H, ρH.character h := hsum_inv
  have hdual :=
    Representation.card_inv_mul_sum_char_eq_finrank
      (ρ := ρH.dual)
  have hρ :=
    Representation.card_inv_mul_sum_char_eq_finrank
      (ρ := ρH)
  have hfinrank_cast :
      (Module.finrank k (LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρ.dual H) : k) =
        (Module.finrank k (LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρ H) : k) := by
    change (Module.finrank k (Representation.invariants ρH.dual) : k) =
      (Module.finrank k (Representation.invariants ρH) : k)
    calc
      (Module.finrank k (Representation.invariants ρH.dual) : k) =
          (Nat.card H : k)⁻¹ * ∑ h : H, ρH.dual.character h := by
            symm
            exact hdual
      _ = (Nat.card H : k)⁻¹ * ∑ h : H, ρH.character h := by
            rw [hsum]
      _ = (Module.finrank k (Representation.invariants ρH) : k) := hρ
  have hfinrank :
      Module.finrank k (LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρ.dual H) =
        Module.finrank k (LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρ H) := by
    exact_mod_cast hfinrank_cast
  unfold LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
  rw [Submodule.finrank_quotient, Submodule.finrank_quotient,
    Subspace.dual_finrank_eq, hfinrank]

theorem chapter11_artin_conductor_dual
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) :
    chapter11ArtinConductor D ρ.dual = chapter11ArtinConductor D ρ := by
  unfold chapter11ArtinConductor
  simp_rw [chapter11_fixed_space_codimension_dual]

theorem chapter11_swan_conductor_dual
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) :
    chapter11SwanConductor D ρ.dual = chapter11SwanConductor D ρ := by
  unfold chapter11SwanConductor
  simp_rw [chapter11_fixed_space_codimension_dual]

/-- The restriction of an unramified twist to inertia is the original restriction. -/
theorem chapter11_unramified_twist_restricts_to_same_inertia_representation
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (χ : G →* kˣ) (hχ : chapter11UnramifiedCharacter D χ) :
    (chapter11Twist χ ρ).comp D.inertia.subtype =
      ρ.comp D.inertia.subtype := by
  ext x v
  simp [chapter11Twist, hχ x]

theorem chapter11_artin_conductor_unramified_twist
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (χ : G →* kˣ) (hχ : chapter11UnramifiedCharacter D χ) :
    chapter11ArtinConductor D (chapter11Twist χ ρ) =
      chapter11ArtinConductor D ρ := by
  have hcodim (i : ℕ) :
      LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
          (chapter11Twist χ ρ) (D.lower i) =
        LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ (D.lower i) := by
    have hfixed :
        LastLib.Book03RamificationTheory.Chapter10.fixedSpace
            (chapter11Twist χ ρ) (D.lower i) =
          LastLib.Book03RamificationTheory.Chapter10.fixedSpace ρ (D.lower i) := by
      ext v
      constructor
      · intro hv
        rw [LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff] at hv ⊢
        intro g
        have hχg : χ (g : G) = 1 :=
          hχ ⟨(g : G), (chapter11_lower_le_inertia D i) g.property⟩
        simpa [chapter11Twist, hχg] using hv g
      · intro hv
        rw [LastLib.Book03RamificationTheory.Chapter10.fixedSpace.mem_iff] at hv ⊢
        intro g
        have hχg : χ (g : G) = 1 :=
          hχ ⟨(g : G), (chapter11_lower_le_inertia D i) g.property⟩
        simpa [chapter11Twist, hχg] using hv g
    unfold LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
    rw [hfixed]
  unfold chapter11ArtinConductor
  simp_rw [hcodim]

theorem chapter11_swan_conductor_unramified_twist
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (χ : G →* kˣ) (hχ : chapter11UnramifiedCharacter D χ) :
    chapter11SwanConductor D (chapter11Twist χ ρ) =
      chapter11SwanConductor D ρ := by
  sorry

/-- The levelwise restriction data which is needed for a ramified twist. -/
def chapter11RamifiedTwistLevelCharacter
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (χ : G →* kˣ) (i : ℕ) :
    D.lower i →* kˣ :=
  χ.comp (D.lower i).subtype

theorem chapter11_ramified_twist_has_nontrivial_level_data
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (χ : G →* kˣ)
    (hχ : ¬chapter11UnramifiedCharacter D χ) :
    ∃ i : ℕ, chapter11RamifiedTwistLevelCharacter D χ i ≠ 1 := by
  sorry

/- The source warning is exposed by `chapter11RamifiedTwistLevelCharacter`: a
  ramified-twist formula needs the restrictions to the lower ramification
  groups, not merely the two separate conductor exponents. -/

end
end LastLib.Book03RamificationTheory.Chapter11
