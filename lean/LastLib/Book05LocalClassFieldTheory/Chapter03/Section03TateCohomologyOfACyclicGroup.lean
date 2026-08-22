import LastLib.Book05LocalClassFieldTheory.Chapter03.Section02Hilbert90
import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

namespace LastLib.Book05LocalClassFieldTheory.Chapter03

noncomputable section

open CategoryTheory
open scoped BigOperators

/-! ## 3.3. Tate cohomology of a cyclic group -/

/-- Tate cohomology in an arbitrary integer degree, using Mathlib's canonical complex. -/
abbrev chapter03TateCohomology
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (r : ℤ) : ModuleCat ℤ :=
  tateCohomology A r

abbrev chapter03TateH0
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) : ModuleCat ℤ :=
  chapter03TateCohomology A 0

abbrev chapter03TateHMinusOne
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) : ModuleCat ℤ :=
  chapter03TateCohomology A (-1)

/-- The alternating norm and difference maps used by the cyclic model. -/
abbrev chapter03TateNormMap
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) :=
  letI : Module ℤ A.V := A.hV2
  A.norm.hom.toLinearMap

abbrev chapter03TateDifferenceMap
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) :=
  letI : Module ℤ A.V := A.hV2
  (A.applyAsHom σ - 𝟙 A).hom.toLinearMap

theorem chapter03_tate_norm_range_le_difference_kernel
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) :
    letI : Module ℤ A.V := A.hV2
    LinearMap.range (chapter03TateNormMap A) ≤
      LinearMap.ker (chapter03TateDifferenceMap A σ) := by
  let _ : Module ℤ A.V := A.hV2
  rintro _ ⟨y, rfl⟩
  change (chapter03TateDifferenceMap A σ) (chapter03TateNormMap A y) = 0
  have h := congrArg (fun f => f.hom)
    ((Rep.FiniteCyclicGroup.normHomCompSub (k := ℤ) (G := G) A σ).zero)
  have h' := congrArg (fun f => f y) h
  simpa [chapter03TateNormMap, chapter03TateDifferenceMap] using h'

theorem chapter03_tate_difference_range_le_norm_kernel
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) :
    letI : Module ℤ A.V := A.hV2
    LinearMap.range (chapter03TateDifferenceMap A σ) ≤
      LinearMap.ker (chapter03TateNormMap A) := by
  let _ : Module ℤ A.V := A.hV2
  rintro _ ⟨y, rfl⟩
  change (chapter03TateNormMap A) (chapter03TateDifferenceMap A σ y) = 0
  have h := congrArg (fun f => f.hom)
    ((Rep.FiniteCyclicGroup.subCompNormHom (k := ℤ) (G := G) A σ).zero)
  have h' := congrArg (fun f => f y) h
  simpa [chapter03TateNormMap, chapter03TateDifferenceMap] using h'

/-- The concrete quotient model for `A^G / N_G A` supplied by the short-complex API. -/
abbrev chapter03TateH0Concrete
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) : ModuleCat ℤ :=
  (Rep.FiniteCyclicGroup.normHomCompSub (k := ℤ) (G := G) A σ).homology

/-- The concrete quotient model for `ker(N_G) / D A`. -/
abbrev chapter03TateHMinusOneConcrete
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) : ModuleCat ℤ :=
  (Rep.FiniteCyclicGroup.subCompNormHom (k := ℤ) (G := G) A σ).homology

/-- The quotient implementation of `A^G/N_GA`, with its kernel/range data exposed. -/
noncomputable def chapter03_tate_h0_concrete_quotient_iso
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) :
    chapter03TateH0Concrete A σ ≅
      (Rep.FiniteCyclicGroup.normHomCompSub (k := ℤ) (G := G) A σ).moduleCatLeftHomologyData.H :=
  (Rep.FiniteCyclicGroup.normHomCompSub (k := ℤ) (G := G) A σ).moduleCatHomologyIso

/-- The quotient implementation of `ker(N_G)/D A`, with its kernel/range data exposed. -/
noncomputable def chapter03_tate_hminusone_concrete_quotient_iso
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) :
    chapter03TateHMinusOneConcrete A σ ≅
      (Rep.FiniteCyclicGroup.subCompNormHom (k := ℤ) (G := G) A σ).moduleCatLeftHomologyData.H :=
  (Rep.FiniteCyclicGroup.subCompNormHom (k := ℤ) (G := G) A σ).moduleCatHomologyIso

/-- The canonical two-periodicity isomorphism for cyclic Tate cohomology. -/
noncomputable def chapter03_tate_periodicity
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G)
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) (r : ℤ) :
    chapter03TateCohomology A (r + 2) ≅ chapter03TateCohomology A r := by
  classical
  let _ : Module ℤ A.V := A.hV2
  let _ : Module ℤ (G → A.V) := Pi.Function.module G ℤ A.V
  let S0 : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk A.norm.toModuleCatHom
      (groupCohomology.d₀₁ A) (by
        simpa only [← Category.assoc] using Rep.norm_comp_d_eq_zero A)
  let S : ShortComplex (ModuleCat ℤ) :=
    (tateComplex A).sc' (-1) 0 1
  let e : S ≅ S0 :=
    ShortComplex.isoMk (groupHomology.chainsIso₀ A)
      (groupCohomology.cochainsIso₀ A) (groupCohomology.cochainsIso₁ A) (by
        simp [S, S0, Rep.tateNorm]
        change (groupHomology.chainsIso₀ A).hom ≫ A.norm.toModuleCatHom =
          (groupHomology.chainsIso₀ A).hom ≫ A.norm.toModuleCatHom ≫
            ((groupCohomology.cochainsIso₀ A).inv ≫
              (groupCohomology.cochainsIso₀ A).hom)
        simp) (by
        change (groupCohomology.cochainsIso₀ A).hom ≫ groupCohomology.d₀₁ A =
          (groupCohomology.inhomogeneousCochains A).d 0 1 ≫
            (groupCohomology.cochainsIso₁ A).hom
        exact groupCohomology.comp_d₀₁_eq A)
  have h0 : chapter03TateCohomology A 0 ≅ S0.homology :=
    (tateComplex A).homologyIsoSc' (-1) 0 1 (by norm_num) (by norm_num) ≪≫
      ShortComplex.homologyMapIso e
  let U : ShortComplex (ModuleCat ℤ) :=
    Rep.FiniteCyclicGroup.subCompNormHom (k := ℤ) (G := G) A σ
  let Sm : ShortComplex (ModuleCat ℤ) :=
    (tateComplex A).sc' (-2) (-1) 0
  let _ : Module ℤ (G →₀ A.V) := Finsupp.module G A.V
  let _ : Module ℤ ((Fin 1 → G) →₀ A.V) := Finsupp.module (Fin 1 → G) A.V
  let q : U.X₁ ⟶ Sm.X₁ := by
    exact ModuleCat.ofHom <|
      (groupHomology.chainsIso₁ A).inv.hom.comp
        (Finsupp.lsingle σ⁻¹)
  let φm : U ⟶ Sm := by
    refine ShortComplex.homMk q
      (groupHomology.chainsIso₀ A).inv (groupCohomology.cochainsIso₀ A).inv ?_ ?_
    · dsimp [U, Sm, q]
      change (ModuleCat.ofHom (Finsupp.lsingle σ⁻¹) ≫
          (groupHomology.chainsIso₁ A).inv) ≫
          (groupHomology.inhomogeneousChains A).d 1 0 =
        ModuleCat.ofHom (A.applyAsHom σ - 𝟙 A).hom.toLinearMap ≫
          (groupHomology.chainsIso₀ A).inv
      rw [Category.assoc, groupHomology.eq_d₁₀_comp_inv]
      apply ConcreteCategory.hom_ext
      intro x
      change (groupHomology.chainsIso₀ A).inv
          (groupHomology.d₁₀ A (Finsupp.single σ⁻¹ x)) =
        (groupHomology.chainsIso₀ A).inv
          ((A.applyAsHom σ - 𝟙 A).hom x)
      rw [groupHomology.d₁₀_single]
      simp [Rep.sub_hom, Rep.applyAsHom]
    · simp [U, Sm, Rep.tateNorm]
      change (groupHomology.chainsIso₀ A).inv ≫
          (groupHomology.chainsIso₀ A).hom ≫ A.norm.toModuleCatHom ≫
            (groupCohomology.cochainsIso₀ A).inv =
        A.norm.toModuleCatHom ≫ (groupCohomology.cochainsIso₀ A).inv
      simp
  have hdf : (groupHomology.chainsIso₁ A).hom ≫ groupHomology.d₁₀ A =
      (groupHomology.inhomogeneousChains A).d 1 0 ≫
        (groupHomology.chainsIso₀ A).hom := by
    rw [← cancel_epi (groupHomology.chainsIso₁ A).inv]
    simp only [Iso.inv_hom_id_assoc]
    change groupHomology.d₁₀ A =
      (groupHomology.chainsIso₁ A).inv ≫
        (groupHomology.inhomogeneousChains A).d 1 0 ≫
          (groupHomology.chainsIso₀ A).hom
    rw [← Category.assoc, groupHomology.eq_d₁₀_comp_inv]
    simp
  have hdf' : (groupHomology.chainsIso₁ A).hom ≫ groupHomology.d₁₀ A =
      Sm.f ≫ (groupHomology.chainsIso₀ A).hom := by
    exact hdf
  have hrange (x : A.V) :
      (groupHomology.chainsIso₀ A).inv x ∈ LinearMap.range Sm.f.hom ↔
        x ∈ LinearMap.range (A.applyAsHom σ - 𝟙 A).hom.toLinearMap := by
    constructor
    · rintro ⟨y, hy⟩
      have hxy := congrArg (fun f => f y) hdf'
      change groupHomology.d₁₀ A ((groupHomology.chainsIso₁ A).hom y) =
        (groupHomology.chainsIso₀ A).hom (Sm.f y) at hxy
      have hdx : groupHomology.d₁₀ A ((groupHomology.chainsIso₁ A).hom y) = x := by
        calc
          groupHomology.d₁₀ A ((groupHomology.chainsIso₁ A).hom y) =
              (groupHomology.chainsIso₀ A).hom (Sm.f y) := hxy
          _ = (groupHomology.chainsIso₀ A).hom
                ((groupHomology.chainsIso₀ A).inv x) := by rw [hy]
          _ = x := by simp
      have hxker : x ∈ Representation.Coinvariants.ker A.ρ := by
        rw [← groupHomology.range_d₁₀_eq_coinvariantsKer]
        exact ⟨(groupHomology.chainsIso₁ A).hom y, hdx⟩
      rw [Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ σ hσ] at hxker
      simpa [Rep.sub_hom, Rep.applyAsHom] using hxker
    · rintro ⟨a, ha⟩
      refine ⟨q a, ?_⟩
      have hcomm := congrArg (fun f => f a) φm.comm₁₂
      change Sm.f (q a) = (groupHomology.chainsIso₀ A).inv
        ((A.applyAsHom σ - 𝟙 A).hom a) at hcomm
      have ha' : (A.applyAsHom σ - 𝟙 A).hom a = x := ha
      simpa only [ha'] using hcomm
  have hOp : IsIso (ShortComplex.opcyclesMap φm) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    constructor
    · intro z z' hz
      obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective U.pOpcycles).1 inferInstance z
      obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective U.pOpcycles).1 inferInstance z'
      have hxmap :
          (ShortComplex.opcyclesMap φm) (U.pOpcycles x) = Sm.pOpcycles (φm.τ₂ x) := by
        have h := congrArg (fun f => f x) (ShortComplex.p_opcyclesMap φm)
        change (ShortComplex.opcyclesMap φm) (U.pOpcycles x) = Sm.pOpcycles (φm.τ₂ x) at h
        exact h
      have hymap :
          (ShortComplex.opcyclesMap φm) (U.pOpcycles y) = Sm.pOpcycles (φm.τ₂ y) := by
        have h := congrArg (fun f => f y) (ShortComplex.p_opcyclesMap φm)
        change (ShortComplex.opcyclesMap φm) (U.pOpcycles y) = Sm.pOpcycles (φm.τ₂ y) at h
        exact h
      have hz' : Sm.pOpcycles (φm.τ₂ x) = Sm.pOpcycles (φm.τ₂ y) := by
        rw [← hxmap, hz, hymap]
      have hmem := (ShortComplex.moduleCat_pOpcycles_eq_iff Sm _ _).1 hz'
      apply (ShortComplex.moduleCat_pOpcycles_eq_iff U x y).2
      apply (hrange (x - y)).1
      rcases hmem with ⟨w, hw⟩
      refine ⟨w, ?_⟩
      have hτ2x : φm.τ₂ x = (groupHomology.chainsIso₀ A).inv x := by rfl
      have hτ2y : φm.τ₂ y = (groupHomology.chainsIso₀ A).inv y := by rfl
      rw [hτ2x, hτ2y] at hw
      rw [map_sub]
      exact hw
    · intro z
      obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective Sm.pOpcycles).1 inferInstance z
      let x : A.V := (groupHomology.chainsIso₀ A).hom y
      refine ⟨U.pOpcycles x, ?_⟩
      have hxmap :
          (ShortComplex.opcyclesMap φm) (U.pOpcycles x) = Sm.pOpcycles (φm.τ₂ x) := by
        have h := congrArg (fun f => f x) (ShortComplex.p_opcyclesMap φm)
        change (ShortComplex.opcyclesMap φm) (U.pOpcycles x) = Sm.pOpcycles (φm.τ₂ x) at h
        exact h
      change (ShortComplex.opcyclesMap φm) (U.pOpcycles x) = Sm.pOpcycles y
      rw [hxmap]
      change Sm.pOpcycles ((groupHomology.chainsIso₀ A).inv x) = Sm.pOpcycles y
      have hi := congrArg (fun f => f y) (groupHomology.chainsIso₀ A).hom_inv_id
      change (groupHomology.chainsIso₀ A).inv
          ((groupHomology.chainsIso₀ A).hom y) = y at hi
      exact congrArg (fun z => Sm.pOpcycles z) hi
  letI : MulAction G A.V :=
    { smul := fun g x => A.ρ g x
      one_smul := by
        intro x
        exact congrArg (fun f => f x) A.ρ.map_one
      mul_smul := by
        intro g h x
        change A.ρ (g * h) x = A.ρ g (A.ρ h x)
        rw [map_mul]
        rfl }
  let T : ShortComplex (ModuleCat ℤ) :=
    Rep.FiniteCyclicGroup.normHomCompSub (k := ℤ) (G := G) A σ
  let ev : S0.X₃ ⟶ T.X₃ :=
    ModuleCat.ofHom
      { toFun := fun f => f σ
        map_add' := by intro f g; rfl
        map_smul' := by intro z f; rfl }
  let φ : S0 ⟶ T :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := ev
      comm₁₂ := by simp [S0, T]
      comm₂₃ := by
        dsimp [S0, T, ev]
        apply ConcreteCategory.hom_ext
        intro x
        change (A.applyAsHom σ - 𝟙 A).hom.toLinearMap x =
          (groupCohomology.d₀₁ A).hom x σ
        change A.ρ σ x - x = A.ρ σ x - x
        rfl }
  have hcycles : IsIso (ShortComplex.cyclesMap φ) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    constructor
    · intro z z' hz
      apply (ModuleCat.mono_iff_injective S0.iCycles).1 inferInstance
      have hz' := congrArg (fun w => T.iCycles w) hz
      rw [← ConcreteCategory.comp_apply, ShortComplex.cyclesMap_i,
        ← ConcreteCategory.comp_apply, ShortComplex.cyclesMap_i] at hz'
      simpa [φ] using hz'
    · intro z
      let x : A.V := T.iCycles z
      have hDx : (A.applyAsHom σ - 𝟙 A).hom.toLinearMap x = 0 := by
        have hz0 := T.iCycles_g
        have hz0' := congrArg (fun f => f z) hz0
        simpa [T, x] using hz0'
      have hDx' : A.ρ σ x - x = 0 := by
        simpa [Rep.sub_hom, Rep.applyAsHom] using hDx
      have hσx : σ • x = x := by
        change A.ρ σ x = x
        exact sub_eq_zero.mp hDx'
      have hx : (groupCohomology.d₀₁ A) x = 0 := by
        ext τ
        rw [groupCohomology.d₀₁_hom_apply]
        have hfix : τ • x = x :=
          smul_eq_self_of_mem_zpowers (hσ τ) hσx
        exact sub_eq_zero.mpr hfix
      let z' := S0.cyclesMk x hx
      refine ⟨z', ?_⟩
      apply (ModuleCat.mono_iff_injective T.iCycles).1 inferInstance
      rw [← ConcreteCategory.comp_apply, ShortComplex.cyclesMap_i]
      simpa [φ, z'] using (S0.i_cyclesMk x hx)
  letI : IsIso (ShortComplex.cyclesMap φ) := hcycles
  letI : IsIso (ShortComplex.homologyMap φ) :=
    ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi hcycles (by infer_instance)
  have h0T : chapter03TateCohomology A 0 ≅ T.homology :=
    h0 ≪≫ asIso (ShortComplex.homologyMap φ)
  letI : IsIso (ShortComplex.opcyclesMap φm) := hOp
  haveI : Mono φm.τ₃ := by
    change Mono (groupCohomology.cochainsIso₀ A).inv
    infer_instance
  letI : IsIso (ShortComplex.homologyMap φm) :=
    ShortComplex.isIso_homologyMap_of_isIso_opcyclesMap_of_mono hOp (by infer_instance)
  have hm : chapter03TateCohomology A (-1) ≅ U.homology :=
    (tateComplex A).homologyIsoSc' (-2) (-1) 0 (by norm_num) (by norm_num) ≪≫
      (asIso (ShortComplex.homologyMap φm)).symm
  have even_add_two {n : ℕ} (hn : Even n) : Even (n + 2) := by
    rcases hn with ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    omega
  have odd_add_two {n : ℕ} (hn : Odd n) : Odd (n + 2) := by
    rcases hn with ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    omega
  cases r with
  | ofNat n =>
      cases n with
      | zero =>
          letI : NeZero 2 := ⟨by norm_num⟩
          let h2 : chapter03TateCohomology A 2 ≅ T.homology :=
            (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 2).app A ≪≫
              Rep.FiniteCyclicGroup.groupCohomologyIsoEven A σ hσ 2 (by norm_num)
          simpa [chapter03TateCohomology] using h2 ≪≫ h0T.symm
      | succ n =>
          letI : NeZero (n + 1) := ⟨by omega⟩
          letI : NeZero (n + 3) := ⟨by omega⟩
          by_cases he : Even (n + 1)
          · have he3 : Even (n + 3) := by
              convert even_add_two he using 1
            let hs : chapter03TateCohomology A (n + 3) ≅ T.homology :=
              (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) (n + 3)).app A ≪≫
                Rep.FiniteCyclicGroup.groupCohomologyIsoEven A σ hσ (n + 3)
                  he3
            let ht : chapter03TateCohomology A (n + 1) ≅ T.homology :=
              (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) (n + 1)).app A ≪≫
                Rep.FiniteCyclicGroup.groupCohomologyIsoEven A σ hσ (n + 1)
                  he
            convert hs ≪≫ ht.symm using 1 <;> congr 1
          · have ho : Odd (n + 1) := Nat.not_even_iff_odd.mp he
            have ho3 : Odd (n + 3) := by
              convert odd_add_two ho using 1
            let hs : chapter03TateCohomology A (n + 3) ≅ U.homology :=
              (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) (n + 3)).app A ≪≫
                Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A σ hσ (n + 3) ho3
            let ht : chapter03TateCohomology A (n + 1) ≅ U.homology :=
              (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) (n + 1)).app A ≪≫
                Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A σ hσ (n + 1) ho
            convert hs ≪≫ ht.symm using 1 <;> congr 1
  | negSucc n =>
      cases n with
      | zero =>
          letI : NeZero 1 := ⟨by norm_num⟩
          let h1 : chapter03TateCohomology A 1 ≅ U.homology :=
            (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 1).app A ≪≫
              Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A σ hσ 1 (by norm_num)
          simpa [chapter03TateCohomology] using h1 ≪≫ hm.symm
      | succ n =>
          cases n with
          | zero =>
              letI : NeZero 1 := ⟨by norm_num⟩
              let hminus2 : chapter03TateCohomology A (-2) ≅ T.homology :=
                (TateCohomology.isoGroupHomology (R := ℤ) (G := G) (-2) 1 (by norm_num)).app A ≪≫
                  Rep.FiniteCyclicGroup.groupHomologyIsoOdd A σ hσ 1 (by norm_num)
              simpa [chapter03TateCohomology] using h0T ≪≫ hminus2.symm
          | succ n =>
              cases n with
              | zero =>
                  letI : NeZero 2 := ⟨by norm_num⟩
                  let hminus3 : chapter03TateCohomology A (-3) ≅ U.homology :=
                    (TateCohomology.isoGroupHomology (R := ℤ) (G := G) (-3) 2 (by norm_num)).app A ≪≫
                      Rep.FiniteCyclicGroup.groupHomologyIsoEven A σ hσ 2
                        (by norm_num)
                  simpa [chapter03TateCohomology] using hm ≪≫ hminus3.symm
              | succ m =>
                  letI : NeZero (m + 1) := ⟨by omega⟩
                  letI : NeZero (m + 3) := ⟨by omega⟩
                  by_cases he : Even (m + 1)
                  · have he3 : Even (m + 3) := by
                      convert even_add_two he using 1
                    let hs : chapter03TateCohomology A (-(m + 2)) ≅ U.homology :=
                      (TateCohomology.isoGroupHomology (R := ℤ) (G := G)
                        (-(m + 2)) (m + 1) (by omega)).app A ≪≫
                        Rep.FiniteCyclicGroup.groupHomologyIsoEven A σ hσ (m + 1)
                          he
                    let ht : chapter03TateCohomology A (-(m + 4)) ≅ U.homology :=
                      (TateCohomology.isoGroupHomology (R := ℤ) (G := G)
                        (-(m + 4)) (m + 3) (by omega)).app A ≪≫
                        Rep.FiniteCyclicGroup.groupHomologyIsoEven A σ hσ (m + 3)
                          he3
                    convert hs ≪≫ ht.symm using 1 <;> congr 1
                  · have ho : Odd (m + 1) := Nat.not_even_iff_odd.mp he
                    have ho3 : Odd (m + 3) := by
                      convert odd_add_two ho using 1
                    let hs : chapter03TateCohomology A (-(m + 2)) ≅ T.homology :=
                      (TateCohomology.isoGroupHomology (R := ℤ) (G := G)
                        (-(m + 2)) (m + 1) (by omega)).app A ≪≫
                        Rep.FiniteCyclicGroup.groupHomologyIsoOdd A σ hσ (m + 1) ho
                    let ht : chapter03TateCohomology A (-(m + 4)) ≅ T.homology :=
                      (TateCohomology.isoGroupHomology (R := ℤ) (G := G)
                        (-(m + 4)) (m + 3) (by omega)).app A ≪≫
                        Rep.FiniteCyclicGroup.groupHomologyIsoOdd A σ hσ (m + 3) ho3
                    convert hs ≪≫ ht.symm using 1 <;> congr 1

noncomputable def chapter03_tate_h0_cyclic_formula
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G)
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    chapter03TateH0 A ≅ chapter03TateH0Concrete A σ := by
  letI : NeZero 2 := ⟨by norm_num⟩
  let h2 : chapter03TateCohomology A 2 ≅ chapter03TateH0Concrete A σ :=
    (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 2).app A ≪≫
      Rep.FiniteCyclicGroup.groupCohomologyIsoEven A σ hσ 2 (by norm_num)
  exact (chapter03_tate_periodicity A σ hσ 0).symm ≪≫ h2

noncomputable def chapter03_tate_hminusone_cyclic_formula
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G)
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    chapter03TateHMinusOne A ≅ chapter03TateHMinusOneConcrete A σ := by
  letI : NeZero 1 := ⟨by norm_num⟩
  let h1 : chapter03TateCohomology A 1 ≅ chapter03TateHMinusOneConcrete A σ :=
    (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 1).app A ≪≫
      Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A σ hσ 1 (by norm_num)
  exact (chapter03_tate_periodicity A σ hσ (-1)).symm ≪≫ h1

/-- The multiplicative Galois module `Lˣ` used in the local-field specialization. -/
abbrev chapter03MultiplicativeGaloisModule
    (K L : Type*) [Field K] [Field L] [Algebra K L] :=
  Rep.ofAlgebraAutOnUnits K L

attribute [local instance] IsCyclic.commGroup in
private noncomputable def chapter03_fixed_units_add_equiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (σ : Gal(L/K)) (hσ : ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ) :
    Additive Kˣ ≃+
      LinearMap.ker ((chapter03MultiplicativeGaloisModule K L).applyAsHom σ - 𝟙
        (chapter03MultiplicativeGaloisModule K L)).hom.toLinearMap := by
  let f : Additive Kˣ →+
      LinearMap.ker ((chapter03MultiplicativeGaloisModule K L).applyAsHom σ - 𝟙
        (chapter03MultiplicativeGaloisModule K L)).hom.toLinearMap :=
    { toFun := fun x =>
        ⟨Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x.toMul), by
          apply LinearMap.mem_ker.mpr
          simp only [Rep.sub_hom, Representation.IntertwiningMap.sub_toLinearMap]
          apply sub_eq_zero.mpr
          change Additive.ofMul (Units.map σ.toRingEquiv.toMonoidHom
              (Units.map (algebraMap K L).toMonoidHom x.toMul)) =
            Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x.toMul)
          apply congrArg Additive.ofMul
          apply Units.ext
          simp⟩
      map_zero' := by
        apply Subtype.ext
        change Additive.ofMul (Units.map (algebraMap K L).toMonoidHom
          (1 : Kˣ)) = (0 : Additive Lˣ)
        simp
      map_add' := by
        intro x y
        apply Subtype.ext
        change Additive.ofMul (Units.map (algebraMap K L).toMonoidHom
            (x.toMul * y.toMul)) =
          Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x.toMul) +
            Additive.ofMul (Units.map (algebraMap K L).toMonoidHom y.toMul)
        simp }
  apply AddEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Additive.ofMul.injective
    apply Units.ext
    apply (algebraMap K L).injective
    have hxy' := congrArg Subtype.val hxy
    change Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x.toMul) =
      Additive.ofMul (Units.map (algebraMap K L).toMonoidHom y.toMul) at hxy'
    exact congrArg Units.val (congrArg Additive.toMul hxy')
  · intro z
    let zval : Additive Lˣ := z.1
    have hzσ : (chapter03MultiplicativeGaloisModule K L).ρ σ z.1 = z.1 := by
      apply sub_eq_zero.mp
      simpa [Rep.sub_hom, Rep.applyAsHom] using z.2
    have hzσ' : (chapter03MultiplicativeGaloisModule K L).ρ σ zval = zval := by
      exact hzσ
    have hzfix : ∀ τ : Gal(L / K), τ (zval.toMul : L) = (zval.toMul : L) := by
      intro τ
      have hzτ :=
        (Representation.mem_invariants_iff_of_forall_mem_zpowers
          (chapter03MultiplicativeGaloisModule K L).ρ σ hσ zval).2 hzσ' τ
      change Additive.ofMul (Units.map τ.toRingEquiv.toMonoidHom zval.toMul) = zval at hzτ
      exact congrArg Units.val (congrArg Additive.toMul hzτ)
    obtain ⟨a, ha⟩ :=
      (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (x := (zval.toMul : L))).2 hzfix
    have ha0 : a ≠ 0 := by
      intro ha0
      subst a
      exact Units.ne_zero zval.toMul (by simpa using ha.symm)
    let x : Kˣ := Units.mk0 a ha0
    refine ⟨Additive.ofMul x, ?_⟩
    apply Subtype.ext
    change Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x) = z.1
    change Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x) = zval
    apply Additive.ofMul.injective
    apply Units.ext
    change algebraMap K L a = (zval.toMul : L)
    exact ha

attribute [local instance] IsCyclic.commGroup in
noncomputable def chapter03_tate_h0_multiplicative_norm_quotient
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] [Fintype Gal(L/K)]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) :
    chapter03TateH0 (chapter03MultiplicativeGaloisModule K L) ≅
      ModuleCat.of ℤ (Additive (chapter03NormQuotient K L)) := by
  let A := chapter03MultiplicativeGaloisModule K L
  let T := Rep.FiniteCyclicGroup.normHomCompSub (k := ℤ) (G := Gal(L / K)) A σ
  let eK : Additive Kˣ ≃+ T.moduleCatLeftHomologyData.K := by
    change Additive Kˣ ≃+ LinearMap.ker ((A.applyAsHom σ - 𝟙 A).hom.toLinearMap)
    exact chapter03_fixed_units_add_equiv K L σ
      (chapter03_cyclic_extension_generator K L n σ hcyc)
  let eT : chapter03TateH0 A ≅ ModuleCat.of ℤ T.moduleCatLeftHomologyData.H :=
    chapter03_tate_h0_cyclic_formula A σ
      (chapter03_cyclic_extension_generator K L n σ hcyc) ≪≫
      T.moduleCatHomologyIso
  let qH : Additive Kˣ →ₗ[ℤ] T.moduleCatLeftHomologyData.H :=
    T.moduleCatLeftHomologyData.π.hom.comp eK.toIntLinearEquiv.toLinearMap
  have hqH : Function.Surjective qH := by
    intro z
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective T.moduleCatLeftHomologyData.π).1
      inferInstance z
    obtain ⟨x, rfl⟩ := eK.surjective y
    exact ⟨x, rfl⟩
  letI : (chapter03NormSubgroup K L).Normal :=
    Subgroup.Normal.of_commutator_le (G := Kˣ) (H := chapter03NormSubgroup K L) (by
      rw [(commutator_eq_bot_iff (G := Kˣ)).2 inferInstance]
      exact bot_le)
  letI : CommGroup (chapter03NormQuotient K L) :=
    QuotientGroup.Quotient.commGroup (chapter03NormSubgroup K L)
  letI : Module ℤ (Additive (chapter03NormQuotient K L)) := inferInstance
  let qN : Additive Kˣ →ₗ[ℤ] Additive (chapter03NormQuotient K L) :=
    { toFun := fun x =>
        Additive.ofMul (QuotientGroup.mk' (chapter03NormSubgroup K L) x.toMul)
      map_add' := by
        intro x y
        change Additive.ofMul (QuotientGroup.mk' (chapter03NormSubgroup K L)
            (x.toMul * y.toMul)) =
            Additive.ofMul (QuotientGroup.mk' (chapter03NormSubgroup K L) x.toMul) +
            Additive.ofMul (QuotientGroup.mk' (chapter03NormSubgroup K L) y.toMul)
        simp
      map_smul' := by
        intro z x
        change Additive.ofMul (QuotientGroup.mk' (chapter03NormSubgroup K L)
            (z • x : Additive Kˣ).toMul) = z •
          Additive.ofMul (QuotientGroup.mk' (chapter03NormSubgroup K L) x.toMul)
        simp }
  have hnorm (u : Lˣ) :
      A.norm.hom.toLinearMap (Additive.ofMul u) =
        Additive.ofMul (Units.map (algebraMap K L).toMonoidHom
          (chapter03NormUnit K L u)) := by
    apply Additive.ext
    apply Units.ext
    change (Additive.toMul (A.norm.hom (Additive.ofMul u))).1 =
      algebraMap K L (Algebra.norm K (u : L))
    have hu' :
        ((Rep.toAdditive (M := Gal(L / K)) (G := Lˣ)).symm (Additive.ofMul u) :
          Additive Lˣ) = Additive.ofMul u := rfl
    have hF : (inferInstance : Fintype (Gal(L / K))) = AlgEquiv.fintype K L :=
      Subsingleton.elim _ _
    cases hF
    have hnorm' :=
      groupCohomology.norm_ofAlgebraAutOnUnits_eq (K := K) (L := L) u
    rw [hu'] at hnorm'
    exact hnorm'
  have hqN : Function.Surjective qN := by
    intro z
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (chapter03NormSubgroup K L) z.toMul
    refine ⟨Additive.ofMul x, ?_⟩
    change Additive.ofMul (QuotientGroup.mk' (chapter03NormSubgroup K L) x) = z
    exact congrArg Additive.ofMul hx
  have hker : LinearMap.ker qH = LinearMap.ker qN := by
    ext x
    constructor
    · intro hx
      have hx0 : qH x = 0 := LinearMap.mem_ker.mp hx
      have hxrange : eK x ∈ LinearMap.range T.moduleCatToCycles := by
        apply (Submodule.Quotient.mk_eq_zero _).mp
        change T.moduleCatLeftHomologyData.π.hom (eK x) = 0
        exact hx0
      rcases hxrange with ⟨y, hy⟩
      let yval : Additive Lˣ := y
      have hn : chapter03NormUnit K L yval.toMul = x.toMul := by
        have hy' := congrArg Subtype.val hy
        change A.norm.hom.toLinearMap yval =
          Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x.toMul) at hy'
        have hny : A.norm.hom.toLinearMap yval =
            Additive.ofMul (Units.map (algebraMap K L).toMonoidHom
              (chapter03NormUnit K L yval.toMul)) := by
          exact hnorm yval.toMul
        rw [hny] at hy'
        apply Units.ext
        apply (algebraMap K L).injective
        exact congrArg Units.val (congrArg Additive.toMul hy')
      apply LinearMap.mem_ker.mpr
      change Additive.ofMul (QuotientGroup.mk' (chapter03NormSubgroup K L) x.toMul) = 0
      apply Additive.ofMul.injective
      exact (QuotientGroup.eq_one_iff _).2
        ((chapter03_mem_norm_subgroup_iff K L x.toMul).2 ⟨yval.toMul, hn⟩)
    · intro hx
      have hx0 : qN x = 0 := LinearMap.mem_ker.mp hx
      change Additive.ofMul (QuotientGroup.mk' (chapter03NormSubgroup K L) x.toMul) = 0 at hx0
      have hxmem : x.toMul ∈ chapter03NormSubgroup K L := by
        apply (QuotientGroup.eq_one_iff _).1
        exact Additive.ofMul.injective hx0
      have hxnorm : ∃ u : Lˣ, chapter03NormUnit K L u = x.toMul :=
        (chapter03_mem_norm_subgroup_iff K L x.toMul).1 hxmem
      rcases hxnorm with ⟨u, hu⟩
      have he : T.moduleCatToCycles (Additive.ofMul u) = eK x := by
        apply Subtype.ext
        change A.norm.hom.toLinearMap (Additive.ofMul u) =
          Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x.toMul)
        rw [hnorm, hu]
      apply LinearMap.mem_ker.mpr
      change qH x = 0
      change T.moduleCatLeftHomologyData.π.hom (eK x) = 0
      rw [← he]
      change (LinearMap.range T.moduleCatToCycles).mkQ
        (T.moduleCatToCycles (Additive.ofMul u)) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨_, rfl⟩
  let eH := qH.quotKerEquivOfSurjective hqH
  let eN := qN.quotKerEquivOfSurjective hqN
  let eQ := Submodule.quotEquivOfEq (LinearMap.ker qH) (LinearMap.ker qN) hker
  convert eT ≪≫ eH.symm.toModuleIso ≪≫ eQ.toModuleIso ≪≫ eN.toModuleIso using 1

attribute [local instance] IsCyclic.commGroup in
theorem chapter03_tate_hminusone_multiplicative_zero
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] [Fintype Gal(L/K)]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) :
    Subsingleton (chapter03TateHMinusOne (chapter03MultiplicativeGaloisModule K L)) := by
  let _ : NeZero 1 := ⟨by norm_num⟩
  let e1 : chapter03TateCohomology (chapter03MultiplicativeGaloisModule K L) 1 ≅
      groupCohomology (chapter03MultiplicativeGaloisModule K L) 1 :=
    (TateCohomology.isoGroupCohomology (R := ℤ) (G := Gal(L / K)) 1).app
      (chapter03MultiplicativeGaloisModule K L)
  let ep : chapter03TateCohomology (chapter03MultiplicativeGaloisModule K L) 1 ≅
      chapter03TateHMinusOne (chapter03MultiplicativeGaloisModule K L) :=
    by
      convert chapter03_tate_periodicity (chapter03MultiplicativeGaloisModule K L) σ
        (chapter03_cyclic_extension_generator K L n σ hcyc) (-1) using 1; norm_num
  let hsub : Subsingleton (groupCohomology (chapter03MultiplicativeGaloisModule K L) 1) :=
    chapter03_hilbert90_h1_subsingleton K L
  constructor
  intro x y
  calc
    x = ep.hom (ep.inv x) := by simp
    _ = ep.hom (ep.inv y) := by
      congr 1
      calc
        ep.inv x = e1.inv (e1.hom (ep.inv x)) := by simp
        _ = e1.inv (e1.hom (ep.inv y)) := by
          rw [Subsingleton.elim (e1.hom (ep.inv x)) (e1.hom (ep.inv y))]
        _ = ep.inv y := by simp
    _ = y := by simp

/-- Hilbert 90 written as the vanishing of the first ordinary cohomology group. -/
theorem chapter03_group_cohomology_h1_multiplicative_zero
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    Subsingleton (groupCohomology.H1 (chapter03MultiplicativeGaloisModule K L)) := by
  exact chapter03_hilbert90_h1_subsingleton K L

attribute [local instance] IsCyclic.commGroup in
/-- Periodicity identifies the second ordinary group cohomology with the norm quotient. -/
noncomputable def chapter03_group_cohomology_h2_multiplicative_norm_quotient
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] [Fintype Gal(L/K)]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) :
    groupCohomology (chapter03MultiplicativeGaloisModule K L) 2 ≅
      ModuleCat.of ℤ (Additive (chapter03NormQuotient K L)) := by
  letI : NeZero 2 := ⟨by norm_num⟩
  let e2 : chapter03TateCohomology (chapter03MultiplicativeGaloisModule K L) 2 ≅
      groupCohomology (chapter03MultiplicativeGaloisModule K L) 2 :=
    (TateCohomology.isoGroupCohomology (R := ℤ) (G := Gal(L / K)) 2).app
      (chapter03MultiplicativeGaloisModule K L)
  let hp : chapter03TateCohomology (chapter03MultiplicativeGaloisModule K L) 2 ≅
      chapter03TateH0 (chapter03MultiplicativeGaloisModule K L) :=
    by
      convert chapter03_tate_periodicity (chapter03MultiplicativeGaloisModule K L) σ
        (chapter03_cyclic_extension_generator K L n σ hcyc) 0 using 1; norm_num
  exact e2.symm ≪≫ hp ≪≫
    chapter03_tate_h0_multiplicative_norm_quotient K L n σ hcyc

end

end LastLib.Book05LocalClassFieldTheory.Chapter03
