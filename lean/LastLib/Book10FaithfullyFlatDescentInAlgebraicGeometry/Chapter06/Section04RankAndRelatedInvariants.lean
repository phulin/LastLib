import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06.Dependencies
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06

noncomputable section

open TensorProduct

universe u v

/-! ## 6.4 Rank and related invariants -/

theorem fiberRank_isLocallyConstant
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M] :
    IsLocallyConstant (fiberRank (R := R) M) := by
  have h : fiberRank (R := R) M = Module.rankAtStalk M := by
    funext p
    exact fiberRank_eq_stalkRank p
  rw [h]
  exact Module.isLocallyConstant_rankAtStalk

theorem prime_lies_over_of_faithfullyFlat
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (p : PrimeSpectrum A) :
    ∃ q : PrimeSpectrum B, q.comap (algebraMap A B) = p := by
  exact (PrimeSpectrum.comap_surjective_of_faithfullyFlat p)

theorem fiberRank_baseChange
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.Finite A M] [Module.Flat A M]
    (q : PrimeSpectrum B) :
    fiberRank (R := B) (B ⊗[A] M) q =
      fiberRank (R := A) M (q.comap (algebraMap A B)) := by
  simpa [fiberRank] using
    (Module.rankAtStalk_baseChange (R := A) (M := M) q)

theorem hasConstantRank_baseChange_iff
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    [Module.Finite A M] [Module.Flat A M]
    (r : ℕ) :
    HasConstantRank (R := B) (B ⊗[A] M) r ↔ HasConstantRank (R := A) M r := by
  constructor
  · intro hB p
    obtain ⟨q, hq⟩ := prime_lies_over_of_faithfullyFlat (A := A) (B := B) p
    have h := hB q
    rw [fiberRank_baseChange (A := A) (B := B) (M := M) q, hq] at h
    exact h
  · intro hA q
    rw [fiberRank_baseChange (A := A) (B := B) (M := M) q]
    exact hA _

theorem hasRankIn_baseChange_iff
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    [Module.Finite A M] [Module.Flat A M]
    (ranks : Set ℕ) :
    HasRankIn (R := B) (B ⊗[A] M) ranks ↔ HasRankIn (R := A) M ranks := by
  constructor
  · intro hB p
    obtain ⟨q, hq⟩ := prime_lies_over_of_faithfullyFlat (A := A) (B := B) p
    have h := hB q
    rw [fiberRank_baseChange (A := A) (B := B) (M := M) q, hq] at h
    exact h
  · intro hA q
    rw [fiberRank_baseChange (A := A) (B := B) (M := M) q]
    exact hA _

/-- The fiberwise rank locus of a module. -/
def fiberRankLocus
    {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (ranks : Set ℕ) : Set (PrimeSpectrum R) :=
  {p | fiberRank (R := R) M p ∈ ranks}

theorem mem_fiberRankLocus_iff
    {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (ranks : Set ℕ) (p : PrimeSpectrum R) :
    p ∈ fiberRankLocus M ranks ↔ fiberRank (R := R) M p ∈ ranks :=
  Iff.rfl

theorem fiberRankLocus_baseChange
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.Finite A M] [Module.Flat A M]
    (ranks : Set ℕ) :
    fiberRankLocus (B ⊗[A] M) ranks =
      (PrimeSpectrum.comap (algebraMap A B)) ⁻¹' fiberRankLocus M ranks := by
  ext q
  simp only [fiberRankLocus, Set.mem_preimage, Set.mem_ofPred_eq]
  rw [fiberRank_baseChange (A := A) (B := B) (M := M) q]

/-- Faithfully flat descent of rank loci. -/
theorem fiberRankLocus_descends_of_faithfullyFlat
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    [Module.Finite A M] [Module.Flat A M]
    (ranks : Set ℕ) :
    (∀ q : PrimeSpectrum B, q ∈ fiberRankLocus (B ⊗[A] M) ranks) ↔
      ∀ p : PrimeSpectrum A, p ∈ fiberRankLocus M ranks := by
  change HasRankIn (R := B) (B ⊗[A] M) ranks ↔ HasRankIn (R := A) M ranks
  exact hasRankIn_baseChange_iff (A := A) (B := B) (M := M) ranks

/-! A finite presentation and its relation map.  The presentation is used only to compute the
Fitting ideal; `fittingIdeal_eq_of_presentation` below records independence of this choice. -/
structure FinitePresentationData
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] where
  generators : ℕ
  relations : ℕ
  presentation : (Fin generators → R) →ₗ[R] M
  relationMap : (Fin relations → R) →ₗ[R] (Fin generators → R)
  presentation_surjective : Function.Surjective presentation
  exact : Function.Exact relationMap presentation

noncomputable def finitePresentationData
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] :
    FinitePresentationData R M := by
  let h := Module.FinitePresentation.exists_fin' R M
  let n := Classical.choose h
  let hn := Classical.choose_spec h
  let m := Classical.choose hn
  let hm := Classical.choose_spec hn
  let f := Classical.choose hm
  let hf := Classical.choose_spec hm
  let g := Classical.choose hf
  let hfg := Classical.choose_spec hf
  exact
    { generators := n
      relations := m
      presentation := f
      relationMap := g
      presentation_surjective := hfg.1
      exact := hfg.2 }

/-- The ideal generated by the coordinate coefficients of the exterior-power relation map. -/
def fittingIdealOfPresentation
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (P : FinitePresentationData R M) (i : ℕ) : Ideal R :=
  Ideal.span
    {a : R |
      ∃ x : determinantModule R (Fin P.relations → R) (P.generators - i),
        ∃ φ : determinantModule R (Fin P.generators → R) (P.generators - i) →ₗ[R] R,
          a = φ
            (determinantMap (R := R) (M := (Fin P.relations → R))
              (N := (Fin P.generators → R)) (P.generators - i) P.relationMap x)}

/-- The `i`th Fitting ideal, computed from any chosen finite free presentation. -/
noncomputable def fittingIdeal
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] (i : ℕ) : Ideal R :=
  fittingIdealOfPresentation (finitePresentationData (R := R) (M := M)) i

theorem fittingIdeal_eq_of_presentation
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] (P : FinitePresentationData R M) (i : ℕ) :
    fittingIdeal (R := R) (M := M) i = fittingIdealOfPresentation P i := by
  sorry

theorem fittingIdeal_baseChange
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FinitePresentation A M] (i : ℕ) :
    fittingIdeal (R := B) (M := B ⊗[A] M) i =
      (fittingIdeal (R := A) (M := M) i).map (algebraMap A B) := by
  sorry

theorem ideal_comap_map_eq_self_of_faithfullyFlat
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (I : Ideal A) :
    (I.map (algebraMap A B)).comap (algebraMap A B) = I := by
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I

/-- The determinant criterion is stated as invertibility of the induced exterior-power map. -/
def IsDeterminantInvertible
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (r : ℕ) (f : M →ₗ[R] N) : Prop :=
  Function.Bijective (determinantMap r f)

theorem determinantMap_id
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (r : ℕ) :
    determinantMap r (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  exact exteriorPower.map_id

theorem determinantMap_comp
    {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (r : ℕ) (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    determinantMap r (g ∘ₗ f) = determinantMap r g ∘ₗ determinantMap r f := by
  exact exteriorPower.map_comp f g

private theorem finiteFree_determinantMap_bijective_iff
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (r : ℕ) (f : M →ₗ[R] N)
    (bM : Module.Basis (Fin r) R M) (bN : Module.Basis (Fin r) R N) :
    Function.Bijective f ↔ Function.Bijective (determinantMap r f) := by
  classical
  constructor
  · intro hf
    refine ⟨?_, exteriorPower.map_surjective hf.2⟩
    let e := LinearEquiv.ofBijective f hf
    exact exteriorPower.map_injective e.symm.toLinearMap (by
      apply LinearMap.ext
      intro x
      exact e.left_inv x)
  · intro hdet
    let bMdet := bM.exteriorPower r
    let bNdet := bN.exteriorPower r
    let s : Set.powersetCard (Fin r) r :=
      Set.powersetCard.ofFinEmb r (Fin r) (Function.Embedding.refl _)
    have hs (t : Set.powersetCard (Fin r) r) : t = s := by
      apply Set.powersetCard.eq_iff_subset.mpr
      intro i hi
      simp [s]
    let _ : Subsingleton (Set.powersetCard (Fin r) r) :=
      ⟨fun a b => (hs a).trans (hs b).symm⟩
    have huCoord :
        IsUnit (bNdet.repr ((LinearEquiv.ofBijective (determinantMap r f) hdet)
          (bMdet s)) s) := by
      have hu := LinearEquiv.isUnit_det
        (LinearEquiv.ofBijective (determinantMap r f) hdet) bMdet bNdet
      simpa [LinearMap.toMatrix_apply, Matrix.det_eq_elem_of_subsingleton _ s] using hu
    have he : Set.powersetCard.ofFinEmbEquiv.symm s = (OrderIso.refl _).toOrderEmbedding := by
      have h₁ := Finset.orderEmbOfFin_unique'
        (s := (Finset.univ : Finset (Fin r))) (k := r)
        (f := Set.powersetCard.ofFinEmbEquiv.symm s) (by simp) (by
          intro i
          simp)
      have h₂ := Finset.orderEmbOfFin_unique'
        (s := (Finset.univ : Finset (Fin r))) (k := r)
        (f := (OrderIso.refl _).toOrderEmbedding) (by simp) (by
          intro i
          simp)
      exact h₁.trans h₂.symm
    have hunit : IsUnit (bN.det (f ∘ bM)) := by
      rw [Module.Basis.det_apply]
      change IsUnit (Matrix.det (Matrix.of fun i j : Fin r => bN.repr (f (bM j)) i))
      have huCoord' :
          IsUnit (Matrix.det (Matrix.of fun i j : Fin r => bN.repr (f (bM i)) j)) := by
        simpa [bMdet, bNdet, exteriorPower.basis_repr_apply,
        exteriorPower.ιMultiDual_apply_ιMulti, exteriorPower.basis_apply,
        exteriorPower.ιMulti_family, determinantMap, he, Module.Basis.toMatrix,
        Module.Basis.toMatrix_apply,
        Matrix.det_transpose] using huCoord
      have hmat :
          Matrix.of (fun i j : Fin r => bN.repr (f (bM i)) j) =
            (Matrix.of (fun i j : Fin r => bN.repr (f (bM j)) i)).transpose := by
        rfl
      rw [hmat, Matrix.det_transpose] at huCoord'
      exact huCoord'
    have hbasis :
        LinearIndependent R (f ∘ bM) ∧ Submodule.span R (Set.range (f ∘ bM)) = ⊤ :=
      (bN.is_basis_iff_det).mpr hunit
    let b' : Module.Basis (Fin r) R N := Module.Basis.mk hbasis.1 hbasis.2.ge
    let e : M ≃ₗ[R] N := bM.repr.trans b'.repr.symm
    have heq : (e : M →ₗ[R] N) = f := by
      apply bM.ext
      intro i
      simp [e, b']
    rw [← heq]
    exact e.bijective

def DeterminantBaseChangeWitness
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] (r : ℕ) : Prop :=
  Nonempty
    (B ⊗[A] determinantModule A M r ≃ₗ[B]
      determinantModule B (B ⊗[A] M) r)

private noncomputable def determinantBaseChangeMap
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] (r : ℕ) :
    letI : Module A (determinantModule B (B ⊗[A] M) r) :=
      Module.compHom _ (algebraMap A B)
    determinantModule A M r →ₗ[A] determinantModule B (B ⊗[A] M) r := by
  letI : Module A (determinantModule B (B ⊗[A] M) r) :=
    Module.compHom _ (algebraMap A B)
  letI : IsScalarTower A B (determinantModule B (B ⊗[A] M) r) :=
    IsScalarTower.of_compHom A B _
  let altA : AlternatingMap A (B ⊗[A] M)
      (determinantModule B (B ⊗[A] M) r) (Fin r) :=
    { toMultilinearMap :=
        @MultilinearMap.restrictScalars A (Fin r)
          (fun _ : Fin r => B ⊗[A] M)
          (determinantModule B (B ⊗[A] M) r)
          _ _ _ _ _ B _ _ _ _ _ (IsScalarTower.of_compHom A B _)
          (exteriorPower.ιMulti B r).toMultilinearMap
      map_eq_zero_of_eq' := by
        intro v i j hij hne
        exact (exteriorPower.ιMulti B r).map_eq_zero_of_eq' v i j hij hne }
  exact exteriorPower.alternatingMapLinearEquiv
    (altA.compLinearMap (TensorProduct.mk A B M 1))

private theorem determinant_isBaseChange_of_finiteFree
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.Free A M] [Module.Finite A M]
    (r : ℕ) :
    letI : Module A (determinantModule B (B ⊗[A] M) r) :=
      Module.compHom _ (algebraMap A B)
    letI : IsScalarTower A B (determinantModule B (B ⊗[A] M) r) :=
      IsScalarTower.of_compHom A B _
    @IsBaseChange A (determinantModule A M r)
      (determinantModule B (B ⊗[A] M) r) B
      _ _ _ _ _ _ _ _ (IsScalarTower.of_compHom A B _)
      (determinantBaseChangeMap (A := A) (B := B) (M := M) r) := by
  let I := Module.Free.ChooseBasisIndex A M
  let b : Module.Basis I A M := Module.Free.chooseBasis A M
  let _ : Fintype I := Module.Free.ChooseBasisIndex.fintype A M
  let _ : LinearOrder I :=
    LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  let _ : Module A (determinantModule B (B ⊗[A] M) r) :=
    Module.compHom _ (algebraMap A B)
  let _ : IsScalarTower A B (determinantModule B (B ⊗[A] M) r) :=
    IsScalarTower.of_compHom A B _
  let ε : M →ₗ[A] B ⊗[A] M := TensorProduct.mk A B M 1
  let hε : IsBaseChange B ε := TensorProduct.isBaseChange A M B
  let bB : Module.Basis I B (B ⊗[A] M) := hε.basis b
  let bM := b.exteriorPower r
  let bMB := bB.exteriorPower r
  have hbMB :
      @IsBaseChange A (Set.powersetCard I r → A)
        (determinantModule B (B ⊗[A] M) r) B
        _ _ _ _ _ _ (Module.compHom _ (algebraMap A B)) _
        (IsScalarTower.of_compHom A B _)
        (Fintype.linearCombination A bMB) := by
    exact @IsBaseChange.of_fintype_basis B _
      (determinantModule B (B ⊗[A] M) r) _ _ A _ _
      (Module.compHom _ (algebraMap A B))
      (IsScalarTower.of_compHom A B _) (Set.powersetCard I r) bMB _
  let d := determinantBaseChangeMap (A := A) (B := B) (M := M) r
  have hmap : d = (Fintype.linearCombination A bMB).comp bM.equivFun.toLinearMap := by
    apply bM.ext
    intro s
    change d (bM s) =
      (Fintype.linearCombination A bMB) (bM.equivFun (bM s))
    have hsrepr : bM.equivFun (bM s) = Pi.single s 1 := by
      rw [Module.Basis.equivFun_apply]
      have hrepr : bM.repr (bM s) = Finsupp.single s 1 := by
        simpa [bM] using exteriorPower.basis_repr A r b s
      rw [hrepr]
      ext t
      simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
    rw [hsrepr, Fintype.linearCombination_apply_single, one_smul]
    have hbMs : bM s = exteriorPower.ιMulti_family A r b s := by
      simp [bM, exteriorPower.basis_apply]
    rw [hbMs]
    simp [d, determinantBaseChangeMap, exteriorPower.ιMulti_family]
    change (exteriorPower.ιMulti B r)
        (fun i => (TensorProduct.mk A B M 1)
          (b ((Set.powersetCard.ofFinEmbEquiv.symm s) i))) = bMB s
    rw [exteriorPower.basis_apply B r bB s]
    congr 1
    funext i
    simpa [ε] using
      (hε.basis_apply b (Set.powersetCard.ofFinEmbEquiv.symm s i)).symm
  have hcomp :
      @IsBaseChange A (determinantModule A M r)
        (determinantModule B (B ⊗[A] M) r) B
        _ _ _ _ _ _ (Module.compHom _ (algebraMap A B)) _
        (IsScalarTower.of_compHom A B _)
        ((Fintype.linearCombination A bMB).comp bM.equivFun.toLinearMap) := by
    exact @IsBaseChange.comp_equiv A (determinantModule A M r)
      (determinantModule B (B ⊗[A] M) r) B
      _ _ _ _ _ _ (Module.compHom _ (algebraMap A B)) _
      (IsScalarTower.of_compHom A B _)
      (Set.powersetCard I r → A) _ _ bM.equivFun
      (Fintype.linearCombination A bMB) hbMB
  simpa [d, hmap] using hcomp

private theorem determinantBaseChangeMap_naturality
    {A B M N : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [AddCommGroup N] [Algebra A B] [Module A M] [Module A N]
    (r : ℕ) (f : M →ₗ[A] N) :
    letI : Module A (determinantModule B (B ⊗[A] M) r) :=
      Module.compHom _ (algebraMap A B)
    letI : Module A (determinantModule B (B ⊗[A] N) r) :=
      Module.compHom _ (algebraMap A B)
    letI : IsScalarTower A B (determinantModule B (B ⊗[A] M) r) :=
      IsScalarTower.of_compHom A B _
    letI : IsScalarTower A B (determinantModule B (B ⊗[A] N) r) :=
      IsScalarTower.of_compHom A B _
    ∀ x : determinantModule A M r,
      determinantMap r (f.baseChange B)
          (determinantBaseChangeMap (A := A) (B := B) (M := M) r x) =
        determinantBaseChangeMap (A := A) (B := B) (M := N) r
          (determinantMap r f x) := by
  let _ : Module A (determinantModule B (B ⊗[A] M) r) :=
    Module.compHom _ (algebraMap A B)
  let _ : Module A (determinantModule B (B ⊗[A] N) r) :=
    Module.compHom _ (algebraMap A B)
  let _ : IsScalarTower A B (determinantModule B (B ⊗[A] M) r) :=
    IsScalarTower.of_compHom A B _
  let _ : IsScalarTower A B (determinantModule B (B ⊗[A] N) r) :=
    IsScalarTower.of_compHom A B _
  intro x
  let fB : determinantModule B (B ⊗[A] M) r →ₗ[A]
      determinantModule B (B ⊗[A] N) r :=
    { toFun := determinantMap r (f.baseChange B)
      map_add' := (determinantMap r (f.baseChange B)).map_add
      map_smul' := by
        intro a x
        change (determinantMap r (f.baseChange B))
            ((algebraMap A B a) • x) =
          (algebraMap A B a) • (determinantMap r (f.baseChange B)) x
        exact (determinantMap r (f.baseChange B)).map_smul _ _ }
  have hmap :
      fB.comp (determinantBaseChangeMap (A := A) (B := B) (M := M) r) =
        (determinantBaseChangeMap (A := A) (B := B) (M := N) r).comp
          (determinantMap r f) := by
    apply exteriorPower.linearMap_ext
    ext v
    simp [fB, determinantBaseChangeMap, determinantMap,
      AlternatingMap.compLinearMap_apply]
    change (exteriorPower.map r (f.baseChange B))
        ((exteriorPower.ιMulti B r)
          (fun i => (TensorProduct.mk A B M 1) (v i))) =
      (exteriorPower.ιMulti B r)
        (fun i => (TensorProduct.mk A B N 1) (f (v i)))
    rw [exteriorPower.map_apply_ιMulti]
    congr 1
  exact LinearMap.congr_fun hmap x

private theorem determinantBaseChange_isBaseChange
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.Finite A M] [Module.Projective A M]
    (r : ℕ) :
    letI : Module A (determinantModule B (B ⊗[A] M) r) :=
      Module.compHom _ (algebraMap A B)
    letI : IsScalarTower A B (determinantModule B (B ⊗[A] M) r) :=
      IsScalarTower.of_compHom A B _
    @IsBaseChange A (determinantModule A M r)
      (determinantModule B (B ⊗[A] M) r) B
      _ _ _ _ _ _ _ _ (IsScalarTower.of_compHom A B _)
      (determinantBaseChangeMap (A := A) (B := B) (M := M) r) := by
  let _ : Module A (determinantModule B (B ⊗[A] M) r) :=
    Module.compHom _ (algebraMap A B)
  let _ : IsScalarTower A B (determinantModule B (B ⊗[A] M) r) :=
    IsScalarTower.of_compHom A B _
  let hproj := Module.Finite.exists_comp_eq_id_of_projective A M
  let n := Classical.choose hproj
  let hnp := Classical.choose_spec hproj
  let p := Classical.choose hnp
  let hpiData := Classical.choose_spec hnp
  let i := Classical.choose hpiData
  have hpi : p.comp i = LinearMap.id := by
    exact (Classical.choose_spec hpiData).2.2
  let F := Fin n → A
  let _ : Module.Free A F := inferInstance
  let _ : Module.Finite A F := inferInstance
  let _ : Module A (determinantModule B (B ⊗[A] F) r) :=
    Module.compHom _ (algebraMap A B)
  let _ : IsScalarTower A B (determinantModule B (B ⊗[A] F) r) :=
    IsScalarTower.of_compHom A B _
  have hF :
      @IsBaseChange A (determinantModule A F r)
        (determinantModule B (B ⊗[A] F) r) B
        _ _ _ _ _ _ _ _ (IsScalarTower.of_compHom A B _)
        (determinantBaseChangeMap (A := A) (B := B) (M := F) r) := by
    exact determinant_isBaseChange_of_finiteFree
      (A := A) (B := B) (M := F) r
  let eF : B ⊗[A] determinantModule A F r ≃ₗ[B]
      determinantModule B (B ⊗[A] F) r :=
    @IsBaseChange.equiv A (determinantModule A F r)
      (determinantModule B (B ⊗[A] F) r) B
      _ _ _ _ _ _ _ _ (IsScalarTower.of_compHom A B _)
      (determinantBaseChangeMap (A := A) (B := B) (M := F) r) hF
  let hom : B ⊗[A] determinantModule A M r →ₗ[B]
      determinantModule B (B ⊗[A] M) r :=
    (determinantMap r (p.baseChange B)).comp
      (eF.toLinearMap.comp ((determinantMap r i).baseChange B))
  let inv : determinantModule B (B ⊗[A] M) r →ₗ[B]
      B ⊗[A] determinantModule A M r :=
    ((determinantMap r p).baseChange B).comp
      (eF.symm.toLinearMap.comp (determinantMap r (i.baseChange B)))
  let q : F →ₗ[A] F := i.comp p
  have heF_tmul (b : B) (x : determinantModule A F r) :
      eF (b ⊗ₜ[A] x) = b • determinantBaseChangeMap (A := A) (B := B) (M := F) r x := by
    simpa [eF] using
      (@IsBaseChange.equiv_tmul A (determinantModule A F r)
        (determinantModule B (B ⊗[A] F) r) B
        _ _ _ _ _ _ _ _ (IsScalarTower.of_compHom A B _)
        (determinantBaseChangeMap (A := A) (B := B) (M := F) r) hF b x)
  have hq :
      eF.toLinearMap.comp ((determinantMap r q).baseChange B) =
        (determinantMap r (q.baseChange B)).comp eF.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b x =>
        simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul]
        change eF (b ⊗ₜ[A] (determinantMap r q) x) =
          (determinantMap r (q.baseChange B))
            (eF (b ⊗ₜ[A] x))
        rw [heF_tmul, heF_tmul, map_smul]
        rw [determinantBaseChangeMap_naturality
          (A := A) (B := B) (M := F) (N := F) r q x]
    | add x y hx hy =>
        simp only [LinearMap.comp_apply] at hx hy ⊢
        simp only [map_add, hx, hy]
  have hpiB :
      p.baseChange B ∘ₗ i.baseChange B = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hpi, LinearMap.baseChange_id]
  have hpiA_det :
      determinantMap r p ∘ₗ determinantMap r i = LinearMap.id := by
    rw [← determinantMap_comp, hpi, determinantMap_id]
  have hpiB_det :
      determinantMap r (p.baseChange B) ∘ₗ determinantMap r (i.baseChange B) =
        LinearMap.id := by
    rw [← determinantMap_comp, hpiB, determinantMap_id]
  have hpiA_det_base :
      (determinantMap r p).baseChange B ∘ₗ
          (determinantMap r i).baseChange B = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hpiA_det, LinearMap.baseChange_id]
  have hqA :
      (determinantMap r q).baseChange B =
        (determinantMap r i).baseChange B ∘ₗ
          (determinantMap r p).baseChange B := by
    change (determinantMap r (i.comp p)).baseChange B = _
    rw [determinantMap_comp, LinearMap.baseChange_comp]
  have hqB :
      determinantMap r (q.baseChange B) =
        determinantMap r (i.baseChange B) ∘ₗ
          determinantMap r (p.baseChange B) := by
    change determinantMap r ((i.comp p).baseChange B) = _
    rw [LinearMap.baseChange_comp, determinantMap_comp]
  have hqA_i :
      (determinantMap r q).baseChange B ∘ₗ
          (determinantMap r i).baseChange B =
        (determinantMap r i).baseChange B := by
    rw [hqA, LinearMap.comp_assoc, hpiA_det_base, LinearMap.comp_id]
  have hqB_i :
      determinantMap r (q.baseChange B) ∘ₗ
          determinantMap r (i.baseChange B) =
        determinantMap r (i.baseChange B) := by
    rw [hqB, LinearMap.comp_assoc, hpiB_det, LinearMap.comp_id]
  have hee :
      eF.toLinearMap.comp eF.symm.toLinearMap = LinearMap.id := by
    ext z
    simp
  have hee' :
      eF.symm.toLinearMap.comp eF.toLinearMap = LinearMap.id := by
    ext z
    simp
  have hqA_apply (x : B ⊗[A] determinantModule A F r) :
      (determinantMap r q).baseChange B x =
        (determinantMap r i).baseChange B
          ((determinantMap r p).baseChange B x) := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hqA x
  have hq_apply (x : B ⊗[A] determinantModule A F r) :
      eF.toLinearMap ((determinantMap r q).baseChange B x) =
        determinantMap r (q.baseChange B) (eF.toLinearMap x) := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hq x
  have hqB_i_apply (x : determinantModule B (B ⊗[A] M) r) :
      determinantMap r (q.baseChange B)
          (determinantMap r (i.baseChange B) x) =
        determinantMap r (i.baseChange B) x := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hqB_i x
  have hpiB_det_apply (x : determinantModule B (B ⊗[A] M) r) :
      determinantMap r (p.baseChange B)
          (determinantMap r (i.baseChange B) x) = x := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun hpiB_det x
  have hee_apply (x : determinantModule B (B ⊗[A] F) r) :
      eF.toLinearMap (eF.symm.toLinearMap x) = x := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun hee x
  have hqB_comp_apply (x : determinantModule B (B ⊗[A] F) r) :
      determinantMap r (q.baseChange B) x =
        determinantMap r (i.baseChange B)
          (determinantMap r (p.baseChange B) x) := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hqB x
  have hqA_i_apply (x : B ⊗[A] determinantModule A M r) :
      (determinantMap r q).baseChange B
          ((determinantMap r i).baseChange B x) =
        (determinantMap r i).baseChange B x := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hqA_i x
  have hee'_apply (x : B ⊗[A] determinantModule A F r) :
      eF.symm.toLinearMap (eF.toLinearMap x) = x := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun hee' x
  have hpiA_det_base_apply (x : B ⊗[A] determinantModule A M r) :
      (determinantMap r p).baseChange B
          ((determinantMap r i).baseChange B x) = x := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun hpiA_det_base x
  have hhom_tmul (x : determinantModule A M r) :
      hom (1 ⊗ₜ[A] x) =
        determinantBaseChangeMap (A := A) (B := B) (M := M) r x := by
    dsimp [hom]
    rw [heF_tmul]
    rw [← determinantBaseChangeMap_naturality
      (A := A) (B := B) (M := M) (N := F) r i x]
    simpa only [one_smul] using
      hpiB_det_apply
        (determinantBaseChangeMap (A := A) (B := B) (M := M) r x)
  exact @IsBaseChange.of_equiv A (determinantModule A M r)
    (determinantModule B (B ⊗[A] M) r) B
    _ _ _ _ _ _ _ _ (IsScalarTower.of_compHom A B _)
    (determinantBaseChangeMap (A := A) (B := B) (M := M) r)
    (LinearEquiv.ofLinearMap hom inv (by
    dsimp [hom, inv]
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply]
    change determinantMap r (p.baseChange B)
        (eF.toLinearMap ((determinantMap r i).baseChange B
          ((determinantMap r p).baseChange B
            (eF.symm.toLinearMap (determinantMap r (i.baseChange B) z))))) = z
    rw [← hqA_apply, hq_apply]
    rw [hee_apply, hqB_i_apply, hpiB_det_apply]) (by
    dsimp [hom, inv]
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply]
    change (determinantMap r p).baseChange B
        (eF.symm.toLinearMap
          (determinantMap r (i.baseChange B)
            (determinantMap r (p.baseChange B)
              (eF.toLinearMap ((determinantMap r i).baseChange B z))))) = z
    rw [← hqB_comp_apply, ← hq_apply, hee'_apply, hqA_i_apply,
      hpiA_det_base_apply])) hhom_tmul

theorem determinantModule_commutes_with_baseChange
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.Finite A M] [Module.Projective A M]
    (r : ℕ) :
    DeterminantBaseChangeWitness (A := A) (B := B) (M := M) r := by
  let _ : Module A (determinantModule B (B ⊗[A] M) r) :=
    Module.compHom _ (algebraMap A B)
  let _ : IsScalarTower A B (determinantModule B (B ⊗[A] M) r) :=
    IsScalarTower.of_compHom A B _
  have h := determinantBaseChange_isBaseChange (A := A) (B := B) (M := M) r
  exact ⟨@IsBaseChange.equiv A (determinantModule A M r)
    (determinantModule B (B ⊗[A] M) r) B
    _ _ _ _ _ _ _ _ (IsScalarTower.of_compHom A B _)
    (determinantBaseChangeMap (A := A) (B := B) (M := M) r) h⟩

theorem determinantMap_commutes_with_baseChange
    {A B M N : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [AddCommGroup N] [Algebra A B] [Module A M] [Module A N]
    [Module.Finite A M] [Module.Projective A M]
    [Module.Finite A N] [Module.Projective A N]
    (r : ℕ) (f : M →ₗ[A] N) :
    ∃ (eM : B ⊗[A] determinantModule A M r ≃ₗ[B]
        determinantModule B (B ⊗[A] M) r)
      (eN : B ⊗[A] determinantModule A N r ≃ₗ[B]
        determinantModule B (B ⊗[A] N) r),
      determinantMap r (f.baseChange B) ∘ₗ eM.toLinearMap =
        eN.toLinearMap ∘ₗ (determinantMap r f).baseChange B := by
  let _ : Module A (determinantModule B (B ⊗[A] M) r) :=
    Module.compHom _ (algebraMap A B)
  let _ : IsScalarTower A B (determinantModule B (B ⊗[A] M) r) :=
    IsScalarTower.of_compHom A B _
  let _ : Module A (determinantModule B (B ⊗[A] N) r) :=
    Module.compHom _ (algebraMap A B)
  let _ : IsScalarTower A B (determinantModule B (B ⊗[A] N) r) :=
    IsScalarTower.of_compHom A B _
  have hM := determinantBaseChange_isBaseChange (A := A) (B := B) (M := M) r
  have hN := determinantBaseChange_isBaseChange (A := A) (B := B) (M := N) r
  let eM : B ⊗[A] determinantModule A M r ≃ₗ[B]
      determinantModule B (B ⊗[A] M) r :=
    @IsBaseChange.equiv A (determinantModule A M r)
      (determinantModule B (B ⊗[A] M) r) B
      _ _ _ _ _ _ _ _ (IsScalarTower.of_compHom A B _)
      (determinantBaseChangeMap (A := A) (B := B) (M := M) r) hM
  let eN : B ⊗[A] determinantModule A N r ≃ₗ[B]
      determinantModule B (B ⊗[A] N) r :=
    @IsBaseChange.equiv A (determinantModule A N r)
      (determinantModule B (B ⊗[A] N) r) B
      _ _ _ _ _ _ _ _ (IsScalarTower.of_compHom A B _)
      (determinantBaseChangeMap (A := A) (B := B) (M := N) r) hN
  have hM_tmul (b : B) (x : determinantModule A M r) :
      eM (b ⊗ₜ[A] x) =
        b • determinantBaseChangeMap (A := A) (B := B) (M := M) r x := by
    simpa [eM] using
      (@IsBaseChange.equiv_tmul A (determinantModule A M r)
        (determinantModule B (B ⊗[A] M) r) B
        _ _ _ _ _ _ _ _ (IsScalarTower.of_compHom A B _)
        (determinantBaseChangeMap (A := A) (B := B) (M := M) r) hM b x)
  have hN_tmul (b : B) (x : determinantModule A N r) :
      eN (b ⊗ₜ[A] x) =
        b • determinantBaseChangeMap (A := A) (B := B) (M := N) r x := by
    simpa [eN] using
      (@IsBaseChange.equiv_tmul A (determinantModule A N r)
        (determinantModule B (B ⊗[A] N) r) B
        _ _ _ _ _ _ _ _ (IsScalarTower.of_compHom A B _)
        (determinantBaseChangeMap (A := A) (B := B) (M := N) r) hN b x)
  refine ⟨eM, eN, ?_⟩
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul]
      change determinantMap r (f.baseChange B) (eM (b ⊗ₜ[A] x)) =
        eN (b ⊗ₜ[A] (determinantMap r f x))
      rw [hM_tmul, hN_tmul, map_smul]
      rw [determinantBaseChangeMap_naturality
        (A := A) (B := B) (M := M) (N := N) r f x]
  | add x y hx hy =>
      simp only [LinearMap.comp_apply] at hx hy ⊢
      simp only [map_add, hx, hy]

theorem finiteProjective_determinantMap_bijective_iff
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.FinitePresentation R M]
    [Module.FinitePresentation R N] [Module.Flat R M] [Module.Flat R N]
    (r : ℕ) (f : M →ₗ[R] N)
    (hM : HasConstantRank (R := R) M r) (hN : HasConstantRank (R := R) N r) :
    Function.Bijective f ↔ IsDeterminantInvertible r f := by
  constructor
  · intro hf
    change Function.Bijective (determinantMap r f)
    let e := LinearEquiv.ofBijective f hf
    refine ⟨?_, exteriorPower.map_surjective hf.2⟩
    exact exteriorPower.map_injective e.symm.toLinearMap (by
      apply LinearMap.ext
      intro x
      exact e.left_inv x)
  · intro hdet
    let _ : Module.Projective R M := Module.Flat.projective_of_finitePresentation
    let _ : Module.Projective R N := Module.Flat.projective_of_finitePresentation
    change Function.Bijective (determinantMap r f) at hdet
    apply bijective_of_localized_maximal f
    intro J hJ
    let p : PrimeSpectrum R := ⟨J, hJ.isPrime⟩
    have hMfin : Module.finrank (Localization.AtPrime J)
        (LocalizedModule J.primeCompl M) = r := by
      simpa [fiberRank, Module.rankAtStalk, p] using hM p
    have hNfin : Module.finrank (Localization.AtPrime J)
        (LocalizedModule J.primeCompl N) = r := by
      simpa [fiberRank, Module.rankAtStalk, p] using hN p
    let _ : Module.Free (Localization.AtPrime J)
        (LocalizedModule J.primeCompl M) := Module.free_of_flat_of_isLocalRing
    let _ : Module.Free (Localization.AtPrime J)
        (LocalizedModule J.primeCompl N) := Module.free_of_flat_of_isLocalRing
    let bM : Module.Basis (Fin r) (Localization.AtPrime J)
        (LocalizedModule J.primeCompl M) :=
      Module.finBasisOfFinrankEq (Localization.AtPrime J)
        (LocalizedModule J.primeCompl M) hMfin
    let bN : Module.Basis (Fin r) (Localization.AtPrime J)
        (LocalizedModule J.primeCompl N) :=
      Module.finBasisOfFinrankEq (Localization.AtPrime J)
        (LocalizedModule J.primeCompl N) hNfin
    let eMloc := LocalizedModule.equivTensorProduct J.primeCompl M
    let eNloc := LocalizedModule.equivTensorProduct J.primeCompl N
    let bMt : Module.Basis (Fin r) (Localization.AtPrime J)
        (Localization.AtPrime J ⊗[R] M) := bM.map eMloc
    let bNt : Module.Basis (Fin r) (Localization.AtPrime J)
        (Localization.AtPrime J ⊗[R] N) := bN.map eNloc
    obtain ⟨eMdet, eNdet, hcomm⟩ := determinantMap_commutes_with_baseChange
      (A := R) (B := Localization.AtPrime J) (M := M) (N := N) r f
    have hdetBase : Function.Bijective
        ((determinantMap r f).baseChange (Localization.AtPrime J)) := by
      let e := LinearEquiv.ofBijective (determinantMap r f) hdet
      have he : e.toLinearMap = determinantMap r f := by
        rfl
      have hebase :
          (e.baseChange R (Localization.AtPrime J)
            (determinantModule R M r) (determinantModule R N r)).toLinearMap =
            (determinantMap r f).baseChange (Localization.AtPrime J) := by
        rw [LinearEquiv.coe_baseChange, he]
      have hE : Function.Bijective
          (e.baseChange R (Localization.AtPrime J)
            (determinantModule R M r) (determinantModule R N r)).toLinearMap :=
        (e.baseChange R (Localization.AtPrime J)
          (determinantModule R M r) (determinantModule R N r)).bijective
      rw [hebase] at hE
      exact hE
    have hdetLocal : Function.Bijective
        (determinantMap r (f.baseChange (Localization.AtPrime J))) := by
      have hcomp : Function.Bijective
          (eNdet.toLinearMap ∘ₗ (determinantMap r f).baseChange
            (Localization.AtPrime J)) :=
        eNdet.bijective.comp hdetBase
      have hcomp' : Function.Bijective
          (determinantMap r (f.baseChange (Localization.AtPrime J)) ∘ₗ
            eMdet.toLinearMap) := by
        simpa [hcomm] using hcomp
      constructor
      · intro x y hxy
        obtain ⟨u, hu⟩ := eMdet.surjective x
        obtain ⟨v, hv⟩ := eMdet.surjective y
        have huv : u = v := by
          apply hcomp'.1
          simp only [LinearMap.comp_apply]
          calc
            determinantMap r (f.baseChange (Localization.AtPrime J)) (eMdet u) =
                determinantMap r (f.baseChange (Localization.AtPrime J)) x :=
              congrArg _ hu
            _ = determinantMap r (f.baseChange (Localization.AtPrime J)) y := hxy
            _ = determinantMap r (f.baseChange (Localization.AtPrime J)) (eMdet v) :=
              (congrArg _ hv).symm
        calc
          x = eMdet u := hu.symm
          _ = eMdet v := congrArg eMdet huv
          _ = y := hv
      · intro y
        obtain ⟨u, hu⟩ := hcomp'.2 y
        exact ⟨eMdet u, hu⟩
    have hbase : Function.Bijective (f.baseChange (Localization.AtPrime J)) :=
      (finiteFree_determinantMap_bijective_iff r
        (f.baseChange (Localization.AtPrime J)) bMt bNt).2 hdetLocal
    have hlocal_comm :
        eNloc.toLinearMap ∘ₗ LocalizedModule.map J.primeCompl f =
          f.baseChange (Localization.AtPrime J) ∘ₗ eMloc.toLinearMap := by
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.linearMap_ext J.primeCompl
        (LocalizedModule.mkLinearMap J.primeCompl M)
        (TensorProduct.mk R (Localization.AtPrime J) N 1)
      ext x
      simp [eMloc, eNloc, LinearMap.comp_apply]
    have hcomp : Function.Bijective
        (f.baseChange (Localization.AtPrime J) ∘ₗ eMloc.toLinearMap) :=
      hbase.comp eMloc.bijective
    have hcomp' : Function.Bijective
        (eNloc.toLinearMap ∘ₗ LocalizedModule.map J.primeCompl f) := by
      simpa [hlocal_comm] using hcomp
    constructor
    · intro x y hxy
      apply hcomp'.1
      simp only [LinearMap.comp_apply]
      rw [hxy]
    · intro y
      obtain ⟨x, hx⟩ := hcomp'.2 (eNloc y)
      exact ⟨x, eNloc.injective (by simpa [LinearMap.comp_apply] using hx)⟩

theorem determinant_invertible_detected_after_faithfullyFlat_baseChange
    {A B M N : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [AddCommGroup N] [Algebra A B] [Module A M] [Module A N]
    [Module.FaithfullyFlat A B] [Module.FinitePresentation A M]
    [Module.FinitePresentation A N] [Module.Flat A M] [Module.Flat A N]
    (r : ℕ) (f : M →ₗ[A] N) :
    IsDeterminantInvertible r f ↔
      IsDeterminantInvertible r (f.baseChange B) := by
  let _ : Module.Projective A M := Module.Flat.projective_of_finitePresentation
  let _ : Module.Projective A N := Module.Flat.projective_of_finitePresentation
  change Function.Bijective (determinantMap r f) ↔
    Function.Bijective (determinantMap r (f.baseChange B))
  obtain ⟨eM, eN, hcomm⟩ := determinantMap_commutes_with_baseChange
    (A := A) (B := B) (M := M) (N := N) r f
  have hconj :
      Function.Bijective (determinantMap r (f.baseChange B)) ↔
        Function.Bijective ((determinantMap r f).baseChange B) := by
    constructor
    · intro hB
      have hcomp :
          Function.Bijective
            (determinantMap r (f.baseChange B) ∘ₗ eM.toLinearMap) :=
        hB.comp eM.bijective
      have hcomp' :
          Function.Bijective
            (eN.toLinearMap ∘ₗ (determinantMap r f).baseChange B) := by
        simpa [hcomm] using hcomp
      constructor
      · intro x y hxy
        apply hcomp'.1
        simp only [LinearMap.comp_apply]
        rw [hxy]
      · intro y
        obtain ⟨x, hx⟩ := hcomp'.2 (eN y)
        exact ⟨x, eN.injective (by simpa [LinearMap.comp_apply] using hx)⟩
    · intro hA
      have hcomp :
          Function.Bijective
            (eN.toLinearMap ∘ₗ (determinantMap r f).baseChange B) :=
        eN.bijective.comp hA
      have hcomp' :
          Function.Bijective
            (determinantMap r (f.baseChange B) ∘ₗ eM.toLinearMap) := by
        simpa [hcomm] using hcomp
      constructor
      · intro x y hxy
        obtain ⟨u, hu⟩ := eM.surjective x
        obtain ⟨v, hv⟩ := eM.surjective y
        have huv : u = v := by
          apply hcomp'.1
          simp only [LinearMap.comp_apply]
          calc
            determinantMap r (f.baseChange B) (eM u) =
                determinantMap r (f.baseChange B) x := congrArg _ hu
            _ = determinantMap r (f.baseChange B) y := hxy
            _ = determinantMap r (f.baseChange B) (eM v) := (congrArg _ hv).symm
        calc
          x = eM u := hu.symm
          _ = eM v := congrArg eM huv
          _ = y := hv
      · intro y
        obtain ⟨u, hu⟩ := hcomp'.2 y
        exact ⟨eM u, hu⟩
  rw [hconj]
  simpa only [LinearMap.baseChange_eq_ltensor] using
    (Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B
      (determinantMap r f)).symm

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06
