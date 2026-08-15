import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06.Dependencies
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06

noncomputable section

open TensorProduct

universe u v

/-! ## 6.4 Rank and related invariants -/

local instance chapter06SumLinearOrder (α : Type*) [LinearOrder α] :
    LinearOrder (α ⊕ Unit) :=
  LinearOrder.lift' (toLex : (α ⊕ Unit) ≃ (α ⊕ₗ Unit)) toLex.injective

local instance chapter06SumPreorder (α : Type*) [LinearOrder α] :
    Preorder (α ⊕ Unit) :=
  (chapter06SumLinearOrder α).toPreorder

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

private def determinantCoefficientIdeal
    {R U V : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V] (k : ℕ) (f : U →ₗ[R] V) : Ideal R :=
  Ideal.span
    {a : R |
      ∃ x : determinantModule R U k,
        ∃ φ : determinantModule R V k →ₗ[R] R,
          a = φ (determinantMap k f x)}

private theorem determinantCoefficientIdeal_comp_le_left
    {R U V W : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (k : ℕ) (f : U →ₗ[R] V) (g : V →ₗ[R] W) :
    determinantCoefficientIdeal k (g ∘ₗ f) ≤ determinantCoefficientIdeal k f := by
  rw [determinantCoefficientIdeal, Ideal.span_le]
  rintro a ⟨x, φ, rfl⟩
  apply Ideal.subset_span
  refine ⟨x, φ.comp (determinantMap k g), ?_⟩
  change φ ((exteriorPower.map k (g ∘ₗ f)) x) =
    (φ.comp (exteriorPower.map k g)) ((exteriorPower.map k f) x)
  rw [exteriorPower.map_comp]
  rfl

private theorem determinantCoefficientIdeal_comp_le_right
    {R U V W : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (k : ℕ) (f : U →ₗ[R] V) (g : V →ₗ[R] W) :
    determinantCoefficientIdeal k (g ∘ₗ f) ≤ determinantCoefficientIdeal k g := by
  rw [determinantCoefficientIdeal, Ideal.span_le]
  rintro a ⟨x, φ, rfl⟩
  apply Ideal.subset_span
  refine ⟨(determinantMap k f) x, φ, ?_⟩
  change φ ((exteriorPower.map k (g ∘ₗ f)) x) = φ ((exteriorPower.map k g) ((exteriorPower.map k f) x))
  rw [exteriorPower.map_comp]
  rfl

private theorem determinantCoefficientIdeal_comp_eq_of_equiv
    {R U V U' V' : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup U'] [Module R U'] [AddCommGroup V'] [Module R V']
    (k : ℕ) (f : U →ₗ[R] V) (eU : U' ≃ₗ[R] U) (eV : V ≃ₗ[R] V') :
    determinantCoefficientIdeal k (eV.toLinearMap ∘ₗ f ∘ₗ eU.toLinearMap) =
      determinantCoefficientIdeal k f := by
  apply le_antisymm
  · calc
      determinantCoefficientIdeal k (eV.toLinearMap ∘ₗ f ∘ₗ eU.toLinearMap) ≤
          determinantCoefficientIdeal k (f ∘ₗ eU.toLinearMap) := by
            simpa only [LinearMap.comp_assoc] using
              determinantCoefficientIdeal_comp_le_left k
                (f ∘ₗ eU.toLinearMap) eV.toLinearMap
      _ ≤ determinantCoefficientIdeal k f :=
        determinantCoefficientIdeal_comp_le_right
          (R := R) (U := U') (V := U) (W := V) k eU.toLinearMap f
  · have h₁ :
        determinantCoefficientIdeal k
            (eV.symm.toLinearMap ∘ₗ
              (eV.toLinearMap ∘ₗ f ∘ₗ eU.toLinearMap) ∘ₗ eU.symm.toLinearMap) ≤
          determinantCoefficientIdeal k
            (eV.toLinearMap ∘ₗ f ∘ₗ eU.toLinearMap) := by
      calc
        determinantCoefficientIdeal k
            (eV.symm.toLinearMap ∘ₗ
              (eV.toLinearMap ∘ₗ f ∘ₗ eU.toLinearMap) ∘ₗ eU.symm.toLinearMap) ≤
            determinantCoefficientIdeal k
              ((eV.toLinearMap ∘ₗ f ∘ₗ eU.toLinearMap) ∘ₗ eU.symm.toLinearMap) := by
                simpa only [LinearMap.comp_assoc] using
                  determinantCoefficientIdeal_comp_le_left k
                    ((eV.toLinearMap ∘ₗ f ∘ₗ eU.toLinearMap) ∘ₗ eU.symm.toLinearMap)
                    eV.symm.toLinearMap
        _ ≤ determinantCoefficientIdeal k
              (eV.toLinearMap ∘ₗ f ∘ₗ eU.toLinearMap) :=
          determinantCoefficientIdeal_comp_le_right
            (R := R) (U := U) (V := U') (W := V') k
            eU.symm.toLinearMap
            (eV.toLinearMap ∘ₗ f ∘ₗ eU.toLinearMap)
    have hcomp :
        eV.symm.toLinearMap ∘ₗ
            (eV.toLinearMap ∘ₗ f ∘ₗ eU.toLinearMap) ∘ₗ eU.symm.toLinearMap = f := by
      ext x
      simp [LinearMap.comp_apply]
    rw [hcomp] at h₁
    exact h₁

private theorem fittingIdealOfPresentation_eq_determinantCoefficientIdeal
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (P : FinitePresentationData R M) (i : ℕ) :
    fittingIdealOfPresentation P i =
      determinantCoefficientIdeal (P.generators - i) P.relationMap := by
  rfl

private theorem determinantCoefficientIdeal_eq_span_basisCoords
    {R U V : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (k : ℕ) (f : U →ₗ[R] V)
    (bU : Module.Basis ι R (determinantModule R U k))
    (bV : Module.Basis κ R (determinantModule R V k)) :
    determinantCoefficientIdeal k f =
      Ideal.span
        {a : R | ∃ i : ι, ∃ j : κ,
          a = bV.coord j (determinantMap k f (bU i))} := by
  apply le_antisymm
  · rw [determinantCoefficientIdeal, Ideal.span_le]
    rintro a ⟨x, φ, rfl⟩
    rw [← bU.sum_repr x]
    simp only [map_sum, map_smul]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    rw [← bV.sum_repr (determinantMap k f (bU i))]
    simp only [map_sum, map_smul]
    apply Submodule.sum_mem
    intro j hj
    rw [smul_eq_mul, mul_comm]
    apply Ideal.mul_mem_left
    apply Ideal.subset_span
    refine ⟨i, j, ?_⟩
    rfl
  · rw [Ideal.span_le]
    rintro a ⟨i, j, rfl⟩
    exact Ideal.subset_span ⟨bU i, bV.coord j, rfl⟩

private noncomputable def piBaseChangeEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) :
    B ⊗[A] (Fin n → A) ≃ₗ[B] (Fin n → B) := by
  letI : IsScalarTower A B (Fin n → B) :=
    IsScalarTower.of_algebraMap_smul (fun a x => by
      ext j
      simp [Algebra.smul_def])
  let c := Fintype.linearCombination A (Pi.basisFun B (Fin n))
  let h : IsBaseChange B c := IsBaseChange.of_fintype_basis A (Pi.basisFun B (Fin n))
  exact h.equiv

private theorem piBaseChangeEquiv_tmul
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)
    (b : B) (x : Fin n → A) :
    piBaseChangeEquiv (A := A) (B := B) n (b ⊗ₜ[A] x) =
      b • (fun j => algebraMap A B (x j)) := by
  let _ : IsScalarTower A B (Fin n → B) :=
    IsScalarTower.of_algebraMap_smul (fun a x => by
      ext j
      simp [Algebra.smul_def])
  let c := Fintype.linearCombination A (Pi.basisFun B (Fin n))
  let h : IsBaseChange B c := IsBaseChange.of_fintype_basis A (Pi.basisFun B (Fin n))
  have hh := h.equiv_tmul b x
  change h.equiv (b ⊗ₜ[A] x) = _ at hh
  rw [show piBaseChangeEquiv (A := A) (B := B) n = h.equiv by rfl]
  rw [hh]
  ext j
  simp [c, Fintype.linearCombination_apply, Algebra.smul_def, Pi.single_apply]

private theorem piBaseChangeEquiv_symm_apply_single
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) (j : Fin n) :
    (piBaseChangeEquiv (A := A) (B := B) n).symm (Pi.single j 1) =
      1 ⊗ₜ[A] (Pi.single j 1) := by
  apply (piBaseChangeEquiv (A := A) (B := B) n).injective
  rw [(piBaseChangeEquiv (A := A) (B := B) n).apply_symm_apply]
  rw [piBaseChangeEquiv_tmul]
  ext k
  simp [Pi.single_apply]

private theorem baseChange_pi_apply_basis
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {n m : ℕ} (f : (Fin n → A) →ₗ[A] (Fin m → A)) (j : Fin n) :
    ((piBaseChangeEquiv (A := A) (B := B) m).toLinearMap ∘ₗ
      (f.baseChange B) ∘ₗ
        (piBaseChangeEquiv (A := A) (B := B) n).symm.toLinearMap)
        (Pi.basisFun B (Fin n) j) =
      (fun k => algebraMap A B (f (Pi.basisFun A (Fin n) j) k)) := by
  rw [Pi.basisFun_apply]
  simp only [LinearMap.comp_apply]
  change piBaseChangeEquiv (A := A) (B := B) m
      ((f.baseChange B)
        ((piBaseChangeEquiv (A := A) (B := B) n).symm (Pi.single j 1))) = _
  rw [piBaseChangeEquiv_symm_apply_single]
  simp only [LinearMap.baseChange_tmul]
  rw [piBaseChangeEquiv_tmul]
  ext k
  simp

private theorem determinantCoefficientIdeal_baseChange_pi
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {n m : ℕ} (k : ℕ) (f : (Fin n → A) →ₗ[A] (Fin m → A)) :
    determinantCoefficientIdeal (R := B) k
        ((piBaseChangeEquiv (A := A) (B := B) m).toLinearMap ∘ₗ
          (f.baseChange B) ∘ₗ
            (piBaseChangeEquiv (A := A) (B := B) n).symm.toLinearMap) =
      (determinantCoefficientIdeal (R := A) k f).map (algebraMap A B) := by
  let fB : (Fin n → B) →ₗ[B] (Fin m → B) :=
    (piBaseChangeEquiv (A := A) (B := B) m).toLinearMap ∘ₗ
      (f.baseChange B) ∘ₗ
        (piBaseChangeEquiv (A := A) (B := B) n).symm.toLinearMap
  let bUA := (Pi.basisFun A (Fin n)).exteriorPower k
  let bVA := (Pi.basisFun A (Fin m)).exteriorPower k
  let bUB := (Pi.basisFun B (Fin n)).exteriorPower k
  let bVB := (Pi.basisFun B (Fin m)).exteriorPower k
  rw [determinantCoefficientIdeal_eq_span_basisCoords k fB bUB bVB,
    determinantCoefficientIdeal_eq_span_basisCoords k f bUA bVA]
  have hentry (i : Set.powersetCard (Fin n) k)
      (j : Set.powersetCard (Fin m) k) :
      bVB.coord j (determinantMap k fB (bUB i)) =
        algebraMap A B (bVA.coord j (determinantMap k f (bUA i))) := by
    simp [fB, bUA, bVA, bUB, bVB, exteriorPower.basis_coord,
      exteriorPower.ιMultiDual_apply_ιMulti, exteriorPower.basis_apply,
      exteriorPower.ιMulti_family, determinantMap]
    rw [RingHom.map_det]
    congr 1
    ext i₁ j₁
    simpa [fB, Pi.basisFun_apply] using
      congrFun
        (baseChange_pi_apply_basis f
          (Set.powersetCard.ofFinEmbEquiv.symm i i₁))
        (Set.powersetCard.ofFinEmbEquiv.symm j j₁)
  have hset :
      {a : B | ∃ i, ∃ j,
          a = bVB.coord j (determinantMap k fB (bUB i))} =
        (algebraMap A B) '' {a : A | ∃ i, ∃ j,
          a = bVA.coord j (determinantMap k f (bUA i))} := by
    ext a
    constructor
    · rintro ⟨i, j, rfl⟩
      exact ⟨bVA.coord j (determinantMap k f (bUA i)), ⟨i, j, rfl⟩, (hentry i j).symm⟩
    · rintro ⟨a, ⟨i, j, rfl⟩, rfl⟩
      exact ⟨i, j, (hentry i j).symm⟩
  rw [Ideal.map_span, hset]

private theorem determinantCoefficientIdeal_baseChange
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {n m : ℕ} (k : ℕ) (f : (Fin n → A) →ₗ[A] (Fin m → A)) :
    determinantCoefficientIdeal (R := B) k (f.baseChange B) =
      (determinantCoefficientIdeal (R := A) k f).map (algebraMap A B) := by
  let e0 := piBaseChangeEquiv (A := A) (B := B) m
  let e1 := piBaseChangeEquiv (A := A) (B := B) n
  calc
    determinantCoefficientIdeal (R := B) k (f.baseChange B) =
        determinantCoefficientIdeal (R := B) k
          (e0.toLinearMap ∘ₗ (f.baseChange B ∘ₗ e1.symm.toLinearMap)) := by
            symm
            simpa only [LinearMap.comp_assoc] using
              determinantCoefficientIdeal_comp_eq_of_equiv k
                (f.baseChange B) e1.symm e0
    _ = (determinantCoefficientIdeal (R := A) k f).map (algebraMap A B) := by
      simpa [e0, e1, LinearMap.comp_assoc] using
        determinantCoefficientIdeal_baseChange_pi
          (A := A) (B := B) (n := n) (m := m) k f

private theorem determinantCoefficientIdeal_succ_le_pi
    {R : Type*} [CommRing R] (n m k : ℕ)
    (f : (Fin n → R) →ₗ[R] (Fin m → R)) :
    determinantCoefficientIdeal (R := R) (k + 1) f ≤
      determinantCoefficientIdeal (R := R) k f := by
  classical
  let bU := (Pi.basisFun R (Fin n)).exteriorPower (k + 1)
  let bV := (Pi.basisFun R (Fin m)).exteriorPower (k + 1)
  let bU' := (Pi.basisFun R (Fin n)).exteriorPower k
  let bV' := (Pi.basisFun R (Fin m)).exteriorPower k
  rw [determinantCoefficientIdeal_eq_span_basisCoords (k + 1) f bU bV,
    determinantCoefficientIdeal_eq_span_basisCoords k f bU' bV']
  apply Ideal.span_le.mpr
  rintro a ⟨i, j, rfl⟩
  simp [bU, bV, bU', bV', exteriorPower.basis_coord,
    exteriorPower.ιMultiDual_apply_ιMulti, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, determinantMap]
  rw [Matrix.det_succ_row _ 0]
  apply Ideal.sum_mem
  intro l hl
  apply Ideal.mul_mem_left
  let eI := Set.powersetCard.ofFinEmbEquiv.symm i
  let eJ := Set.powersetCard.ofFinEmbEquiv.symm j
  let i' := Set.powersetCard.ofFinEmb k _ ((Fin.succAboveOrderEmb 0).trans eI).toEmbedding
  let j' := Set.powersetCard.ofFinEmb k _ ((Fin.succAboveOrderEmb l).trans eJ).toEmbedding
  have hi : Set.powersetCard.ofFinEmbEquiv.symm i' =
      (Fin.succAboveOrderEmb 0).trans eI := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    symm
    apply Finset.orderEmbOfFin_unique' i'.prop
    intro x
    simp [i']
  have hj : Set.powersetCard.ofFinEmbEquiv.symm j' =
      (Fin.succAboveOrderEmb l).trans eJ := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    symm
    apply Finset.orderEmbOfFin_unique' j'.prop
    intro x
    simp [j']
  apply Ideal.subset_span
  refine ⟨i'.val, i'.prop, j'.val, j'.prop, ?_⟩
  simp [hi, hj, eI, eJ, Matrix.submatrix, Matrix.of_apply]

private theorem determinantCoordinate_prod_succ
    {R U V : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    {ι κ : Type*} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
    (bU : Module.Basis ι R U) (bV : Module.Basis κ R V)
    (k : ℕ) (f : U →ₗ[R] V)
    (s : Set.powersetCard ι k) (t : Set.powersetCard κ k) :
    letI : LinearOrder (ι ⊕ Unit) :=
      LinearOrder.lift' (toLex : (ι ⊕ Unit) ≃ (ι ⊕ₗ Unit)) toLex.injective
    letI : LinearOrder (κ ⊕ Unit) :=
      LinearOrder.lift' (toLex : (κ ⊕ Unit) ≃ (κ ⊕ₗ Unit)) toLex.injective
    let bU1 := bU.prod (Module.Basis.singleton Unit R)
    let bV1 := bV.prod (Module.Basis.singleton Unit R)
    let s1 : Set.powersetCard (ι ⊕ Unit) (k + 1) :=
      ⟨s.val.disjSum {()}, by simp⟩
    let t1 : Set.powersetCard (κ ⊕ Unit) (k + 1) :=
      ⟨t.val.disjSum {()}, by simp⟩
    (bV1.exteriorPower (k + 1)).coord t1
        (determinantMap (k + 1) (f.prodMap (LinearMap.id : R →ₗ[R] R))
          (bU1.exteriorPower (k + 1) s1)) =
      (bV.exteriorPower k).coord t
        (determinantMap k f (bU.exteriorPower k s)) := by
  classical
  dsimp
  let bU1 := bU.prod (Module.Basis.singleton Unit R)
  let bV1 := bV.prod (Module.Basis.singleton Unit R)
  let s1 : Set.powersetCard (ι ⊕ Unit) (k + 1) :=
    ⟨s.val.disjSum {()}, by simp⟩
  let t1 : Set.powersetCard (κ ⊕ Unit) (k + 1) :=
    ⟨t.val.disjSum {()}, by simp⟩
  let eS : Fin k ↪o ι := Set.powersetCard.ofFinEmbEquiv.symm s
  let eT : Fin k ↪o κ := Set.powersetCard.ofFinEmbEquiv.symm t
  let E : Fin (k + 1) → (ι ⊕ Unit) :=
    Fin.snoc (fun x => Sum.inl (eS x)) (Sum.inr ())
  let F : Fin (k + 1) → (κ ⊕ Unit) :=
    Fin.snoc (fun x => Sum.inl (eT x)) (Sum.inr ())
  have hE : StrictMono E := by
    intro a b hab
    induction a using Fin.lastCases with
    | last =>
        exact False.elim ((not_lt_of_ge (Fin.le_last b)) hab)
    | cast a =>
        induction b using Fin.lastCases with
        | last =>
            simp only [E, Fin.snoc_castSucc, Fin.snoc_last]
            change toLex (Sum.inl (eS a)) < toLex (Sum.inr ())
            exact Sum.Lex.inl_lt_inr _ _
        | cast b =>
            have hab' : a < b := by simpa using hab
            simp only [E, Fin.snoc_castSucc]
            change toLex (Sum.inl (eS a)) < toLex (Sum.inl (eS b))
            exact (Sum.Lex.inl_lt_inl_iff).2 (eS.strictMono hab')
  have hF : StrictMono F := by
    intro a b hab
    induction a using Fin.lastCases with
    | last =>
        exact False.elim ((not_lt_of_ge (Fin.le_last b)) hab)
    | cast a =>
        induction b using Fin.lastCases with
        | last =>
            simp only [F, Fin.snoc_castSucc, Fin.snoc_last]
            change toLex (Sum.inl (eT a)) < toLex (Sum.inr ())
            exact Sum.Lex.inl_lt_inr _ _
        | cast b =>
            have hab' : a < b := by simpa using hab
            simp only [F, Fin.snoc_castSucc]
            change toLex (Sum.inl (eT a)) < toLex (Sum.inl (eT b))
            exact (Sum.Lex.inl_lt_inl_iff).2 (eT.strictMono hab')
  let Eo := OrderEmbedding.ofStrictMono E hE
  let Fo := OrderEmbedding.ofStrictMono F hF
  have hS : Set.powersetCard.ofFinEmbEquiv.symm s1 = Eo := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    symm
    apply Finset.orderEmbOfFin_unique' s1.prop
    intro x
    cases x using Fin.lastCases with
    | last =>
        have he : Eo (Fin.last k) = Sum.inr () := by simp [Eo, E]
        rw [he]
        simp [s1]
    | cast i =>
        have hi :=
          (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s (eS i)).mp
            ⟨i, rfl⟩
        have he : Eo i.castSucc = Sum.inl (eS i) := by simp [Eo, E]
        rw [he]
        simpa [s1, Set.powersetCard.mem_coe_iff] using hi
  have hT : Set.powersetCard.ofFinEmbEquiv.symm t1 = Fo := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    symm
    apply Finset.orderEmbOfFin_unique' t1.prop
    intro x
    cases x using Fin.lastCases with
    | last =>
        have he : Fo (Fin.last k) = Sum.inr () := by simp [Fo, F]
        rw [he]
        simp [t1]
    | cast i =>
        have hi :=
          (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t (eT i)).mp
            ⟨i, rfl⟩
        have he : Fo i.castSucc = Sum.inl (eT i) := by simp [Fo, F]
        rw [he]
        simpa [t1, Set.powersetCard.mem_coe_iff] using hi
  change (bV1.exteriorPower (k + 1)).coord t1
      (determinantMap (k + 1) (f.prodMap (LinearMap.id : R →ₗ[R] R))
        (bU1.exteriorPower (k + 1) s1)) =
    (bV.exteriorPower k).coord t
      (determinantMap k f (bU.exteriorPower k s))
  simp [exteriorPower.basis_coord, exteriorPower.ιMultiDual_apply_ιMulti,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family, determinantMap]
  rw [hS, hT]
  rw [Matrix.det_succ_row _ (Fin.last k)]
  simp [Fin.sum_univ_castSucc, bU1, bV1, Eo, Fo, E, F, eS, eT,
    Module.Basis.prod_apply, Module.Basis.singleton_repr,
    Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
    Matrix.submatrix, Matrix.of_apply]

private theorem determinantCoordinate_prod_empty
    {R U V : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    {ι κ : Type*} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
    (bU : Module.Basis ι R U) (bV : Module.Basis κ R V)
    (k : ℕ) (f : U →ₗ[R] V)
    (s : Set.powersetCard ι k) (t : Set.powersetCard κ k) :
    letI : LinearOrder (ι ⊕ Unit) :=
      LinearOrder.lift' (toLex : (ι ⊕ Unit) ≃ (ι ⊕ₗ Unit)) toLex.injective
    letI : LinearOrder (κ ⊕ Unit) :=
      LinearOrder.lift' (toLex : (κ ⊕ Unit) ≃ (κ ⊕ₗ Unit)) toLex.injective
    let bU1 := bU.prod (Module.Basis.singleton Unit R)
    let bV1 := bV.prod (Module.Basis.singleton Unit R)
    let s1 : Set.powersetCard (ι ⊕ Unit) k :=
      ⟨s.val.disjSum ∅, by simp⟩
    let t1 : Set.powersetCard (κ ⊕ Unit) k :=
      ⟨t.val.disjSum ∅, by simp⟩
    (bV1.exteriorPower k).coord t1
        (determinantMap k (f.prodMap (LinearMap.id : R →ₗ[R] R))
          (bU1.exteriorPower k s1)) =
      (bV.exteriorPower k).coord t
        (determinantMap k f (bU.exteriorPower k s)) := by
  classical
  dsimp
  let bU1 := bU.prod (Module.Basis.singleton Unit R)
  let bV1 := bV.prod (Module.Basis.singleton Unit R)
  let s1 : Set.powersetCard (ι ⊕ Unit) k :=
    ⟨s.val.disjSum ∅, by simp⟩
  let t1 : Set.powersetCard (κ ⊕ Unit) k :=
    ⟨t.val.disjSum ∅, by simp⟩
  let eS : Fin k ↪o ι := Set.powersetCard.ofFinEmbEquiv.symm s
  let eT : Fin k ↪o κ := Set.powersetCard.ofFinEmbEquiv.symm t
  let E : Fin k → (ι ⊕ Unit) := fun x => Sum.inl (eS x)
  let F : Fin k → (κ ⊕ Unit) := fun x => Sum.inl (eT x)
  have hE : StrictMono E := by
    intro a b hab
    simp only [E]
    change toLex (Sum.inl (eS a)) < toLex (Sum.inl (eS b))
    exact (Sum.Lex.inl_lt_inl_iff).2 (eS.strictMono hab)
  have hF : StrictMono F := by
    intro a b hab
    simp only [F]
    change toLex (Sum.inl (eT a)) < toLex (Sum.inl (eT b))
    exact (Sum.Lex.inl_lt_inl_iff).2 (eT.strictMono hab)
  let Eo := OrderEmbedding.ofStrictMono E hE
  let Fo := OrderEmbedding.ofStrictMono F hF
  have hS : Set.powersetCard.ofFinEmbEquiv.symm s1 = Eo := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    symm
    apply Finset.orderEmbOfFin_unique' s1.prop
    intro x
    have hi :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s (eS x)).mp
        ⟨x, rfl⟩
    simpa [Eo, E, s1, Set.powersetCard.mem_coe_iff] using hi
  have hT : Set.powersetCard.ofFinEmbEquiv.symm t1 = Fo := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    symm
    apply Finset.orderEmbOfFin_unique' t1.prop
    intro x
    have hi :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t (eT x)).mp
        ⟨x, rfl⟩
    simpa [Fo, F, t1, Set.powersetCard.mem_coe_iff] using hi
  change (bV1.exteriorPower k).coord t1
      (determinantMap k (f.prodMap (LinearMap.id : R →ₗ[R] R))
        (bU1.exteriorPower k s1)) =
    (bV.exteriorPower k).coord t
      (determinantMap k f (bU.exteriorPower k s))
  simp [hS, hT, bU1, bV1, Eo, Fo, E, F, eS, eT,
    exteriorPower.basis_coord, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, determinantMap, Module.Basis.prod_apply,
    Module.Basis.prod_repr_inl]

private theorem determinantCoordinate_prod_empty_singleton
    {R U V : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    {ι κ : Type*} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
    (bU : Module.Basis ι R U) (bV : Module.Basis κ R V)
    (k : ℕ) (f : U →ₗ[R] V)
    (s : Set.powersetCard ι (k + 1)) (t : Set.powersetCard κ k) :
    letI : LinearOrder (ι ⊕ Unit) :=
      LinearOrder.lift' (toLex : (ι ⊕ Unit) ≃ (ι ⊕ₗ Unit)) toLex.injective
    letI : LinearOrder (κ ⊕ Unit) :=
      LinearOrder.lift' (toLex : (κ ⊕ Unit) ≃ (κ ⊕ₗ Unit)) toLex.injective
    let bU1 := bU.prod (Module.Basis.singleton Unit R)
    let bV1 := bV.prod (Module.Basis.singleton Unit R)
    let s1 : Set.powersetCard (ι ⊕ Unit) (k + 1) :=
      ⟨s.val.disjSum ∅, by simp⟩
    let t1 : Set.powersetCard (κ ⊕ Unit) (k + 1) :=
      ⟨t.val.disjSum {()}, by simp⟩
    (bV1.exteriorPower (k + 1)).coord t1
        (determinantMap (k + 1) (f.prodMap (LinearMap.id : R →ₗ[R] R))
          (bU1.exteriorPower (k + 1) s1)) = 0 := by
  classical
  dsimp
  let bU1 := bU.prod (Module.Basis.singleton Unit R)
  let bV1 := bV.prod (Module.Basis.singleton Unit R)
  let s1 : Set.powersetCard (ι ⊕ Unit) (k + 1) :=
    ⟨s.val.disjSum ∅, by simp⟩
  let t1 : Set.powersetCard (κ ⊕ Unit) (k + 1) :=
    ⟨t.val.disjSum {()}, by simp⟩
  let eS : Fin (k + 1) ↪o ι := Set.powersetCard.ofFinEmbEquiv.symm s
  let eT : Fin k ↪o κ := Set.powersetCard.ofFinEmbEquiv.symm t
  let E : Fin (k + 1) → (ι ⊕ Unit) := fun x => Sum.inl (eS x)
  let F : Fin (k + 1) → (κ ⊕ Unit) :=
    Fin.snoc (fun x => Sum.inl (eT x)) (Sum.inr ())
  have hE : StrictMono E := by
    intro a b hab
    simp only [E]
    change toLex (Sum.inl (eS a)) < toLex (Sum.inl (eS b))
    exact (Sum.Lex.inl_lt_inl_iff).2 (eS.strictMono hab)
  have hF : StrictMono F := by
    intro a b hab
    induction a using Fin.lastCases with
    | last =>
        exact False.elim ((not_lt_of_ge (Fin.le_last b)) hab)
    | cast a =>
        induction b using Fin.lastCases with
        | last =>
            simp only [F, Fin.snoc_castSucc, Fin.snoc_last]
            change toLex (Sum.inl (eT a)) < toLex (Sum.inr ())
            exact Sum.Lex.inl_lt_inr _ _
        | cast b =>
            have hab' : a < b := by simpa using hab
            simp only [F, Fin.snoc_castSucc]
            change toLex (Sum.inl (eT a)) < toLex (Sum.inl (eT b))
            exact (Sum.Lex.inl_lt_inl_iff).2 (eT.strictMono hab')
  let Eo := OrderEmbedding.ofStrictMono E hE
  let Fo := OrderEmbedding.ofStrictMono F hF
  have hS : Set.powersetCard.ofFinEmbEquiv.symm s1 = Eo := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    symm
    apply Finset.orderEmbOfFin_unique' s1.prop
    intro x
    have hi :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s (eS x)).mp
        ⟨x, rfl⟩
    simpa [Eo, E, s1, Set.powersetCard.mem_coe_iff] using hi
  have hT : Set.powersetCard.ofFinEmbEquiv.symm t1 = Fo := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    symm
    apply Finset.orderEmbOfFin_unique' t1.prop
    intro x
    cases x using Fin.lastCases with
    | last =>
        have he : Fo (Fin.last k) = Sum.inr () := by simp [Fo, F]
        rw [he]
        simp [t1]
    | cast i =>
        have hi :=
          (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t (eT i)).mp
            ⟨i, rfl⟩
        have he : Fo i.castSucc = Sum.inl (eT i) := by simp [Fo, F]
        rw [he]
        simpa [t1, Set.powersetCard.mem_coe_iff] using hi
  change (bV1.exteriorPower (k + 1)).coord t1
      (determinantMap (k + 1) (f.prodMap (LinearMap.id : R →ₗ[R] R))
        (bU1.exteriorPower (k + 1) s1)) = 0
  simp [exteriorPower.basis_coord, exteriorPower.ιMultiDual_apply_ιMulti,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family, determinantMap]
  rw [hS, hT]
  apply Matrix.det_eq_zero_of_column_eq_zero (Fin.last k)
  intro i
  simp [bU1, bV1, Eo, Fo, E, F, eS, eT,
    Module.Basis.prod_apply, Module.Basis.prod_repr_inr]

private theorem determinantCoordinate_prod_singleton_empty
    {R U V : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    {ι κ : Type*} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
    (bU : Module.Basis ι R U) (bV : Module.Basis κ R V)
    (k : ℕ) (f : U →ₗ[R] V)
    (s : Set.powersetCard ι k) (t : Set.powersetCard κ (k + 1)) :
    letI : LinearOrder (ι ⊕ Unit) :=
      LinearOrder.lift' (toLex : (ι ⊕ Unit) ≃ (ι ⊕ₗ Unit)) toLex.injective
    letI : LinearOrder (κ ⊕ Unit) :=
      LinearOrder.lift' (toLex : (κ ⊕ Unit) ≃ (κ ⊕ₗ Unit)) toLex.injective
    let bU1 := bU.prod (Module.Basis.singleton Unit R)
    let bV1 := bV.prod (Module.Basis.singleton Unit R)
    let s1 : Set.powersetCard (ι ⊕ Unit) (k + 1) :=
      ⟨s.val.disjSum {()}, by simp⟩
    let t1 : Set.powersetCard (κ ⊕ Unit) (k + 1) :=
      ⟨t.val.disjSum ∅, by simp⟩
    (bV1.exteriorPower (k + 1)).coord t1
        (determinantMap (k + 1) (f.prodMap (LinearMap.id : R →ₗ[R] R))
          (bU1.exteriorPower (k + 1) s1)) = 0 := by
  classical
  dsimp
  let bU1 := bU.prod (Module.Basis.singleton Unit R)
  let bV1 := bV.prod (Module.Basis.singleton Unit R)
  let s1 : Set.powersetCard (ι ⊕ Unit) (k + 1) :=
    ⟨s.val.disjSum {()}, by simp⟩
  let t1 : Set.powersetCard (κ ⊕ Unit) (k + 1) :=
    ⟨t.val.disjSum ∅, by simp⟩
  let eS : Fin k ↪o ι := Set.powersetCard.ofFinEmbEquiv.symm s
  let eT : Fin (k + 1) ↪o κ := Set.powersetCard.ofFinEmbEquiv.symm t
  let E : Fin (k + 1) → (ι ⊕ Unit) :=
    Fin.snoc (fun x => Sum.inl (eS x)) (Sum.inr ())
  let F : Fin (k + 1) → (κ ⊕ Unit) := fun x => Sum.inl (eT x)
  have hE : StrictMono E := by
    intro a b hab
    induction a using Fin.lastCases with
    | last =>
        exact False.elim ((not_lt_of_ge (Fin.le_last b)) hab)
    | cast a =>
        induction b using Fin.lastCases with
        | last =>
            simp only [E, Fin.snoc_castSucc, Fin.snoc_last]
            change toLex (Sum.inl (eS a)) < toLex (Sum.inr ())
            exact Sum.Lex.inl_lt_inr _ _
        | cast b =>
            have hab' : a < b := by simpa using hab
            simp only [E, Fin.snoc_castSucc]
            change toLex (Sum.inl (eS a)) < toLex (Sum.inl (eS b))
            exact (Sum.Lex.inl_lt_inl_iff).2 (eS.strictMono hab')
  have hF : StrictMono F := by
    intro a b hab
    simp only [F]
    change toLex (Sum.inl (eT a)) < toLex (Sum.inl (eT b))
    exact (Sum.Lex.inl_lt_inl_iff).2 (eT.strictMono hab)
  let Eo := OrderEmbedding.ofStrictMono E hE
  let Fo := OrderEmbedding.ofStrictMono F hF
  have hS : Set.powersetCard.ofFinEmbEquiv.symm s1 = Eo := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    symm
    apply Finset.orderEmbOfFin_unique' s1.prop
    intro x
    cases x using Fin.lastCases with
    | last =>
        have he : Eo (Fin.last k) = Sum.inr () := by simp [Eo, E]
        rw [he]
        simp [s1]
    | cast i =>
        have hi :=
          (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s (eS i)).mp
            ⟨i, rfl⟩
        have he : Eo i.castSucc = Sum.inl (eS i) := by simp [Eo, E]
        rw [he]
        simpa [s1, Set.powersetCard.mem_coe_iff] using hi
  have hT : Set.powersetCard.ofFinEmbEquiv.symm t1 = Fo := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    symm
    apply Finset.orderEmbOfFin_unique' t1.prop
    intro x
    have hi :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t (eT x)).mp
        ⟨x, rfl⟩
    simpa [Fo, F, t1, Set.powersetCard.mem_coe_iff] using hi
  change (bV1.exteriorPower (k + 1)).coord t1
      (determinantMap (k + 1) (f.prodMap (LinearMap.id : R →ₗ[R] R))
        (bU1.exteriorPower (k + 1) s1)) = 0
  simp [exteriorPower.basis_coord, exteriorPower.ιMultiDual_apply_ιMulti,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family, determinantMap]
  rw [hS, hT]
  apply Matrix.det_eq_zero_of_row_eq_zero (Fin.last k)
  intro j
  simp [bU1, bV1, Eo, Fo, E, F, eS, eT,
    Module.Basis.prod_apply, Module.Basis.prod_repr_inl]

private theorem determinantCoefficientIdeal_prodMap_succ
    {R U V : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    {ι κ : Type*} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
    (bU : Module.Basis ι R U) (bV : Module.Basis κ R V)
    (k : ℕ) (f : U →ₗ[R] V)
    (hmono : determinantCoefficientIdeal (R := R) (k + 1) f ≤
      determinantCoefficientIdeal (R := R) k f) :
    determinantCoefficientIdeal (R := R) (k + 1)
        (f.prodMap (LinearMap.id : R →ₗ[R] R)) =
      determinantCoefficientIdeal (R := R) k f := by
  classical
  let bU1 := bU.prod (Module.Basis.singleton Unit R)
  let bV1 := bV.prod (Module.Basis.singleton Unit R)
  rw [determinantCoefficientIdeal_eq_span_basisCoords (k + 1)
      (f.prodMap (LinearMap.id : R →ₗ[R] R))
      (bU1.exteriorPower (k + 1)) (bV1.exteriorPower (k + 1)),
    determinantCoefficientIdeal_eq_span_basisCoords k f
      (bU.exteriorPower k) (bV.exteriorPower k)]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro a ⟨s, t, rfl⟩
    have hs_right : s.val.toRight = ∅ ∨ s.val.toRight = {()} := by
      by_cases h : () ∈ s.val.toRight
      · right
        ext x
        cases x
        simp [h]
      · left
        ext x
        cases x
        simp [h]
    have ht_right : t.val.toRight = ∅ ∨ t.val.toRight = {()} := by
      by_cases h : () ∈ t.val.toRight
      · right
        ext x
        cases x
        simp [h]
      · left
        ext x
        cases x
        simp [h]
    rcases hs_right with hs_right | hs_right <;>
      rcases ht_right with ht_right | ht_right
    · let s0 : Set.powersetCard ι (k + 1) :=
        ⟨s.val.toLeft, by
          change s.val.toLeft.card = k + 1
          have h := Set.powersetCard.card_eq s
          rw [← Finset.toLeft_disjSum_toRight (u := s.val), Finset.card_disjSum]
              at h
          simpa [hs_right] using h⟩
      let t0 : Set.powersetCard κ (k + 1) :=
        ⟨t.val.toLeft, by
          change t.val.toLeft.card = k + 1
          have h := Set.powersetCard.card_eq t
          rw [← Finset.toLeft_disjSum_toRight (u := t.val), Finset.card_disjSum]
              at h
          simpa [ht_right] using h⟩
      have hs : s = (⟨s0.val.disjSum ∅, by simp⟩ :
          Set.powersetCard (ι ⊕ Unit) (k + 1)) := by
        apply Subtype.ext
        calc
          s.val = s.val.toLeft.disjSum s.val.toRight :=
            (Finset.toLeft_disjSum_toRight (u := s.val)).symm
          _ = s.val.toLeft.disjSum ∅ := by rw [hs_right]
      have ht : t = (⟨t0.val.disjSum ∅, by simp⟩ :
          Set.powersetCard (κ ⊕ Unit) (k + 1)) := by
        apply Subtype.ext
        calc
          t.val = t.val.toLeft.disjSum t.val.toRight :=
            (Finset.toLeft_disjSum_toRight (u := t.val)).symm
          _ = t.val.toLeft.disjSum ∅ := by rw [ht_right]
      rw [hs, ht, determinantCoordinate_prod_empty bU bV (k + 1) f s0 t0]
      rw [← determinantCoefficientIdeal_eq_span_basisCoords k f
        (bU.exteriorPower k) (bV.exteriorPower k)]
      refine hmono ?_
      rw [determinantCoefficientIdeal_eq_span_basisCoords (k + 1) f
        (bU.exteriorPower (k + 1)) (bV.exteriorPower (k + 1))]
      exact Ideal.subset_span ⟨s0, t0, rfl⟩
    · let s0 : Set.powersetCard ι (k + 1) :=
        ⟨s.val.toLeft, by
          change s.val.toLeft.card = k + 1
          have h := Set.powersetCard.card_eq s
          rw [← Finset.toLeft_disjSum_toRight (u := s.val), Finset.card_disjSum]
              at h
          simpa [hs_right] using h⟩
      let t0 : Set.powersetCard κ k :=
        ⟨t.val.toLeft, by
          change t.val.toLeft.card = k
          have h := Set.powersetCard.card_eq t
          rw [← Finset.toLeft_disjSum_toRight (u := t.val), Finset.card_disjSum]
              at h
          have h' : t.val.toLeft.card + 1 = k + 1 := by
            simpa [ht_right] using h
          exact Nat.add_right_cancel h'⟩
      have hs : s = (⟨s0.val.disjSum ∅, by simp⟩ :
          Set.powersetCard (ι ⊕ Unit) (k + 1)) := by
        apply Subtype.ext
        calc
          s.val = s.val.toLeft.disjSum s.val.toRight :=
            (Finset.toLeft_disjSum_toRight (u := s.val)).symm
          _ = s.val.toLeft.disjSum ∅ := by rw [hs_right]
      have ht : t = (⟨t0.val.disjSum {()}, by simp⟩ :
          Set.powersetCard (κ ⊕ Unit) (k + 1)) := by
        apply Subtype.ext
        calc
          t.val = t.val.toLeft.disjSum t.val.toRight :=
            (Finset.toLeft_disjSum_toRight (u := t.val)).symm
          _ = t.val.toLeft.disjSum {()} := by rw [ht_right]
      rw [hs, ht, determinantCoordinate_prod_empty_singleton bU bV k f s0 t0]
      exact Ideal.zero_mem _
    · let s0 : Set.powersetCard ι k :=
        ⟨s.val.toLeft, by
          change s.val.toLeft.card = k
          have h := Set.powersetCard.card_eq s
          rw [← Finset.toLeft_disjSum_toRight (u := s.val), Finset.card_disjSum]
              at h
          have h' : s.val.toLeft.card + 1 = k + 1 := by
            simpa [hs_right] using h
          exact Nat.add_right_cancel h'⟩
      let t0 : Set.powersetCard κ (k + 1) :=
        ⟨t.val.toLeft, by
          change t.val.toLeft.card = k + 1
          have h := Set.powersetCard.card_eq t
          rw [← Finset.toLeft_disjSum_toRight (u := t.val), Finset.card_disjSum]
              at h
          simpa [ht_right] using h⟩
      have hs : s = (⟨s0.val.disjSum {()}, by simp⟩ :
          Set.powersetCard (ι ⊕ Unit) (k + 1)) := by
        apply Subtype.ext
        calc
          s.val = s.val.toLeft.disjSum s.val.toRight :=
            (Finset.toLeft_disjSum_toRight (u := s.val)).symm
          _ = s.val.toLeft.disjSum {()} := by rw [hs_right]
      have ht : t = (⟨t0.val.disjSum ∅, by simp⟩ :
          Set.powersetCard (κ ⊕ Unit) (k + 1)) := by
        apply Subtype.ext
        calc
          t.val = t.val.toLeft.disjSum t.val.toRight :=
            (Finset.toLeft_disjSum_toRight (u := t.val)).symm
          _ = t.val.toLeft.disjSum ∅ := by rw [ht_right]
      rw [hs, ht, determinantCoordinate_prod_singleton_empty bU bV k f s0 t0]
      exact Ideal.zero_mem _
    · let s0 : Set.powersetCard ι k :=
        ⟨s.val.toLeft, by
          change s.val.toLeft.card = k
          have h := Set.powersetCard.card_eq s
          rw [← Finset.toLeft_disjSum_toRight (u := s.val), Finset.card_disjSum]
              at h
          have h' : s.val.toLeft.card + 1 = k + 1 := by
            simpa [hs_right] using h
          exact Nat.add_right_cancel h'⟩
      let t0 : Set.powersetCard κ k :=
        ⟨t.val.toLeft, by
          change t.val.toLeft.card = k
          have h := Set.powersetCard.card_eq t
          rw [← Finset.toLeft_disjSum_toRight (u := t.val), Finset.card_disjSum]
              at h
          have h' : t.val.toLeft.card + 1 = k + 1 := by
            simpa [ht_right] using h
          exact Nat.add_right_cancel h'⟩
      have hs : s = (⟨s0.val.disjSum {()}, by simp⟩ :
          Set.powersetCard (ι ⊕ Unit) (k + 1)) := by
        apply Subtype.ext
        calc
          s.val = s.val.toLeft.disjSum s.val.toRight :=
            (Finset.toLeft_disjSum_toRight (u := s.val)).symm
          _ = s.val.toLeft.disjSum {()} := by rw [hs_right]
      have ht : t = (⟨t0.val.disjSum {()}, by simp⟩ :
          Set.powersetCard (κ ⊕ Unit) (k + 1)) := by
        apply Subtype.ext
        calc
          t.val = t.val.toLeft.disjSum t.val.toRight :=
            (Finset.toLeft_disjSum_toRight (u := t.val)).symm
          _ = t.val.toLeft.disjSum {()} := by rw [ht_right]
      rw [hs, ht, determinantCoordinate_prod_succ bU bV k f s0 t0]
      exact Ideal.subset_span ⟨s0, t0, rfl⟩
  · apply Ideal.span_le.mpr
    rintro a ⟨s, t, rfl⟩
    have hcoord := determinantCoordinate_prod_succ bU bV k f s t
    rw [← hcoord]
    exact Ideal.subset_span ⟨
      (⟨s.val.disjSum {()}, by simp⟩ : Set.powersetCard (ι ⊕ Unit) (k + 1)),
      (⟨t.val.disjSum {()}, by simp⟩ : Set.powersetCard (κ ⊕ Unit) (k + 1)), rfl⟩

private noncomputable def piProdEquiv
    {R : Type*} [CommRing R] (n : ℕ) :
    ((Fin n → R) × R) ≃ₗ[R] (Fin (n + 1) → R) := by
  let e : (Fin (n + 1) → R) ≃ₗ[R] R × (Fin n → R) :=
    (LinearEquiv.piCongrLeft R (fun _ : Option (Fin n) => R)
      (finSuccEquiv' (Fin.last n))).trans
      (LinearEquiv.piOptionEquivProd R)
  exact (LinearEquiv.prodComm R (Fin n → R) R).trans e.symm

private theorem piProdEquiv_apply_castSucc
    {R : Type*} [CommRing R] (n : ℕ) (x : Fin n → R) (r : R) (j : Fin n) :
    piProdEquiv (R := R) n (x, r) j.castSucc = x j := by
  simp [piProdEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piOptionEquivProd,
    Equiv.piOptionEquivProd, finSuccEquiv'_last_apply_castSucc]

private theorem piProdEquiv_apply_last
    {R : Type*} [CommRing R] (n : ℕ) (x : Fin n → R) (r : R) :
    piProdEquiv (R := R) n (x, r) (Fin.last n) = r := by
  simp [piProdEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piOptionEquivProd,
    Equiv.piOptionEquivProd, finSuccEquiv'_at]

private theorem piProdEquiv_symm_apply_fst
    {R : Type*} [CommRing R] (n : ℕ) (x : Fin (n + 1) → R) (j : Fin n) :
    ((piProdEquiv (R := R) n).symm x).1 j = x j.castSucc := by
  have h := congrFun ((piProdEquiv (R := R) n).apply_symm_apply x) j.castSucc
  rw [piProdEquiv_apply_castSucc] at h
  exact h

private theorem piProdEquiv_symm_apply_snd
    {R : Type*} [CommRing R] (n : ℕ) (x : Fin (n + 1) → R) :
    ((piProdEquiv (R := R) n).symm x).2 = x (Fin.last n) := by
  have h := congrFun ((piProdEquiv (R := R) n).apply_symm_apply x) (Fin.last n)
  rw [piProdEquiv_apply_last] at h
  exact h

private noncomputable def piSumProdEquiv
    {R : Type*} [CommRing R] (n d : ℕ) :
    ((Fin n → R) × (Fin d → R)) ≃ₗ[R] (Fin (n + d) → R) := by
  let e : (Fin (n + d) → R) ≃ₗ[R]
      ((Fin n → R) × (Fin d → R)) :=
    (LinearEquiv.funCongrLeft R R finSumFinEquiv).trans
      (LinearEquiv.sumPiEquivProdPi R (Fin n) (Fin d) (fun _ => R))
  exact e.symm

private noncomputable def piReindex
    {R : Type*} [CommRing R] {a b : ℕ} (h : a = b) :
    (Fin a → R) ≃ₗ[R] (Fin b → R) :=
  LinearEquiv.funCongrLeft R R (finCongr h.symm)

private theorem piReindex_apply
    {R : Type*} [CommRing R] {a b : ℕ} (h : a = b)
    (x : Fin a → R) (j : Fin b) :
    piReindex (R := R) h x j = x (finCongr h.symm j) := by
  rfl

private theorem piReindex_symm_apply
    {R : Type*} [CommRing R] {a b : ℕ} (h : a = b)
    (x : Fin b → R) (j : Fin a) :
    (piReindex (R := R) h).symm x j = x (finCongr h j) := by
  rfl

private noncomputable def piExtendMap
    {R : Type*} [CommRing R] (n m d : ℕ)
    (f : (Fin n → R) →ₗ[R] (Fin m → R)) :
    (Fin (n + d) → R) →ₗ[R] (Fin (m + d) → R) := by
  induction d with
  | zero => exact f
  | succ d ih =>
      let eU := piReindex (R := R) (Nat.add_assoc n d 1)
      let eV := piReindex (R := R) (Nat.add_assoc m d 1)
      exact
        ((eV.toLinearMap.comp
            ((piProdEquiv (R := R) (m + d)).toLinearMap.comp
              ((ih.prodMap (LinearMap.id : R →ₗ[R] R)).comp
                (piProdEquiv (R := R) (n + d)).symm.toLinearMap))).comp
          eU.symm.toLinearMap)

private theorem piExtendMap_succ
    {R : Type*} [CommRing R] (n m d : ℕ)
    (f : (Fin n → R) →ₗ[R] (Fin m → R)) :
    piExtendMap n m (d + 1) f =
      let eU := piReindex (R := R) (Nat.add_assoc n d 1)
      let eV := piReindex (R := R) (Nat.add_assoc m d 1)
      let eU' := eU.symm.trans (piProdEquiv (R := R) (n + d)).symm
      let eV' := (piProdEquiv (R := R) (m + d)).trans eV
      eV'.toLinearMap ∘ₗ
        ((piExtendMap n m d f).prodMap (LinearMap.id : R →ₗ[R] R)) ∘ₗ
          eU'.toLinearMap := by
  let eU := piReindex (R := R) (Nat.add_assoc n d 1)
  let eV := piReindex (R := R) (Nat.add_assoc m d 1)
  let eU' := eU.symm.trans (piProdEquiv (R := R) (n + d)).symm
  let eV' := (piProdEquiv (R := R) (m + d)).trans eV
  change piExtendMap n m (d + 1) f =
    eV'.toLinearMap ∘ₗ
      ((piExtendMap n m d f).prodMap (LinearMap.id : R →ₗ[R] R)) ∘ₗ
        eU'.toLinearMap
  apply LinearMap.ext
  intro x
  funext j
  simp only [piExtendMap, piReindex, eU, eV, eU', eV', LinearMap.comp_apply]
  rfl

private theorem piSumProdEquiv_apply_left
    {R : Type*} [CommRing R] (n d : ℕ)
    (x : Fin n → R) (y : Fin d → R) (j : Fin n) :
    piSumProdEquiv (R := R) n d (x, y) (Fin.castAdd d j) = x j := by
  simp [piSumProdEquiv]

private theorem piSumProdEquiv_apply_right
    {R : Type*} [CommRing R] (n d : ℕ)
    (x : Fin n → R) (y : Fin d → R) (j : Fin d) :
    piSumProdEquiv (R := R) n d (x, y) (Fin.natAdd n j) = y j := by
  simp [piSumProdEquiv]

private theorem piSumProdEquiv_symm_apply_fst
    {R : Type*} [CommRing R] (n d : ℕ)
    (x : Fin (n + d) → R) (j : Fin n) :
    ((piSumProdEquiv (R := R) n d).symm x).1 j = x (Fin.castAdd d j) := by
  have h := congrFun ((piSumProdEquiv (R := R) n d).apply_symm_apply x)
    (Fin.castAdd d j)
  rw [piSumProdEquiv_apply_left] at h
  exact h

private theorem piSumProdEquiv_symm_apply_snd
    {R : Type*} [CommRing R] (n d : ℕ)
    (x : Fin (n + d) → R) (j : Fin d) :
    ((piSumProdEquiv (R := R) n d).symm x).2 j = x (Fin.natAdd n j) := by
  have h := congrFun ((piSumProdEquiv (R := R) n d).apply_symm_apply x)
    (Fin.natAdd n j)
  rw [piSumProdEquiv_apply_right] at h
  exact h

private theorem piExtendMap_apply_left
    {R : Type*} [CommRing R] (n m d : ℕ)
    (f : (Fin n → R) →ₗ[R] (Fin m → R))
    (x : Fin (n + d) → R) (j : Fin m) :
    piExtendMap n m d f x (Fin.castAdd d j) =
      f (fun i => x (Fin.castAdd d i)) j := by
  induction d with
  | zero =>
      simp [piExtendMap]
  | succ d ih =>
      rw [piExtendMap_succ]
      have hV :
          finCongr (Nat.add_assoc m d 1).symm (Fin.castAdd (d + 1) j) =
            Fin.castSucc (Fin.castAdd d j) := by
        apply Fin.ext
        rfl
      have hU (i : Fin n) :
          finCongr (Nat.add_assoc n d 1) (Fin.castSucc (Fin.castAdd d i)) =
            Fin.castAdd (d + 1) i := by
        apply Fin.ext
        rfl
      have hUlast :
          finCongr (Nat.add_assoc n d 1) (Fin.last (n + d)) =
            Fin.natAdd n (Fin.last d) := by
        apply Fin.ext
        rfl
      change
        piReindex (R := R) (Nat.add_assoc m d 1)
            ((piProdEquiv (R := R) (m + d))
              (((piExtendMap n m d f).prodMap
                (LinearMap.id : R →ₗ[R] R))
                ((piProdEquiv (R := R) (n + d)).symm
                  ((piReindex (R := R) (Nat.add_assoc n d 1)).symm x))))
            (Fin.castAdd (d + 1) j) =
          f (fun i => x (Fin.castAdd (d + 1) i)) j
      rw [piReindex_apply, hV, piProdEquiv_apply_castSucc]
      change
        piExtendMap n m d f
            ((piProdEquiv (R := R) (n + d)).symm
              ((piReindex (R := R) (Nat.add_assoc n d 1)).symm x)).1
            (Fin.castAdd d j) =
          f (fun i => x (Fin.castAdd (d + 1) i)) j
      rw [ih]
      apply congrArg (fun g : Fin n → R => f g j)
      funext i
      rw [piProdEquiv_symm_apply_fst, piReindex_symm_apply, hU]

private theorem piExtendMap_apply_right
    {R : Type*} [CommRing R] (n m d : ℕ)
    (f : (Fin n → R) →ₗ[R] (Fin m → R))
    (x : Fin (n + d) → R) (j : Fin d) :
    piExtendMap n m d f x (Fin.natAdd m j) = x (Fin.natAdd n j) := by
  induction d with
  | zero =>
      exact Fin.elim0 j
  | succ d ih =>
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
      cases j with
      | inl j =>
          rw [piExtendMap_succ]
          have hV :
              finCongr (Nat.add_assoc m d 1).symm
                  (Fin.natAdd m (Fin.castAdd 1 j)) =
                Fin.castSucc (Fin.natAdd m j) := by
            apply Fin.ext
            rfl
          have hU (j : Fin d) :
              finCongr (Nat.add_assoc n d 1)
                  (Fin.castSucc (Fin.natAdd n j)) =
                Fin.natAdd n (Fin.castAdd 1 j) := by
            apply Fin.ext
            rfl
          change
            piReindex (R := R) (Nat.add_assoc m d 1)
                ((piProdEquiv (R := R) (m + d))
                  (((piExtendMap n m d f).prodMap
                    (LinearMap.id : R →ₗ[R] R))
                    ((piProdEquiv (R := R) (n + d)).symm
                      ((piReindex (R := R) (Nat.add_assoc n d 1)).symm x))))
                (Fin.natAdd m (Fin.castAdd 1 j)) =
              x (Fin.natAdd n (Fin.castAdd 1 j))
          rw [piReindex_apply, hV, piProdEquiv_apply_castSucc]
          change
            piExtendMap n m d f
                ((piProdEquiv (R := R) (n + d)).symm
                  ((piReindex (R := R) (Nat.add_assoc n d 1)).symm x)).1
                (Fin.natAdd m j) =
              x (Fin.natAdd n (Fin.castAdd 1 j))
          rw [ih, piProdEquiv_symm_apply_fst, piReindex_symm_apply, hU]
      | inr j =>
          rw [piExtendMap_succ]
          have hV :
              finCongr (Nat.add_assoc m d 1).symm
                  (Fin.natAdd m (Fin.natAdd d j)) =
                Fin.last (m + d) := by
            apply Fin.ext
            simp
          have hUlast :
              finCongr (Nat.add_assoc n d 1)
                  (Fin.last (n + d)) =
                Fin.natAdd n (Fin.natAdd d j) := by
            apply Fin.ext
            simp
          change
            piReindex (R := R) (Nat.add_assoc m d 1)
                ((piProdEquiv (R := R) (m + d))
                  (((piExtendMap n m d f).prodMap
                    (LinearMap.id : R →ₗ[R] R))
                    ((piProdEquiv (R := R) (n + d)).symm
                      ((piReindex (R := R) (Nat.add_assoc n d 1)).symm x))))
                (Fin.natAdd m (Fin.natAdd d j)) =
              x (Fin.natAdd n (Fin.natAdd d j))
          rw [piReindex_apply, hV, piProdEquiv_apply_last]
          change
            ((piProdEquiv (R := R) (n + d)).symm
              ((piReindex (R := R) (Nat.add_assoc n d 1)).symm x)).2 =
              x (Fin.natAdd n (Fin.natAdd d j))
          rw [piProdEquiv_symm_apply_snd, piReindex_symm_apply, hUlast]

private theorem determinantCoefficientIdeal_piExtendMap
    {R : Type*} [CommRing R] (n m d k : ℕ)
    (f : (Fin n → R) →ₗ[R] (Fin m → R)) :
    determinantCoefficientIdeal (R := R) (k + d)
        (piExtendMap n m d f) =
      determinantCoefficientIdeal (R := R) k f := by
  classical
  induction d with
  | zero => simp [piExtendMap]
  | succ d ih =>
      let eU := piReindex (R := R) (Nat.add_assoc n d 1)
      let eV := piReindex (R := R) (Nat.add_assoc m d 1)
      let eU' := eU.symm.trans (piProdEquiv (R := R) (n + d)).symm
      let eV' := (piProdEquiv (R := R) (m + d)).trans eV
      have hconj :
          determinantCoefficientIdeal (R := R) (k + d + 1)
              (eV'.toLinearMap ∘ₗ
                ((piExtendMap n m d f).prodMap
                  (LinearMap.id : R →ₗ[R] R)) ∘ₗ eU'.toLinearMap) =
            determinantCoefficientIdeal (R := R) (k + d + 1)
              ((piExtendMap n m d f).prodMap
                (LinearMap.id : R →ₗ[R] R)) :=
        determinantCoefficientIdeal_comp_eq_of_equiv
          (R := R) (k + d + 1)
          ((piExtendMap n m d f).prodMap (LinearMap.id : R →ₗ[R] R))
          eU' eV'
      have hprod := determinantCoefficientIdeal_prodMap_succ
        (Pi.basisFun R (Fin (n + d))) (Pi.basisFun R (Fin (m + d)))
        (k + d) (piExtendMap n m d f)
        (determinantCoefficientIdeal_succ_le_pi
          (n + d) (m + d) (k + d) (piExtendMap n m d f))
      calc
        determinantCoefficientIdeal (R := R) (k + (d + 1))
            (piExtendMap n m (d + 1) f) =
            determinantCoefficientIdeal (R := R) (k + d + 1)
              (eV'.toLinearMap ∘ₗ
                ((piExtendMap n m d f).prodMap
                  (LinearMap.id : R →ₗ[R] R)) ∘ₗ eU'.toLinearMap) := by
                  have hmap :
                      piExtendMap n m (d + 1) f =
                        eV'.toLinearMap ∘ₗ
                          ((piExtendMap n m d f).prodMap
                            (LinearMap.id : R →ₗ[R] R)) ∘ₗ eU'.toLinearMap := by
                    apply LinearMap.ext
                    intro x
                    funext j
                    simp only [piExtendMap, piReindex, eU, eV, eU', eV',
                      LinearMap.comp_apply]
                    rfl
                  rw [hmap]
                  simp only [Nat.add_assoc]
        _ = determinantCoefficientIdeal (R := R) (k + d + 1)
              ((piExtendMap n m d f).prodMap
                (LinearMap.id : R →ₗ[R] R)) := hconj
        _ = determinantCoefficientIdeal (R := R) (k + d)
              (piExtendMap n m d f) := hprod
        _ = determinantCoefficientIdeal (R := R) k f := ih

private theorem piExtendMap_eq_sumConjugate
    {R : Type*} [CommRing R] (n m d : ℕ)
    (f : (Fin n → R) →ₗ[R] (Fin m → R)) :
    piExtendMap n m d f =
      (piSumProdEquiv (R := R) m d).toLinearMap ∘ₗ
      (f.prodMap (LinearMap.id : (Fin d → R) →ₗ[R] (Fin d → R))) ∘ₗ
          (piSumProdEquiv (R := R) n d).symm.toLinearMap := by
  classical
  apply LinearMap.ext
  intro x
  funext j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases j with
  | inl j =>
      have hmain :
          piExtendMap n m d f x (Fin.castAdd d j) =
            f (((piSumProdEquiv (R := R) n d).symm x).1) j := by
        rw [piExtendMap_apply_left]
        apply congrArg (fun g : Fin n → R => f g j)
        funext i
        rw [piSumProdEquiv_symm_apply_fst]
      simpa [piSumProdEquiv, LinearMap.comp_apply] using hmain
  | inr j =>
      have hmain :
          piExtendMap n m d f x (Fin.natAdd m j) =
            ((piSumProdEquiv (R := R) n d).symm x).2 j := by
        rw [piExtendMap_apply_right, piSumProdEquiv_symm_apply_snd]
      simpa [piSumProdEquiv, LinearMap.comp_apply] using hmain

private theorem determinantCoefficientIdeal_precomp_snd
    {R X U V : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V]
    (k : ℕ) (f : U →ₗ[R] V) :
    determinantCoefficientIdeal (R := R) k
        (f ∘ₗ LinearMap.snd R X U) =
      determinantCoefficientIdeal (R := R) k f := by
  apply le_antisymm
  · exact determinantCoefficientIdeal_comp_le_right k
      (LinearMap.snd R X U) f
  · have hcomp :
        (f ∘ₗ LinearMap.snd R X U) ∘ₗ LinearMap.inr R X U = f := by
      ext x
      rfl
    calc
      determinantCoefficientIdeal (R := R) k f =
          determinantCoefficientIdeal (R := R) k
            ((f ∘ₗ LinearMap.snd R X U) ∘ₗ LinearMap.inr R X U) := by
              rw [hcomp]
      _ ≤ determinantCoefficientIdeal (R := R) k
          (f ∘ₗ LinearMap.snd R X U) := by
            simpa only [LinearMap.comp_assoc] using
              determinantCoefficientIdeal_comp_le_right k
                (LinearMap.inr R X U) (f ∘ₗ LinearMap.snd R X U)

private theorem determinantCoefficientIdeal_precomp_of_rightInverse
    {R X U V : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V]
    (k : ℕ) (f : U →ₗ[R] V) (s : X →ₗ[R] U) (r : U →ₗ[R] X)
    (hsr : s ∘ₗ r = LinearMap.id) :
    determinantCoefficientIdeal (R := R) k (f ∘ₗ s) =
      determinantCoefficientIdeal (R := R) k f := by
  apply le_antisymm
  · exact determinantCoefficientIdeal_comp_le_right k s f
  · calc
      determinantCoefficientIdeal (R := R) k f =
          determinantCoefficientIdeal (R := R) k
            ((f ∘ₗ s) ∘ₗ r) := by
              rw [LinearMap.comp_assoc, hsr]
              rfl
      _ ≤ determinantCoefficientIdeal (R := R) k (f ∘ₗ s) := by
        simpa only [LinearMap.comp_assoc] using
          determinantCoefficientIdeal_comp_le_right k r (f ∘ₗ s)

private theorem determinantCoefficientIdeal_prodMap
    {R : Type*} [CommRing R] (n m d k : ℕ)
    (f : (Fin n → R) →ₗ[R] (Fin m → R)) :
    determinantCoefficientIdeal (R := R) (k + d)
        (f.prodMap (LinearMap.id : (Fin d → R) →ₗ[R] (Fin d → R))) =
      determinantCoefficientIdeal (R := R) k f := by
  have hconj := determinantCoefficientIdeal_comp_eq_of_equiv
    (R := R) (k + d)
    (f.prodMap (LinearMap.id : (Fin d → R) →ₗ[R] (Fin d → R)))
    (piSumProdEquiv (R := R) n d).symm (piSumProdEquiv (R := R) m d)
  calc
    determinantCoefficientIdeal (R := R) (k + d)
        (f.prodMap (LinearMap.id : (Fin d → R) →ₗ[R] (Fin d → R))) =
        determinantCoefficientIdeal (R := R) (k + d)
          (piExtendMap n m d f) := by
            simpa only [piExtendMap_eq_sumConjugate] using hconj.symm
    _ = determinantCoefficientIdeal (R := R) k f :=
      determinantCoefficientIdeal_piExtendMap n m d k f

private theorem determinantCoefficientIdeal_zero
    {R U V : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (f : U →ₗ[R] V) :
    determinantCoefficientIdeal (R := R) 0 f = ⊤ := by
  rw [determinantCoefficientIdeal, Ideal.eq_top_iff_one]
  apply Ideal.subset_span
  refine ⟨(exteriorPower.zeroEquiv R U).symm 1,
    (exteriorPower.zeroEquiv R V).toLinearMap, ?_⟩
  have hnat := exteriorPower.zeroEquiv_naturality (R := R) f
  have h := congrArg (fun g => g ((exteriorPower.zeroEquiv R U).symm 1)) hnat
  simpa [determinantMap, LinearMap.comp_apply] using h.symm

private theorem determinantCoefficientIdeal_le_of_le_pi
    {R : Type*} [CommRing R] (n m k l : ℕ)
    (hkl : k ≤ l) (f : (Fin n → R) →ₗ[R] (Fin m → R)) :
    determinantCoefficientIdeal (R := R) l f ≤
      determinantCoefficientIdeal (R := R) k f := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l hkl ih =>
      exact (determinantCoefficientIdeal_succ_le_pi n m l f).trans ih

private theorem determinantCoefficientIdeal_piExtendMap_top_of_le
    {R : Type*} [CommRing R] (n m d k : ℕ)
    (hkd : k ≤ d) (f : (Fin n → R) →ₗ[R] (Fin m → R)) :
    determinantCoefficientIdeal (R := R) k (piExtendMap n m d f) = ⊤ := by
  have htop : determinantCoefficientIdeal (R := R) d
      (piExtendMap n m d f) = ⊤ := by
    calc
      determinantCoefficientIdeal (R := R) d (piExtendMap n m d f) =
          determinantCoefficientIdeal (R := R) 0 f := by
            simpa using determinantCoefficientIdeal_piExtendMap n m d 0 f
      _ = ⊤ := determinantCoefficientIdeal_zero f
  have hle := determinantCoefficientIdeal_le_of_le_pi
    (n + d) (m + d) k d hkd (piExtendMap n m d f)
  apply le_antisymm le_top
  rw [htop] at hle
  exact hle

private theorem determinantCoefficientIdeal_prodMap_top_of_le
    {R : Type*} [CommRing R] (n m d k : ℕ)
    (hkd : k ≤ d) (f : (Fin n → R) →ₗ[R] (Fin m → R)) :
    determinantCoefficientIdeal (R := R) k
        (f.prodMap (LinearMap.id : (Fin d → R) →ₗ[R] (Fin d → R))) = ⊤ := by
  calc
    determinantCoefficientIdeal (R := R) k
        (f.prodMap (LinearMap.id : (Fin d → R) →ₗ[R] (Fin d → R))) =
        determinantCoefficientIdeal (R := R) k (piExtendMap n m d f) := by
          simpa only [piExtendMap_eq_sumConjugate] using
            (determinantCoefficientIdeal_comp_eq_of_equiv
              (R := R) k
              (f.prodMap (LinearMap.id : (Fin d → R) →ₗ[R] (Fin d → R)))
              (piSumProdEquiv (R := R) n d).symm
              (piSumProdEquiv (R := R) m d)).symm
    _ = ⊤ := determinantCoefficientIdeal_piExtendMap_top_of_le
      n m d k hkd f

private theorem linearMap_factor_of_exact
    {R X K Y Z : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [Module.Projective R X]
    [AddCommGroup K] [Module R K] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z]
    (f : K →ₗ[R] Y) (g : Y →ₗ[R] Z) (hexact : Function.Exact f g)
    (u : X →ₗ[R] Y) (hu : ∀ x, g (u x) = 0) :
    ∃ v : X →ₗ[R] K, f ∘ₗ v = u := by
  let fker : K →ₗ[R] LinearMap.ker g :=
    f.codRestrict _ (fun x => by
      change g (f x) = 0
      have hx : f x ∈ LinearMap.range f := ⟨x, rfl⟩
      have hx' : f x ∈ LinearMap.ker g := by
        rw [LinearMap.exact_iff.mp hexact]
        exact hx
      exact hx')
  have hfker : Function.Surjective fker := by
    intro y
    have hy : y.1 ∈ LinearMap.range f := by
      rw [← LinearMap.exact_iff.mp hexact]
      exact y.2
    rcases hy with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  let uker : X →ₗ[R] LinearMap.ker g :=
    u.codRestrict _ (fun x => hu x)
  obtain ⟨v, hv⟩ := Module.projective_lifting_property fker uker hfker
  refine ⟨v, ?_⟩
  ext x
  have hx := congrArg (fun w => w x) hv
  exact congrArg Subtype.val hx

theorem fittingIdeal_eq_of_presentation
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] (P : FinitePresentationData R M) (i : ℕ) :
    fittingIdeal (R := R) (M := M) i = fittingIdealOfPresentation P i := by
  let Q : FinitePresentationData R M :=
    finitePresentationData (R := R) (M := M)
  have hPzero : P.presentation ∘ₗ P.relationMap = 0 := by
    apply LinearMap.ext
    intro x
    have hx : P.relationMap x ∈ LinearMap.ker P.presentation := by
      rw [LinearMap.exact_iff.mp P.exact]
      exact ⟨x, rfl⟩
    exact hx
  have hQzero : Q.presentation ∘ₗ Q.relationMap = 0 := by
    apply LinearMap.ext
    intro x
    have hx : Q.relationMap x ∈ LinearMap.ker Q.presentation := by
      rw [LinearMap.exact_iff.mp Q.exact]
      exact ⟨x, rfl⟩
    exact hx
  obtain ⟨α, hα⟩ :=
    Module.projective_lifting_property Q.presentation P.presentation
      Q.presentation_surjective
  have hαrel : ∀ x, Q.presentation (α (P.relationMap x)) = 0 := by
    intro x
    calc
      Q.presentation (α (P.relationMap x)) =
          P.presentation (P.relationMap x) := by
            simpa only [LinearMap.comp_apply] using
              congrArg (fun g => g (P.relationMap x)) hα
      _ = 0 := by
        simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
          congrArg (fun g => g x) hPzero
  obtain ⟨β, hβ⟩ :=
    linearMap_factor_of_exact Q.relationMap Q.presentation Q.exact
      (α ∘ₗ P.relationMap) hαrel
  obtain ⟨γ, hγ⟩ :=
    Module.projective_lifting_property P.presentation Q.presentation
      P.presentation_surjective
  have hγrel : ∀ x, P.presentation (γ (Q.relationMap x)) = 0 := by
    intro x
    calc
      P.presentation (γ (Q.relationMap x)) =
          Q.presentation (Q.relationMap x) := by
            simpa only [LinearMap.comp_apply] using
              congrArg (fun g => g (Q.relationMap x)) hγ
      _ = 0 := by
        simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
          congrArg (fun g => g x) hQzero
  obtain ⟨δ, hδ⟩ :=
    linearMap_factor_of_exact P.relationMap P.presentation P.exact
      (γ ∘ₗ Q.relationMap) hγrel
  let p :
      (Fin P.generators → R) × (Fin Q.generators → R) →ₗ[R] M :=
    P.presentation.comp (LinearMap.fst R (Fin P.generators → R)
      (Fin Q.generators → R)) +
      Q.presentation.comp (LinearMap.snd R (Fin P.generators → R)
        (Fin Q.generators → R))
  let h₁ :
      (Fin P.relations → R) ×
          ((Fin Q.relations → R) × (Fin P.generators → R)) →ₗ[R]
        (Fin P.generators → R) :=
    P.relationMap.comp (LinearMap.fst R (Fin P.relations → R)
      ((Fin Q.relations → R) × (Fin P.generators → R))) +
      (LinearMap.snd R (Fin Q.relations → R) (Fin P.generators → R)).comp
        (LinearMap.snd R (Fin P.relations → R)
          ((Fin Q.relations → R) × (Fin P.generators → R)))
  let h₂ :
      (Fin P.relations → R) ×
          ((Fin Q.relations → R) × (Fin P.generators → R)) →ₗ[R]
        (Fin Q.generators → R) :=
    Q.relationMap.comp
        ((LinearMap.fst R (Fin Q.relations → R) (Fin P.generators → R)).comp
          (LinearMap.snd R (Fin P.relations → R)
            ((Fin Q.relations → R) × (Fin P.generators → R)))) -
      α.comp
        ((LinearMap.snd R (Fin Q.relations → R) (Fin P.generators → R)).comp
          (LinearMap.snd R (Fin P.relations → R)
            ((Fin Q.relations → R) × (Fin P.generators → R))))
  let h := h₁.prod h₂
  let h₁' :
      (Fin P.relations → R) ×
          ((Fin Q.relations → R) × (Fin Q.generators → R)) →ₗ[R]
        (Fin P.generators → R) :=
    P.relationMap.comp (LinearMap.fst R (Fin P.relations → R)
      ((Fin Q.relations → R) × (Fin Q.generators → R))) -
      γ.comp
        ((LinearMap.snd R (Fin Q.relations → R) (Fin Q.generators → R)).comp
          (LinearMap.snd R (Fin P.relations → R)
            ((Fin Q.relations → R) × (Fin Q.generators → R))))
  let h₂' :
      (Fin P.relations → R) ×
          ((Fin Q.relations → R) × (Fin Q.generators → R)) →ₗ[R]
        (Fin Q.generators → R) :=
    Q.relationMap.comp
        ((LinearMap.fst R (Fin Q.relations → R) (Fin Q.generators → R)).comp
          (LinearMap.snd R (Fin P.relations → R)
            ((Fin Q.relations → R) × (Fin Q.generators → R)))) +
      (LinearMap.snd R (Fin Q.relations → R) (Fin Q.generators → R)).comp
        (LinearMap.snd R (Fin P.relations → R)
          ((Fin Q.relations → R) × (Fin Q.generators → R)))
  let h' := h₁'.prod h₂'
  have hzero : p ∘ₗ h = 0 := by
    apply LinearMap.ext
    rintro ⟨x, y, z⟩
    change
      P.presentation (P.relationMap x + z) +
          Q.presentation (Q.relationMap y - α z) = 0
    rw [map_add, map_sub]
    have hαz : Q.presentation (α z) = P.presentation z := by
      simpa only [LinearMap.comp_apply] using congrArg (fun g => g z) hα
    have hx := congrArg (fun g => g x) hPzero
    have hy := congrArg (fun g => g y) hQzero
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hx hy
    rw [hαz, hx, hy]
    abel
  have h'zero : p ∘ₗ h' = 0 := by
    apply LinearMap.ext
    rintro ⟨x, y, z⟩
    change
      P.presentation (P.relationMap x - γ z) +
          Q.presentation (Q.relationMap y + z) = 0
    rw [map_sub, map_add]
    have hγz : P.presentation (γ z) = Q.presentation z := by
      simpa only [LinearMap.comp_apply] using congrArg (fun g => g z) hγ
    have hx := congrArg (fun g => g x) hPzero
    have hy := congrArg (fun g => g y) hQzero
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hx hy
    rw [hγz, hx, hy]
    abel
  have hexact : Function.Exact h p := by
    apply LinearMap.exact_of_comp_eq_zero_of_ker_le_range hzero
    rintro ⟨u, v⟩ hz
    change P.presentation u + Q.presentation v = 0 at hz
    have hαu : Q.presentation (α u) = P.presentation u := by
      simpa only [LinearMap.comp_apply] using congrArg (fun g => g u) hα
    have hvzero : Q.presentation (v + α u) = 0 := by
      rw [map_add, hαu]
      rw [add_comm]
      exact hz
    have hvrange : v + α u ∈ LinearMap.range Q.relationMap := by
      rw [← LinearMap.exact_iff.mp Q.exact]
      exact hvzero
    rcases hvrange with ⟨y, hy⟩
    refine ⟨(0, (y, u)), ?_⟩
    apply Prod.ext
    · change P.relationMap 0 + u = u
      simp
    · change Q.relationMap y - α u = v
      rw [hy]
      abel
  have hexact' : Function.Exact h' p := by
    apply LinearMap.exact_of_comp_eq_zero_of_ker_le_range h'zero
    rintro ⟨u, v⟩ hz
    change P.presentation u + Q.presentation v = 0 at hz
    have hγv : P.presentation (γ v) = Q.presentation v := by
      simpa only [LinearMap.comp_apply] using congrArg (fun g => g v) hγ
    have huzero : P.presentation (u + γ v) = 0 := by
      rw [map_add, hγv]
      exact hz
    have hurange : u + γ v ∈ LinearMap.range P.relationMap := by
      rw [← LinearMap.exact_iff.mp P.exact]
      exact huzero
    rcases hurange with ⟨x, hx⟩
    refine ⟨(x, (0, v)), ?_⟩
    apply Prod.ext
    · change P.relationMap x - γ v = u
      rw [hx]
      abel
    · change Q.relationMap 0 + v = v
      simp
  have hzero' : ∀ x, p (h x) = 0 := by
    intro x
    have hx := congrArg (fun g => g x) hzero
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hx
  have h'zero' : ∀ x, p (h' x) = 0 := by
    intro x
    have hx := congrArg (fun g => g x) h'zero
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hx
  obtain ⟨s, hs⟩ := linearMap_factor_of_exact h' p hexact' h hzero'
  obtain ⟨t, ht⟩ := linearMap_factor_of_exact h p hexact h' h'zero'
  have hfit : ∀ k, determinantCoefficientIdeal (R := R) k h =
      determinantCoefficientIdeal (R := R) k h' := by
    intro k
    apply le_antisymm
    · calc
        determinantCoefficientIdeal (R := R) k h =
            determinantCoefficientIdeal (R := R) k (h' ∘ₗ s) := by rw [hs]
        _ ≤ determinantCoefficientIdeal (R := R) k h' :=
          determinantCoefficientIdeal_comp_le_right k s h'
    · calc
        determinantCoefficientIdeal (R := R) k h' =
            determinantCoefficientIdeal (R := R) k (h ∘ₗ t) := by rw [ht]
        _ ≤ determinantCoefficientIdeal (R := R) k h :=
          determinantCoefficientIdeal_comp_le_right k t h
  let eDomQ :
      ((Fin P.relations → R) ×
          ((Fin Q.relations → R) × (Fin P.generators → R))) ≃ₗ[R]
        ((Fin P.relations → R) ×
          ((Fin Q.relations → R) × (Fin P.generators → R))) :=
    { toFun := fun z => (z.1, (z.2.1 + β z.1, z.2.2 + P.relationMap z.1))
      invFun := fun z => (z.1, (z.2.1 - β z.1, z.2.2 - P.relationMap z.1))
      left_inv := by
        intro z
        rcases z with ⟨x, y, w⟩
        simp
      right_inv := by
        intro z
        rcases z with ⟨x, y, w⟩
        simp
      map_add' := by
        intro x y
        ext <;> simp [map_add, add_assoc, add_comm, add_left_comm]
      map_smul' := by
        intro c x
        ext <;> simp }
  let eCodQ :
      ((Fin P.generators → R) × (Fin Q.generators → R)) ≃ₗ[R]
        ((Fin P.generators → R) × (Fin Q.generators → R)) :=
    { toFun := fun z => (z.1, z.2 + α z.1)
      invFun := fun z => (z.1, z.2 - α z.1)
      left_inv := by
        intro z
        simp
      right_inv := by
        intro z
        simp
      map_add' := by
        intro x y
        ext <;> simp [map_add, add_assoc, add_comm, add_left_comm]
      map_smul' := by
        intro c x
        ext <;> simp }
  let hQ₁ :
      (Fin P.relations → R) ×
          ((Fin Q.relations → R) × (Fin P.generators → R)) →ₗ[R]
        (Fin P.generators → R) :=
    LinearMap.snd R (Fin Q.relations → R) (Fin P.generators → R) ∘ₗ
      LinearMap.snd R (Fin P.relations → R)
        ((Fin Q.relations → R) × (Fin P.generators → R))
  let hQ₂ :
      (Fin P.relations → R) ×
          ((Fin Q.relations → R) × (Fin P.generators → R)) →ₗ[R]
        (Fin Q.generators → R) :=
    Q.relationMap.comp
      ((LinearMap.fst R (Fin Q.relations → R) (Fin P.generators → R)).comp
        (LinearMap.snd R (Fin P.relations → R)
          ((Fin Q.relations → R) × (Fin P.generators → R))))
  let hQ := hQ₁.prod hQ₂
  have hQconj :
      eCodQ.toLinearMap ∘ₗ h ∘ₗ eDomQ.symm.toLinearMap = hQ := by
    apply LinearMap.ext
    rintro ⟨x, y, z⟩
    change
      (P.relationMap x + (z - P.relationMap x),
          Q.relationMap (y - β x) - α (z - P.relationMap x) +
            α (P.relationMap x + (z - P.relationMap x))) =
        (z, Q.relationMap y)
    have hβx := congrArg (fun g => g x) hβ
    simp only [LinearMap.comp_apply] at hβx
    rw [map_sub, map_add, hβx]
    apply Prod.ext <;> abel_nf
  let eDomP :
      ((Fin P.relations → R) ×
          ((Fin Q.relations → R) × (Fin Q.generators → R))) ≃ₗ[R]
        ((Fin P.relations → R) ×
          ((Fin Q.relations → R) × (Fin Q.generators → R))) :=
    { toFun := fun z => (z.1 + δ z.2.1, (z.2.1, z.2.2 + Q.relationMap z.2.1))
      invFun := fun z => (z.1 - δ z.2.1, (z.2.1, z.2.2 - Q.relationMap z.2.1))
      left_inv := by
        intro z
        rcases z with ⟨x, y, w⟩
        simp
      right_inv := by
        intro z
        rcases z with ⟨x, y, w⟩
        simp
      map_add' := by
        intro a b
        rcases a with ⟨x, y, z⟩
        rcases b with ⟨x', y', z'⟩
        apply Prod.ext
        · change (x + x') + δ (y + y') =
            (x + δ y) + (x' + δ y')
          rw [map_add]
          abel
        · apply Prod.ext
          · rfl
          · change (z + z') + Q.relationMap (y + y') =
              (z + Q.relationMap y) + (z' + Q.relationMap y')
            rw [map_add]
            abel
      map_smul' := by
        intro c x
        ext <;> simp }
  let eCodP :
      ((Fin P.generators → R) × (Fin Q.generators → R)) ≃ₗ[R]
        ((Fin P.generators → R) × (Fin Q.generators → R)) :=
    { toFun := fun z => (z.1 + γ z.2, z.2)
      invFun := fun z => (z.1 - γ z.2, z.2)
      left_inv := by
        intro z
        simp
      right_inv := by
        intro z
        simp
      map_add' := by
        intro x y
        ext <;> simp [map_add, add_assoc, add_comm, add_left_comm]
      map_smul' := by
        intro c x
        ext <;> simp }
  let hP₁ :
      (Fin P.relations → R) ×
          ((Fin Q.relations → R) × (Fin Q.generators → R)) →ₗ[R]
        (Fin P.generators → R) :=
    P.relationMap.comp (LinearMap.fst R (Fin P.relations → R)
      ((Fin Q.relations → R) × (Fin Q.generators → R)))
  let hP₂ :
      (Fin P.relations → R) ×
          ((Fin Q.relations → R) × (Fin Q.generators → R)) →ₗ[R]
        (Fin Q.generators → R) :=
    LinearMap.snd R (Fin Q.relations → R) (Fin Q.generators → R) ∘ₗ
      LinearMap.snd R (Fin P.relations → R)
        ((Fin Q.relations → R) × (Fin Q.generators → R))
  let hP := hP₁.prod hP₂
  have hPconj :
      eCodP.toLinearMap ∘ₗ h' ∘ₗ eDomP.symm.toLinearMap = hP := by
    apply LinearMap.ext
    rintro ⟨x, y, z⟩
    change
      (P.relationMap (x - δ y) - γ (z - Q.relationMap y) +
          γ (Q.relationMap y + (z - Q.relationMap y)),
        Q.relationMap y + (z - Q.relationMap y)) =
        (P.relationMap x, z)
    have hδy := congrArg (fun g => g y) hδ
    simp only [LinearMap.comp_apply] at hδy
    rw [map_sub, map_add, hδy]
    apply Prod.ext <;> abel_nf
  have hfitQconj : ∀ k, determinantCoefficientIdeal (R := R) k hQ =
      determinantCoefficientIdeal (R := R) k h := by
    intro k
    have hh := determinantCoefficientIdeal_comp_eq_of_equiv
      (R := R) k h eDomQ.symm eCodQ
    simpa only [hQconj] using hh
  have hfitPconj : ∀ k, determinantCoefficientIdeal (R := R) k hP =
      determinantCoefficientIdeal (R := R) k h' := by
    intro k
    have hh := determinantCoefficientIdeal_comp_eq_of_equiv
      (R := R) k h' eDomP.symm eCodP
    simpa only [hPconj] using hh
  let qprod :
      ((Fin Q.relations → R) × (Fin P.generators → R)) →ₗ[R]
        ((Fin Q.generators → R) × (Fin P.generators → R)) :=
    Q.relationMap.prodMap
      (LinearMap.id : (Fin P.generators → R) →ₗ[R] (Fin P.generators → R))
  let qdrop :
      ((Fin P.relations → R) ×
          ((Fin Q.relations → R) × (Fin P.generators → R))) →ₗ[R]
        ((Fin Q.relations → R) × (Fin P.generators → R)) :=
    LinearMap.snd R (Fin P.relations → R)
      ((Fin Q.relations → R) × (Fin P.generators → R))
  let qswap :
      ((Fin Q.generators → R) × (Fin P.generators → R)) ≃ₗ[R]
        ((Fin P.generators → R) × (Fin Q.generators → R)) :=
    LinearEquiv.prodComm R (Fin Q.generators → R) (Fin P.generators → R)
  have hQfactor : qswap.toLinearMap ∘ₗ qprod ∘ₗ qdrop = hQ := by
    apply LinearMap.ext
    rintro ⟨x, y, z⟩
    simp [qprod, qdrop, qswap, hQ, hQ₁, hQ₂, LinearMap.comp_apply]
  have hfitQprod : ∀ k, determinantCoefficientIdeal (R := R) k hQ =
      determinantCoefficientIdeal (R := R) k qprod := by
    intro k
    calc
      determinantCoefficientIdeal (R := R) k hQ =
          determinantCoefficientIdeal (R := R) k
            (qswap.toLinearMap ∘ₗ qprod ∘ₗ qdrop) := by rw [hQfactor]
      _ = determinantCoefficientIdeal (R := R) k (qprod ∘ₗ qdrop) := by
        have hqrefl :
            qswap.toLinearMap ∘ₗ (qprod ∘ₗ qdrop) ∘ₗ
                (LinearEquiv.refl R _).toLinearMap =
              qswap.toLinearMap ∘ₗ qprod ∘ₗ qdrop := by
          apply LinearMap.ext
          intro z
          simp only [LinearMap.comp_apply]
          rfl
        have hh := determinantCoefficientIdeal_comp_eq_of_equiv
          (R := R) k (qprod ∘ₗ qdrop) (LinearEquiv.refl R _) qswap
        rw [hqrefl] at hh
        exact hh
      _ = determinantCoefficientIdeal (R := R) k qprod :=
        determinantCoefficientIdeal_precomp_snd k qprod
  let pprod :
      ((Fin P.relations → R) × (Fin Q.generators → R)) →ₗ[R]
        ((Fin P.generators → R) × (Fin Q.generators → R)) :=
    P.relationMap.prodMap
      (LinearMap.id : (Fin Q.generators → R) →ₗ[R] (Fin Q.generators → R))
  let pdrop :
      ((Fin P.relations → R) ×
          ((Fin Q.relations → R) × (Fin Q.generators → R))) →ₗ[R]
        ((Fin P.relations → R) × (Fin Q.generators → R)) :=
    (LinearMap.fst R (Fin P.relations → R)
      ((Fin Q.relations → R) × (Fin Q.generators → R))).prod
      ((LinearMap.snd R (Fin Q.relations → R) (Fin Q.generators → R)).comp
        (LinearMap.snd R (Fin P.relations → R)
          ((Fin Q.relations → R) × (Fin Q.generators → R))))
  let psection :
      ((Fin P.relations → R) × (Fin Q.generators → R)) →ₗ[R]
        ((Fin P.relations → R) ×
          ((Fin Q.relations → R) × (Fin Q.generators → R))) :=
    (LinearMap.fst R (Fin P.relations → R) (Fin Q.generators → R)).prod
      ((0 : ((Fin P.relations → R) × (Fin Q.generators → R)) →ₗ[R]
          (Fin Q.relations → R)).prod
        (LinearMap.snd R (Fin P.relations → R) (Fin Q.generators → R)))
  have hpsection : pdrop ∘ₗ psection = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨x, z⟩
    simp [pdrop, psection, LinearMap.comp_apply]
  have hPfactor : pprod ∘ₗ pdrop = hP := by
    apply LinearMap.ext
    rintro ⟨x, y, z⟩
    simp [pprod, pdrop, hP, hP₁, hP₂, LinearMap.comp_apply]
  have hfitPprod : ∀ k, determinantCoefficientIdeal (R := R) k hP =
      determinantCoefficientIdeal (R := R) k pprod := by
    intro k
    calc
      determinantCoefficientIdeal (R := R) k hP =
          determinantCoefficientIdeal (R := R) k (pprod ∘ₗ pdrop) := by
            rw [hPfactor]
      _ = determinantCoefficientIdeal (R := R) k pprod :=
        determinantCoefficientIdeal_precomp_of_rightInverse
          k pprod pdrop psection hpsection
  change determinantCoefficientIdeal (R := R) (Q.generators - i) Q.relationMap =
    determinantCoefficientIdeal (R := R) (P.generators - i) P.relationMap
  have hcommon (k : ℕ) :
      determinantCoefficientIdeal (R := R) k qprod =
        determinantCoefficientIdeal (R := R) k pprod := by
    calc
      determinantCoefficientIdeal (R := R) k qprod =
          determinantCoefficientIdeal (R := R) k hQ := (hfitQprod k).symm
      _ = determinantCoefficientIdeal (R := R) k h := hfitQconj k
      _ = determinantCoefficientIdeal (R := R) k h' := hfit k
      _ = determinantCoefficientIdeal (R := R) k hP := (hfitPconj k).symm
      _ = determinantCoefficientIdeal (R := R) k pprod := hfitPprod k
  have hQprod (k : ℕ) :
      determinantCoefficientIdeal (R := R) (k + P.generators) qprod =
        determinantCoefficientIdeal (R := R) k Q.relationMap := by
    simpa [qprod] using
      (determinantCoefficientIdeal_prodMap
        (R := R) Q.relations Q.generators P.generators k Q.relationMap)
  have hPprod (k : ℕ) :
      determinantCoefficientIdeal (R := R) (k + Q.generators) pprod =
        determinantCoefficientIdeal (R := R) k P.relationMap := by
    simpa [pprod] using
      (determinantCoefficientIdeal_prodMap
        (R := R) P.relations P.generators Q.generators k P.relationMap)
  by_cases hPi : i ≤ P.generators
  · by_cases hQi : i ≤ Q.generators
    · have hQsum :
          (Q.generators - i) + P.generators =
            P.generators + Q.generators - i := by omega
      have hPsum :
          (P.generators - i) + Q.generators =
            P.generators + Q.generators - i := by omega
      calc
        determinantCoefficientIdeal (R := R) (Q.generators - i) Q.relationMap =
            determinantCoefficientIdeal (R := R)
              ((Q.generators - i) + P.generators) qprod :=
          (hQprod (Q.generators - i)).symm
        _ = determinantCoefficientIdeal (R := R)
              (P.generators + Q.generators - i) qprod := by rw [hQsum]
        _ = determinantCoefficientIdeal (R := R)
              (P.generators + Q.generators - i) pprod := hcommon _
        _ = determinantCoefficientIdeal (R := R)
              ((P.generators - i) + Q.generators) pprod := by rw [hPsum]
        _ = determinantCoefficientIdeal (R := R) (P.generators - i) P.relationMap :=
          hPprod (P.generators - i)
    · have hQ_le_i : Q.generators ≤ i := Nat.le_of_not_ge hQi
      have hQ_le_P : Q.generators ≤ P.generators := by omega
      have hqtop :
          determinantCoefficientIdeal (R := R) P.generators qprod = ⊤ := by
        calc
          determinantCoefficientIdeal (R := R) P.generators qprod =
              determinantCoefficientIdeal (R := R) (0 + P.generators) qprod := by
                rw [zero_add]
          _ = determinantCoefficientIdeal (R := R) 0 Q.relationMap := hQprod 0
          _ = ⊤ := determinantCoefficientIdeal_zero Q.relationMap
      have hpRelTop :
          determinantCoefficientIdeal (R := R)
              (P.generators - Q.generators) P.relationMap = ⊤ := by
        calc
          determinantCoefficientIdeal (R := R)
              (P.generators - Q.generators) P.relationMap =
              determinantCoefficientIdeal (R := R)
                ((P.generators - Q.generators) + Q.generators) pprod :=
            (hPprod (P.generators - Q.generators)).symm
          _ = determinantCoefficientIdeal (R := R) P.generators pprod := by
            rw [Nat.sub_add_cancel hQ_le_P]
          _ = determinantCoefficientIdeal (R := R) P.generators qprod := (hcommon _).symm
          _ = ⊤ := hqtop
      have hPmono : P.generators - i ≤ P.generators - Q.generators := by omega
      have hpTop :
          determinantCoefficientIdeal (R := R)
              (P.generators - i) P.relationMap = ⊤ := by
        apply le_antisymm le_top
        have hle := determinantCoefficientIdeal_le_of_le_pi
          P.relations P.generators (P.generators - i)
            (P.generators - Q.generators) hPmono P.relationMap
        rw [hpRelTop] at hle
        exact hle
      have hqTop :
          determinantCoefficientIdeal (R := R) (Q.generators - i) Q.relationMap = ⊤ := by
        rw [Nat.sub_eq_zero_of_le hQ_le_i]
        exact determinantCoefficientIdeal_zero Q.relationMap
      rw [hqTop, hpTop]
  · have hP_le_i : P.generators ≤ i := Nat.le_of_not_ge hPi
    by_cases hQi : i ≤ Q.generators
    · have hP_le_Q : P.generators ≤ Q.generators := by omega
      have hqtop :
          determinantCoefficientIdeal (R := R) Q.generators pprod = ⊤ := by
        calc
          determinantCoefficientIdeal (R := R) Q.generators pprod =
              determinantCoefficientIdeal (R := R) (0 + Q.generators) pprod := by
                rw [zero_add]
          _ = determinantCoefficientIdeal (R := R) 0 P.relationMap := hPprod 0
          _ = ⊤ := determinantCoefficientIdeal_zero P.relationMap
      have hqRelTop :
          determinantCoefficientIdeal (R := R)
              (Q.generators - P.generators) Q.relationMap = ⊤ := by
        calc
          determinantCoefficientIdeal (R := R)
              (Q.generators - P.generators) Q.relationMap =
              determinantCoefficientIdeal (R := R)
                ((Q.generators - P.generators) + P.generators) qprod :=
            (hQprod (Q.generators - P.generators)).symm
          _ = determinantCoefficientIdeal (R := R) Q.generators qprod := by
            rw [Nat.sub_add_cancel hP_le_Q]
          _ = determinantCoefficientIdeal (R := R) Q.generators pprod := hcommon _
          _ = ⊤ := hqtop
      have hQmono : Q.generators - i ≤ Q.generators - P.generators := by omega
      have hqTop :
          determinantCoefficientIdeal (R := R)
              (Q.generators - i) Q.relationMap = ⊤ := by
        apply le_antisymm le_top
        have hle := determinantCoefficientIdeal_le_of_le_pi
          Q.relations Q.generators (Q.generators - i)
            (Q.generators - P.generators) hQmono Q.relationMap
        rw [hqRelTop] at hle
        exact hle
      have hpTop :
          determinantCoefficientIdeal (R := R) (P.generators - i) P.relationMap = ⊤ := by
        rw [Nat.sub_eq_zero_of_le hP_le_i]
        exact determinantCoefficientIdeal_zero P.relationMap
      rw [hqTop, hpTop]
    · have hQ_le_i : Q.generators ≤ i := Nat.le_of_not_ge hQi
      have hqTop :
          determinantCoefficientIdeal (R := R) (Q.generators - i) Q.relationMap = ⊤ := by
        rw [Nat.sub_eq_zero_of_le hQ_le_i]
        exact determinantCoefficientIdeal_zero Q.relationMap
      have hpTop :
          determinantCoefficientIdeal (R := R) (P.generators - i) P.relationMap = ⊤ := by
        rw [Nat.sub_eq_zero_of_le hP_le_i]
        exact determinantCoefficientIdeal_zero P.relationMap
      rw [hqTop, hpTop]

theorem fittingIdeal_baseChange
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FinitePresentation A M] (i : ℕ) :
    fittingIdeal (R := B) (M := B ⊗[A] M) i =
      (fittingIdeal (R := A) (M := M) i).map (algebraMap A B) := by
  let P : FinitePresentationData A M :=
    finitePresentationData (R := A) (M := M)
  let e0 : B ⊗[A] (Fin P.generators → A) ≃ₗ[B] (Fin P.generators → B) :=
    piBaseChangeEquiv (A := A) (B := B) P.generators
  let e1 : B ⊗[A] (Fin P.relations → A) ≃ₗ[B] (Fin P.relations → B) :=
    piBaseChangeEquiv (A := A) (B := B) P.relations
  have hp0 : Function.Surjective (P.presentation.baseChange B) := by
    exact LinearMap.baseChange_surjective B P.presentation_surjective
  have hbase_exact :
      Function.Exact (P.relationMap.baseChange B) (P.presentation.baseChange B) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using
      (lTensor_exact B P.exact P.presentation_surjective)
  have hconj :
      Function.Exact
        (e0.toLinearMap ∘ₗ P.relationMap.baseChange B)
        (P.presentation.baseChange B ∘ₗ e0.symm.toLinearMap) := by
    exact
      (LinearEquiv.conj_exact_iff_exact (P.relationMap.baseChange B)
        (P.presentation.baseChange B) e0).2 hbase_exact
  have hpre :
      Function.Exact
        ((e0.toLinearMap ∘ₗ P.relationMap.baseChange B) ∘ₗ e1.symm.toLinearMap)
        (P.presentation.baseChange B ∘ₗ e0.symm.toLinearMap) := by
    exact (e1.symm.precomp_exact_iff_exact).2 hconj
  let P_B : FinitePresentationData B (B ⊗[A] M) :=
    { generators := P.generators
      relations := P.relations
      presentation := P.presentation.baseChange B ∘ₗ e0.symm.toLinearMap
      relationMap := e0.toLinearMap ∘ₗ (P.relationMap.baseChange B ∘ₗ e1.symm.toLinearMap)
      presentation_surjective := hp0.comp e0.symm.surjective
      exact := by
        simpa only [LinearMap.comp_assoc] using hpre }
  rw [fittingIdeal_eq_of_presentation P_B]
  change fittingIdealOfPresentation P_B i =
    (fittingIdealOfPresentation P i).map (algebraMap A B)
  rw [fittingIdealOfPresentation_eq_determinantCoefficientIdeal P_B i,
    fittingIdealOfPresentation_eq_determinantCoefficientIdeal P i]
  change determinantCoefficientIdeal (R := B) (P.generators - i)
      (e0.toLinearMap ∘ₗ
        (P.relationMap.baseChange B ∘ₗ e1.symm.toLinearMap)) =
    (determinantCoefficientIdeal (R := A) (P.generators - i) P.relationMap).map
      (algebraMap A B)
  calc
    determinantCoefficientIdeal (R := B) (P.generators - i)
        (e0.toLinearMap ∘ₗ
          (P.relationMap.baseChange B ∘ₗ e1.symm.toLinearMap)) =
        determinantCoefficientIdeal (R := B) (P.generators - i)
          (P.relationMap.baseChange B) := by
            simpa only [LinearMap.comp_assoc] using
              determinantCoefficientIdeal_comp_eq_of_equiv
                (P.generators - i) (P.relationMap.baseChange B) e1.symm e0
    _ = (determinantCoefficientIdeal (R := A) (P.generators - i)
      P.relationMap).map (algebraMap A B) :=
        determinantCoefficientIdeal_baseChange
          (A := A) (B := B) (n := P.relations) (m := P.generators)
          (P.generators - i) P.relationMap

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
