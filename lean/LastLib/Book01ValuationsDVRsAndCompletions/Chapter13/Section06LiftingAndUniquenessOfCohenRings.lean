import LastLib.Book01ValuationsDVRsAndCompletions.Chapter13.Section05CohenRingsExistence
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.RingTheory.Teichmuller
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.TrivSqZeroExt.Basic

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter13

open Filter Ideal IsLocalRing

noncomputable section

/-! # Book 1, Chapter 13, Section 13.6: The lifting property and uniqueness of Cohen rings -/

universe u v

/-- A square-zero thickening with nilpotent prime. -/
def Chapter13SquareZeroPrimeExtension
    (R : Type u) [CommRing R] (I : Ideal R) (p : ℕ) : Prop :=
  I ^ 2 = ⊥ ∧ ∃ M : ℕ, (p : R) ^ M = 0

/-- Compatibility of a ring map with specified residue-field identifications. -/
def Chapter13ResidueMapCompatibility
    {C A k ℓ : Type*}
    [CommRing C] [IsLocalRing C] [CommRing A] [IsLocalRing A]
    [Field k] [Field ℓ]
    (eC : Chapter13ResidueRing C ≃+* k)
    (eA : Chapter13ResidueRing A ≃+* ℓ)
    (φ : k →+* ℓ) (u : C →+* A) : Prop :=
  ∀ c : C,
    eA (Chapter13ResidueMap A (u c)) = φ (eC (Chapter13ResidueMap C c))

/-- Convergence of a sequence for an adic filtration. -/
def Chapter13AdicSequenceConverges
    {A : Type*} [CommRing A] (I : Ideal A)
    (z : ℕ → A) (x : A) : Prop :=
  ∀ n : ℕ, Filter.Eventually
    (fun m : ℕ => z m - x ∈ I ^ n) (atTop : Filter ℕ)

/-- The completed polynomial ring used as a smooth presentation of a Cohen ring. -/
abbrev Chapter13CohenSmoothPresentation
    (k : Type u) (p : ℕ) : Type u :=
  AdicCompletion (Ideal.span {(p : MvPolynomial k ℤ)}) (MvPolynomial k ℤ)

/-- The variable indexed by a residue-field element in the smooth presentation. -/
def Chapter13CohenSmoothVariable
    (k : Type u) (p : ℕ) (x : k) : Chapter13CohenSmoothPresentation k p :=
  algebraMap (MvPolynomial k ℤ) (Chapter13CohenSmoothPresentation k p)
    (MvPolynomial.X x)

/-- Rigidity of Cohen-ring maps with fixed residue map and fixed `p`-basis lifts. -/
theorem chapter13_cohen_lift_rigidity
    {C R : Type u} [CommRing C] [IsLocalRing C] [CommRing R]
    {k : Type v} [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hC : Chapter13IsCohenRing C k p)
    (I : Ideal R) (hI : Chapter13SquareZeroPrimeExtension R I p)
    (B : Set k) (hB : Chapter13PBasis (Chapter13PthPowerSubfield k p) B p)
    (γ : B → C) (eC : Chapter13ResidueRing C ≃+* k)
    (hγ : ∀ b : B, eC (Chapter13ResidueMap C (γ b)) = b)
    (u u' : C →+* R)
    (hquot : (Ideal.Quotient.mk I).comp u = (Ideal.Quotient.mk I).comp u')
    (hlift : ∀ b : B, u (γ b) = u' (γ b)) :
    u = u' := by
  sorry

/-- The completed polynomial presentation has the expected finite-level quotients. -/
theorem chapter13_cohen_smooth_presentation_quotients
    (k : Type u) [Field k] (p n : ℕ) [Fact (Nat.Prime p)] [CharP k p] :
    Nonempty
      (Chapter13CohenSmoothPresentation k p ⧸
          Ideal.span {((p : Chapter13CohenSmoothPresentation k p) ^ n)} ≃+*
        MvPolynomial k (ZMod (p ^ n))) := by
  let P := MvPolynomial k ℤ
  let I : Ideal P := Ideal.span {(p : P)}
  let E := AdicCompletion I P
  have hIFG : I.FG := by
    exact Submodule.fg_span (Set.finite_singleton (p : P))
  have hmapI : Ideal.map (algebraMap P E) (I ^ n) =
      Ideal.span {((p : E) ^ n)} := by
    dsimp [I]
    rw [Ideal.span_singleton_pow, Ideal.map_span]
    simp [AdicCompletion.algebraMap_apply]
  have hkerEval : RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      Ideal.span {((p : E) ^ n)} := by
    ext x
    constructor
    · intro hx
      change (AdicCompletion.evalₐ I n) x = 0 at hx
      have hx' : AdicCompletion.eval I P n x = 0 := by
        rw [← AdicCompletion.factor_evalₐ_eq_eval I x (by simp)]
        simpa using congrArg
          (Ideal.Quotient.factor (show I ^ n ≤ I ^ n • ⊤ by simp)) hx
      have hx'' : x ∈ I ^ n • (⊤ : Submodule P E) := by
        rw [AdicCompletion.pow_smul_top_eq_ker_eval hIFG]
        exact hx'
      rw [Ideal.smul_top_eq_map, hmapI] at hx''
      exact hx''
    · intro hx
      have hx' : x ∈ I ^ n • (⊤ : Submodule P E) := by
        rw [Ideal.smul_top_eq_map, hmapI]
        exact hx
      have hx'' : AdicCompletion.eval I P n x = 0 := by
        have hx''' : x ∈ (AdicCompletion.eval I P n).ker := by
          rw [← AdicCompletion.pow_smul_top_eq_ker_eval hIFG]
          exact hx'
        change AdicCompletion.eval I P n x = 0 at hx'''
        exact hx'''
      have heq : I ^ n • (⊤ : Ideal P) = I ^ n := by simp
      have hfactor : Function.Injective
          (Ideal.Quotient.factor (show I ^ n ≤ I ^ n • ⊤ by
            exact le_of_eq heq.symm)) := by
        simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker] using
          Ideal.map_mk_eq_bot_of_le (le_of_eq heq.symm)
      apply hfactor
      change (Ideal.Quotient.factor (show I ^ n ≤ I ^ n • ⊤ by
        exact le_of_eq heq.symm)) ((AdicCompletion.evalₐ I n) x) = 0
      rw [AdicCompletion.factor_evalₐ_eq_eval]
      exact hx''
  have hIpow : I ^ n = Ideal.span {((p ^ n : ℕ) : P)} := by
    simp [I, Ideal.span_singleton_pow]
  let qE : E ⧸ Ideal.span {((p : E) ^ n)} ≃+* P ⧸ I ^ n :=
    (Ideal.quotEquivOfEq hkerEval).symm.trans
      (RingHom.quotientKerEquivOfSurjective
        (AdicCompletion.surjective_evalₐ I n))
  let qI : P ⧸ I ^ n ≃+* P ⧸ Ideal.span {((p ^ n : ℕ) : P)} :=
    Ideal.quotEquivOfEq hIpow
  let qP : P ⧸ Ideal.span {((p ^ n : ℕ) : P)} ≃+*
      MvPolynomial k (ZMod (p ^ n)) := by
    let hmap : Ideal.map (MvPolynomial.C : ℤ →+* P)
        (Ideal.span {((p ^ n : ℕ) : ℤ)}) =
        Ideal.span {((p ^ n : ℕ) : P)} := by
      rw [Ideal.map_span]
      congr 2
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [Set.mem_singleton_iff.mp hy]
      · intro hx
        refine ⟨(p ^ n : ℤ), Set.mem_singleton _, ?_⟩
        simpa [Set.mem_singleton_iff.mp hx]
    let eCoeff := Int.quotientSpanNatEquivZMod (p ^ n)
    let eMv := MvPolynomial.mapEquiv k eCoeff
    let ePoly := MvPolynomial.quotientEquivQuotientMvPolynomial
      (σ := k) (Ideal.span {((p ^ n : ℕ) : ℤ)})
    let eIdeal := Ideal.quotEquivOfEq hmap
    exact eIdeal.symm.trans (ePoly.toRingEquiv.symm.trans eMv)
  exact ⟨qE.trans (qI.trans qP)⟩

/-- Homomorphisms out of the smooth presentation are arbitrary on its variables. -/
theorem chapter13_cohen_smooth_presentation_ring_homs
    {k R : Type u} [Field k] [CommRing R] (p M : ℕ)
    [Fact (Nat.Prime p)] [CharP k p]
    (hM : (p : R) ^ M = 0) :
    Function.Bijective
      (fun f : Chapter13CohenSmoothPresentation k p →+* R =>
        fun x : k => f (Chapter13CohenSmoothVariable k p x)) := by
  let P := MvPolynomial k ℤ
  let I : Ideal P := Ideal.span {(p : P)}
  let E := AdicCompletion I P
  have hIFG : I.FG := by
    exact Submodule.fg_span (Set.finite_singleton (p : P))
  have hmapI : Ideal.map (algebraMap P E) (I ^ M) =
      Ideal.span {((p : E) ^ M)} := by
    dsimp [I]
    rw [Ideal.span_singleton_pow, Ideal.map_span]
    simp [AdicCompletion.algebraMap_apply]
  have hkerEval : RingHom.ker (AdicCompletion.evalₐ I M).toRingHom =
      Ideal.span {((p : E) ^ M)} := by
    ext x
    constructor
    · intro hx
      change (AdicCompletion.evalₐ I M) x = 0 at hx
      have hx' : AdicCompletion.eval I P M x = 0 := by
        rw [← AdicCompletion.factor_evalₐ_eq_eval I x (by simp)]
        simpa using congrArg
          (Ideal.Quotient.factor (show I ^ M ≤ I ^ M • ⊤ by simp)) hx
      have hx'' : x ∈ I ^ M • (⊤ : Submodule P E) := by
        rw [AdicCompletion.pow_smul_top_eq_ker_eval hIFG]
        exact hx'
      rw [Ideal.smul_top_eq_map, hmapI] at hx''
      exact hx''
    · intro hx
      have hx' : x ∈ I ^ M • (⊤ : Submodule P E) := by
        rw [Ideal.smul_top_eq_map, hmapI]
        exact hx
      have hx'' : AdicCompletion.eval I P M x = 0 := by
        have hx''' : x ∈ (AdicCompletion.eval I P M).ker := by
          rw [← AdicCompletion.pow_smul_top_eq_ker_eval hIFG]
          exact hx'
        change AdicCompletion.eval I P M x = 0 at hx'''
        exact hx'''
      have heq : I ^ M • (⊤ : Ideal P) = I ^ M := by simp
      have hfactor : Function.Injective
          (Ideal.Quotient.factor (show I ^ M ≤ I ^ M • ⊤ by
            exact le_of_eq heq.symm)) := by
        simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker] using
          Ideal.map_mk_eq_bot_of_le (le_of_eq heq.symm)
      apply hfactor
      change (Ideal.Quotient.factor (show I ^ M ≤ I ^ M • ⊤ by
        exact le_of_eq heq.symm)) ((AdicCompletion.evalₐ I M) x) = 0
      rw [AdicCompletion.factor_evalₐ_eq_eval]
      exact hx''
  have hIpow : I ^ M = Ideal.span {((p ^ M : ℕ) : P)} := by
    simp [I, Ideal.span_singleton_pow]
  have hmap : Ideal.map (MvPolynomial.C : ℤ →+* P)
      (Ideal.span {((p ^ M : ℕ) : ℤ)}) = Ideal.span {((p ^ M : ℕ) : P)} := by
    rw [Ideal.map_span]
    congr 2
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [Set.mem_singleton_iff.mp hy]
    · intro hx
      refine ⟨(p ^ M : ℤ), Set.mem_singleton _, ?_⟩
      simpa [Set.mem_singleton_iff.mp hx]
  let eCoeff := Int.quotientSpanNatEquivZMod (p ^ M)
  let eMv := MvPolynomial.mapEquiv k eCoeff
  let ePoly := MvPolynomial.quotientEquivQuotientMvPolynomial
    (σ := k) (Ideal.span {((p ^ M : ℕ) : ℤ)})
  let eIdeal := Ideal.quotEquivOfEq hmap
  let qP : P ⧸ Ideal.span {((p ^ M : ℕ) : P)} ≃+* MvPolynomial k (ZMod (p ^ M)) :=
    eIdeal.symm.trans (ePoly.toRingEquiv.symm.trans eMv)
  let qI : P ⧸ I ^ M ≃+* P ⧸ Ideal.span {((p ^ M : ℕ) : P)} :=
    Ideal.quotEquivOfEq hIpow
  let Φ : E →+* MvPolynomial k (ZMod (p ^ M)) :=
    qP.toRingHom.comp (qI.toRingHom.comp (AdicCompletion.evalₐ I M).toRingHom)
  have hΦsurj : Function.Surjective Φ := by
    exact qP.surjective.comp (qI.surjective.comp (AdicCompletion.surjective_evalₐ I M))
  have hkerΦ : RingHom.ker Φ = Ideal.span {((p : E) ^ M)} := by
    ext x
    change Φ x = 0 ↔ x ∈ Ideal.span {((p : E) ^ M)}
    constructor
    · intro hx
      have hx' : (AdicCompletion.evalₐ I M) x = 0 := by
        apply qI.injective
        apply qP.injective
        simpa [Φ] using hx
      have hx'' : x ∈ RingHom.ker (AdicCompletion.evalₐ I M).toRingHom := hx'
      rwa [hkerEval] at hx''
    · intro hx
      have hx' : (AdicCompletion.evalₐ I M) x = 0 := by
        have hx'' : x ∈ RingHom.ker (AdicCompletion.evalₐ I M).toRingHom := by
          rwa [hkerEval]
        exact hx''
      simpa [Φ] using congrArg qP (congrArg qI hx')
  have hΦvar (x : k) : Φ (Chapter13CohenSmoothVariable k p x) = MvPolynomial.X x := by
    have hqI : qI ((Ideal.Quotient.mk (I ^ M)) (MvPolynomial.X x)) =
        Ideal.Quotient.mk (Ideal.span {((p ^ M : ℕ) : P)}) (MvPolynomial.X x) := by
      simp [qI]
    have hePoly : ePoly.symm
        (Ideal.Quotient.mk (Ideal.map (MvPolynomial.C : ℤ →+* P)
          (Ideal.span {((p ^ M : ℕ) : ℤ)})) (MvPolynomial.X x)) =
        MvPolynomial.X x := by
      apply ePoly.injective
      simp [ePoly, MvPolynomial.quotientEquivQuotientMvPolynomial]
    have heIdeal : eIdeal.symm
        (Ideal.Quotient.mk (Ideal.span {((p ^ M : ℕ) : P)}) (MvPolynomial.X x)) =
        Ideal.Quotient.mk (Ideal.map (MvPolynomial.C : ℤ →+* P)
          (Ideal.span {((p ^ M : ℕ) : ℤ)})) (MvPolynomial.X x) := by
      exact Ideal.quotEquivOfEq_mk hmap.symm (MvPolynomial.X x)
    change qP (qI ((Ideal.Quotient.mk (I ^ M)) (MvPolynomial.X x))) =
      MvPolynomial.X x
    rw [hqI]
    change eMv (ePoly.symm (eIdeal.symm
      (Ideal.Quotient.mk (Ideal.span {((p ^ M : ℕ) : P)}) (MvPolynomial.X x)))) =
      MvPolynomial.X x
    rw [heIdeal, hePoly]
    simp [eMv, eCoeff]
  obtain ⟨q, hq⟩ := CharP.exists R
  letI : CharP R q := hq
  have hdiv : q ∣ p ^ M := by
    apply (CharP.cast_eq_zero_iff R q (p ^ M)).mp
    simpa [Nat.cast_pow] using hM
  let coeff : ZMod (p ^ M) →+* R := ZMod.castHom hdiv R
  let F : (k → R) → (E →+* R) := fun d =>
    (MvPolynomial.eval₂Hom coeff d).comp Φ
  have hFvar (d : k → R) (x : k) :
      F d (Chapter13CohenSmoothVariable k p x) = d x := by
    simp [F, hΦvar]
  have factorization : ∀ f : E →+* R,
      f = F (fun x : k => f (Chapter13CohenSmoothVariable k p x)) := by
    intro f
    have hkill : ∀ z ∈ Ideal.span {((p : E) ^ M)}, f z = 0 := by
      intro z hz
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hz
      rw [hy, map_mul, map_pow]
      have hfp : f (p : E) = (p : R) := map_natCast f p
      rw [hfp, hM, zero_mul]
    let qΦ := RingHom.quotientKerEquivOfSurjective hΦsurj
    have hkillKer : ∀ z ∈ RingHom.ker Φ, f z = 0 := by
      intro z hz
      apply hkill z
      rw [← hkerΦ]
      exact hz
    let fbar : E ⧸ RingHom.ker Φ →+* R :=
      Ideal.Quotient.lift _ f hkillKer
    let g : MvPolynomial k (ZMod (p ^ M)) →+* R :=
      fbar.comp qΦ.symm.toRingHom
    have hgΦ : g.comp Φ = f := by
      ext z
      change fbar (qΦ.symm (Φ z)) = f z
      rw [show qΦ.symm (Φ z) = Ideal.Quotient.mk (RingHom.ker Φ) z by
        simpa [qΦ] using congrFun
          (RingHom.quotientKerEquivOfSurjective_symm_comp hΦsurj) z]
      exact Ideal.Quotient.lift_mk _ _ _
    have hgC : ∀ z : ZMod (p ^ M),
        g (MvPolynomial.C z) = (MvPolynomial.eval₂Hom coeff
          (fun x : k => f (Chapter13CohenSmoothVariable k p x))) (MvPolynomial.C z) := by
      intro z
      obtain ⟨a, rfl⟩ := ZMod.intCast_surjective z
      simp [g, coeff]
    have hgX : ∀ x : k,
        g (MvPolynomial.X x) = (MvPolynomial.eval₂Hom coeff
          (fun x : k => f (Chapter13CohenSmoothVariable k p x))) (MvPolynomial.X x) := by
      intro x
      calc
        g (MvPolynomial.X x) = g (Φ (Chapter13CohenSmoothVariable k p x)) := by
          rw [hΦvar]
        _ = f (Chapter13CohenSmoothVariable k p x) := by
          simpa [RingHom.comp_apply] using
            congrArg (fun h : E →+* R => h (Chapter13CohenSmoothVariable k p x)) hgΦ
        _ = (MvPolynomial.eval₂Hom coeff
            (fun x : k => f (Chapter13CohenSmoothVariable k p x))) (MvPolynomial.X x) := by
          simp
    have hgeq : g = MvPolynomial.eval₂Hom coeff
        (fun x : k => f (Chapter13CohenSmoothVariable k p x)) :=
      MvPolynomial.ringHom_ext hgC hgX
    calc
      f = g.comp Φ := hgΦ.symm
      _ = (MvPolynomial.eval₂Hom coeff
          (fun x : k => f (Chapter13CohenSmoothVariable k p x))).comp Φ := by
        rw [hgeq]
      _ = F (fun x : k => f (Chapter13CohenSmoothVariable k p x)) := by
        rfl
  constructor
  · intro f g hfg
    calc
      f = F (fun x : k => f (Chapter13CohenSmoothVariable k p x)) := factorization f
      _ = F (fun x : k => g (Chapter13CohenSmoothVariable k p x)) := by
        exact congrArg F hfg
      _ = g := (factorization g).symm
  · intro d
    refine ⟨F d, ?_⟩
    exact funext (hFvar d)

/-- Derivations out of the smooth presentation are arbitrary on its variables. -/
theorem chapter13_cohen_smooth_presentation_derivations
    {k N : Type u} [Field k] [AddCommGroup N]
    (p M : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    [Module (Chapter13CohenSmoothPresentation k p) N]
    (hM : ∀ n : N,
      (p : Chapter13CohenSmoothPresentation k p) ^ M • n = 0) :
    Function.Bijective
      (fun D : Derivation ℤ (Chapter13CohenSmoothPresentation k p) N =>
        fun x : k => D (Chapter13CohenSmoothVariable k p x)) := by
  let E := Chapter13CohenSmoothPresentation k p
  let J : Ideal E := Ideal.span {((p : E) ^ M)}
  let q : E →+* (E ⧸ J) := Ideal.Quotient.mk J
  let lsmulE : E →+* Module.End E N := (Algebra.lsmul ℤ E N).toRingHom
  have hp : lsmulE ((p : E) ^ M) = 0 := by
    ext n
    change (p : E) ^ M • n = 0
    exact hM n
  have hJ : ∀ x : E, x ∈ J → lsmulE x = 0 := by
    intro x hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
    rw [hy, map_mul, hp, zero_mul]
  let lsmulQ : (E ⧸ J) →+* Module.End E N :=
    Ideal.Quotient.lift J lsmulE hJ
  letI : Module (E ⧸ J) N :=
    { smul := fun r n => lsmulQ r n
      one_smul := by intro n; change lsmulQ 1 n = n; rw [map_one]; rfl
      mul_smul := by
        intro r s n
        change lsmulQ (r * s) n = lsmulQ r (lsmulQ s n)
        rw [map_mul]
        rfl
      smul_add := by
        intro r x y
        change lsmulQ r (x + y) = lsmulQ r x + lsmulQ r y
        exact (lsmulQ r).map_add x y
      smul_zero := by
        intro r
        change lsmulQ r 0 = 0
        exact (lsmulQ r).map_zero
      add_smul := by
        intro r s n
        change lsmulQ (r + s) n = lsmulQ r n + lsmulQ s n
        rw [map_add]
        rfl
      zero_smul := by
        intro n
        change lsmulQ 0 n = 0
        rw [map_zero]
        rfl }
  letI : Module (E ⧸ J)ᵐᵒᵖ N :=
    Module.compHom N ((RingHom.id (E ⧸ J)).fromOpposite mul_comm)
  letI : IsCentralScalar (E ⧸ J) N :=
    ⟨fun r n => by rfl⟩
  let B := TrivSqZeroExt (E ⧸ J) N
  letI : CommRing B := by
    dsimp [B]
    infer_instance
  have hq : ((p : E ⧸ J) ^ M) = 0 := by
    change Ideal.Quotient.mk J ((p : E) ^ M) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simp [J])
  have hMB : (p : B) ^ M = 0 := by
    change ((TrivSqZeroExt.inlHom (E ⧸ J) N) (p : E ⧸ J)) ^ M = 0
    rw [← (TrivSqZeroExt.inlHom (E ⧸ J) N).map_pow]
    rw [hq]
    exact (TrivSqZeroExt.inlHom (E ⧸ J) N).map_zero
  have hq_smul (x : E) (n : N) : q x • n = x • n := by
    change lsmulQ (q x) n = lsmulE x n
    simp [q, lsmulQ]
  let encode : Derivation ℤ E N → E →+* B := fun D =>
    { toFun := fun x => (q x, D x)
      map_one' := by
        ext <;> simp [q]
      map_zero' := by
        ext <;> simp [q]
      map_add' := by
        intro x y
        change (q (x + y), D (x + y)) = (q x, D x) + (q y, D y)
        ext <;> simp [q]
      map_mul' := by
        intro x y
        let ux : B := (q x, D x)
        let uy : B := (q y, D y)
        ext
        · change TrivSqZeroExt.fst
            ((q (x * y), D (x * y)) : B) = TrivSqZeroExt.fst (ux * uy)
          rw [TrivSqZeroExt.fst_mul]
          change q (x * y) = q x * q y
          exact q.map_mul x y
        · change TrivSqZeroExt.snd
            ((q (x * y), D (x * y)) : B) = TrivSqZeroExt.snd (ux * uy)
          rw [TrivSqZeroExt.snd_mul]
          change D (x * y) = q x • D y + q y • D x
          rw [D.leibniz]
          rw [hq_smul, hq_smul] }
  let homs := chapter13_cohen_smooth_presentation_ring_homs
    (k := k) (R := B) p M hMB
  constructor
  · intro D₁ D₂ hD
    have henc : encode D₁ = encode D₂ := by
      apply homs.1
      funext x
      apply Prod.ext
      · rfl
      · exact congrFun hD x
    apply Derivation.ext
    intro x
    exact congrArg (fun f : E →+* B => (f x).2) henc
  · intro δ
    let b : k → B := fun x => (q (Chapter13CohenSmoothVariable k p x), δ x)
    obtain ⟨F, hF⟩ := homs.2 b
    let fstF : E →+* (E ⧸ J) :=
      (TrivSqZeroExt.fstHom (E ⧸ J) (E ⧸ J) N).toRingHom.comp F
    have hfst : fstF = q := by
      have hqH := chapter13_cohen_smooth_presentation_ring_homs
        (k := k) (R := E ⧸ J) p M hq
      have hvars : (fun x : k =>
          TrivSqZeroExt.fst (F (Chapter13CohenSmoothVariable k p x))) =
          (fun x : k => q (Chapter13CohenSmoothVariable k p x)) := by
        funext x
        have hx := congrArg TrivSqZeroExt.fst (congrFun hF x)
        simpa [b] using hx
      exact hqH.1 hvars
    let dAdd : E →+ N :=
      (TrivSqZeroExt.sndHom (E ⧸ J) N).toAddMonoidHom.comp F.toAddMonoidHom
    let d : E →ₗ[ℤ] N := dAdd.toIntLinearMap
    let D : Derivation ℤ E N := Derivation.mk' d (by
      intro x y
      change (F (x * y)).2 = x • (F y).2 + y • (F x).2
      change (F (x * y)).2 = x • TrivSqZeroExt.snd (F y) +
        y • TrivSqZeroExt.snd (F x)
      have hm := congrArg Prod.snd (F.map_mul x y)
      change (F (x * y)).2 = TrivSqZeroExt.snd (F x * F y) at hm
      have hfx : TrivSqZeroExt.fst (F x) = q x := by
        simpa [fstF] using congrArg (fun f : E →+* (E ⧸ J) => f x) hfst
      have hfy : TrivSqZeroExt.fst (F y) = q y := by
        simpa [fstF] using congrArg (fun f : E →+* (E ⧸ J) => f y) hfst
      rw [TrivSqZeroExt.snd_mul] at hm
      simpa [hfx, hfy, smul_comm, hq_smul] using hm)
    refine ⟨D, ?_⟩
    funext x
    have hx := congrArg Prod.snd (congrFun hF x)
    exact hx

/-- A chosen set of residue lifts gives a surjective map from the smooth presentation. -/
theorem chapter13_cohen_smooth_presentation_surjective
    {C k : Type u} [CommRing C] [IsLocalRing C] [Field k] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p]
    (hC : Chapter13IsCohenRing C k p)
    (eC : Chapter13ResidueRing C ≃+* k) (c : k → C)
    (hc : ∀ x : k, eC (Chapter13ResidueMap C (c x)) = x) :
    ∃ π : Chapter13CohenSmoothPresentation k p →+* C,
      Function.Surjective π ∧
        (∀ x : k, π (Chapter13CohenSmoothVariable k p x) = c x) ∧
        ∃ J : Ideal (Chapter13CohenSmoothPresentation k p),
          J = RingHom.ker π ∧
            ∀ n : ℕ, ∀ z,
              z ∈ J ∧ z ∈ Ideal.span {((p : Chapter13CohenSmoothPresentation k p) ^ n)} ↔
              ∃ y ∈ J, z = (p : Chapter13CohenSmoothPresentation k p) ^ n * y := by
  let m : Ideal C := IsLocalRing.maximalIdeal C
  let P := MvPolynomial k ℤ
  let IP : Ideal P := Ideal.span {(p : P)}
  let E := AdicCompletion IP P
  let IE : Ideal E := Ideal.map (algebraMap P E) IP
  have hmax : m = Ideal.span {(p : C)} := by
    simpa [m] using hC.1.2.1
  letI : IsAdicComplete m C := by
    simpa [m] using hC.2
  have hp_mem (n : ℕ) : (p : C) ^ n ∈ m ^ n := by
    rw [hmax, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  have hpn (n : ℕ) : (p : C ⧸ m ^ n) ^ n = 0 := by
    change Ideal.Quotient.mk (m ^ n) ((p : C) ^ n) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hp_mem n)
  let f : ∀ n : ℕ, E →+* C ⧸ m ^ n := fun n =>
    Classical.choose ((chapter13_cohen_smooth_presentation_ring_homs
      (k := k) (R := C ⧸ m ^ n) p n (hpn n)).2
      (fun x : k => Ideal.Quotient.mk (m ^ n) (c x)))
  have hfvar (n : ℕ) :
      (fun x : k => f n (Chapter13CohenSmoothVariable k p x)) =
        (fun x : k => Ideal.Quotient.mk (m ^ n) (c x)) := by
    simpa [f] using Classical.choose_spec ((chapter13_cohen_smooth_presentation_ring_homs
      (k := k) (R := C ⧸ m ^ n) p n (hpn n)).2
      (fun x : k => Ideal.Quotient.mk (m ^ n) (c x)))
  have hf : ∀ {r n : ℕ} (hr : r ≤ n),
      (Ideal.Quotient.factorPow m hr).comp (f n) = f r := by
    intro r n hr
    apply (chapter13_cohen_smooth_presentation_ring_homs
      (k := k) (R := C ⧸ m ^ r) p r (hpn r)).1
    funext x
    change Ideal.Quotient.factorPow m hr (f n (Chapter13CohenSmoothVariable k p x)) =
      f r (Chapter13CohenSmoothVariable k p x)
    rw [congrFun (hfvar n) x, congrFun (hfvar r) x]
    rfl
  let π : E →+* C := IsAdicComplete.liftRingHom m f hf
  have hπvar (x : k) : π (Chapter13CohenSmoothVariable k p x) = c x := by
    apply (IsHausdorff.eq_iff_smodEq (I := m)).2
    intro n
    have hn := IsAdicComplete.mk_liftRingHom m f hf n
      (Chapter13CohenSmoothVariable k p x)
    rw [SModEq.sub_mem]
    simp only [smul_eq_mul, Ideal.mul_top]
    have heq : Ideal.Quotient.mk (m ^ n)
        (π (Chapter13CohenSmoothVariable k p x)) =
        Ideal.Quotient.mk (m ^ n) (c x) := by
      have hn' : Ideal.Quotient.mk (m ^ n)
          (π (Chapter13CohenSmoothVariable k p x)) =
          f n (Chapter13CohenSmoothVariable k p x) := by
        simpa [π] using hn
      exact hn'.trans (congrFun (hfvar n) x)
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp heq
  have hIE : IE = Ideal.span {(p : E)} := by
    dsimp [IE, IP]
    rw [Ideal.map_span]
    simp [AdicCompletion.algebraMap_apply]
  have hnat : ∀ n : ℕ, π (n : E) = (n : C) := by
    intro n
    induction n with
    | zero =>
        rw [Nat.cast_zero]
        simpa using (map_zero π)
    | succ n ih =>
        rw [Nat.cast_succ, map_add, map_one, ih]
        exact (Nat.cast_succ n).symm
  have hπp : π (p : E) = (p : C) := hnat p
  have hmapI : Ideal.map π IE = m := by
    rw [hIE, Ideal.map_span]
    rw [hmax]
    simpa only [Set.image_singleton] using
      congrArg (fun t : C => Ideal.span {t}) hπp
  have hquot_surj : Function.Surjective
      ((Ideal.Quotient.mk (Ideal.map π IE)).comp π) := by
    rw [hmapI]
    intro z
    obtain ⟨x, hx⟩ := eC.symm.surjective z
    refine ⟨Chapter13CohenSmoothVariable k p x, ?_⟩
    apply eC.injective
    change eC (Ideal.Quotient.mk m (π (Chapter13CohenSmoothVariable k p x))) = eC z
    have hcx : eC (Ideal.Quotient.mk m (c x)) = x := by
      change eC (Chapter13ResidueMap C (c x)) = x
      exact hc x
    rw [hπvar x, hcx]
    simpa using congrArg eC hx
  letI : IsAdicComplete IE E := by
    apply (IsAdicComplete.map_algebraMap_iff (I := IP) (M := E)).2
    exact AdicCompletion.isAdicComplete (M := P)
      (Submodule.fg_span (Set.finite_singleton (p : P)))
  letI : IsHausdorff (Ideal.map π IE) C := by
    rw [hmapI]
    infer_instance
  have hπsurj : Function.Surjective π :=
    surjective_of_mk_map_comp_surjective π hquot_surj
  refine ⟨π, hπsurj, hπvar, ?_⟩
  let J : Ideal E := RingHom.ker π
  refine ⟨J, rfl, ?_⟩
  obtain ⟨hdom, hdvr⟩ := hC.1.1
  letI : IsDomain C := hdom
  letI : IsDiscreteValuationRing C := hdvr
  have hp_ne : (p : C) ≠ 0 := by
    intro hp
    have hmne : m ≠ ⊥ := by
      simpa [m] using IsDiscreteValuationRing.not_a_field C
    apply hmne
    rw [hmax, hp]
    simp
  intro n z
  constructor
  · rintro ⟨hzJ, hzpow⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hzpow
    refine ⟨y, ?_, hy⟩
    change π y = 0
    have hz0 : (p : C) ^ n * π y = 0 := by
      calc
        (p : C) ^ n * π y = π ((p : E) ^ n * y) := by
          rw [map_mul, map_pow]
          rw [hπp]
        _ = π z := by rw [hy]
        _ = 0 := hzJ
    exact (mul_eq_zero.mp hz0).resolve_left (pow_ne_zero n hp_ne)
  · rintro ⟨y, hyJ, rfl⟩
    change π y = 0 at hyJ
    refine ⟨?_, ?_⟩
    · change π ((p : E) ^ n * y) = 0
      simp [hyJ]
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- Cohen rings lift maps across square-zero thickenings with nilpotent prime. -/
theorem chapter13_cohen_lift_across_square_zero
    {C R : Type u} [CommRing C] [IsLocalRing C] [CommRing R]
    {k : Type v} [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hC : Chapter13IsCohenRing C k p)
    (I : Ideal R) (hI : Chapter13SquareZeroPrimeExtension R I p)
    (v : C →+* (R ⧸ I)) :
    ∃ u : C →+* R, (Ideal.Quotient.mk I).comp u = v := by
  sorry

/-- The mapping property of a Cohen ring into a complete local ring. -/
theorem chapter13_cohen_ring_mapping_property
    {C A : Type u} [CommRing C] [IsLocalRing C] [CommRing A] [IsLocalRing A]
    {k ℓ : Type v} [Field k] [Field ℓ] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p] [CharP ℓ p]
    (hC : Chapter13IsCohenRing C k p)
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (eC : Chapter13ResidueRing C ≃+* k)
    (eA : Chapter13ResidueRing A ≃+* ℓ)
    (φ : k →+* ℓ) :
    ∃ u : C →+* A,
      IsLocalHom u ∧ Chapter13ResidueMapCompatibility eC eA φ u := by
  sorry

/-- Uniqueness of the mapping property after fixing lifts of a `p`-basis. -/
theorem chapter13_cohen_ring_mapping_property_unique
    {C A : Type u} [CommRing C] [IsLocalRing C] [CommRing A] [IsLocalRing A]
    {k ℓ : Type v} [Field k] [Field ℓ] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p] [CharP ℓ p]
    (hC : Chapter13IsCohenRing C k p)
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (eC : Chapter13ResidueRing C ≃+* k)
    (eA : Chapter13ResidueRing A ≃+* ℓ)
    (φ : k →+* ℓ) (B : Set k)
    (hB : Chapter13PBasis (Chapter13PthPowerSubfield k p) B p)
    (γ : B → C) (u u' : C →+* A)
    (hγ : ∀ b : B, eC (Chapter13ResidueMap C (γ b)) = b)
    (hu : IsLocalHom u ∧ Chapter13ResidueMapCompatibility eC eA φ u)
    (hu' : IsLocalHom u' ∧ Chapter13ResidueMapCompatibility eC eA φ u')
    (hlift : ∀ b : B, u (γ b) = u' (γ b)) :
    u = u' := by
  sorry

/-- Existence and isomorphism of maps between Cohen rings with the same residue field. -/
theorem chapter13_cohen_ring_uniqueness
    {C C' k : Type u} [CommRing C] [IsLocalRing C]
    [CommRing C'] [IsLocalRing C'] [Field k] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p]
    (hC : Chapter13IsCohenRing C k p)
    (hC' : Chapter13IsCohenRing C' k p)
    (eC : Chapter13ResidueRing C ≃+* k)
    (eC' : Chapter13ResidueRing C' ≃+* k) :
    (∃ u : C →+* C', IsLocalHom u ∧
      Chapter13ResidueMapCompatibility eC eC' (RingHom.id k) u) ∧
      (∀ u : C →+* C', IsLocalHom u →
        Chapter13ResidueMapCompatibility eC eC' (RingHom.id k) u →
        ∃ e : C ≃+* C', e.toRingHom = u) := by
  sorry

/-- An imperfect residue field permits nontrivial Cohen-ring automorphisms over the residue map. -/
theorem chapter13_imperfect_cohen_noncanonical_automorphism
    {C k : Type u} [CommRing C] [IsLocalRing C] [Field k] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p]
    (hC : Chapter13IsCohenRing C k p)
    (eC : Chapter13ResidueRing C ≃+* k)
    (B : Set k) (hB : Chapter13PBasis (Chapter13PthPowerSubfield k p) B p)
    (b : B) (γ : B → C) (hp : (p : C) ≠ 0)
    (hγ : ∀ x : B, eC (Chapter13ResidueMap C (γ x)) = x) :
    ∃ σ : C →+* C,
      IsLocalHom σ ∧
        Chapter13ResidueMapCompatibility eC eC (RingHom.id k) σ ∧
        σ (γ b) = γ b + (p : C) ∧
        Function.Bijective σ ∧ σ ≠ RingHom.id C := by
  sorry

/-- Perfect residue fields have unique Cohen-ring maps. -/
theorem chapter13_perfect_cohen_mapping_unique
    {C A : Type u} [CommRing C] [IsLocalRing C] [CommRing A] [IsLocalRing A]
    {k ℓ : Type v} [Field k] [Field ℓ] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p] [CharP ℓ p]
    (hC : Chapter13IsCohenRing C k p)
    (hperfect : Chapter13PerfectAtPrime k p)
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (eC : Chapter13ResidueRing C ≃+* k)
    (eA : Chapter13ResidueRing A ≃+* ℓ) (φ : k →+* ℓ) :
    ∃! u : C →+* A,
      IsLocalHom u ∧ Chapter13ResidueMapCompatibility eC eA φ u := by
  obtain ⟨u, hu, hcompat⟩ := chapter13_cohen_ring_mapping_property
    p hC hA eC eA φ
  refine ⟨u, ⟨hu, hcompat⟩, ?_⟩
  intro v hv
  let B : Set k := ∅
  have hB : Chapter13PBasis (Chapter13PthPowerSubfield k p) B p :=
    chapter13_perfect_field_empty_p_basis p hperfect
  symm
  apply chapter13_cohen_ring_mapping_property_unique
    p hC hA eC eA φ B hB (fun b => b.property.elim) u v
  · intro b
    exact b.property.elim
  · exact ⟨hu, hcompat⟩
  · exact hv
  · intro b
    exact b.property.elim

/-- The multiplicative Teichmuller section in the perfect case. -/
theorem chapter13_teichmuller_lift
    {C k : Type u} [CommRing C] [IsLocalRing C] [Field k] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p]
    (hC : Chapter13IsCohenRing C k p)
    (hperfect : Chapter13PerfectAtPrime k p)
    (eC : Chapter13ResidueRing C ≃+* k) :
    ∃ τ : k →* C,
      (∀ x : k, eC (Chapter13ResidueMap C (τ x)) = x) ∧
        (∀ x : k, ∃ y : ℕ → C,
          (∀ n : ℕ,
            eC (Chapter13ResidueMap C (y n)) ^ (p ^ n) = x) ∧
          Chapter13AdicSequenceConverges
            (IsLocalRing.maximalIdeal C)
            (fun n : ℕ => (y n) ^ (p ^ n)) (τ x)) := by
  let I : Ideal C := IsLocalRing.maximalIdeal C
  letI : CharP (C ⧸ I) p := by
    apply (eC.symm.toRingHom.charP_iff_charP p).mp
    infer_instance
  letI : IsAdicComplete I C := by
    simpa [I] using hC.2
  letI : PerfectRing k p := PerfectRing.ofSurjective k p (by
    unfold Chapter13PerfectAtPrime at hperfect
    change Function.Surjective (fun x : k => x ^ p)
    exact hperfect)
  let lift : k →* Perfection (C ⧸ I) p :=
    Perfection.liftMonoidHom p k (C ⧸ I) eC.symm.toMonoidHom
  let τ : k →* C := (Perfection.teichmuller p I).comp lift
  refine ⟨τ, ?_, ?_⟩
  · intro x
    change eC (Ideal.Quotient.mk I (τ x)) = x
    rw [show τ x = Perfection.teichmuller p I (lift x) by rfl,
      Perfection.mk_teichmuller]
    change eC (Perfection.coeffMonoidHom (C ⧸ I) p 0 (lift x)) = x
    simp [lift]
  · intro x
    let y : ℕ → C := fun n =>
      (Ideal.Quotient.mk_surjective (I := I)
        (Perfection.coeff (C ⧸ I) p n (lift x))).choose
    have hy : ∀ n : ℕ,
        Ideal.Quotient.mk I (y n) = Perfection.coeff (C ⧸ I) p n (lift x) := by
      intro n
      exact (Ideal.Quotient.mk_surjective (I := I)
        (Perfection.coeff (C ⧸ I) p n (lift x))).choose_spec
    refine ⟨y, ?_, ?_⟩
    · intro n
      change eC (Ideal.Quotient.mk I (y n)) ^ (p ^ n) = x
      rw [hy n]
      rw [← map_pow]
      change eC ((Perfection.coeffMonoidHom (C ⧸ I) p n (lift x)) ^ (p ^ n)) = x
      rw [Perfection.coeffMonoidHom_pow_p_pow_self]
      change eC (Perfection.coeff (C ⧸ I) p 0 (lift x)) = x
      change eC (Perfection.coeffMonoidHom (C ⧸ I) p 0 (lift x)) = x
      rw [Perfection.coeffMonoidHom_zero_liftMonoidHom]
      simpa using eC.apply_symm_apply x
    · intro n
      filter_upwards [eventually_ge_atTop n] with m hm
      have hsm :
          Perfection.teichmuller p I (lift x) ≡ (y m) ^ (p ^ m)
            [SMOD I ^ (m + 1)] :=
        Perfection.teichmuller_sModEq (hy m)
      have hdiff : (y m) ^ (p ^ m) - τ x ∈ I ^ (m + 1) := by
        exact SModEq.sub_mem.mp hsm.symm
      exact (Ideal.pow_le_pow_right (Nat.le_trans hm (Nat.le_succ _))) hdiff

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter13
