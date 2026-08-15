import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section07NormsAndIdeals

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators Polynomial

/-! ## 4.5. Residue-field shadows -/

/- A residue map is recorded by its quotient kernel and surjectivity. -/
def chapter04ResidueMap
    (R k : Type*) [CommRing R] [Field k] (m : Ideal R)
    (ρ : R →+* k) : Prop :=
  Function.Surjective ρ ∧ ∀ x : R, ρ x = 0 ↔ x ∈ m

@[simp] theorem chapter04ResidueMap_iff
    (R k : Type*) [CommRing R] [Field k] (m : Ideal R)
    (ρ : R →+* k) :
    chapter04ResidueMap R k m ρ ↔
      Function.Surjective ρ ∧ ∀ x : R, ρ x = 0 ↔ x ∈ m := Iff.rfl

theorem chapter04ResidueMap_ker_eq
    (R k : Type*) [CommRing R] [Field k] (m : Ideal R)
    (ρ : R →+* k) (hρ : chapter04ResidueMap R k m ρ) :
    RingHom.ker ρ = m := by
  ext x
  rw [RingHom.mem_ker]
  exact hρ.2 x

/- A residue map identifies its quotient with the target field. -/
theorem chapter04ResidueMap_quotient_equiv
    (R k : Type*) [CommRing R] [Field k] (m : Ideal R)
    (ρ : R →+* k) (hρ : chapter04ResidueMap R k m ρ) :
    Nonempty ((R ⧸ m) ≃+* k) := by
  let e : (R ⧸ m) ≃+* k :=
    (Ideal.quotEquivOfEq (chapter04ResidueMap_ker_eq R k m ρ hρ).symm).trans
      (RingHom.quotientKerEquivOfSurjective hρ.1)
  exact ⟨e⟩

/- The pair of reduced formulas used in Proposition 4.2 (§4.5). -/
def chapter04ResidueTraceNormStatement
    {A B k l : Type*} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra k l] [FiniteDimensional k l]
    (redA : A →+* k) (redB : B →+* l)
    (e : ℕ) (t n : A) (x u : B) : Prop :=
  redA t = (e : k) * Algebra.trace k l (redB x) ∧
    redA n = Algebra.norm k (redB u) ^ e

@[simp] theorem chapter04ResidueTraceNormStatement_iff
    {A B k l : Type*} [CommRing A] [CommRing B] [Field k] [Field l]
    [Algebra k l] [FiniteDimensional k l]
    (redA : A →+* k) (redB : B →+* l)
    (e : ℕ) (t n : A) (x u : B) :
    chapter04ResidueTraceNormStatement redA redB e t n x u ↔
      redA t = (e : k) * Algebra.trace k l (redB x) ∧
        redA n = Algebra.norm k (redB u) ^ e := Iff.rfl

/-
Proposition 4.2.  The maps `redA` and `redB` are explicit residue maps, and
`hcompat` says that the local algebra map descends to the residue extension.
This avoids identifying quotient representatives by definitional equality.
-/
theorem chapter04_residue_trace_and_norm
    (A B K L k l : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [IsDedekindDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Field k] [Field l] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L]
    [IsScalarTower A K L] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Algebra k l] [FiniteDimensional k l]
    [IsIntegrallyClosed A] [Module.Finite A B]
    [Module.Free A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (redA : A →+* k) (redB : B →+* l)
    (hredA : chapter04ResidueMap A k (IsLocalRing.maximalIdeal A) redA)
    (hredB : chapter04ResidueMap B l (IsLocalRing.maximalIdeal B) redB)
    (hcompat : ∀ a : A,
      redB (algebraMap A B a) = algebraMap k l (redA a))
    (e : ℕ) (t n : A) (x : B) (u : Bˣ)
    (htrace : algebraMap A K t = Algebra.trace K L (algebraMap B L x))
    (hnorm : algebraMap A K n = Algebra.norm K (algebraMap B L (u : B)))
    (he : e = (IsLocalRing.maximalIdeal B).ramificationIdx A) :
    chapter04ResidueTraceNormStatement
      redA redB e t n x (u : B) := by
  have ht : t = Algebra.intTrace A B x := by
    apply (IsFractionRing.injective A K)
    rw [htrace,
      (Algebra.algebraMap_intTrace (A := A) (B := B) (K := K) (L := L) x).symm]
  have hn : n = Algebra.intNorm A B (u : B) := by
    apply (IsFractionRing.injective A K)
    rw [hnorm,
      (Algebra.algebraMap_intNorm (A := A) (B := B) (K := K) (L := L) (u : B)).symm]
  have hredA' :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11ResidueMap
        A k (IsLocalRing.maximalIdeal A) redA := by
    simpa only [chapter04ResidueMap,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11ResidueMap] using hredA
  have hredB' :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11ResidueMap
        B l (IsLocalRing.maximalIdeal B) redB := by
    simpa only [chapter04ResidueMap,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11ResidueMap] using hredB
  have hres :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_finite_dvr_residue_trace_and_norm
      A B k l redA redB hredA' hredB' hcompat e x (u : B) he
  change redA t = (e : k) * Algebra.trace k l (redB x) ∧
    redA n = Algebra.norm k (redB (u : B)) ^ e
  refine ⟨?_, ?_⟩
  · simpa [ht] using hres.1
  · simpa [hn] using hres.2

/- For an unramified extension, the integer factor is one (§4.5). -/
theorem chapter04_unramified_reduction_commutes_with_trace_and_norm
    {k l : Type*} [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] (t n : k) (x u : l)
    (h : chapter04ResidueTraceNormStatement
      (RingHom.id k) (RingHom.id l) 1 t n x u) :
    t = Algebra.trace k l x ∧ n = Algebra.norm k u := by
  simpa [chapter04ResidueTraceNormStatement] using h

/- When the residue extension is trivial, Proposition 4.2 becomes a power
formula for the residue of a unit (§4.5). -/
theorem chapter04_totally_ramified_residue_norm_of_unit
    (k : Type*) [Field k] (e : ℕ) (n u : k)
    (h : n = Algebra.norm k u ^ e) :
    n = u ^ e := by
  simpa using h

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04
