import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section01LinearAlgebraTurnedIntoArithmetic
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section08TraceAndBoundedness

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04

noncomputable section

open scoped nonZeroDivisors

/-! ## 4.6. Trace pairings and separability -/

/- The pointwise trace pairing, bundled canonically as a bilinear form. -/
def chapter04TracePairing
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : LinearMap.BilinForm K L :=
  Algebra.traceForm K L

@[simp] theorem chapter04TracePairing_apply
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x y : L) :
    chapter04TracePairing K L x y = Algebra.trace K L (x * y) := by
  rfl

/- The trace pairing is Mathlib's canonical trace bilinear form (§4.6). -/
theorem chapter04_trace_pairing_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x y : L) :
    (Algebra.traceForm K L x) y = Algebra.trace K L (x * y) := by
  exact Algebra.traceForm_apply (R := K) (S := L) x y

/- Separability is equivalent to nondegeneracy of the trace pairing (§4.6). -/
theorem chapter04_trace_pairing_nondegenerate_iff_separable
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    (Algebra.traceForm K L).Nondegenerate ↔ Algebra.IsSeparable K L := by
  exact (traceForm_nondegenerate_tfae K L).out 2 0

/- An inseparable extension has a degenerate trace pairing (§4.6). -/
theorem chapter04_inseparable_trace_pairing_is_degenerate
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hsep : ¬Algebra.IsSeparable K L) :
    ¬(Algebra.traceForm K L).Nondegenerate := by
  intro hnon
  exact hsep ((chapter04_trace_pairing_nondegenerate_iff_separable K L).mp hnon)

/- A nontrivial purely inseparable extension has identically zero trace pairing
and hence loses all separable first-order information (§4.6). -/
theorem chapter04_purely_inseparable_trace_pairing_is_zero
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    (hdegree : 1 < Module.finrank K L) :
    ∀ x y : L, Algebra.trace K L (x * y) = 0 := by
  intro x y
  exact chapter04_purely_inseparable_trace_eq_zero K L hdegree (x * y)

/- The integral trace dual `B^∨` from §4.6. -/
def chapter04TraceDual
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] : Set L :=
  {z | ∀ y : B, ∃ a : A,
    algebraMap A K a = Algebra.trace K L (z * algebraMap B L y)}

@[simp] theorem chapter04TraceDual_mem_iff
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] (z : L) :
    z ∈ chapter04TraceDual A B K L ↔
      ∀ y : B, ∃ a : A,
        algebraMap A K a = Algebra.trace K L (z * algebraMap B L y) := Iff.rfl

/- In the separable case the trace dual is represented by Mathlib's bundled
fractional-ideal structure (§4.6). -/
theorem chapter04_trace_dual_is_fractional
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K]
    [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [Module.Finite A B] [Module.Free A B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B] :
    ∃ I : FractionalIdeal B⁰ L,
      (I : Set L) = chapter04TraceDual A B K L := by
  let _ : IsIntegralClosure B A L := IsIntegralClosure.of_isIntegrallyClosed B A L
  let I : FractionalIdeal B⁰ L :=
    FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L)
  refine ⟨I, ?_⟩
  have hI : (I : Submodule B L) =
      Submodule.traceDual A K (1 : Submodule B L) := by
    simp [I]
  change (I : Submodule B L) = chapter04TraceDual A B K L
  rw [hI]
  ext z
  constructor
  · intro hz y
    have hz' := (Submodule.mem_traceDual.mp hz)
      (algebraMap B L y) (by simp [Submodule.one_eq_range])
    rcases hz' with ⟨a, ha⟩
    exact ⟨a, by simpa [Algebra.traceForm_apply] using ha⟩
  · intro hz
    apply Submodule.mem_traceDual.mpr
    intro b hb
    rcases (show ∃ y : B, algebraMap B L y = b by
      simpa [Submodule.one_eq_range] using hb) with ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := hz y
    exact ⟨a, by simpa [Algebra.traceForm_apply] using ha⟩

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04
