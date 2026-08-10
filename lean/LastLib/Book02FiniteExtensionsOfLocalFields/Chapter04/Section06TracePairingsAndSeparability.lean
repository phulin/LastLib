import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section05ResidueFieldShadows

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04

noncomputable section

open scoped nonZeroDivisors

/-! ## 4.6. Trace pairings and separability -/

/- The trace pairing is Mathlib's canonical trace bilinear form (§4.6). -/
theorem chapter04_trace_pairing_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x y : L) :
    (Algebra.traceForm K L x) y = Algebra.trace K L (x * y) := by
  sorry

/- Separability is equivalent to nondegeneracy of the trace pairing (§4.6). -/
theorem chapter04_trace_pairing_nondegenerate_iff_separable
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    (Algebra.traceForm K L).Nondegenerate ↔ Algebra.IsSeparable K L := by
  sorry

/- An inseparable extension has a degenerate trace pairing (§4.6). -/
theorem chapter04_inseparable_trace_pairing_is_degenerate
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hsep : ¬Algebra.IsSeparable K L) :
    ¬(Algebra.traceForm K L).Nondegenerate := by
  sorry

/- A nontrivial purely inseparable extension has identically zero trace pairing
and hence loses all separable first-order information (§4.6). -/
theorem chapter04_purely_inseparable_trace_pairing_is_zero
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    (hdegree : 1 < Module.finrank K L) :
    ∀ x y : L, Algebra.trace K L (x * y) = 0 := by
  sorry

/- The integral trace dual `B^∨` from §4.6. -/
def chapter04TraceDual
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] : Set L :=
  {z | ∀ y : B, ∃ a : A,
    algebraMap A K a = Algebra.trace K L (z * algebraMap B L y)}

/- In the separable case the trace dual is represented by Mathlib's bundled
fractional-ideal structure (§4.6). -/
theorem chapter04_trace_dual_is_fractional
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [Field K] [Field L] [Algebra A B] [Algebra A K]
    [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [Module.Finite A B] [Module.Free A B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B] :
    ∃ I : FractionalIdeal B⁰ L,
      (I : Set L) = chapter04TraceDual A B K L := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04
