import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section02CharacteristicPolynomialsAndIntegralRestriction

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04

noncomputable section

/-! ## 4.3. Transitivity -/

/- Trace is transitive in a finite tower of fields (§4.3). -/
theorem chapter04_trace_transitive
    (K M L : Type*) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] [FiniteDimensional K M]
    [FiniteDimensional M L] [FiniteDimensional K L] (x : L) :
    Algebra.trace K L x =
      Algebra.trace K M (Algebra.trace M L x) := by
  exact (Algebra.trace_trace (R := K) (S := M) (T := L) x).symm

/- Norm is transitive in a finite tower of fields (§4.3). -/
theorem chapter04_norm_transitive
    (K M L : Type*) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] [FiniteDimensional K M]
    [FiniteDimensional M L] [FiniteDimensional K L] (x : L) :
    Algebra.norm K x =
      Algebra.norm K (Algebra.norm M x) := by
  simpa using (Algebra.norm_norm (R := K) (S := M) (A := L) (a := x)).symm

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04
