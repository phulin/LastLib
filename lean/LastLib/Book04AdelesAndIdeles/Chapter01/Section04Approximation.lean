import LastLib.Book04AdelesAndIdeles.Chapter01.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter01

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

/-! ## 1.4 Approximation in a Dedekind domain -/

/- SOURCE_ISSUE (§1.4, Proposition 1.2): the source writes
`\operatorname{ord}_{\mathfrak p}(a-x_{\mathfrak p})\geq m_{\mathfrak p}`
for `x_{\mathfrak p}\in K_{\mathfrak p}`, although `ord_{\mathfrak p}` was
introduced only on `K^\times` (and the difference may be zero).  The
interfaces below use the completion's canonical multiplicative valuation
`Valued.v` for local neighborhoods, and use the additive order only for
global elements of `K`.
-/

variable (K : Type*) [Field K] [NumberField K]

theorem chapter01_local_neighborhood_coe_iff
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : K) (m : ℤ) :
    (x : v.adicCompletion K) ∈ chapter01LocalNeighborhood v m ↔
      Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (-m) := by
  rfl

theorem chapter01_completion_valuation_agrees_with_global
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : K) :
    Valued.v (x : v.adicCompletion K) = v.valuation K x := by
  sorry

theorem chapter01_finite_approximation
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (x : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∈ S → v.adicCompletion K)
    (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∈ S → ℤ) :
    ∃ a : K,
      (∀ v (hv : v ∈ S),
        chapter01LocallyClose v (x v hv) (a : v.adicCompletion K) (m v hv)) ∧
        ∀ q : IsDedekindDomain.HeightOneSpectrum (𝓞 K), q ∉ S →
          0 ≤ chapter01Order q a := by
  sorry

theorem chapter01_finite_approximation_with_controlled_denominator
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (x : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∈ S → v.adicCompletion K)
    (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∈ S → ℤ) :
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K),
      chapter01FractionalIdealIntegralOutside S I ∧
        (∀ v (hv : v ∈ S),
          x v hv ∈ chapter01LocalFractionalIdealBall v I) ∧
        ∃ a : K, a ∈ I ∧
          (∀ v (hv : v ∈ S),
            chapter01LocallyClose v (x v hv) (a : v.adicCompletion K) (m v hv)) := by
  sorry

theorem chapter01_principal_parts_approximation
    (x : chapter01FiniteAdeleRing K) :
    ∃ a : K, ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      x v - (a : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
  sorry

theorem chapter01_finite_adele_nonintegral_support_finite
    (x : chapter01FiniteAdeleRing K) :
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
      x v ∉ v.adicCompletionIntegers K}.Finite := by
  sorry

theorem chapter01_order_finite_support_for_nonzero_global (a : K) (ha : a ≠ 0) :
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | chapter01Order v a ≠ 0}.Finite :=
  by sorry

theorem chapter01_no_nonzero_global_element_positive_at_every_prime :
    ¬∃ a : K, a ≠ 0 ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), 0 < chapter01Order v a := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter01
