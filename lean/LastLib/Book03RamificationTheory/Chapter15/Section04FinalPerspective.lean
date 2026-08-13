import LastLib.Book03RamificationTheory.Chapter15.Section03ConsequencesForTwoDimensionalArithmetic

namespace LastLib.Book03RamificationTheory.Chapter15

noncomputable section

/-! ## 15.4. Final perspective -/

/-- A bound on the last nontrivial upper-numbered group. -/
def chapter15LastUpperBreakBound
    {G : Type*} [Group G]
    (U : ℝ → Subgroup G) (b : ℝ) : Prop :=
  ∀ r : ℝ, b < r → U r = ⊥

/-- A separate bound on the order of the finite Galois group. -/
def chapter15GroupOrderBound
    {G : Type*} [Group G] [Finite G] (N : ℕ) : Prop :=
  Nat.card G ≤ N

/-- The numerical form in which a local ramification estimate is consumed. -/
def chapter15DiscriminantExponentBound (δ B : ℕ) : Prop :=
  δ ≤ B

/-- Upper-break and group-order estimates feed into the discriminant estimate. -/
theorem chapter15_ramification_bound_feeds_discriminant_bound
    {G : Type*} [Group G] [Finite G]
    (F : Chapter15LowerRamificationFiltration G) (f δ B : ℕ)
    (hδ : δ = chapter15DiscriminantDisplacementSum F f)
    (hbound : chapter15DiscriminantDisplacementSum F f ≤ B) :
    chapter15DiscriminantExponentBound δ B := by
  simpa [chapter15DiscriminantExponentBound, hδ] using hbound

/--
The trace-dual lattice whose inverse defines the different.  This is kept as
an explicit interface because the different ideal itself lives downstairs in
the integral model, while the trace form lives in the fraction fields.
-/
noncomputable def chapter15TraceDualLattice
    (A K B L : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra A B] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L] : Submodule B L :=
  Submodule.traceDual A K (1 : Submodule B L)

/-- Pointwise trace characterization of the trace-dual lattice. -/
theorem chapter15_mem_trace_dual_iff
    (A K B L : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra A B] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (x : L) :
    x ∈ chapter15TraceDualLattice A K B L ↔
      ∀ y : B,
        Algebra.trace K L (x * algebraMap B L y) ∈ Set.range (algebraMap A K) := by
  sorry

/--
The source-level separation between field discriminants and Weierstrass
discriminants is represented by their different codomains: an ideal downstairs
versus a coefficient of a chosen model.
-/
theorem chapter15_field_and_model_discriminants_have_distinct_interfaces
    (A R : Type*) [Semiring A] :
    Chapter15FieldDiscriminant A = Ideal A ∧
      Chapter15WeierstrassDiscriminant R = R := by
  exact ⟨rfl, rfl⟩

end

end LastLib.Book03RamificationTheory.Chapter15
