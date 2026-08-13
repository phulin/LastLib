import LastLib.Book04AdelesAndIdeles.Chapter16.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter14.Section05ExactBoundaryOfNormPrinciple

namespace LastLib.Book04AdelesAndIdeles.Chapter16

noncomputable section

open Set Filter
open scoped BigOperators NumberField RestrictedProduct Topology

/-!
## 16.3 What has not been asserted

The negative boundary statements in the source are recorded by leaving the
corresponding maps undeclared.  The positive interfaces below describe local
norm subgroups and the cyclic norm principle without silently adding
reciprocity, Fourier inversion, or Poisson summation.
-/

def chapter16LocalNormSubgroup
    {ι K L : Type*} {Kloc : ι → Type*} {Lloc : ι → Type*}
    [Group K] [Group L] [∀ i, Group (Kloc i)] [∀ i, Group (Lloc i)]
    (localNorm : ∀ i, Lloc i →* Kloc i) (i : ι) : Subgroup (Kloc i) :=
  (localNorm i).range

def chapter16GlobalNormSubgroup
    {K L : Type*} [Group K] [Group L]
    (globalNorm : L →* K) : Subgroup K :=
  globalNorm.range

def chapter16AdelicNormSubgroup
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : Chapter16ExtensionNormData K L) : Subgroup (Chapter16Ideles K) :=
  N.adeleNorm.range

structure Chapter16LocalNormData
    (ι K L : Type*) [Field K] [Field L]
    (Kloc : ι → Type*) (Lloc : ι → Type*)
    [∀ i, Group (Kloc i)] [∀ i, Group (Lloc i)]
    [Algebra K L] [FiniteDimensional K L] where
  localNorm : ∀ i, Lloc i →* Kloc i
  toLocalK : K → ∀ i, Kloc i
  toLocalL : L → ∀ i, Lloc i
  compatibility : ∀ (x : L) (i : ι),
    toLocalK (Algebra.norm K x) i = localNorm i (toLocalL x i)

def chapter16CyclicNormPrinciple
    {ι K L : Type*} [Field K] [Field L]
    (Kloc : ι → Type*) (Lloc : ι → Type*)
    [∀ i, Group (Kloc i)] [∀ i, Group (Lloc i)]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L / K)]
    (D : Chapter16LocalNormData ι K L Kloc Lloc) : Prop :=
  ∀ x : K,
    (∀ i, D.toLocalK x i ∈ (D.localNorm i).range) →
      x ∈ Set.range (Algebra.norm K (S := L))

/- LOCAL_DEPENDENCY_GUESS:
The project has no earlier local-global norm interface for completions.  The
data above is the weakest reusable interface for the canonical local norms;
the cyclic theorem below is the Hasse norm theorem boundary named by the
source, not an unconditional norm principle for arbitrary extensions.
-/

theorem chapter16_cyclic_hasse_norm_theorem
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [IsCyclic Gal(L / K)]
    (N : LastLib.Book04AdelesAndIdeles.Chapter14.Chapter14AdelicNormInterface K L) :
    Subsingleton (LastLib.Book04AdelesAndIdeles.Chapter14.chapter14KnotGroup N) := by
  exact LastLib.Book04AdelesAndIdeles.Chapter14.chapter14_hasse_norm_theorem N

/-!
No declaration of a reciprocity homomorphism is made here, and the finite ray
class quotients above are not identified with Galois groups.  Likewise, the
Pontryagin-dual/additive character interface is only a self-duality platform:
Fourier inversion and Poisson summation remain future theorems.  The local norm
interfaces do not assert a local--global norm principle outside the cyclic
theorem explicitly marked above.
-/

end

end LastLib.Book04AdelesAndIdeles.Chapter16
