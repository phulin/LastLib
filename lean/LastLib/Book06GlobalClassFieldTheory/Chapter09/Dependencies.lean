import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.Topology.Algebra.PontryaginDual

namespace LastLib.Book06GlobalClassFieldTheory.Chapter09

noncomputable section

/-!
The chapter uses the field norm on multiplicative groups.  Mathlib exposes the
norm as a monoid hom on the field itself, so this is the canonical unit-group
version used by the declarations below.
-/
def chapter09FieldNormUnitHom
    (K L : Type*) [Field K] [Field L] [Algebra K L] : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K (S := L))

@[simp]
theorem chapter09FieldNormUnitHom_apply
    (K L : Type*) [Field K] [Field L] [Algebra K L] (x : Lˣ) :
    ((chapter09FieldNormUnitHom K L x : Kˣ) : K) = Algebra.norm K (x : L) := by
  rfl

/-!
Earlier chapters do not yet provide an idele group/class-group construction.
This small interface records exactly the maps needed by the knot and norm
quotients, without committing those quotients to a particular implementation.
-/
structure Chapter09IdeleNormData
    (K L I_K I_L : Type*) [Field K] [Field L] [Algebra K L]
    [CommGroup I_K] [CommGroup I_L] where
  principalK : Kˣ →* I_K
  principalL : Lˣ →* I_L
  ideleNorm : I_L →* I_K
  principalK_injective : Function.Injective principalK
  principalL_injective : Function.Injective principalL
  norm_compatibility :
    ideleNorm.comp principalL =
      principalK.comp (chapter09FieldNormUnitHom K L)

/-!
The source repeatedly uses exact sequences of groups.  This is a deliberately
small interface: the kernel/range equality is stated in the ambient groups,
where it can be reused for the idele sequence and its later cohomological
models.
-/
def chapter09GroupExact
    {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : B →* C) : Prop :=
  Function.Injective f ∧ Function.Surjective g ∧ f.range = g.ker

/-!
At a split place the local algebra is a product.  The family `A_v` is left
abstract so that the same interface covers both a field completion and a
finite product of completions.
-/
structure Chapter09LocalNormData
    (K V : Type*) [Field K]
    (K_v A_v : V → Type*)
    [∀ v, Monoid (K_v v)] [∀ v, Monoid (A_v v)] where
  baseEmbedding : ∀ v, Kˣ →* (K_v v)ˣ
  localNorm : ∀ v, (A_v v)ˣ →* (K_v v)ˣ

def chapter09EverywhereLocalNorm
    {K V : Type*} [Field K] {K_v A_v : V → Type*}
    [∀ v, Monoid (K_v v)] [∀ v, Monoid (A_v v)]
    (P : Chapter09LocalNormData K V K_v A_v) (a : Kˣ) : Prop :=
  ∀ v, P.baseEmbedding v a ∈ (P.localNorm v).range

end

end LastLib.Book06GlobalClassFieldTheory.Chapter09
