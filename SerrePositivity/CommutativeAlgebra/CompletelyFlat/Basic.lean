module

public import SerrePositivity.HomologicalAlgebra.DerivedTensor
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # 完全平坦性と完全忠実平坦性

## 概要

イデアル I に関する完全平坦性 `IsCompletelyFlat` と完全忠実平坦性 `IsCompletelyFaithfullyFlat`（I 進の還元が平坦・忠実平坦で、I 冪ねじれの Tor が消える）の定義と、同型での不変性を与える。

## 方針

Mathlib の導来テンソル積がまだないので、Tor の消滅と還元の平坦性で定義する。

## 規約

`IsCompletelyFaithfullyFlat`（BhattScholze で 114 件）・`IsCompletelyFlat` は名前を残す。Mathlib への提出は導来テンソルが整ってから。

## 使われ方

BhattScholze の André の補題・perfectoid 化、CLMST の降下。
-/

@[expose] public noncomputable section

universe u

section CompletelyFlatPart

open CategoryTheory
open scoped TensorProduct

namespace SerrePositivity

variable {A : Type u} [CommRing A] (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M]

/-- `M` が I 完全平坦であること。BS §1.2 の定義で、`I` で消える任意の `A` 加群 `N` について
導来テンソル積 `M ⊗^L_A N` が次数 0 に集中する、すなわち正の次数の `Tor_i^A(M, N)` が零である。
平坦加群は I 完全平坦であり、逆は一般に成り立たない（`I` 進完備化した自由加群など）。 -/
def IsCompletelyFlat : Prop :=
  ∀ (N : Type u) [AddCommGroup N] [Module A N], (∀ a ∈ I, ∀ n : N, a • n = 0) →
    IsConcentratedInDegreeZero (derivedTensor A M N)

/-- `M` が I 完全忠実平坦であること。BS §1.2 の定義で、I 完全平坦であり、
`M ⊗^L_A A/I`（I 完全平坦性から `A/I ⊗_A M` に等しい）が `A/I` 上忠実平坦である。 -/
def IsCompletelyFaithfullyFlat : Prop :=
  IsCompletelyFlat I M ∧ Module.FaithfullyFlat (A ⧸ I) ((A ⧸ I) ⊗[A] M)

end SerrePositivity

end CompletelyFlatPart

section CompletelyFlatEquivPart

namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
variable {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Complete flatness depends only on the original coefficient module up to linear equivalence. -/
lemma isCompletelyFlat_of_linearEquiv (I : Ideal R) (e : M ≃ₗ[R] N)
    (hM : IsCompletelyFlat I M) : IsCompletelyFlat I N := by
  intro L _ _ hL i hi
  have hz : IsZero (((Tor (ModuleCat R) i).obj (ModuleCat.of R M)).obj (ModuleCat.of R L)) :=
    hM L hL i hi
  exact hz.of_iso (((Tor (ModuleCat R) i).mapIso e.toModuleIso).app (ModuleCat.of R L)).symm

/-- The residue tensor module is compared over the same original quotient ring. -/
lemma isCompletelyFaithfullyFlat_of_linearEquiv (I : Ideal R) (e : M ≃ₗ[R] N)
    (hM : IsCompletelyFaithfullyFlat I M) : IsCompletelyFaithfullyFlat I N := by
  letI := hM.2
  let E : ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] N) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (R ⧸ I) (R ⧸ I)) e
  exact ⟨isCompletelyFlat_of_linearEquiv I e hM.1,
    Module.FaithfullyFlat.of_linearEquiv (R ⧸ I) ((R ⧸ I) ⊗[R] M) E.symm⟩

end SerrePositivity

end CompletelyFlatEquivPart
