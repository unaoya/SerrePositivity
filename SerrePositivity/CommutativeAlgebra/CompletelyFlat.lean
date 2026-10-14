module

public import SerrePositivity.HomologicalAlgebra.DerivedTensor
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# I 完全平坦性と I 完全忠実平坦性

## 概要

イデアル `I ⊆ A` に関する `A` 加群 `M` の I 完全平坦性と I 完全忠実平坦性を、
Bhatt–Scholze, *Prisms and prismatic cohomology*, §1.2（著者版 pp.10–11）の定義どおりに定める。

- I 完全平坦：`I` で消える任意の `A` 加群 `N` について、`M ⊗^L_A N` が次数 0 に集中する。
- I 完全忠実平坦：I 完全平坦であり、さらに `A/I ⊗_A M` が `A/I` 上忠実平坦。

## 規約と注意

原典は `M` を `D(A)` の複体として定義するが、ここでは加群 `M` に限る。
原典の「I-torsion な加群」は、`I` の元がすべて零として作用する加群と読む。
`I` の冪で消える加群や `I^∞` ねじれ加群に広げても、完全列と有向余極限によって同値な条件になる。
ただしその同値性はここでは証明しない。
`N = A/I` の場合、`M ⊗^L_A A/I` の 0 次ホモロジーは `A/I ⊗_A M` である。
忠実平坦性の条件はこの加群について述べる。

## 使われ方

André の平坦性補題（`BhattScholze/Inputs/AndreFlatness.lean`）の主張に使う。
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

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
