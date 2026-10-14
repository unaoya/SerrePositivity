module

public import SerrePositivity.HomologicalAlgebra.Tor
public import Mathlib.CategoryTheory.Abelian.LeftDerived

/-!
# 加群の導来テンソル積

## 概要

`R` 加群 `M`, `N` の導来テンソル積 `M ⊗^L_R N` を、`N` の射影分解 `P` に `M ⊗_R -` を
施した複体 `M ⊗_R P` のホモトピー類として定義する。
値は `ModuleCat R` の ℕ 添字鎖複体のホモトピー圏の対象である。
「次数 0 に集中する」という条件もこの対象について定義する。

## 方針

Mathlib の `Functor.leftDerivedToHomotopyCategory` をテンソル関手 `M ⊗_R -` に適用する。
Mathlib の `Tor` も同じ関手のホモロジーとして定義されている。
そのため `M ⊗^L_R N` の `i` 次ホモロジーは、定義により `TorModule R i M N` と一致する
（`derivedTensor_homology_eq`）。導来圏 `D(R)` 自体への移行や、
両変数の分解の比較はこのファイルでは扱わない。

## 規約と注意

原典（Bhatt–Scholze など）は `D(R)` をコホモロジー添字で書く。
加群どうしの導来テンソル積は非正次数にあり、ここでのホモロジー `i` 次は
コホモロジー `-i` 次に当たる。「次数 0 に集中する」は両方の添字で同じ条件である。

## 使われ方

`CommutativeAlgebra/CompletelyFlat.lean` の I 完全平坦性の定義に使う。
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace SerrePositivity

variable (R : Type u) [CommRing R]

/-- 導来テンソル積 `M ⊗^L_R N`。`N` の射影分解 `P` に対する複体 `M ⊗_R P` のホモトピー類である。
`M ⊗_R -` の左導来関手をホモトピー圏の値で取ったもので、
Mathlib の `Tor` と同じく第 2 変数を分解する。 -/
noncomputable abbrev derivedTensor (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : HomotopyCategory (ModuleCat.{u} R) (ComplexShape.down ℕ) :=
  ((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R M)).leftDerivedToHomotopyCategory.obj
    (ModuleCat.of R N)

/-- ℕ 添字鎖複体のホモトピー圏の対象が次数 0 に集中すること。
正の次数のホモロジーがすべて零であるという条件で、ホモトピー同値で不変である。 -/
def IsConcentratedInDegreeZero {C : Type*} [Category* C] [Abelian C]
    (K : HomotopyCategory C (ComplexShape.down ℕ)) : Prop :=
  ∀ i : ℕ, 0 < i → IsZero ((HomotopyCategory.homologyFunctor C _ i).obj K)

variable {R}

/-- `M ⊗^L_R N` の `i` 次ホモロジーは `Tor_i^R(M, N)` そのものである。
Mathlib の `Tor` が同じ左導来関手のホモロジーとして定義されているので、定義から従う。 -/
theorem derivedTensor_homology_eq (i : ℕ) (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) _ i).obj (derivedTensor R M N) =
      ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R M)).obj (ModuleCat.of R N) :=
  rfl

/-- `M ⊗^L_R N` が次数 0 に集中することと、正の次数の `Tor_i^R(M, N)` がすべて零であることは同値。
`derivedTensor_homology_eq` と、`ModuleCat` の零対象が台集合の自明性で判定できることによる。 -/
theorem isConcentratedInDegreeZero_derivedTensor_iff (M N : Type u) [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] :
    IsConcentratedInDegreeZero (derivedTensor R M N) ↔
      ∀ i : ℕ, 0 < i → Subsingleton (TorModule R i M N) := by
  refine forall₂_congr fun i _ ↦ ?_
  rw [derivedTensor_homology_eq]
  exact ModuleCat.isZero_iff_subsingleton

end SerrePositivity
