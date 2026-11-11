module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordErasure
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# 元の一列削除の単体圏による表示

概要：Fin.succAbove で一列を除いた語と、その元の包含を構成する。
方針：列の色を包含で制限する。像は削除する一列の補集合。
規約：既存の部分語による削除とは元の包含の比較で照合する。
使われ方：単体圏の面・退化の恒等式による混合縮約の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

/-- 一列を除いた方向列の明示的な表示。 -/
def puncture {k : ℕ} (d : Fin (k + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (j : Fin (k + 1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word :=
  ⟨k, fun i => d (j.succAbove i)⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (puncture)


def punctureInclusion {k : ℕ} (d : Fin (k + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (j : Fin (k + 1)) :
    puncture d j ⟶ (⟨k + 1, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) where
  orderHom := (Fin.succAboveOrderEmb j).toOrderHom
  direction_eq _ := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (punctureInclusion)


lemma punctureInclusion_injective {k : ℕ} (d : Fin (k + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (j : Fin (k + 1)) : Function.Injective (punctureInclusion d j).orderHom :=
  Fin.succAbove_right_injective

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (punctureInclusion_injective)


lemma punctureInclusion_range {k : ℕ} (d : Fin (k + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (j : Fin (k + 1)) : Set.range (punctureInclusion d j).orderHom = {j}ᶜ :=
  Fin.range_succAbove j

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (punctureInclusion_range)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
