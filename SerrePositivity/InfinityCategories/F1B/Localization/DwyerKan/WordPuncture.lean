module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordErasure
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# 元の一列削除の単体圏による表示

概要：Fin.succAbove で一列を除いた語と、その元の包含を構成する。
方針：列の色を包含で制限する。像は削除する一列の補集合。
規約：既存の部分語による削除とは元の包含の比較で照合する。
使われ方：単体圏の面・退化の恒等式による混合縮約の比較。
-/

@[expose] public section
namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

/-- 一列を除いた方向列の明示的な表示。 -/
def puncture {k : ℕ} (d : Fin (k + 1) → Direction) (j : Fin (k + 1)) : Word :=
  ⟨k, fun i => d (j.succAbove i)⟩

def punctureInclusion {k : ℕ} (d : Fin (k + 1) → Direction) (j : Fin (k + 1)) :
    puncture d j ⟶ (⟨k + 1, d⟩ : Word) where
  orderHom := (Fin.succAboveOrderEmb j).toOrderHom
  direction_eq _ := rfl

lemma punctureInclusion_injective {k : ℕ} (d : Fin (k + 1) → Direction)
    (j : Fin (k + 1)) : Function.Injective (punctureInclusion d j).orderHom :=
  Fin.succAbove_right_injective

lemma punctureInclusion_range {k : ℕ} (d : Fin (k + 1) → Direction)
    (j : Fin (k + 1)) : Set.range (punctureInclusion d j).orderHom = {j}ᶜ :=
  Fin.range_succAbove j

end SerrePositivity.EInfinity.Hammock.Word
