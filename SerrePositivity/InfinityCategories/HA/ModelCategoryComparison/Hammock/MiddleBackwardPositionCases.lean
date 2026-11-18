module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackwardPositions

/-!
# 元の中央 backward 語の全位置の場合分け

概要：両端・左右の forward 区間・中央の列が元の全頂点と全列を尽くす。
方針：元の位置の自然数の値を照合し、元の Fin の等式に戻す。
規約：空の区間も扱い、正の長さを仮定しない。
使われ方：抽出後の再構成を元の全頂点・全列と照合する。
-/

@[expose] public section
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ForwardPath

variable (n m : ℕ)

lemma firstColumn_val : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.firstColumn n m).val = 0 := rfl
lemma leftColumn_val (i : Fin n) : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftColumn n m i).val = 1 + i.val := rfl

lemma middleColumn_val : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.middleColumn n m).val = n + 1 := by
  dsimp [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.middleColumn, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single]
  omega

lemma rightColumn_val (i : Fin m) : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightColumn n m i).val = n + 2 + i.val := by
  dsimp [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightColumn, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftWithMiddle, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single]
  omega

lemma lastColumn_val : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.lastColumn n m).val = n + m + 2 := by
  dsimp [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.lastColumn, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftWithMiddle, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single]
  omega

lemma vertex_cases {P : Fin ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length + 1) → Prop} (h0 : P 0)
    (hl : ∀ i, P (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftVertex n m i)) (hr : ∀ i, P (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightVertex n m i))
    (hN : P (Fin.last (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length)) (j : Fin ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length + 1)) : P j := by
  have hlen := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.length_eq n m
  have hj := j.isLt
  by_cases hz : j.val = 0
  · have he : j = 0 := Fin.ext hz
    exact he ▸ h0
  by_cases hh : j.val ≤ n + 1
  · let i : Fin (n + 1) := ⟨j.val - 1, by omega⟩
    have he : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftVertex n m i = j := by
      apply Fin.ext
      rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftVertex_val]
      dsimp [i]
      omega
    exact he ▸ hl i
  by_cases hh' : j.val ≤ n + m + 2
  · let i : Fin (m + 1) := ⟨j.val - (n + 2), by omega⟩
    have he : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightVertex n m i = j := by
      apply Fin.ext
      rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightVertex_val]
      dsimp [i]
      omega
    exact he ▸ hr i
  · have he : Fin.last (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length = j := by
      apply Fin.ext
      change (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length = j.val
      omega
    exact he ▸ hN

lemma column_cases {P : Fin (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length → Prop} (h0 : P (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.firstColumn n m))
    (hl : ∀ i, P (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftColumn n m i)) (hc : P (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.middleColumn n m))
    (hr : ∀ i, P (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightColumn n m i)) (hN : P (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.lastColumn n m))
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length) : P j := by
  have hlen := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.length_eq n m
  have hj := j.isLt
  by_cases hz : j.val = 0
  · have he : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.firstColumn n m = j := Fin.ext (by rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.firstColumn_val]; omega)
    exact he ▸ h0
  by_cases hh : j.val ≤ n
  · let i : Fin n := ⟨j.val - 1, by omega⟩
    have he : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftColumn n m i = j := by
      apply Fin.ext
      rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftColumn_val]
      dsimp [i]
      omega
    exact he ▸ hl i
  by_cases hc' : j.val = n + 1
  · have he : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.middleColumn n m = j := Fin.ext (by rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.middleColumn_val]; omega)
    exact he ▸ hc
  by_cases hh' : j.val ≤ n + m + 1
  · let i : Fin m := ⟨j.val - (n + 2), by omega⟩
    have he : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightColumn n m i = j := by
      apply Fin.ext
      rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightColumn_val]
      dsimp [i]
      omega
    exact he ▸ hr i
  · have he : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.lastColumn n m = j := Fin.ext (by rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.lastColumn_val]; omega)
    exact he ▸ hN

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions
