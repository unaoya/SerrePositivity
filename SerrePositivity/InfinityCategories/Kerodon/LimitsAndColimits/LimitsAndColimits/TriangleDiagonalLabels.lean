module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleTwoCutCoordinates

/-!
概要：長辺の二値ラベルを、三対象の中間点を飛ばすラベルへ厳密に対応させる。
方針：標準面 δ₁ の有限座標を計算する。
規約：全次数と全ての頂点を保持する。
使われ方：再構成全対角の Hom 比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

def triangleDiagonalLabel {n : ℕ} (t : Fin (n + 1) →o Fin 2) : Fin (n + 1) →o Fin 3 :=
  (SimplexCategory.δ (1 : Fin 3)).toOrderHom.comp t

lemma triangleDiagonalLabel_zero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) : triangleDiagonalLabel t i = 0 := by
  change (SimplexCategory.δ (1 : Fin 3)).toOrderHom (t i) = 0
  rw [hi]
  rfl

lemma triangleDiagonalLabel_two {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 1) : triangleDiagonalLabel t i = 2 := by
  change (SimplexCategory.δ (1 : Fin 3)).toOrderHom (t i) = 2
  rw [hi]
  rfl

lemma triangleDiagonalLabel_ne_one {n : ℕ} (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) :
    triangleDiagonalLabel t i ≠ 1 := by
  have h : ∀ k : Fin 2, (SimplexCategory.δ (1 : Fin 3)).toOrderHom k ≠ 1 := by decide
  exact h (t i)

lemma triangleZeroLabel_diagonal {n : ℕ} (t : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel (triangleDiagonalLabel t) = t := by
  apply OrderHom.ext
  funext i
  have cases : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  rcases cases (t i) with h | h
  · change (if (SimplexCategory.δ (1 : Fin 3)).toOrderHom (t i) = 0 then (0 : Fin 2) else 1) = t i
    rw [h]
    rfl
  · change (if (SimplexCategory.δ (1 : Fin 3)).toOrderHom (t i) = 0 then (0 : Fin 2) else 1) = t i
    rw [h]
    rfl

lemma controlledTriangleCutMap_congr {n : ℕ} {s t : Fin (n + 1) →o Fin 2} (h : s = t)
    {i : Fin (n + 1)} (hi : s i = 0) (hi' : t i = 0) (j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap.{u} s hi j = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap t hi' j := by
  cases h
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
