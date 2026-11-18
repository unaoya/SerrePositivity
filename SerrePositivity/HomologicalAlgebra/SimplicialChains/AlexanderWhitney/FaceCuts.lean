module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.SimplicialCuts

/-!
# 面写像と連続区間への制限

概要：Berger–Fresse §1.1.4 の AW 公式と微分の可換性に使う面写像の計算を行う。
方針：除く頂点が区間の前・後・中にある場合を単体圏の射として比較する。
規約：面写像は n 単体を n+1 単体の一つの面へ埋め込む向きで記述する。
使われ方：AW 公式の境界の有限和を前半と後半へ分割する。
-/

@[expose] public section

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory
open scoped _root_.Simplicial

/-- 概要：区間の始点以前の頂点を除くと区間全体が一つずれる（Berger–Fresse §1.1.4）。
方針：全ての選択頂点が除去位置以後であることを使う。
規約：除去位置と区間の始点が等しい場合を含む。
使われ方：AW 境界公式の後半の面を計算する。 -/
lemma segmentMap_face_before {n : ℕ} (i : Fin (n + 2))
    (a b : ℕ) (h : a + b ≤ n) (hi : i.val ≤ a) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b n h ≫ SimplexCategory.δ i =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap (a + 1) b (n + 1) (by omega) := by
  ext k : 3
  change i.succAbove ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b n h).toOrderHom k) = _
  rw [Fin.succAbove_of_le_castSucc _ _ (by change i.val ≤ a + k.val; omega)]
  apply Fin.ext
  change a + k.val + 1 = a + 1 + k.val
  omega

/-- 概要：区間の終点より後の頂点を除いても区間は変わらない（Berger–Fresse §1.1.4）。
方針：全ての選択頂点が除去位置より前であることを使う。
規約：除去位置が区間の終点と等しい場合は含まない。
使われ方：AW 境界公式の前半の面を計算する。 -/
lemma segmentMap_face_after {n : ℕ} (i : Fin (n + 2))
    (a b : ℕ) (h : a + b ≤ n) (hi : a + b < i.val) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b n h ≫ SimplexCategory.δ i =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b (n + 1) (by omega) := by
  ext k : 3
  change i.succAbove ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b n h).toOrderHom k) = _
  rw [Fin.succAbove_of_castSucc_lt _ _ (by
    change a + k.val < i.val
    have := k.isLt
    change k.val < b + 1 at this
    omega)]
  rfl

/-- 概要：区間内部の面写像は長さを一つ増やした区間の面である（Berger–Fresse §1.1.4）。
方針：区間の始点を引いた除去位置で同じ頂点を飛ばすことを確認する。
規約：増やした区間の両端の面も含める。
使われ方：AW 境界公式を二つの因子の微分と比較する。 -/
lemma segmentMap_face_inside {n : ℕ} (i : Fin (n + 2))
    (a b : ℕ) (h : a + b ≤ n) (ha : a ≤ i.val) (hb : i.val ≤ a + b + 1) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b n h ≫ SimplexCategory.δ i =
      SimplexCategory.δ (⟨i.val - a, by omega⟩ : Fin (b + 2)) ≫
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a (b + 1) (n + 1) (by omega) := by
  ext k : 3
  by_cases hk : a + k.val < i.val
  · change i.succAbove ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b n h).toOrderHom k) =
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a (b + 1) (n + 1) (by omega)).toOrderHom
        ((⟨i.val - a, by omega⟩ : Fin (b + 2)).succAbove k)
    rw [Fin.succAbove_of_castSucc_lt _ _ (by change a + k.val < i.val; exact hk),
      Fin.succAbove_of_castSucc_lt _ _ (by change k.val < i.val - a; omega)]
    rfl
  · change i.succAbove ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a b n h).toOrderHom k) =
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap a (b + 1) (n + 1) (by omega)).toOrderHom
        ((⟨i.val - a, by omega⟩ : Fin (b + 2)).succAbove k)
    rw [Fin.succAbove_of_le_castSucc _ _ (by change i.val ≤ a + k.val; omega),
      Fin.succAbove_of_le_castSucc _ _ (by change i.val - a ≤ k.val; omega)]
    rfl

end SerrePositivity.SimplicialChains.AlexanderWhitney
