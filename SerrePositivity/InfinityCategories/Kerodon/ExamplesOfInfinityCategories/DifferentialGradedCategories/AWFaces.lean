module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AlexanderWhitney

/-!
# AW の制限写像と面写像の交換

概要：共有切断点の前後にある面と、切断内の面の制限公式を証明する。
方針：連続した頂点区間を順序写像として表し、頂点番号を比較する。
規約：KST Construction A.5 の標準 AW。単体圏の面は指定頂点を飛ばす包含。
使われ方：AW の鎖写像性で、二重境界和を相殺項と削除後の切断に分ける。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped Simplicial

/-- 概要：開始頂点 a と長さ l の連続区間への制限の添字写像。
方針：頂点 j を a+j へ送る。
規約：KST A.5 の AW、端点を含む。使われ方：前半と後半の面の統一的な計算。 -/
def awInterval (a l n : ℕ) (h : a + l ≤ n) : ⦋l⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom
    { toFun j := ⟨a + j, by have := j.isLt; omega⟩
      monotone' _ _ h := Nat.add_le_add_left h _ }

/-- 概要：区間包含の頂点番号の公式。
方針：順序写像の定義を評価する。
規約：KST A.5。使われ方：面との交換を数の等式に帰着する。 -/
@[simp] lemma awInterval_apply (a l n : ℕ) (h : a + l ≤ n) (j : Fin (l + 1)) :
    ((awInterval a l n h).toOrderHom j : ℕ) = a + j := rfl

/-- 概要：面写像は飛ばす頂点以後の頂点番号を一つ増やす。
方針：Fin.succAbove の二つの分岐を評価する。
規約：KST A.5 の AW、標準単体圏の面。
使われ方：制限と面の交換公式。 -/
lemma awFace_apply {n : ℕ} (k : Fin (n + 2)) (j : Fin (n + 1)) :
    ((SimplexCategory.δ k).toOrderHom j : ℕ) = if (j : ℕ) < k then (j : ℕ) else (j : ℕ) + 1 := by
  change (k.succAbove j : ℕ) = _
  by_cases h : (j : ℕ) < k
  · rw [ite_eq_left h, Fin.succAbove_of_castSucc_lt _ _ h]
    rfl
  · have hkj : k ≤ j.castSucc := by
      change (k : ℕ) ≤ (j : ℕ)
      omega
    rw [ite_eq_right h, Fin.succAbove_of_le_castSucc k j hkj]
    rfl

/-- 概要：区間の始点以前の頂点を削除すると区間全体が一つ後ろへ移る。
方針：区間の全頂点は削除点以上である。
規約：KST A.5 の AW。使われ方：前半の面に対応する後半の不変部分。 -/
lemma awInterval_face_before (a l n : ℕ) (h : a + l ≤ n) (k : Fin (n + 2))
    (hk : (k : ℕ) ≤ a) :
    awInterval a l n h ≫ SimplexCategory.δ k =
      awInterval (a + 1) l (n + 1) (by omega) := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    awFace_apply, awInterval_apply]
  have hj : (j : ℕ) < l + 1 := j.isLt
  split_ifs <;> omega

/-- 概要：区間の終点より後の頂点の削除は区間を変えない。
方針：区間の全頂点は削除点より小さい。
規約：KST A.5 の AW。使われ方：後半の面に対応する前半の不変部分。 -/
lemma awInterval_face_after (a l n : ℕ) (h : a + l ≤ n) (k : Fin (n + 2))
    (hk : a + l < (k : ℕ)) :
    awInterval a l n h ≫ SimplexCategory.δ k =
      awInterval a l (n + 1) (by omega) := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    awFace_apply, awInterval_apply]
  have hj : (j : ℕ) < l + 1 := j.isLt
  split_ifs <;> omega

/-- 概要：区間内の面を先に取ることは、大きな単体で対応する頂点を削除することに等しい。
方針：局所頂点番号 k を a+k に移し、二つの分岐を比較する。
規約：KST A.5 の AW、端点の削除も含む。
使われ方：境界の非対角項を削除後の AW 項へ移す。 -/
lemma awInterval_face_inside (a l n : ℕ) (h : a + (l + 1) ≤ n + 1)
    (k : Fin (l + 2)) :
    SimplexCategory.δ k ≫ awInterval a (l + 1) (n + 1) h =
      awInterval a l n (by omega) ≫
        SimplexCategory.δ (⟨a + k, by have := k.isLt; omega⟩ : Fin (n + 2)) := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    awFace_apply, awInterval_apply]
  split_ifs <;> omega

/-- 概要：AW の前半は零から切断点までの連続区間。
方針：各頂点で二つの順序写像を比較する。
規約：KST A.5。使われ方：区間公式を実 AW の成分へ適用する。 -/
lemma awFront_eq_interval (n : ℕ) (i : Fin (n + 1)) :
    awFront n i = awInterval 0 i n (by have := i.isLt; omega) := by
  ext j
  simp only [awFront_apply, awInterval_apply, Nat.zero_add]

/-- 概要：AW の後半は切断点から最終頂点までの連続区間。
方針：各頂点で二つの順序写像を比較する。
規約：KST A.5。使われ方：区間公式を実 AW の成分へ適用する。 -/
lemma awBack_eq_interval (n : ℕ) (i : Fin (n + 1)) :
    awBack n i = awInterval i (n - i) n (by have := i.isLt; omega) := by
  ext j
  rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
