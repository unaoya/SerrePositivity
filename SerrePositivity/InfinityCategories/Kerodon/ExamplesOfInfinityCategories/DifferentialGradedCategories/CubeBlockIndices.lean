module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex
public import Mathlib.Order.Fin.Basic

/-!
# 二つの座標区間の境目の添字

概要：p+q 次元単体の先頭 p 区間と末尾 q 区間の頂点の包含と像を記述する。
方針：頂点番号をそれぞれ t と p+t に写し、像を境目 p での二つの filter と同定する。
規約：境目の頂点は両側に一度ずつ属する。
使われ方：HA 1.3.1.16、Kerodon 2.5.8（Tag 00S0） の AW の唯一の切断項の評価。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：先頭 p 区間の頂点を p+q 区間の頂点へ埋め込む。
方針：頂点番号を変えない。
規約：末尾の境目 p を含む。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW の接頭成分。 -/
def cubePrefixOrder (p q : ℕ) : Fin (p + 1) →o Fin (p + q + 1) where
  toFun t := ⟨t.val, by omega⟩
  monotone' := fun _ _ h ↦ h

/-- 概要：末尾 q 区間の頂点を p+q 区間の頂点へ埋め込む。
方針：頂点番号に p を加える。
規約：最初の境目 p を含む。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW の接尾成分。 -/
def cubeSuffixOrder (p q : ℕ) : Fin (q + 1) →o Fin (p + q + 1) where
  toFun t := ⟨p + t.val, by omega⟩
  monotone' := fun _ _ h ↦ Nat.add_le_add_left h p

/-- 概要：先頭区間の頂点の包含は単射である。
方針：頂点番号の等式を取る。
規約：p=0 も含む。
使われ方：HA 1.3.1.16 の単射な引き戻しの成分計算。 -/
lemma cubePrefixOrder_injective (p q : ℕ) : Function.Injective (cubePrefixOrder p q) := by
  intro a b h
  exact Fin.ext (congrArg (fun t : Fin (p + q + 1) ↦ t.val) h)

/-- 概要：末尾区間の頂点の包含は単射である。
方針：頂点番号の等式から共通の加数 p を消す。
規約：q=0 も含む。
使われ方：HA 1.3.1.16 の単射な引き戻しの成分計算。 -/
lemma cubeSuffixOrder_injective (p q : ℕ) : Function.Injective (cubeSuffixOrder p q) := by
  intro a b h
  exact Fin.ext (Nat.add_left_cancel (congrArg (fun t : Fin (p + q + 1) ↦ t.val) h))

/-- 概要：先頭区間の全頂点の像は境目以下の頂点集合である。
方針：番号が p 以下の点を同じ番号で逆に取る。
規約：filter は p+q 区間の全体集合内で取る。
使われ方：Kerodon 2.5.8（Tag 00S0） の接頭集合と単体の像の対応。 -/
lemma cubePrefixOrder_image_univ (p q : ℕ) :
    Finset.univ.image (cubePrefixOrder p q) =
      (Finset.univ : Finset (Fin (p + q + 1))).filter (· ≤ ⟨p, by omega⟩) := by
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨t, rfl⟩
    change t.val ≤ p
    omega
  · intro ha
    have ha' : a.val ≤ p := ha
    exact ⟨⟨a.val, by omega⟩, Fin.ext rfl⟩

/-- 概要：末尾区間の全頂点の像は境目以上の頂点集合である。
方針：番号が p 以上の点から p を引いて逆に取る。
規約：filter は p+q 区間の全体集合内で取る。
使われ方：Kerodon 2.5.8（Tag 00S0） の接尾集合と単体の像の対応。 -/
lemma cubeSuffixOrder_image_univ (p q : ℕ) :
    Finset.univ.image (cubeSuffixOrder p q) =
      (Finset.univ : Finset (Fin (p + q + 1))).filter (⟨p, by omega⟩ ≤ ·) := by
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨t, rfl⟩
    change p ≤ p + t.val
    omega
  · intro ha
    have ha' : p ≤ a.val := ha
    refine ⟨⟨a.val - p, by have h := a.isLt; omega⟩, Fin.ext ?_⟩
    change p + (a.val - p) = a.val
    omega

/-- 概要：境目以下の頂点数は p+1 である。
方針：単射な接頭包含の像の濃度を計算する。
規約：境目の頂点を数える。
使われ方：HA 1.3.1.16 の AW 接頭成分の次数を −p に同定する。 -/
lemma cubePrefixOrder_card (p q : ℕ) :
    ((Finset.univ : Finset (Fin (p + q + 1))).filter (· ≤ ⟨p, by omega⟩)).card = p + 1 := by
  rw [← cubePrefixOrder_image_univ,
    Finset.card_image_of_injective _ (cubePrefixOrder_injective p q)]
  simp

/-- 概要：境目以上の頂点数は q+1 である。
方針：単射な接尾包含の像の濃度を計算する。
規約：境目の頂点を数える。
使われ方：HA 1.3.1.16 の AW 接尾成分の次数を −q に同定する。 -/
lemma cubeSuffixOrder_card (p q : ℕ) :
    ((Finset.univ : Finset (Fin (p + q + 1))).filter (⟨p, by omega⟩ ≤ ·)).card = q + 1 := by
  rw [← cubeSuffixOrder_image_univ,
    Finset.card_image_of_injective _ (cubeSuffixOrder_injective p q)]
  simp

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
