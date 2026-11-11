module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleHorizontalFaceIndex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleInsertSign

/-!
# shuffle の二因子交換と垂直境界の面番号

概要：水平集合の補集合を使い、第二因子の面番号に対する挿入を第一因子の場合から構成する。
方針：水平・垂直の座標と挿入を交換する厳密な等式を使う。
規約：KST Construction A.5 の標準 shuffle。係数の二因子の順序自体は変えない。
使われ方：垂直境界項の有限な添字の対応と実単体写像の同定。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped Simplicial

/-- 概要：水平集合を補集合へ交換した shuffle。
方針：補集合の濃度 q を使う。
規約：KST A.5、p と q を交換する。使われ方：垂直境界の順位の構成。 -/
def ShuffleIndex.transpose {p q n : ℕ} (s : ShuffleIndex p n) (h : p + q = n) :
    ShuffleIndex q n := ⟨s.valᶜ, s.compl_card h⟩

/-- 概要：二因子交換後の第一写像は元の第二写像。
方針：二つの前半の濃度の定義を比較する。
規約：KST A.5。使われ方：垂直境界の実写像の同定。 -/
lemma ShuffleIndex.transpose_left {p q n : ℕ} (s : ShuffleIndex p n) (h : p + q = n) :
    (s.transpose h).left = s.right h := rfl

/-- 概要：二因子交換後の第二写像は元の第一写像。
方針：補集合を二回取ると元の集合へ戻る。
規約：KST A.5。使われ方：垂直境界の他方の成分の同定。 -/
lemma ShuffleIndex.transpose_right {p q n : ℕ} (s : ShuffleIndex p n) (h : p + q = n) :
    (s.transpose h).right (show q + p = n by omega) = s.left := by
  ext x
  rw [ShuffleIndex.right_apply, ShuffleIndex.left_apply]
  change ((s.valᶜ)ᶜ.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ))).card = _
  rw [compl_compl]

/-- 概要：二回の二因子交換は元の shuffle に戻る。
方針：水平集合の二重補集合を計算する。
規約：KST A.5。使われ方：水平・垂直の対応の対称性。 -/
@[simp] lemma ShuffleIndex.transpose_transpose {p q n : ℕ} (s : ShuffleIndex p n) (h : p + q = n) :
    (s.transpose h).transpose (show q + p = n by omega) = s := by
  apply Subtype.ext
  exact compl_compl s.val

/-- 概要：垂直挿入を二因子交換すると水平挿入になる。
方針：水平挿入の補集合の公式を使い、再び補集合を取る。
規約：KST A.5。使われ方：第二因子の面番号の構成への移送。 -/
lemma ShuffleIndex.transpose_insertVertical {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (a : Fin (n + 1)) :
    (s.insertVertical a).transpose (show p + (q + 1) = n + 1 by omega) =
      (s.transpose h).insertHorizontal a := by
  apply Subtype.ext
  change (s.insertVertical a).valᶜ = ((s.transpose h).insertHorizontal a).val
  have he : ((s.transpose h).insertHorizontal a).valᶜ = (s.insertVertical a).val := by
    rw [ShuffleIndex.insertHorizontal_compl]
    change (s.valᶜ)ᶜ.map a.succAboveEmb = s.val.map a.succAboveEmb
    rw [compl_compl]
  have ht := congrArg (fun z : Finset (Fin (n + 1)) ↦ zᶜ) he
  simpa only [compl_compl] using ht.symm

/-- 概要：第二因子の面番号に対応する挿入位置。
方針：補集合の水平ステップの順位による位置を使う。
規約：KST A.5。使われ方：垂直境界項の実構成。 -/
def ShuffleIndex.verticalFacePosition {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (i : Fin (q + 2)) : Fin (n + 1) :=
  (s.transpose h).horizontalFacePosition i

/-- 概要：垂直境界項で削除する頂点。
方針：二因子交換後の水平境界の頂点を使う。
規約：KST A.5。使われ方：垂直境界側の面番号。 -/
def ShuffleIndex.verticalFaceVertex {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (i : Fin (q + 2)) : Fin (n + 2) :=
  (s.transpose h).horizontalFaceVertex i

/-- 概要：面番号から選んだ垂直挿入の第一写像の面は元の第一写像。
方針：二因子交換後の水平境界の第二成分の公式を使う。
規約：KST A.5、第一因子の次数 p は変えない。
使われ方：垂直境界項の順方向の対応の第一成分。 -/
lemma ShuffleIndex.verticalFace_left {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (i : Fin (q + 2)) :
    SimplexCategory.δ (s.verticalFaceVertex h i) ≫ (s.insertVertical (s.verticalFacePosition h i)).left =
      s.left := by
  have ht := (s.transpose h).horizontalFace_right (show q + p = n by omega) i
  rw [← s.transpose_insertVertical h ((s.transpose h).horizontalFacePosition i),
    ShuffleIndex.transpose_right, s.transpose_right] at ht
  exact ht

/-- 概要：面番号から選んだ垂直挿入の第二写像の面は指定した第二因子の面。
方針：二因子交換後の水平境界の第一成分の公式を使う。
規約：KST Construction A.5、第二因子の全ての面。
使われ方：垂直境界項の順方向の対応。 -/
lemma ShuffleIndex.verticalFace_right {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (i : Fin (q + 2)) :
    SimplexCategory.δ (s.verticalFaceVertex h i) ≫
        (s.insertVertical (s.verticalFacePosition h i)).right (show p + (q + 1) = n + 1 by omega) =
      s.right h ≫ SimplexCategory.δ i := by
  have ht := (s.transpose h).horizontalFace_left i
  rw [← s.transpose_insertVertical h ((s.transpose h).horizontalFacePosition i),
    ShuffleIndex.transpose_left, s.transpose_left] at ht
  exact ht

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
