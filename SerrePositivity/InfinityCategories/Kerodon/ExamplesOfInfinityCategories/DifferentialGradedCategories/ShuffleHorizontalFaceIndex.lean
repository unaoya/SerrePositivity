module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleRank
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleEndFace

/-!
# 第一因子の面番号から水平境界項への写像

概要：第一因子の面 i を、shuffle への水平挿入と削除すべき頂点に送る。
方針：最初・最後の面を区別し、内部では第 i−1 水平ステップの直前へ挿入する。
規約：KST Construction A.5、非被約複体の両端も含む。
使われ方：水平の境界和と shuffle の純粋水平境界項の有限な添字の対応。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped Simplicial

/-- 概要：内部の面番号 i に対応する水平ステップの番号 i−1。
方針：零番目と最後の面以外では 1≤i≤p を使う。
規約：KST A.5。使われ方：内部の面の標準列挙による復元。 -/
def horizontalFaceInteriorRank {p : ℕ} (i : Fin (p + 2))
    (h₀ : i ≠ 0) (h₁ : i ≠ Fin.last (p + 1)) : Fin p :=
  ⟨(i : ℕ) - 1, by
    have hn₀ : (i : ℕ) ≠ 0 := fun h ↦ h₀ (Fin.ext h)
    have hn₁ : (i : ℕ) ≠ p + 1 := fun h ↦ h₁ (Fin.ext h)
    have := i.isLt
    omega⟩

/-- 概要：水平の境界の面番号に対する挿入位置。
方針：最初・最後は端点、内部は対応する水平ステップの直前を取る。
規約：KST A.5。使われ方：水平境界項の実 shuffle の構成。 -/
def ShuffleIndex.horizontalFacePosition {p n : ℕ} (s : ShuffleIndex p n) (i : Fin (p + 2)) :
    Fin (n + 1) :=
  if h₀ : i = 0 then 0 else if h₁ : i = Fin.last (p + 1) then Fin.last n else
    (s.horizontalStep (horizontalFaceInteriorRank i h₀ h₁)).castSucc

/-- 概要：水平境界項で削除する頂点。
方針：端の面では最初・最後の頂点、内部では挿入ステップ直後の頂点を取る。
規約：KST A.5。使われ方：shuffle の境界側の面番号。 -/
def ShuffleIndex.horizontalFaceVertex {p n : ℕ} (s : ShuffleIndex p n) (i : Fin (p + 2)) :
    Fin (n + 2) :=
  if i = 0 then 0 else if i = Fin.last (p + 1) then Fin.last (n + 1) else
    (s.horizontalFacePosition i).succ

/-- 概要：内部の面を作る水平ステップの第一座標の直後は元の面番号。
方針：水平ステップの順位の公式と i−1+1=i を使う。
規約：KST A.5。使われ方：水平の内部面の実単体写像の同定。 -/
lemma ShuffleIndex.horizontalFaceInterior_coface {p n : ℕ} (s : ShuffleIndex p n)
    (i : Fin (p + 2)) (h₀ : i ≠ 0) (h₁ : i ≠ Fin.last (p + 1)) :
    (s.left.toOrderHom (s.horizontalStep (horizontalFaceInteriorRank i h₀ h₁)).castSucc).succ = i := by
  apply Fin.ext
  change (s.left.toOrderHom (s.horizontalStep (horizontalFaceInteriorRank i h₀ h₁)).castSucc : ℕ) + 1 = (i : ℕ)
  rw [s.horizontalStep_left]
  change (i : ℕ) - 1 + 1 = (i : ℕ)
  have hn₀ : (i : ℕ) ≠ 0 := fun h ↦ h₀ (Fin.ext h)
  omega

/-- 概要：面番号から選んだ水平挿入の第一写像の面は、指定した第一因子の面に一致。
方針：最初・最後・内部の三つの場合で、既に検証した面の公式を適用する。
規約：KST Construction A.5、第一因子の全ての面。
使われ方：水平の境界項の順方向の対応。 -/
lemma ShuffleIndex.horizontalFace_left {p n : ℕ} (s : ShuffleIndex p n) (i : Fin (p + 2)) :
    SimplexCategory.δ (s.horizontalFaceVertex i) ≫ (s.insertHorizontal (s.horizontalFacePosition i)).left =
      s.left ≫ SimplexCategory.δ i := by
  by_cases h₀ : i = 0
  · subst i
    simpa only [horizontalFaceVertex, horizontalFacePosition, ite_eq_left rfl, dite_eq_left rfl, ite_true, dite_true] using
      s.insertHorizontal_first_left_face
  · by_cases h₁ : i = Fin.last (p + 1)
    · subst i
      simpa only [horizontalFaceVertex, horizontalFacePosition, ite_eq_right h₀, dite_eq_right h₀,
        ite_eq_left rfl, dite_eq_left rfl, ite_true, dite_true] using s.insertHorizontal_last_left_face
    · have ht := s.insertHorizontal_left_face
        (s.horizontalStep (horizontalFaceInteriorRank i h₀ h₁))
        (s.horizontalStep_mem (horizontalFaceInteriorRank i h₀ h₁))
      rw [s.horizontalFaceInterior_coface i h₀ h₁] at ht
      simpa only [horizontalFaceVertex, horizontalFacePosition, ite_eq_right h₀, dite_eq_right h₀,
        ite_eq_right h₁, dite_eq_right h₁] using ht

/-- 概要：面番号から選んだ水平挿入の第二写像の面は元の第二写像に一致。
方針：最初・最後・内部の三つの場合で第二座標が保たれる公式を適用する。
規約：KST A.5、第二因子の次数 q は変えない。
使われ方：水平の境界項の順方向の対応の第二成分。 -/
lemma ShuffleIndex.horizontalFace_right {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (i : Fin (p + 2)) :
    SimplexCategory.δ (s.horizontalFaceVertex i) ≫
        (s.insertHorizontal (s.horizontalFacePosition i)).right (show (p + 1) + q = n + 1 by omega) =
      s.right h := by
  by_cases h₀ : i = 0
  · subst i
    simpa only [horizontalFaceVertex, horizontalFacePosition, ite_eq_left rfl, dite_eq_left rfl, ite_true, dite_true] using
      s.insertHorizontal_first_right_face h
  · by_cases h₁ : i = Fin.last (p + 1)
    · subst i
      simpa only [horizontalFaceVertex, horizontalFacePosition, ite_eq_right h₀, dite_eq_right h₀,
        ite_eq_left rfl, dite_eq_left rfl, ite_true, dite_true] using s.insertHorizontal_last_right_face h
    · simpa only [horizontalFaceVertex, horizontalFacePosition, ite_eq_right h₀, dite_eq_right h₀,
        ite_eq_right h₁, dite_eq_right h₁] using s.insertHorizontal_right_face h
          (s.horizontalStep (horizontalFaceInteriorRank i h₀ h₁)).castSucc

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
