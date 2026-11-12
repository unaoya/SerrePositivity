module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleInsert
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWFaces

/-!
# shuffle の同種ステップの内部の面

概要：同種ステップの隣に一つのステップを挿入すると、その間の面は対応する因子の面に一致する。
方針：一歩で一つ増える座標の閾値と、挿入した路の座標の変化を比較する。
規約：KST Construction A.5 の標準 shuffle、内部の水平・水平または垂直・垂直の面。
使われ方：shuffle の鎖写像性で各因子の通常境界へ対応する項の同定。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped Simplicial

/-- 概要：単調な座標が一つ増えるステップの前後は座標の閾値で判定できる。
方針：ステップの前後それぞれに単調性を使う。
規約：KST A.5 の格子路の一般補題。
使われ方：入力因子の面が飛ばす頂点の判定。 -/
lemma discretePath_threshold {n p : ℕ} (f : Fin (n + 1) → Fin (p + 1))
    (hf : Monotone f) (a : Fin n) (ha : (f a.succ : ℕ) = (f a.castSucc : ℕ) + 1)
    (x : Fin (n + 1)) :
    (a : ℕ) < (x : ℕ) ↔ (f a.castSucc : ℕ) + 1 ≤ (f x : ℕ) := by
  constructor
  · intro h
    have hax : a.succ ≤ x := by change (a : ℕ) + 1 ≤ (x : ℕ); omega
    have hm : (f a.succ : ℕ) ≤ (f x : ℕ) := hf hax
    omega
  · intro h
    by_contra! hx
    have hxa : x ≤ a.castSucc := hx
    have hm : (f x : ℕ) ≤ (f a.castSucc : ℕ) := hf hxa
    omega

/-- 概要：水平ステップの前後は第一座標の閾値で判定できる。
方針：水平ステップで第一座標が一つ増えることを使う。
規約：KST A.5。使われ方：第一因子の面の頂点の判定。 -/
lemma ShuffleIndex.left_threshold {p n : ℕ} (s : ShuffleIndex p n) (a : Fin n)
    (ha : a ∈ s.val) (x : Fin (n + 1)) :
    (a : ℕ) < (x : ℕ) ↔
      (s.left.toOrderHom a.castSucc : ℕ) + 1 ≤ (s.left.toOrderHom x : ℕ) := by
  apply discretePath_threshold s.left.toOrderHom s.left.toOrderHom.monotone a
  rw [s.left_step, ite_eq_left ha]

/-- 概要：垂直ステップの前後は第二座標の閾値で判定できる。
方針：垂直ステップで第二座標が一つ増えることを使う。
規約：KST A.5。使われ方：第二因子の面の頂点の判定。 -/
lemma ShuffleIndex.right_threshold {p q n : ℕ} (s : ShuffleIndex p n) (h : p + q = n)
    (a : Fin n) (ha : a ∉ s.val) (x : Fin (n + 1)) :
    (a : ℕ) < (x : ℕ) ↔
      ((s.right h).toOrderHom a.castSucc : ℕ) + 1 ≤ ((s.right h).toOrderHom x : ℕ) := by
  apply discretePath_threshold (s.right h).toOrderHom (s.right h).toOrderHom.monotone a
  rw [s.right_step h, ite_eq_left ha]

/-- 概要：水平ステップの直前への水平挿入の面は、第一因子の面に一致する。
方針：挿入後の第一座標と、閾値の頂点を飛ばす面の公式を比較する。
規約：KST A.5、内部の水平・水平の面。
使われ方：第一因子の交代境界に対応する項。 -/
lemma ShuffleIndex.insertHorizontal_left_face {p n : ℕ} (s : ShuffleIndex p n)
    (a : Fin n) (ha : a ∈ s.val) :
    SimplexCategory.δ a.castSucc.succ ≫ (s.insertHorizontal a.castSucc).left =
      s.left ≫ SimplexCategory.δ (s.left.toOrderHom a.castSucc).succ := by
  ext x
  change ((s.insertHorizontal a.castSucc).left.toOrderHom (a.castSucc.succ.succAbove x) : ℕ) =
    ((SimplexCategory.δ (s.left.toOrderHom a.castSucc).succ).toOrderHom (s.left.toOrderHom x) : ℕ)
  rw [s.insertHorizontal_left, awFace_apply]
  have ht := s.left_threshold a ha x
  change (s.left.toOrderHom x : ℕ) + (if (a : ℕ) < (x : ℕ) then 1 else 0) =
    if (s.left.toOrderHom x : ℕ) < (s.left.toOrderHom a.castSucc : ℕ) + 1 then
      (s.left.toOrderHom x : ℕ) else (s.left.toOrderHom x : ℕ) + 1
  split_ifs <;> omega

/-- 概要：水平挿入の面を取ると第二因子の写像は元のまま。
方針：挿入を飛ばした頂点で第二座標が変わらないことを使う。
規約：KST A.5、水平挿入。使われ方：第一因子の境界項の第二成分。 -/
lemma ShuffleIndex.insertHorizontal_right_face {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (a : Fin (n + 1)) :
    SimplexCategory.δ a.succ ≫ (s.insertHorizontal a).right (show (p + 1) + q = n + 1 by omega) =
      s.right h := by
  ext x
  exact s.insertHorizontal_right h a x

/-- 概要：垂直挿入の面を取ると第一因子の写像は元のまま。
方針：挿入を飛ばした頂点で第一座標が変わらないことを使う。
規約：KST A.5、垂直挿入。使われ方：第二因子の境界項の第一成分。 -/
lemma ShuffleIndex.insertVertical_left_face {p n : ℕ} (s : ShuffleIndex p n)
    (a : Fin (n + 1)) :
    SimplexCategory.δ a.succ ≫ (s.insertVertical a).left = s.left := by
  ext x
  exact s.insertVertical_left a x

/-- 概要：垂直ステップの直前への垂直挿入の面は、第二因子の面に一致する。
方針：挿入後の第二座標と、閾値の頂点を飛ばす面の公式を比較する。
規約：KST A.5、内部の垂直・垂直の面。
使われ方：第二因子の交代境界に対応する項。 -/
lemma ShuffleIndex.insertVertical_right_face {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (a : Fin n) (ha : a ∉ s.val) :
    SimplexCategory.δ a.castSucc.succ ≫
        (s.insertVertical a.castSucc).right (show p + (q + 1) = n + 1 by omega) =
      s.right h ≫ SimplexCategory.δ ((s.right h).toOrderHom a.castSucc).succ := by
  ext x
  change (((s.insertVertical a.castSucc).right (show p + (q + 1) = n + 1 by omega)).toOrderHom
      (a.castSucc.succ.succAbove x) : ℕ) =
    ((SimplexCategory.δ ((s.right h).toOrderHom a.castSucc).succ).toOrderHom
      ((s.right h).toOrderHom x) : ℕ)
  rw [s.insertVertical_right, awFace_apply]
  have ht := s.right_threshold h a ha x
  change ((s.right h).toOrderHom x : ℕ) + (if (a : ℕ) < (x : ℕ) then 1 else 0) =
    if ((s.right h).toOrderHom x : ℕ) < ((s.right h).toOrderHom a.castSucc : ℕ) + 1 then
      ((s.right h).toOrderHom x : ℕ) else ((s.right h).toOrderHom x : ℕ) + 1
  split_ifs <;> omega

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
