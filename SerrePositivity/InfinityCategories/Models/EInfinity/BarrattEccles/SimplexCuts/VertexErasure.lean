module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VertexLists
public import Mathlib.Data.Fin.SuccPred

/-!
模型。文献の定義との比較は後で
# 色の頂点列の一頂点の削除

Berger–Fresse §2.2.7、M14 L09a。
元の経路の一頂点の削除を、その色のfiber内の面番号で読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C19：有限関数の列から一頂点を除く操作はsuccAboveによる制限。 -/
lemma eraseIdx_ofFn {β : Type*} {N : ℕ} (f : Fin (N + 1) → β) (k : Fin (N + 1)) :
    (List.ofFn f).eraseIdx k.val = List.ofFn (fun j => f (k.succAbove j)) := by
  induction N with
  | zero =>
    have hk : k = 0 := by apply Fin.ext; have h := k.isLt; omega
    subst k
    simp [List.ofFn_succ]
  | succ N ih =>
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [List.ofFn_succ]
    · rw [List.ofFn_succ]
      simp only [Fin.val_succ, List.eraseIdx_cons_succ]
      rw [ih]
      rw [List.ofFn_succ]
      simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]

/-- C20の証明分割：先頭の色の選別。 -/
lemma selectColor_cons {r : ℕ} {β : Type*} (c : Fin r) (a : Fin r × β)
    (l : List (Fin r × β)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c (a :: l) = if a.1 = c then a.2 :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c l else _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c l := by
  by_cases h : a.1 = c <;> simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor, h]

/-- C20：一頂点を消すと、同じ色の列の中でだけ先行出現数の位置を消す。 -/
lemma selectColor_eraseIdx {r : ℕ} {β : Type*} (c : Fin r) (l : List (Fin r × β)) (k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c (l.eraseIdx k) =
      if (l[k]?.map Prod.fst) = some c then
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c l).eraseIdx (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c (l.take k)).length
      else _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c l := by
  induction l generalizing k with
  | nil => simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor]
  | cons a l ih =>
    cases k with
    | zero =>
      by_cases h : a.1 = c <;> simp [h, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor]
    | succ k =>
      by_cases h : a.1 = c
      · simp only [List.eraseIdx_cons_succ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor_cons, h, ite_true,
          List.getElem?_cons_succ, List.take_succ_cons, List.length_cons]
        rw [ih]
        split <;> simp_all
      · simp only [List.eraseIdx_cons_succ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor_cons, h, ite_false,
          List.getElem?_cons_succ, List.take_succ_cons]
        exact ih k

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
