module

public import SerrePositivity.EInfinity.SimplexCuts.CornerTraces
public import SerrePositivity.EInfinity.SimplexCuts.VertexErasure

/-!
# 経路の一頂点の削除と出力の面

Berger–Fresse §2.2.7、M14 L09a。
各色の列の削除位置を、経路の指定頂点より前の同色の個数で読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 指定頂点より前の同色の出現数。 -/
def vertexRank {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (c : Fin r) (k : Fin (m + q + 1)) : ℕ :=
  (selectColor c ((List.ofFn (fun i => (label s v i, s.vertical i))).take k.val)).length

/-- 一つの経路の頂点の削除を、各色の出力列で表す。 -/
def deletedVerticesList {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) (c : Fin r) : List (Fin (q + 1)) :=
  if label s v k = c then (verticesList s v c).eraseIdx (vertexRank s v c k)
  else verticesList s v c

/-- C26：出力の面を取ることと、経路の頂点を削除してから色を選ぶことは一致。 -/
lemma deletedVerticesList_eq_selectColor {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (k : Fin (m + q + 1)) (c : Fin r) :
    deletedVerticesList s v k c = selectColor c (deletedTrace s v k) := by
  unfold deletedVerticesList deletedTrace
  rw [← eraseIdx_ofFn (fun i => (label s v i, s.vertical i)) k,
    selectColor_eraseIdx, verticesList_eq_selectColor]
  simp only [List.getElem?_ofFn, k.isLt, dite_eq_left, Option.map_some, Option.some.injEq]
  rfl

/-- C27：交換した角の中間頂点を削除した出力の全ての色の列は一致。 -/
lemma deletedVerticesList_swapSteps {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + q)) (hab : b.val = a.val + 1)
    (c : Fin r) :
    deletedVerticesList (s.swapSteps a b) v b.castSucc c =
      deletedVerticesList s v b.castSucc c := by
  rw [deletedVerticesList_eq_selectColor, deletedVerticesList_eq_selectColor,
    selectColor_deletedTrace_swapSteps s v a b hab c]

/-- C28：指定頂点の色の面番号は、その色の出力列の範囲内にある。 -/
lemma vertexRank_lt_length {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) :
    vertexRank s v (label s v k) k < (verticesList s v (label s v k)).length := by
  let l := List.ofFn (fun i => (label s v i, s.vertical i))
  let c := label s v k
  have hk : k.val < l.length := by simpa only [l, List.length_ofFn] using k.isLt
  have hs : selectColor c l = selectColor c (l.take k.val) ++
      (s.vertical k :: selectColor c (l.drop (k.val + 1))) := by
    calc
      _ = selectColor c (l.take k.val ++ l.drop k.val) :=
        congrArg (selectColor c) (List.take_append_drop k.val l).symm
      _ = _ := by
        rw [selectColor_append, List.drop_eq_getElem_cons hk, selectColor_cons]
        simp only [l, List.getElem_ofFn, c, ite_true]
  rw [verticesList_eq_selectColor]
  have he := congrArg List.length hs
  simp only [List.length_append, List.length_cons] at he
  change (selectColor c (l.take k.val)).length < (selectColor c l).length
  omega

end SerrePositivity.EInfinity.SimplexCuts
