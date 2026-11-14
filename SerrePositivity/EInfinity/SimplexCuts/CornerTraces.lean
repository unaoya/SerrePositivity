module

public import SerrePositivity.EInfinity.SimplexCuts.VertexLists
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSwapCoordinates

/-!
# 角の中間頂点を除いた切断の一致

Berger–Fresse §2.2.7、M14 L09a。
隣接辺を交換した二つの切断から中間頂点を除くと、同じ色付き頂点列になる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 指定した経路の頂点を一つ除いた色付き頂点列。 -/
def deletedTrace {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (k : Fin (m + q + 1)) : List (Fin r × Fin (q + 1)) :=
  List.ofFn (fun j => (label s v (k.succAbove j), s.vertical (k.succAbove j)))

/-- C18：隣接辺の交換で変わる頂点を除くと、全ての色付き座標が一致する。 -/
lemma deletedTrace_swapSteps {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (a b : Fin (m + q)) (hab : b.val = a.val + 1) :
    deletedTrace (s.swapSteps a b) v b.castSucc = deletedTrace s v b.castSucc := by
  unfold deletedTrace
  apply congrArg List.ofFn
  funext j
  have hj : (b.castSucc.succAbove j).val ≠ b.val := by
    intro h
    exact Fin.succAbove_ne b.castSucc j (Fin.ext h)
  apply Prod.ext
  · exact congrArg v (s.horizontal_swapSteps a b hab _ hj)
  · exact s.vertical_swapSteps a b hab _ hj

/-- C18の証明分割：どの色の出力列も、同じ頂点を除けば一致する。 -/
lemma selectColor_deletedTrace_swapSteps {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + q)) (hab : b.val = a.val + 1)
    (c : Fin r) :
    selectColor c (deletedTrace (s.swapSteps a b) v b.castSucc) =
      selectColor c (deletedTrace s v b.castSucc) :=
  congrArg (selectColor c) (deletedTrace_swapSteps s v a b hab)

end SerrePositivity.EInfinity.SimplexCuts
