module

public import SerrePositivity.EInfinity.SimplexCuts.DeletedVertices
public import SerrePositivity.EInfinity.SimplexCuts.Outputs
public import Mathlib.Data.List.Basic

/-!
# 頂点を一つ消した出力次数の一致

Berger–Fresse §2.2.7、M14 L09a。
混合角で等しい削除後の色別リストから、実テンソルで更新する次数の族も一致させる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C149：各色の列の長さは、その出力次数に一を足したもの。 -/
lemma verticesList_length {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (c : Fin r) :
    (verticesList s v.val c).length = outputDegree s v c + 1 := by
  simp only [verticesList, List.length_map, Finset.length_sort, colorPositions_card_eq]

/-- C150：指定頂点の色の列だけが、一文字短くなる。 -/
lemma deletedVerticesList_length {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) (c : Fin r) :
    (deletedVerticesList s v.val k c).length =
      outputDegree s v c + 1 - if label s v.val k = c then 1 else 0 := by
  unfold deletedVerticesList
  by_cases hc : label s v.val k = c
  · rw [ite_eq_left hc, ite_eq_left hc, List.length_eraseIdx_of_lt]
    · rw [verticesList_length]
    · simpa only [hc] using vertexRank_lt_length s v.val k
  · rw [ite_eq_right hc, ite_eq_right hc, Nat.sub_zero, verticesList_length]

/-- C151：正次数なら、削除後の列の長さは更新した出力次数に一を足したもの。 -/
lemma deletedVerticesList_length_update {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : 0 < outputDegree s v (label s v.val k)) (c : Fin r) :
    (deletedVerticesList s v.val k c).length =
      Function.update (outputDegree s v) (label s v.val k)
        (outputDegree s v (label s v.val k) - 1) c + 1 := by
  rw [deletedVerticesList_length]
  by_cases hc : c = label s v.val k
  · subst c
    rw [ite_eq_left rfl, Function.update_self]
    omega
  · rw [ite_eq_right (Ne.symm hc), Function.update_of_ne hc, Nat.sub_zero]

/-- C152：混合角の両側で実テンソルの更新次数の族が一致する。 -/
lemma deletedOutputDegree_swapSteps {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a b : Fin (m + q))
    (hab : b.val = a.val + 1)
    (ho : 0 < outputDegree s v (label s v.val b.castSucc))
    (hn : 0 < outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc)) :
    Function.update (outputDegree (s.swapSteps a b) v)
        (label (s.swapSteps a b) v.val b.castSucc)
        (outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) - 1) =
      Function.update (outputDegree s v) (label s v.val b.castSucc)
        (outputDegree s v (label s v.val b.castSucc) - 1) := by
  funext c
  apply Nat.add_right_cancel (m := 1)
  rw [← deletedVerticesList_length_update _ _ _ hn,
    ← deletedVerticesList_length_update _ _ _ ho, deletedVerticesList_swapSteps s v.val a b hab]

end SerrePositivity.EInfinity.SimplexCuts
