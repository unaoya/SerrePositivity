module

public import SerrePositivity.EInfinity.SimplexCuts.BoundaryVertexLists

/-!
# 削除した出力面の同じ頂点列

Berger–Fresse §2.2.7、M14 L09a。
既存の標準面と色別の削除列を照合し、後の実テンソルの比較に指定射を残す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial

/-- C154：実際の出力境界面の頂点列は、指定頂点を削除した色別リスト。 -/
lemma simplexVertexList_deletedFace {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hd : 0 < outputDegree s v (label s v.val k))
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) :
    simplexVertexList (boundaryFace _ hd j ≫ face s v (label s v.val k)) =
      deletedVerticesList s v.val k (label s v.val k) := by
  rw [simplexVertexList_boundaryFace, simplexVertexList_face, hj]
  simp only [deletedVerticesList, ite_true]

end SerrePositivity.EInfinity.SimplexCuts
