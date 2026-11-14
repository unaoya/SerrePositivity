module

public import SerrePositivity.EInfinity.SimplexCuts.DeletedCutFaces

/-!
# 小さい切断と一致する削除面

Berger–Fresse §2.2.6–7、M14 L09a。
同じ削除色列を、更新出力次数と元の単体圏の指定面の厳密な一致へ移す。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial

/-- C185：削除後の全色の列が一致すれば、更新次数は小さい切断の出力次数。 -/
lemma deletedOutputDegree_eq_of_vertexLists {m n q r : ℕ} (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c) :
    Function.update (outputDegree s v) (label s v.val k)
      (outputDegree s v (label s v.val k) - 1) = outputDegree t w := by
  funext c
  apply Nat.add_right_cancel (m := 1)
  rw [← deletedVerticesList_length_update s v k hd c, ← verticesList_length t w c, hl c]

/-- C186：同じ削除列の指定面は、次数移送の後で小さい切断の面に厳密に一致。 -/
lemma deletedCutFace_eq_of_vertexLists {m n q r : ℕ} (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (c : Fin r) :
    deletedCutFace s v (label s v.val k) hd j c =
      eqToHom (congrArg SimplexCategory.mk
        (congrFun (deletedOutputDegree_eq_of_vertexLists s t v w k hd hl) c)) ≫ face t w c := by
  apply simplexVertexList_injective _ _
  change simplexVertexList _ = simplexVertexList _
  rw [simplexVertexList_cast_source, simplexVertexList_deletedCutFace_at_vertex _ _ _ hd j hj,
    simplexVertexList_face, hl c]
  exact congrFun (deletedOutputDegree_eq_of_vertexLists s t v w k hd hl) c

end SerrePositivity.EInfinity.SimplexCuts
