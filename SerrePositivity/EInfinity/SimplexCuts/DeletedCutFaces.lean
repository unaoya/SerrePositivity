module

public import SerrePositivity.EInfinity.SimplexCuts.DeletedOutputDegrees
public import SerrePositivity.EInfinity.SimplexCuts.DeletedFaceVertexLists

/-!
# 実テンソルの削除面の厳密な比較

Berger–Fresse §2.2.7、M14 L09a。
既存のdeletedCutTensorで使う各色の面を、更新後の同じ次数で書き出す。
混合角の両側の指定面は、始域の次数移送の後で元の単体圏で一致する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial

/-- 既存の削除テンソルの各色の指定面を、更新した始域次数で読む。 -/
def deletedCutFace {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (ha : 0 < outputDegree s v a)
    (j : Fin (outputDegree s v a + 1)) (c : Fin r) :
    (⦋Function.update (outputDegree s v) a (outputDegree s v a - 1) c⦌ : SimplexCategory) ⟶
      ⦋q⦌ :=
  if hc : c = a then
    eqToHom (congrArg SimplexCategory.mk (by subst c; exact Function.update_self _ _ _)) ≫
      (boundaryFace _ ha j ≫ face s v a)
  else
    eqToHom (congrArg SimplexCategory.mk (Function.update_of_ne hc _ _)) ≫ face s v c

/-- C155：指定された面の頂点列は、指定された一色だけを削除する。 -/
lemma simplexVertexList_deletedCutFace {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (ha : 0 < outputDegree s v a)
    (j : Fin (outputDegree s v a + 1)) (c : Fin r) :
    simplexVertexList (deletedCutFace s v a ha j c) =
      if c = a then (verticesList s v.val a).eraseIdx j.val else verticesList s v.val c := by
  unfold deletedCutFace
  split_ifs with hc
  · rw [simplexVertexList_cast_source, simplexVertexList_boundaryFace, simplexVertexList_face]
    subst c
    exact Function.update_self _ _ _
  · rw [simplexVertexList_cast_source, simplexVertexList_face]
    exact Function.update_of_ne hc _ _

/-- C156：同じ経路頂点で指定した削除面は、その頂点の削除列を持つ。 -/
lemma simplexVertexList_deletedCutFace_at_vertex {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hd : 0 < outputDegree s v (label s v.val k))
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (c : Fin r) :
    simplexVertexList (deletedCutFace s v (label s v.val k) hd j c) =
      deletedVerticesList s v.val k c := by
  rw [simplexVertexList_deletedCutFace]
  unfold deletedVerticesList
  by_cases hc : c = label s v.val k
  · subst c
    simp only [ite_true, hj]
  · rw [ite_eq_right hc, ite_eq_right (Ne.symm hc)]

/-- C157：混合角の両側の指定面は、同じ更新次数への移送後、厳密に一致。 -/
lemma deletedCutFace_swapSteps {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a b : Fin (m + q)) (hab : b.val = a.val + 1)
    (ho : 0 < outputDegree s v (label s v.val b.castSucc))
    (hn : 0 < outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc))
    (jo : Fin (outputDegree s v (label s v.val b.castSucc) + 1))
    (jno : jo.val = vertexRank s v.val (label s v.val b.castSucc) b.castSucc)
    (jn : Fin (outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) + 1))
    (jnn : jn.val = vertexRank (s.swapSteps a b) v.val
      (label (s.swapSteps a b) v.val b.castSucc) b.castSucc) (c : Fin r) :
    deletedCutFace (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) hn jn c =
      eqToHom (congrArg SimplexCategory.mk
        (congrFun (deletedOutputDegree_swapSteps s v a b hab ho hn) c)) ≫
        deletedCutFace s v (label s v.val b.castSucc) ho jo c := by
  apply simplexVertexList_injective _ _
  change simplexVertexList _ = simplexVertexList _
  rw [simplexVertexList_cast_source,
    simplexVertexList_deletedCutFace_at_vertex _ _ _ hn jn jnn,
    simplexVertexList_deletedCutFace_at_vertex _ _ _ ho jo jno,
    deletedVerticesList_swapSteps s v.val a b hab]
  exact congrFun (deletedOutputDegree_swapSteps s v a b hab ho hn) c

end SerrePositivity.EInfinity.SimplexCuts
