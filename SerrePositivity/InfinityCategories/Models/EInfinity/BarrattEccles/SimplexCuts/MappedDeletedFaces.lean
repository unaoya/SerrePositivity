module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.DeletedCutFaces

/-!
模型。文献の定義との比較は後で
# 入力の面を合成した小さい切断の指定削除面

Berger–Fresse §2.2.6–7、M14 L09a。
同じ削除色列が入力の単体射による像である場合、次数と指定面を元の単体圏で照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open scoped _root_.Simplicial

/-- C237：単体射の後合成は、同じ順序付き頂点列の像。 -/
lemma simplexVertexList_postcomp {n q q' : ℕ}
    (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋q⦌) (g : (⦋q⦌ : SimplexCategory) ⟶ ⦋q'⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexVertexList (f ≫ g) = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexVertexList f).map g.toOrderHom := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexVertexList, List.map_ofFn]
  rfl

/-- C238：削除後の各色の列が同じ入力射による像なら、更新出力次数は一致。 -/
lemma deletedOutputDegree_eq_of_mapped_vertexLists {m n q q' r : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut n q')
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k))
    (g : (⦋q'⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (hl : ∀ c, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedVerticesList s v.val k c = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList t w.val c).map g.toOrderHom) :
    Function.update (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) - 1) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree t w := by
  funext c
  apply Nat.add_right_cancel (m := 1)
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedVerticesList_length_update s v k hd c, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList_length t w c,
    hl c, List.length_map]

/-- C239：指定削除面は、次数移送・小さい切断の面・同じ入力射の合成と厳密に一致。 -/
lemma deletedCutFace_eq_of_mapped_vertexLists {m n q q' r : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut n q')
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k))
    (g : (⦋q'⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (hl : ∀ c, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedVerticesList s v.val k c = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList t w.val c).map g.toOrderHom)
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) + 1))
    (hj : j.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank s v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) k) (c : Fin r) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedCutFace s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) hd j c =
      eqToHom (congrArg SimplexCategory.mk
        (congrFun (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedOutputDegree_eq_of_mapped_vertexLists s t v w k hd g hl) c)) ≫
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face t w c ≫ g) := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexVertexList_injective _ _
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexVertexList _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexVertexList _
  have hsrc := congrFun (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedOutputDegree_eq_of_mapped_vertexLists s t v w k hd g hl) c
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexVertexList_cast_source hsrc (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face t w c ≫ g),
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexVertexList_deletedCutFace_at_vertex s v k hd j hj c,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexVertexList_postcomp, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexVertexList_face, hl c]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
