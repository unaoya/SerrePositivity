module

public import SerrePositivity.EInfinity.SimplexCuts.DeletedCutFaces

/-!
# 入力の面を合成した小さい切断の指定削除面

Berger–Fresse §2.2.6–7、M14 L09a。
同じ削除色列が入力の単体射による像である場合、次数と指定面を元の単体圏で照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial

/-- C237：単体射の後合成は、同じ順序付き頂点列の像。 -/
lemma simplexVertexList_postcomp {n q q' : ℕ}
    (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋q⦌) (g : (⦋q⦌ : SimplexCategory) ⟶ ⦋q'⦌) :
    simplexVertexList (f ≫ g) = (simplexVertexList f).map g.toOrderHom := by
  simp only [simplexVertexList, List.map_ofFn]
  rfl

/-- C238：削除後の各色の列が同じ入力射による像なら、更新出力次数は一致。 -/
lemma deletedOutputDegree_eq_of_mapped_vertexLists {m n q q' r : ℕ}
    (s : Cut m q) (t : Cut n q')
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (g : (⦋q'⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (hl : ∀ c, deletedVerticesList s v.val k c = (verticesList t w.val c).map g.toOrderHom) :
    Function.update (outputDegree s v) (label s v.val k)
      (outputDegree s v (label s v.val k) - 1) = outputDegree t w := by
  funext c
  apply Nat.add_right_cancel (m := 1)
  rw [← deletedVerticesList_length_update s v k hd c, ← verticesList_length t w c,
    hl c, List.length_map]

/-- C239：指定削除面は、次数移送・小さい切断の面・同じ入力射の合成と厳密に一致。 -/
lemma deletedCutFace_eq_of_mapped_vertexLists {m n q q' r : ℕ}
    (s : Cut m q) (t : Cut n q')
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (g : (⦋q'⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (hl : ∀ c, deletedVerticesList s v.val k c = (verticesList t w.val c).map g.toOrderHom)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (c : Fin r) :
    deletedCutFace s v (label s v.val k) hd j c =
      eqToHom (congrArg SimplexCategory.mk
        (congrFun (deletedOutputDegree_eq_of_mapped_vertexLists s t v w k hd g hl) c)) ≫
          (face t w c ≫ g) := by
  apply simplexVertexList_injective _ _
  change simplexVertexList _ = simplexVertexList _
  have hsrc := congrFun (deletedOutputDegree_eq_of_mapped_vertexLists s t v w k hd g hl) c
  rw [simplexVertexList_cast_source hsrc (face t w c ≫ g),
    simplexVertexList_deletedCutFace_at_vertex s v k hd j hj c,
    simplexVertexList_postcomp, simplexVertexList_face, hl c]

end SerrePositivity.EInfinity.SimplexCuts
