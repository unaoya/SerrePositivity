module

public import SerrePositivity.EInfinity.SimplexCuts.VertexRanks
public import SerrePositivity.EInfinity.SimplexCuts.FaceVertexLists
public import SerrePositivity.EInfinity.SimplexCuts.BoundaryFaces

/-!
# 指定した出力面の頂点列

Berger–Fresse §2.2.7、M14 L09a。
出力の色と面番号を経路の頂点へ戻し、同じ面の列の削除を照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial

/-- C37：経路の指定頂点の色内順位は、昇順同値の逆の面番号。 -/
lemma vertexRank_symm_colorPositionEquiv {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) :
    vertexRank s u.val (label s u.val k) k = ((colorPositionEquiv s u).symm k).2.val := by
  have h := vertexRank_colorPositionEquiv s u
    ((colorPositionEquiv s u).symm k).1 ((colorPositionEquiv s u).symm k).2
  have hk : colorPositionEquiv s u
      ⟨((colorPositionEquiv s u).symm k).1, ((colorPositionEquiv s u).symm k).2⟩ = k :=
    (colorPositionEquiv s u).apply_symm_apply k
  rw [hk] at h
  simpa only [colorPositionEquiv_symm_color] using h

/-- C38：色と面番号で指定した頂点の色は指定色。 -/
lemma label_colorPositionEquiv {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (outputDegree s u a + 1)) :
    label s u.val (colorPositionEquiv s u ⟨a, j⟩) = a := by
  have h := colorPositionEquiv_symm_color s u (colorPositionEquiv s u ⟨a, j⟩)
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

/-- C39：出力面を指定する添字を経路の頂点へ戻したときの全色の列。 -/
lemma deletedTrace_at_outputFace {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (outputDegree s u a + 1))
    (c : Fin r) :
    selectColor c (deletedTrace s u.val (colorPositionEquiv s u ⟨a, j⟩)) =
      if c = a then (verticesList s u.val a).eraseIdx j.val else verticesList s u.val c := by
  rw [← deletedVerticesList_eq_selectColor]
  unfold deletedVerticesList
  rw [label_colorPositionEquiv]
  by_cases h : c = a
  · subst c
    rw [ite_eq_left rfl, ite_eq_left rfl, vertexRank_colorPositionEquiv]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

/-- C40：正次数の標準面も、同じ番号の頂点の削除で読める。 -/
lemma simplexVertexList_boundaryFace {n q : ℕ} (hn : 0 < n)
    (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋q⦌) (j : Fin (n + 1)) :
    simplexVertexList (boundaryFace n hn j ≫ f) = (simplexVertexList f).eraseIdx j.val := by
  cases n with
  | zero => omega
  | succ n => exact simplexVertexList_delta f j

/-- C40の証明分割：次数の等式で始域を移送しても、同じ値の頂点列になる。 -/
lemma simplexVertexList_cast_source {n n' q : ℕ} (h : n = n')
    (f : (⦋n'⦌ : SimplexCategory) ⟶ ⦋q⦌) :
    simplexVertexList (eqToHom (congrArg SimplexCategory.mk h) ≫ f) = simplexVertexList f := by
  cases h
  rfl

end SerrePositivity.EInfinity.SimplexCuts
