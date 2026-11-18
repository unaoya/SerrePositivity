module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VertexRanks
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.FaceVertexLists
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryFaces

/-!
模型。文献の定義との比較は後で
# 指定した出力面の頂点列

Berger–Fresse §2.2.7、M14 L09a。
出力の色と面番号を経路の頂点へ戻し、同じ面の列の削除を照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open scoped _root_.Simplicial

/-- C37：経路の指定頂点の色内順位は、昇順同値の逆の面番号。 -/
lemma vertexRank_symm_colorPositionEquiv {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (k : Fin (m + q + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank s u.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s u.val k) k = ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv s u).symm k).2.val := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank_colorPositionEquiv s u
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv s u).symm k).1 ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv s u).symm k).2
  have hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv s u
      ⟨((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv s u).symm k).1, ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv s u).symm k).2⟩ = k :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv s u).apply_symm_apply k
  rw [hk] at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv_symm_color] using h

/-- C38：色と面番号で指定した頂点の色は指定色。 -/
lemma label_colorPositionEquiv {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s u a + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s u.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv s u ⟨a, j⟩) = a := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv_symm_color s u (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv s u ⟨a, j⟩)
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

/-- C39：出力面を指定する添字を経路の頂点へ戻したときの全色の列。 -/
lemma deletedTrace_at_outputFace {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (a : Fin r) (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s u a + 1))
    (c : Fin r) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedTrace s u.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositionEquiv s u ⟨a, j⟩)) =
      if c = a then (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList s u.val a).eraseIdx j.val else _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList s u.val c := by
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedVerticesList_eq_selectColor]
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedVerticesList
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label_colorPositionEquiv]
  by_cases h : c = a
  · subst c
    rw [ite_eq_left rfl, ite_eq_left rfl, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank_colorPositionEquiv]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

/-- C40：正次数の標準面も、同じ番号の頂点の削除で読める。 -/
lemma simplexVertexList_boundaryFace {n q : ℕ} (hn : 0 < n)
    (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋q⦌) (j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexVertexList (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryFace n hn j ≫ f) = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexVertexList f).eraseIdx j.val := by
  cases n with
  | zero => omega
  | succ n => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexVertexList_delta f j

/-- C40の証明分割：次数の等式で始域を移送しても、同じ値の頂点列になる。 -/
lemma simplexVertexList_cast_source {n n' q : ℕ} (h : n = n')
    (f : (⦋n'⦌ : SimplexCategory) ⟶ ⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexVertexList (eqToHom (congrArg SimplexCategory.mk h) ≫ f) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexVertexList f := by
  cases h
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
