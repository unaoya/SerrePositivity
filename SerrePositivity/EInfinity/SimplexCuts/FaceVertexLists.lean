module

public import SerrePositivity.EInfinity.SimplexCuts.VertexErasure
public import SerrePositivity.EInfinity.SimplexCuts.Faces

/-!
# 面写像と頂点列の削除

Berger–Fresse §2.2.7、M14 L09a。
単体圏の指定面を、同じ昇順の色の頂点列の一文字の削除として読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial

/-- 単体圏の射の順序を保つ頂点列。 -/
def simplexVertexList {n q : ℕ} (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋q⦌) :
    List (Fin (q + 1)) := List.ofFn f.toOrderHom

/-- C34：同じ始域・終域の単体圏の射は、頂点列で区別できる。 -/
lemma simplexVertexList_injective (n q : ℕ) :
    Function.Injective (fun f : (⦋n⦌ : SimplexCategory) ⟶ ⦋q⦌ => simplexVertexList f) := by
  intro f g h
  ext i
  have he := congrArg (fun l : List (Fin (q + 1)) => l[i.val]?) h
  have hc : f.toOrderHom i = g.toOrderHom i := by
    simpa only [simplexVertexList, List.getElem?_ofFn, i.isLt, dite_eq_left,
      Option.some.injEq] using he
  exact congrArg Fin.val hc

/-- C35：指定面の合成は、その番号の頂点を列から削除する。 -/
lemma simplexVertexList_delta {n q : ℕ}
    (f : (⦋n + 1⦌ : SimplexCategory) ⟶ ⦋q⦌) (j : Fin (n + 2)) :
    simplexVertexList (SimplexCategory.δ j ≫ f) = (simplexVertexList f).eraseIdx j.val := by
  unfold simplexVertexList
  rw [eraseIdx_ofFn]
  rfl

/-- C36：BFの同じ指定面の頂点列は、色のfiberから定義した列そのもの。 -/
lemma simplexVertexList_face {m q r : ℕ} (s : Cut m q)
    (u : Surjection.Word r (m + 1)) (a : Fin r) :
    simplexVertexList (face s u a) = verticesList s u.val a := by
  unfold verticesList
  rw [← (colorPositions s u.val a).listMap_orderEmbOfFin_finRange (colorPositions_card_eq s u a)]
  rw [← List.ofFn_id, List.map_map, List.map_ofFn]
  rfl

end SerrePositivity.EInfinity.SimplexCuts
