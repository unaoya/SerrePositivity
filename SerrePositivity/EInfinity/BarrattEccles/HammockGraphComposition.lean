module

public import SerrePositivity.EInfinity.BarrattEccles.HammockGraphTransition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GraphComposition

/-!
# 元の E 代数の固定語の hammock graph の合成

概要：任意の可換環上で、実際の E 代数の固定語の graph を全単体で合成する。
方針：元の弱同値の全縦射を保持する連結関手の単体的合成を代入する。
規約：モデル構造の追加入力は不要。全語の余極限への降下は後続。
使われ方：CAlg_R の高次比較に使う hammock の合成の構成。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra MonoidalCategory

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 元の同じ E 代数の固定語の graph の単体的合成。 -/
def algebraHammockGraphComposition (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y Z : (operad A).Algebra) :
    algebraHammockGraph A a X Y ⊗ algebraHammockGraph A b Y Z ⟶
      algebraHammockGraph A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) X Z := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition (weakEquivalences (operad A).Algebra) a b X Y Z

/-- 全単体の全頂点で、元の同じ二つの zigzag を連結する。 -/
lemma algebraHammockGraphComposition_vertex (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y Z : (operad A).Algebra)
    (n : SimplexCategoryᵒᵖ) (σ : (algebraHammockGraph A a X Y).obj n)
    (τ : (algebraHammockGraph A b Y Z).obj n) (j : Fin (n.unop.len + 1)) :
    ((algebraHammockGraphComposition A a b X Y Z).app n (σ, τ)).obj j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (σ.obj j) (τ.obj j) := rfl

/-- 全単体の全縦射で、元の同じ弱同値の二つの縦射を連結する。 -/
lemma algebraHammockGraphComposition_map (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y Z : (operad A).Algebra)
    (n : SimplexCategoryᵒᵖ) (σ : (algebraHammockGraph A a X Y).obj n)
    (τ : (algebraHammockGraph A b Y Z).obj n) {i j : Fin (n.unop.len + 1)} (h : i ⟶ j) :
    ((algebraHammockGraphComposition A a b X Y Z).app n (σ, τ)).map h =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendMorphisms.map (σ.map h) (τ.map h) := rfl

end SerrePositivity.EInfinity.BarrattEccles
