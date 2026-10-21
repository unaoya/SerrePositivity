module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeAssociativityEdge
public import SerrePositivity.InfinityCategories.F1.FunctorEdgeEvaluationSimplex

/-!
概要：元の結合比較辺の一単体を、端点の正規化から独立した同じ区間族の評価に戻す。
方針：元の辺と頂点評価の一単体公式を別々の境界で使う。
規約：既存の区間族と同じ元の辺を保持する。
使われ方：結合比較の大きな端点を再展開せず prism と照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 元の結合比較辺の一単体は、同じ転置した区間族の評価そのもの。 -/
lemma cocartesianBaseChangeAssociativityEdge_edge_simplex :
    (cocartesianBaseChangeAssociativityEdge l k).edge =
    (transposeFunctorFamily (cocartesianBaseChangeAssociativityIntervalFamily l k)).app
      (Opposite.op ⦋1⦌) homotopyIntervalEdge.edge := rfl

/-- 同じ結合比較辺を元の fibration で評価した一単体を、区間族の評価へ戻す。 -/
lemma cocartesianBaseChangeAssociativityEdge_at_simplex
    (p : CocartesianFibrationCategory (nerve C)) :
    (functorEdgeAt (cocartesianBaseChangeAssociativityEdge l k) (coherentNerveVertex p)).edge =
    (evaluateFunctorAt (Y := CatInfinityFunctor
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) (coherentNerveVertex p)).app
        (Opposite.op ⦋1⦌)
        ((transposeFunctorFamily (cocartesianBaseChangeAssociativityIntervalFamily l k)).app
          (Opposite.op ⦋1⦌) homotopyIntervalEdge.edge) := by
  have h := functorEdgeAt_edge_simplex
    (B := CocartesianFibrationInfinity (nerve C))
    (X := CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))
    (F := cocartesianFibrationInfinityBaseChange (nerveMap k) ≫
      cocartesianFibrationInfinityBaseChange (nerveMap l) ≫ cocartesianStraighteningCoherentMap A)
    (G := cocartesianFibrationInfinityBaseChange (nerveMap (l ⋙ k)) ≫
      cocartesianStraighteningCoherentMap A)
    (cocartesianBaseChangeAssociativityEdge l k) (coherentNerveVertex p)
  exact h.trans (congrArg
    ((evaluateFunctorAt (Y := CatInfinityFunctor
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) (coherentNerveVertex p)).app
        (Opposite.op ⦋1⦌))
    (cocartesianBaseChangeAssociativityEdge_edge_simplex l k))

end SerrePositivity.InfinityCategories
