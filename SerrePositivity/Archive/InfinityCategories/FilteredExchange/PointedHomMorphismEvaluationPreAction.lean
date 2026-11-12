module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedHomMorphismValueComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoMapCoherence
/-!
概要：元の固定射の評価比較の前作用を、同じ値比較と作用比較の二因子で保持する。
方針：同じ頂点同型の合成と逆の像を一般の係数射で計算する。
規約：元の二比較と全係数を保持する。
使われ方：最後射の評価比較の第一射係数作用への接続。
-/

@[expose] public section
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
noncomputable section
universe u
/-- 概要：合成と逆の像は元の指定二因子の像の合成。
方針：頂点同型の合成・逆の像の則を使う。規約：指定値を保持。使われ方：評価の二因子。 -/
private lemma map_trans_symm {X Y : SSet.{u}} {a b c : X _⦋0⦌}
    (e : VertexIso a b) (d : VertexIso c b) (h : X ⟶ Y) :
    VertexIso.map (e ≪≫ d.symm) h = VertexIso.map e h ≪≫ (VertexIso.map d h).symm := by
  rw [vertexIso_map_trans, vertexIso_map_symm]
/-- 概要：元の評価比較の前作用は同じ値比較と作用比較の像の二因子。
方針：同じ合成と逆を前作用へ移す。規約：全係数を保持。使われ方：最後射の評価比較。 -/
lemma pointedHomMorphismEvaluationComparison_map_pre_eq_factors
    {K L : KanObject.{u}} (f : K ⟶ L) {D : SSet.{u + 1}}
    (q : D ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom pointKanObject K).op) :
    VertexIso.map (pointedHomMorphismEvaluationComparison f)
      ((pre q).app ((SSet.uliftFunctor.{u + 1, u}).obj L.obj)) =
    VertexIso.map (pointedHomMorphismValueComparison f)
      ((pre q).app ((SSet.uliftFunctor.{u + 1, u}).obj L.obj)) ≪≫
      (VertexIso.map (VertexIso.map (pointedValueHomActionAt f)
        ((pre (pointedCoherentFiberComparison K ≫
          eqToHom (congrArg (vertexFiber pointedSpaceProjection)
            (spaceInfinityVertex_eq_coherent K).symm))).app
              ((SSet.uliftFunctor.{u + 1, u}).obj L.obj)))
        ((pre q).app ((SSet.uliftFunctor.{u + 1, u}).obj L.obj))).symm := by
  exact map_trans_symm (pointedHomMorphismValueComparison f)
    (VertexIso.map (pointedValueHomActionAt f)
      ((pre (pointedCoherentFiberComparison K ≫
        eqToHom (congrArg (vertexFiber pointedSpaceProjection)
          (spaceInfinityVertex_eq_coherent K).symm))).app
            ((SSet.uliftFunctor.{u + 1, u}).obj L.obj)))
    ((pre q).app ((SSet.uliftFunctor.{u + 1, u}).obj L.obj))
end
end SerrePositivity.InfinityCategories.F2
