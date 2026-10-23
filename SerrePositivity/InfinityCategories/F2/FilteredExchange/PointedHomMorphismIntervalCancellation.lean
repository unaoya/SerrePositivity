module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentKanMorphismComparisonIdentity
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedHomMorphismValueComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.VertexIsoIdentityFactor

/-!
概要：固定 Kan 射での全値比較から、元の二側区間比較の恒等因子を除く。
方針：同じ実辺の区間頂点の等式を保ち、指定二側成分の恒等性を適用する。
規約：左全作用の指定比較を保持。使われ方：元の長辺 prism の普遍比較との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {K L : KanObject.{u}} (f : K ⟶ L)
local notation "C" => pointedCoherentFiberComparison K ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K)))
local notation "V" => eqToHom (congrArg (vertexFiber pointedSpaceProjection)
  (Eq.symm (spaceInfinityVertex_eq_coherent L))) ≫
    QCatEquivalence.hom (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L))
local notation "P" => NatTrans.app (pre C)
  (CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj L))
local notation "A" => FunctorIso.app (pointedLeftHomValueActionIso K L)
  (ULift.up (SSet.opObjEquiv.symm (functorVertex f)))

/-- 同じ固定射で、左全作用の比較成分を同じ右区間の頂点の表示で保持する。 -/
def pointedHomMorphismLeftValueComparison :=
  vertexIsoOfEq A (pointedOppositeHomValue_morphism_vertex f V)
    (congrArg (NatTrans.app P (Opposite.op ⦋0⦌))
      (congrArg ((pointedIntervalValueAction K L).app (Opposite.op ⦋0⦌))
        ((coherentKanLeftHomInterval_morphism f).trans
          (coherentKanRightHomInterval_morphism f).symm)))

/-- 元の固定射の全値比較は、同じ左作用成分から恒等の二側因子を除いた値。 -/
lemma pointedHomMorphismValueComparison_eq_left :
    pointedHomMorphismValueComparison f = pointedHomMorphismLeftValueComparison f := by
  let B := VertexIso.map (VertexIso.map (coherentKanMorphismIntervalComparison f)
    (pointedIntervalValueAction K L)) P
  let m := pointedIntervalValueAction K L ≫ P
  have hv := (coherentKanLeftHomInterval_morphism f).trans
    (coherentKanRightHomInterval_morphism f).symm
  have hb : HEq B (Iso.refl (SSet.HomotopyCategory.mk
      (m.app (Opposite.op ⦋0⦌)
        ((coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌)
          (ULift.up (functorVertex f)))))) := by
    dsimp only [B]
    rw [vertexIso_map_comp]
    exact vertexIso_map_heq_refl_of_heq (coherentKanMorphismIntervalComparison f) hv
      (coherentKanMorphismIntervalComparison_heq_refl_right f) m
  have hd := vertexIso_trans_heq_of_right_refl A B
    (congrArg (m.app (Opposite.op ⦋0⦌)) hv) hb
  have he : HEq (pointedHomMorphismValueComparison f) A :=
    (vertexIsoOfEq_heq _ _ _).trans hd
  exact eq_of_heq (he.trans (vertexIsoOfEq_heq _ _ _).symm)

/-- 元の固定射の評価比較は、同じ左作用の比較と元の右評価比較の逆の二因子。 -/
lemma pointedHomMorphismEvaluationComparison_factor_left :
    pointedHomMorphismEvaluationComparison f =
      pointedHomMorphismLeftValueComparison f ≪≫
        (VertexIso.map (pointedValueHomActionAt f) P).symm := by
  unfold pointedHomMorphismEvaluationComparison
  rw [pointedHomMorphismValueComparison_eq_left]

end SerrePositivity.InfinityCategories.F2
