module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedHomMorphismValueComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.VertexIsoCompositionTransport

/-!
概要：精密化の終点での全値比較を、同じ元の Kan 射の固定比較へ戻す。
方針：実終点の等式で指定成分と左右区間比較を同時に写す。
規約：全係数と指定比較の値を保持。使われ方：元の二辺比較の固定射への統一。
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
  (e : (SimplicialCategory.sHom K L) _⦋1⦌)
local notation "H" => SimplicialCategory.sHom K L
local notation "A" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (CategoryTheory.Functor.obj SSet.opFunctor (SimplicialCategory.sHom pointKanObject K))
local notation "C" => pointedCoherentFiberComparison K ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K)))
local notation "V" => eqToHom (congrArg (vertexFiber pointedSpaceProjection)
  (Eq.symm (spaceInfinityVertex_eq_coherent L))) ≫
    QCatEquivalence.hom (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L))
local notation "P" => NatTrans.app (pre C)
  (CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj L))
local notation "F" => pointedOppositeHomAction K L ≫ CategoryTheory.Functor.map (ihom A) V
local notation "G" => (coherentKanLeftHomInterval K L ≫ pointedIntervalValueAction K L) ≫ P
local notation "η" => pointedLeftHomValueActionIso K L

/-- 元の精密化の終点における全値比較は、同じ射の指定比較そのもの。 -/
lemma pointedHomRefinementTargetValue_heq_morphism (h : (H).δ 0 e = functorVertex f) :
    HEq (FunctorIso.app η (ULift.up (SSet.opObjEquiv.symm ((H).δ 0 e))) ≪≫
      VertexIso.map (VertexIso.map (coherentKanRefinementTargetComparison K L e)
        (pointedIntervalValueAction K L)) P) (pointedHomMorphismValueComparison f) := by
  have hx := congrArg (fun t => ULift.up (SSet.opObjEquiv.symm t)) h
  have hl := congrArg (fun t => (coherentKanLeftHomInterval K L).app (Opposite.op ⦋0⦌)
    (ULift.up (SSet.opObjEquiv.symm t))) h
  have hr := congrArg (fun t => (coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌)
    (ULift.up t)) h
  have hm := vertexIso_map_heq_of_heq (coherentKanRefinementTargetComparison K L e)
    (coherentKanMorphismIntervalComparison f) hl hr
    (coherentKanRefinementTargetComparison_heq_morphism f e h) (pointedIntervalValueAction K L)
  have hn := vertexIso_map_heq_of_heq
    (VertexIso.map (coherentKanRefinementTargetComparison K L e) (pointedIntervalValueAction K L))
    (VertexIso.map (coherentKanMorphismIntervalComparison f) (pointedIntervalValueAction K L))
    (congrArg ((pointedIntervalValueAction K L).app (Opposite.op ⦋0⦌)) hl)
    (congrArg ((pointedIntervalValueAction K L).app (Opposite.op ⦋0⦌)) hr) hm P
  have ht := vertexIso_trans_heq_of_heq
    (FunctorIso.app η (ULift.up (SSet.opObjEquiv.symm ((H).δ 0 e))))
    (VertexIso.map (VertexIso.map (coherentKanRefinementTargetComparison K L e)
      (pointedIntervalValueAction K L)) P)
    (FunctorIso.app η (ULift.up (SSet.opObjEquiv.symm (functorVertex f))))
    (VertexIso.map (VertexIso.map (coherentKanMorphismIntervalComparison f)
      (pointedIntervalValueAction K L)) P)
    (congrArg (NatTrans.app F (Opposite.op ⦋0⦌)) hx)
    (congrArg (NatTrans.app G (Opposite.op ⦋0⦌)) hx)
    (congrArg (NatTrans.app P (Opposite.op ⦋0⦌))
      (congrArg ((pointedIntervalValueAction K L).app (Opposite.op ⦋0⦌)) hr))
    (functorIso_app_heq_of_vertex_eq η hx) hn
  exact ht.trans (vertexIsoOfEq_heq _ _ _).symm

end SerrePositivity.InfinityCategories.F2
