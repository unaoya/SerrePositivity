module

public import SerrePositivity.InfinityCategories.F2.CoherentKanMorphismIntervalComparison
public import SerrePositivity.InfinityCategories.F2.PointedLeftHomValueAction
public import SerrePositivity.InfinityCategories.F2.PointedValueTriangleSquare
public import SerrePositivity.InfinityCategories.F2.PointedOppositeMorphismValueVertex

/-!
概要：元の固定 Kan 射での全係数比較を、同じ値と同じ右区間で保持する。
方針：左作用比較の同じ成分と、同じ二側区間比較を合成する。
規約：比較を選び直さず元の全係数を保持。使われ方：実長辺の普遍比較との照合。
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
local notation "D" => CategoryTheory.Functor.map SSet.uliftFunctor
  (CategoryTheory.Functor.map SSet.opFunctor (eHomWhiskerLeft SSet pointKanObject f))

/-- 元の射の全反転 Hom 作用の値と、同じ右区間輸送の値との指定比較。 -/
def pointedHomMorphismValueComparison :
    VertexIso (functorVertex ((D ≫ pointedCoherentFiberComparison L) ≫ V))
      ((NatTrans.app P (Opposite.op ⦋0⦌))
        ((pointedValueHomTransport K L).app (Opposite.op ⦋0⦌)
          (ULift.up (functorVertex f)))) :=
  vertexIsoOfEq ((pointedLeftHomValueActionIso K L).app
      (ULift.up (SSet.opObjEquiv.symm (functorVertex f))) ≪≫
    VertexIso.map (VertexIso.map (coherentKanMorphismIntervalComparison f)
      (pointedIntervalValueAction K L)) P)
    (pointedOppositeHomValue_morphism_vertex f V) rfl

/-- 元の射の全反転 Hom 作用の値を、同じ射による元の値の評価へ比較する。 -/
def pointedHomMorphismEvaluationComparison :=
  pointedHomMorphismValueComparison f ≪≫ (VertexIso.map (pointedValueHomActionAt f) P).symm

end SerrePositivity.InfinityCategories.F2
