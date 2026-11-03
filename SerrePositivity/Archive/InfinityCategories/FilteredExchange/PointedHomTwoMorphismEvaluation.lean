module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedHomMorphismCompositionDisplay
/-!
概要：元の二 Kan 射の評価比較を、同じ第一射の係数作用と最後射への像で合成する。
方針：元の二比較を同じ内部 Hom の前後作用へ写す。
規約：元の指定評価比較と全係数を保持する。
使われ方：元の raw 二辺値と二射の評価の合成則の照合。
-/

@[expose] public section
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
noncomputable section
universe u
variable {K M L : KanObject.{u}} (f : K ⟶ M) (g : M ⟶ L)
local notation "A" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (CategoryTheory.Functor.obj SSet.opFunctor (SimplicialCategory.sHom pointKanObject K))
local notation "P" => CategoryTheory.Functor.map SSet.uliftFunctor
  (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject f))
local notation "Y" => CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj L)
local notation "ug" => CategoryTheory.Functor.map SSet.uliftFunctor g

/-- 概要：同じ元の二評価の指定された合成。
方針：最後射評価の前作用と第一射評価の後作用を合成する。
規約：全係数と元の指定値を保持。使われ方：合成射評価との照合。 -/
def pointedHomTwoMorphismEvaluationComparison :=
  VertexIso.map (pointedHomMorphismEvaluationComparison g) ((pre P).app Y) ≪≫
    VertexIso.map (pointedHomMorphismEvaluationComparison f) ((ihom A).map ug)
end
end SerrePositivity.InfinityCategories.F2
