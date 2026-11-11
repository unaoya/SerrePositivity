module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SmallUnstraighteningFunctorIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UniverseHomotopyDownNaturality

/-!
概要：持ち上げた二空間間の関手のホモトピー圏を、元の関手のホモトピー圏へ下降する。
方針：内部 Hom の宇宙同型の逆と、全ホモトピー圏の下降関手を合成する。
規約：対象・射・指定同型の値を保持。使われ方：指定 path の合成と下降の交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の関手空間のホモトピー圏への下降関手。 -/
def functorSpaceDown (X Y : SSet.{u}) :
    ((ihom ((SSet.uliftFunctor.{v, u}).obj X)).obj
      ((SSet.uliftFunctor.{v, u}).obj Y)).HomotopyCategory ⥤
        ((ihom X).obj Y).HomotopyCategory :=
  SSet.mapHomotopyCategory (uliftFunctorSpaceIso.{u, v} X Y).inv ⋙
    universeHomotopyDown ((ihom X).obj Y)

/-- 下降関手の指定像は、元の指定頂点同型の表示を戻して下降する操作。 -/
lemma functorSpaceDown_mapIso {X Y : SSet.{u}} [Quasicategory Y]
    {x y : ((ihom ((SSet.uliftFunctor.{v, u}).obj X)).obj
      ((SSet.uliftFunctor.{v, u}).obj Y)) _⦋0⦌} (e : VertexIso x y) :
    (functorSpaceDown.{u, v} X Y).mapIso e =
      downVertexIso (VertexIso.map e (uliftFunctorSpaceIso.{u, v} X Y).inv) := by
  exact (downVertexIso_eq_mapIso
    (VertexIso.map e (uliftFunctorSpaceIso.{u, v} X Y).inv)).symm

/-- 指定関手同型の下降は同じ下降関手による指定像。 -/
lemma functorIsoDown_eq_mapIso {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g)) :
    functorIsoDown e = (functorSpaceDown.{u, v} X Y).mapIso e :=
  (functorSpaceDown_mapIso e).symm

end SerrePositivity.InfinityCategories.F2
