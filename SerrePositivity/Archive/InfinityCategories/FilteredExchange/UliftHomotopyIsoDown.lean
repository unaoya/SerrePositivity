module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSpaceDownFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Homotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-!
概要：元の全ホモトピーを持ち上げた指定同型の下降は、元の同じ指定類である。
方針：全円柱から得る辺を内部 Hom の宇宙同型で戻し、辺の下降を計算する。
規約：代表を選び直さない。使われ方：元の模型 path の等式の大宇宙への反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2
variable {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g)

/-- 持ち上げた全円柱の辺を宇宙同型で戻すと、元の同じ辺の持ち上げになる。 -/
lemma uliftHomotopyEdge_functorSpaceInv :
    (functorEdgeOfSimplicialHomotopy (uliftSimplicialHomotopy.{u, v} H)).map
      ((truncation 2).map (uliftFunctorSpaceIso.{u, v} X Y).inv) =
    uliftTruncatedEdge.{u, v} (functorEdgeOfSimplicialHomotopy H) := by
  apply Truncated.Edge.ext
  apply ULift.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

/-- 持ち上げた指定円柱の同型を下降すると、元の指定円柱の同型を厳密に回収する。 -/
lemma functorIsoDown_uliftHomotopy [KanComplex Y] :
    functorIsoDown (functorIsoOfSimplicialHomotopy (uliftSimplicialHomotopy.{u, v} H)) =
      functorIsoOfSimplicialHomotopy H := by
  rw [functorIsoDown_eq_mapIso]
  apply Iso.ext
  change (universeHomotopyDown ((ihom X).obj Y)).map
    (Truncated.HomotopyCategory.homMk
      ((functorEdgeOfSimplicialHomotopy (uliftSimplicialHomotopy.{u, v} H)).map
        ((truncation 2).map (uliftFunctorSpaceIso.{u, v} X Y).inv))) =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)
  rw [uliftHomotopyEdge_functorSpaceInv, universeHomotopyDown_map_homMk]
  rfl

end SerrePositivity.InfinityCategories.F2
