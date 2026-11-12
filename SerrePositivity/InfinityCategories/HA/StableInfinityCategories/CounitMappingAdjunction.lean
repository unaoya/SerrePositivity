module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CounitIntervalOpposite
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.AdjunctionOpposite
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingAdjunction
/-!
概要：実余単位の各写像空間条件から同じ二関手の ∞ 随伴を構成する。
方針：同じ実ホモトピーを反転し、任意パラメータ族の合成表示で比較する。
規約：標準の写像空間比較と元の全関手を保持する。使われ方：一般 RHom の ∞ 随伴。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 同じ実余単位の全区間比較から、元の二関手の ∞ 随伴と両三角式を得る。 -/
def qcatAdjunctionOfCounitIntervalCondition {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (G ≫ F) (𝟙 Y))
    (h : ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap F x (G.app (Opposite.op ⦋0⦌) y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose (F.app (Opposite.op ⦋0⦌) x)
          (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H y).toTruncated))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.qcatAdjunctionOfOpposite (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitMappingSpaceCondition
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.counitOppositeUnitHom H) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.counitOppositeUnitHom_mappingSpaceCondition H h))
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
