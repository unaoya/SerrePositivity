module
public import SerrePositivity.InfinityCategories.Stable.CounitIntervalOpposite
public import SerrePositivity.InfinityCategories.Stable.AdjunctionOpposite
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitMappingAdjunction
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- 同じ実余単位の全区間比較から、元の二関手の ∞ 随伴と両三角式を得る。 -/
def qcatAdjunctionOfCounitIntervalCondition {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (G ≫ F) (𝟙 Y))
    (h : ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌), IsSimplicialHomotopyEquivalence
      (intervalFunctorMap F x (G.app (Opposite.op ⦋0⦌) y) ≫
        intervalPostcompose (F.app (Opposite.op ⦋0⦌) x)
          (SSet.Truncated.HomotopyCategory.homMk (simplicialHomotopyVertexEdge H y).toTruncated))) :
    QCatAdjunction F G :=
  qcatAdjunctionOfOpposite (qcatAdjunctionOfUnitMappingSpaceCondition
    (counitOppositeUnitHom H) (counitOppositeUnitHom_mappingSpaceCondition H h))
end SerrePositivity.InfinityCategories
