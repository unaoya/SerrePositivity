module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningEdgeLiftFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorCompositionConstant

/-!
概要：元の unstraightening の前合成比較を、同じ普遍持ち上げの終点写像による前合成と結ぶ。
方針：元の三角形族による比較に、指定辺での頂点公式と相対合成の固定成分の式を使う。
規約：標準 pinched 前合成と元の写像空間の比較を保持する。
使われ方：G8 の四角形①の、辺による前合成と相対実射による前合成の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-- 元の pinched 前合成の比較は、元の全写像空間から取り出した実際の終点の前合成と同型。 -/
def unstraighteningPinchedEdgeLiftPrecompositionIso {B : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (functorVertex F) (functorVertex G)) :
    FunctorIso
      (precompose (functorVertex J) (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) ≫
        leftUnstraighteningPinchedMappingSpaceMap F J)
      (leftUnstraighteningPinchedMappingSpaceMap G J ≫
        relativeFunctorOverPre (leftUnstraighteningProjection J)
          (show Over.mk (leftUnstraighteningProjection F) ⟶
              Over.mk (leftUnstraighteningProjection G) from
            Over.homMk (leftUnstraighteningEdgeLiftMap F G e)
              (leftUnstraighteningEdgeLiftMap_projection F G e))) := by
  have h := SetWeight.unstraighteningPinchedPrecompositionIso F G J e
  simp only [SSet.const_comp] at h
  erw [leftUnstraighteningEdgeLiftMap_vertex F G e] at h
  let f : Over.mk (leftUnstraighteningProjection F) ⟶
      Over.mk (leftUnstraighteningProjection G) :=
    Over.homMk (leftUnstraighteningEdgeLiftMap F G e)
      (leftUnstraighteningEdgeLiftMap_projection F G e)
  erw [relativeFunctorComposition_const_first _ _ (Over.mk (leftUnstraighteningProjection J))
    f (leftUnstraighteningMappingSpaceMap G J)] at h
  dsimp only [f, Over.mk, Over.hom, CostructuredArrow.mk] at h
  simp only [leftUnstraighteningPinchedMappingSpaceMap, Category.assoc] at h ⊢
  exact h

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
