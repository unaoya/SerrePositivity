module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantTargetValueProjectionTo
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentNativeUnitValue

/-!
概要：元の余錐単位の固定値への相対後合成を、元の native 単位作用へ厳密に戻す。
方針：同じ円柱の標的表示を移し、元の指定単位表現の値への作用を回収する。
規約：全係数と元の単位を保持。使われ方：五因子の上側三角形項の実端点の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の余錐単位の固定値への作用は、元の native 単位作用の同じ全後合成射。 -/
lemma coherentNativeUnitValue_post {B : SSet.{u}} {C : SSet.{u + 1}}
    (G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (p : C ⟶ (SSet.uliftFunctor.{u + 1, u}).obj B) :
    functorHomotopyRelativePost (coconeTransformationHomotopy (coherentDiagramTotalCocone G)) p ≫
      constantTargetValueProjectionTo p (coherentDiagramTotalCocone_vertex G) =
    vertexFiberι ((ihom C).map (leftUnstraighteningProjection G)) (functorVertex p) ≫
      (ihom C).map (coherentNativeUnitValueAction G) := by
  have h := functorHomotopyConstantPost_value_retarget_action
    (coconeTransformationHomotopy (coherentDiagramTotalCocone G)) (coherentNativeUnitHomotopy G)
    (coherentDiagramTotalCocone_vertex G) (coherentNativeUnitHomotopy_h G).symm p
  simpa only [coherentNativeUnitHomotopy, coherentVertexOfHomotopy_of_vertex,
    coherentNativeUnitValueAction] using h

end SerrePositivity.InfinityCategories.F2
