module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteCoherentProjection
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteCoherentProductNativeLegs
public import SerrePositivity.InfinityCategories.HomotopyLimits.TotalKanNativeCoconeComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.CoherentTransformationUnitCocone

/-!
概要：元の有限 native 積の各脚の全余錐作用を、元の反復射影変換と単位へ比較する。
方針：同じ脚の Kan ホモトピー・相対合成比較・元の単位表現を続ける。
規約：元の脚の全一単体・全余錐・指定三角形を保持する。
使われ方：P_Σ の sifted 余極限閉性へ有限 coherent 積比較を適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable (n : ℕ) {B : SSet.{u}} [IsSiftedInfinity B]
  (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
  (i : Discrete (ULift.{u} (Fin (n + 1))))

/-- 元の全空間射影の余錐は、反復 coherent 射影と元の単位の同じ合成余錐と同型。 -/
def finiteCoherentProjectionCoconeIso
    (T : F2.CoherentTransformationUnitTriangle (finiteCoherentSpaceProduct n F) (F i.as.down)
      (finiteCoherentProjectionVertex n F i.as.down)) :
    VertexIso (X := coconeMappingSpace (finiteCoherentSpaceProduct n F)
      (F2.coherentDiagramTotalVertex (F i.as.down)))
      (F2.coconeMappingPointAt (F2.coherentTotalMapCocone (finiteCoherentSpaceProduct n F)
        (F i.as.down) (finiteCoherentSpaceProductTotalProjection n F i.as.down))
        (F2.coherentDiagramTotalVertex (F i.as.down)) (F2.coherentTotalMapCocone_vertex _ _ _))
      (F2.coconeMappingPointAt (F2.coherentTransformationUnitCocone
        (finiteCoherentSpaceProduct n F) (F i.as.down)
        (finiteCoherentProjectionVertex n F i.as.down) T)
        (F2.coherentDiagramTotalVertex (F i.as.down))
        (F2.coherentTransformationUnitCocone_vertex _ _ _ T)) :=
  (constantCoconeHomotopyIso (finiteCoherentSpaceProduct n F)
    (F2.coherentDiagramTotalVertex (F i.as.down))
    (finiteCoherentProjectionUnitIso n F i.as.down).simplicialHomotopy).symm ≪≫
      (F2.coherentTransformationUnitCoconeIso (finiteCoherentSpaceProduct n F) (F i.as.down)
        (finiteCoherentProjectionVertex n F i.as.down) T).symm

/-- 余錐作用で使う辺は、元の native 有限積錐の同じ脚の全一単体。 -/
lemma finiteSiftedCoherentProductNativeEdge :
    (totalKanNativeEdge (finiteCoherentSpaceProduct n F) (F i.as.down)
      (finiteSiftedCoherentProductNativeKanLeg n F i)).edge =
        (F2.nativeConeLeg (finiteSiftedCoherentProductNativeCone n F)
          (ULift.up (ComposableArrows.mk₀ i))).edge :=
  F2.kanNativeConeLeg_edge _ _ _ _

/-- 元の native 脚の全余錐作用は、反復射影と指定単位の同じ三角形の余錐に同型。 -/
def finiteSiftedCoherentProductNativeCoconeIso
    (T : F2.CoherentTransformationUnitTriangle (finiteCoherentSpaceProduct n F) (F i.as.down)
      (finiteCoherentProjectionVertex n F i.as.down)) :
    VertexIso (X := coconeMappingSpace (finiteCoherentSpaceProduct n F)
      (F2.coherentDiagramTotalVertex (F i.as.down)))
      ((coconePointHomFamily (F2.coherentDiagramTotalCocone (finiteCoherentSpaceProduct n F))
        (F2.coherentDiagramTotalVertex (F i.as.down))).app (Opposite.op ⦋0⦌)
          (totalKanNativeHomPoint (finiteCoherentSpaceProduct n F) (F i.as.down)
            (finiteSiftedCoherentProductNativeKanLeg n F i)))
      (F2.coconeMappingPointAt (F2.coherentTransformationUnitCocone
        (finiteCoherentSpaceProduct n F) (F i.as.down)
        (finiteCoherentProjectionVertex n F i.as.down) T)
        (F2.coherentDiagramTotalVertex (F i.as.down))
        (F2.coherentTransformationUnitCocone_vertex _ _ _ T)) :=
  totalKanNativeCoconeIso (finiteCoherentSpaceProduct n F) (F i.as.down)
    (finiteSiftedCoherentProductNativeKanLeg n F i) ≪≫
      totalKanMapCoconeIso (finiteCoherentSpaceProduct n F) (F i.as.down)
        (finiteCoherentSpaceProductTotalProjection n F i.as.down)
        (Classical.choice (finiteSiftedCoherentProductNativeKanLeg_projection n F i)) ≪≫
          finiteCoherentProjectionCoconeIso n F i T

end SerrePositivity.InfinityCategories.HomotopyLimits
