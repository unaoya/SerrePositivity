module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionHomCylinder
public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentHomNaturality

/-!
概要：部分余極限の余錐制限の Hom 比較を、評価固定の同じ中間円柱から作る。
方針：元の付加比較辺と正規化した制限に、評価固定の自然性データを適用する。
規約：元の全 Hom の族と実際の付加辺を保持する。円柱の raw な射影と評価式を公開する。
使われ方：共通 path end の HR/HL を実際の円柱データに接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A C X : SSet.{u}} [Quasicategory X] {p : A ⟶ X}
  (c : JoinCocone p) (hc : IsColimitCone c) (i : A ⟶ C)
  (F : C ⟶ X) (hi : i ≫ F = p) (d : JoinCocone F)
  (hd : IsColimitCone d) (y : X _⦋0⦌)

/-- 実際の付加比較辺と元の制限に沿う、評価固定の同じ中間比較データ。 -/
def colimitAttachmentRestrictionCylinderData :=
  initialRestrictionHomCylinderData (sliceUnderProjection F) (sliceUnderProjection p)
    (normalizedCoconeRestriction F i hi) (normalizedCoconeRestriction_projection F i hi)
    d hd (colimitAttachmentRestrictionEdge c hc i F hi d) y hc

/-- 余錐制限と Hom 前合成の正方形を、同じ評価固定中間円柱で結ぶ。 -/
def colimitAttachmentRestrictionHomCylinder : SSet.Homotopy
    (normalizedCoconeRestrictionFiber F i hi y ≫ coconeMappingSpaceHomComparison c hc y)
    (coconeMappingSpaceHomComparison d hd y ≫
      colimitAttachmentHomPrecomposition c hc i F hi d y) :=
  initialRestrictionHomCylinder (sliceUnderProjection F) (sliceUnderProjection p)
    (normalizedCoconeRestriction F i hi) (normalizedCoconeRestriction_projection F i hi)
    d hd (colimitAttachmentRestrictionEdge c hc i F hi d) y hc

/-- 公開した正方形の円柱の射は、同じ評価固定円柱の像そのもの。 -/
lemma colimitAttachmentRestrictionHomCylinder_projection :
    (colimitAttachmentRestrictionHomCylinder c hc i F hi d hd y).h =
      (colimitAttachmentRestrictionCylinderData c hc i F hi d hd y).homotopy.h ≫
        leftFibrationInitialProjection (sliceUnderProjection p) c y ≫
          (leftFibrationInitialBaseIso (sliceUnderProjection p) c y).hom := rfl

/-- 中間円柱の評価は全時刻で元の余錐の制限そのものを保つ。 -/
lemma colimitAttachmentRestrictionCylinderData_evaluation :
    (colimitAttachmentRestrictionCylinderData c hc i F hi d hd y).homotopy.h ≫
        leftFibrationInitialEvaluation (sliceUnderProjection p) c y =
      CartesianMonoidalCategory.fst (coconeMappingSpace F y) (Δ[1] : SSet.{u}) ≫
        normalizedCoconeRestrictionFiber F i hi y :=
  initialRestrictionHomCylinderData_evaluation _ _ _ _ _ _ _ _ _

end
end SerrePositivity.InfinityCategories.HomotopyLimits
