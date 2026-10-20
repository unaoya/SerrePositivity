module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionTotalPrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentHomNaturality

/-!
概要：部分余極限で選んだ実際の付加比較辺を、初期 Hom 空間の上で前置する。
方針：正規化した制限の初期 Hom の像と、同じ辺の相対前置写像を合成する。
規約：底は既存の colimitAttachmentHomPrecomposition。使われ方：枝比較の共通始対象への像。
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
  (F : C ⟶ X) (hi : i ≫ F = p) (d : JoinCocone F) (y : X _⦋0⦌)

/-- 枝始点の初期 Hom 空間を、実際の付加比較辺で共通始対象の初期 Hom 空間へ写す。 -/
def colimitAttachmentTotalPrecomposition :
    leftFibrationInitialTotal (sliceUnderProjection F) d y ⟶
      leftFibrationInitialTotal (sliceUnderProjection p) c y :=
  initialRestrictionTotalPrecomposition (sliceUnderProjection F) (sliceUnderProjection p)
    (normalizedCoconeRestriction F i hi) (normalizedCoconeRestriction_projection F i hi)
    d (colimitAttachmentRestrictionEdge c hc i F hi d) y

/-- 前置写像の評価は、同じ元の余錐制限による終点の像である。 -/
lemma colimitAttachmentTotalPrecomposition_evaluation :
    colimitAttachmentTotalPrecomposition c hc i F hi d y ≫
        leftFibrationInitialEvaluation (sliceUnderProjection p) c y =
      leftFibrationInitialEvaluation (sliceUnderProjection F) d y ≫
        normalizedCoconeRestrictionFiber F i hi y :=
  initialRestrictionTotalPrecomposition_evaluation _ _ _ _ _ _ _

/-- 底の通常 Hom 表示は、既存の同じ実際の付加辺の Hom 前合成である。 -/
lemma colimitAttachmentTotalPrecomposition_pinched :
    colimitAttachmentTotalPrecomposition c hc i F hi d y ≫
        leftFibrationInitialProjection (sliceUnderProjection p) c y ≫
          (leftFibrationInitialBaseIso (sliceUnderProjection p) c y).hom =
      leftFibrationInitialProjection (sliceUnderProjection F) d y ≫
        (leftFibrationInitialBaseIso (sliceUnderProjection F) d y).hom ≫
          colimitAttachmentHomPrecomposition c hc i F hi d y :=
  initialRestrictionTotalPrecomposition_pinched _ _ _ _ _ _ _

end
end SerrePositivity.InfinityCategories.HomotopyLimits
