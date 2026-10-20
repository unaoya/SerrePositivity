module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionUniversalClass
public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentHomCylinder
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentTotalPrecomposition

/-!
概要：実際の付加辺による普遍前置と、元の余錐制限円柱の類を照合する。
方針：同じ正規化制限と同じ比較辺で一般の評価固定円柱を具体化する。
規約：元の付加辺と元の円柱を保持。使われ方：左右の枝の共通初期 Hom への比較。
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

/-- 元の付加辺の普遍前置の始点へ至る、同じ終点評価を保つ円柱。 -/
def colimitAttachmentUniversalCylinderData :
    InitialEvaluationCylinder (sliceUnderProjection p) c y
      (normalizedCoconeRestrictionFiber F i hi y) hc
      (leftFibrationInitialSection (sliceUnderProjection F) d hd y ≫
        colimitAttachmentTotalPrecomposition c hc i F hi d y) :=
  initialRestrictionUniversalCylinderData (sliceUnderProjection F) (sliceUnderProjection p)
    (normalizedCoconeRestriction F i hi) (normalizedCoconeRestriction_projection F i hi)
    d hd (colimitAttachmentRestrictionEdge c hc i F hi d) y hc

/-- 付加辺の普遍前置により、元の制限正方形と同じ端点を持つ Hom 円柱を構成する。 -/
def colimitAttachmentUniversalHomCylinder : SSet.Homotopy
    (normalizedCoconeRestrictionFiber F i hi y ≫ coconeMappingSpaceHomComparison c hc y)
    (coconeMappingSpaceHomComparison d hd y ≫
      colimitAttachmentHomPrecomposition c hc i F hi d y) :=
  initialRestrictionUniversalHomCylinder (sliceUnderProjection F) (sliceUnderProjection p)
    (normalizedCoconeRestriction F i hi) (normalizedCoconeRestriction_projection F i hi)
    d hd (colimitAttachmentRestrictionEdge c hc i F hi d) y hc

/-- 同じ評価固定円柱の射影を、全 Hom の族の raw な等式で保持する。 -/
lemma colimitAttachmentUniversalHomCylinder_projection :
    (colimitAttachmentUniversalHomCylinder c hc i F hi d hd y).h =
      (colimitAttachmentUniversalCylinderData c hc i F hi d hd y).homotopy.h ≫
        leftFibrationInitialProjection (sliceUnderProjection p) c y ≫
          (leftFibrationInitialBaseIso (sliceUnderProjection p) c y).hom :=
  initialRestrictionUniversalHomCylinder_projection _ _ _ _ _ _ _ _ _

/-- 普遍前置の円柱は、元の同じ付加辺の制限円柱の射の類を回収する。 -/
lemma colimitAttachmentUniversalHomCylinder_hom_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (colimitAttachmentUniversalHomCylinder c hc i F hi d hd y))) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (colimitAttachmentRestrictionHomCylinder c hc i F hi d hd y))) :=
  initialRestrictionUniversalHomCylinder_hom_arrow _ _ _ _ _ _ _ _ _

end
end SerrePositivity.InfinityCategories.HomotopyLimits
