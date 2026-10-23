module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictLeftWeightedClassification
public import SerrePositivity.InfinityCategories.F2.Ind.LeftRightRoundTripDiagram
public import SerrePositivity.InfinityCategories.F2.Ind.UnderSectionClassification
public import SerrePositivity.InfinityCategories.F1.Fibrations.RightStraighteningInfinityEquivalence

/-!
概要：任意の coherent 前層図式を、元の strict right fibration 図式の実際の分類像へ移す。
方針：共同分類の全添字上の比較と、同じ底上の自然な二重反転比較を合成する。
規約：元の F そのものとの一つの関手同型。各対象の値の同値だけで代用しない。
使われ方：κ-filtered 余極限閉性を、同じ native 余錐上で strict な分類余極限へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ PresheafInfinity C)

/-- 同じ元の strict right 図式の実際の分類像は、元の coherent 図式 F と全高次で関手同型。 -/
def presheafDiagramRightStrictClassificationIso :
    FunctorIso
      (HomotopyLimits.strictCoherentDiagram (presheafDiagramRightStrict F) ≫
        rightStraighteningInfinityMap C) F := by
  let D := underSectionStrictDiagram (presheafDiagramJointProjection F)
  have hr := (leftRightOppositeDiagramIso D).postcomp (leftStraighteningInfinityMap C.op)
  have hl := (strictLeftWeightedClassificationIso D).symm
  exact hr ≪≫ hl ≪≫ presheafDiagramWeightedClassificationIso F

end SerrePositivity.InfinityCategories.F2.Ind
