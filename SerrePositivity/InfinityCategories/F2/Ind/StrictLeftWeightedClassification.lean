module

public import SerrePositivity.InfinityCategories.F2.Ind.SectionProductCurry
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition

/-!
概要：任意の通常の left fibration 図式の実際の分類像を、同じ共同 weighted 分類と比較する。
方針：全単体上の切断の同じ大域実現を介し、初頂点局所化の充満忠実性で降下する。
規約：全添字と全高次で一つの関手同型。各値の同型による代用をしない。
使われ方：元の coherent 前層図式の strict 化と、同じ余極限余錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {B : SSet.{u}} (F : I ⥤ LeftFibrationObject B)

/-- 元の共同 weighted 分類と実際の strict 分類像は、全添字上で関手同型。 -/
def strictLeftWeightedClassificationIso :
    FunctorIso (strictLeftWeightedClassification F)
      (HomotopyLimits.strictCoherentDiagram F ≫ leftStraighteningInfinityMap B) := by
  have h := strictLeftWeightedClassificationSectionIso F ≪≫
    (strictLeftClassificationSectionIso F).symm
  exact (localization_pre_isFullyFaithful
    (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} B)
    SpaceInfinity.{u}).preimageFunctorIso h

end SerrePositivity.InfinityCategories.F2.Ind
