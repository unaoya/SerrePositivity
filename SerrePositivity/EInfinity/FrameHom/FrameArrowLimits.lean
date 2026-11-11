module

public import SerrePositivity.EInfinity.FrameHom.FrameArrowCofinality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalLimitTransfer

/-!
# 元の frame の全矢の図式の極限を次数圏へ制限する

概要：全矢の終域図式の極限と元の frame 上の図式の極限を同値にする。
方針：元の恒等矢の包含の left cofinal 性と厳密な射影の式を使う。
規約：標的は任意の quasicategory。全極限の存在は要求しない。
使われ方：source frame による右 Kan 局所極限の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory SerrePositivity.InfinityCategories
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C)
  {E : SSet.{u}} [SSet.Quasicategory E] (F : nerve C ⟶ E)

lemma identityInclusion_nerve_target :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.identityInclusion A) ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.target A) = nerveMap A := rfl

lemma target_hasLimit_iff : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.target A) ≫ F) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (nerveMap A ≫ F) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.hasLimit_iff_restrict_of_leftCofinal (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.identityInclusion A))
    (identityInclusion_nerve_isLeftCofinal A) (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.target A) ≫ F)
  simpa only [← Category.assoc, identityInclusion_nerve_target] using h

end SerrePositivity.EInfinity.FrameHom.FrameArrows
