module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLiftZigzag

/-!
# Hom の ULift と元の hammock 余極限・縮約の厳密な同型

概要：同じ元の全語の graph 同型を実際の余極限と縮約へ移す。
方針：元の全標準射と正規化の可換式を保持する。
規約：元の代数・元の弱同値・元の全縦射を変更しない。
使われ方：cofibrant 入力と元の全代数の hammock の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLift
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable {C : Type (u + 1)} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C)
def colimitIso : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLift.liftedWeak W) (ULiftHom.objUp.{u + 1, u + 1} X) (ULiftHom.objUp.{u +
  1, u + 1} Y) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y := HasColimit.isoOfNatIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLift.graphDiagramIso W X Y)
def reducedIso : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLift.liftedWeak W) (ULiftHom.objUp.{u + 1, u + 1} X)
  (ULiftHom.objUp.{u + 1, u + 1} Y) ≅
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet W X Y :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLift.liftedWeak W) _ _).symm ≪≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLift.colimitIso W X Y ≪≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso W X Y
lemma colimitIso_graphInclusion (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLift.liftedWeak W) (ULiftHom.objUp.{u + 1, u + 1} X) (ULiftHom.objUp.{u + 1, u + 1}
      Y) w ≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLift.colimitIso W X Y).hom = (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLift.graphIso W w X Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w :=
  HasColimit.ι_isoOfNatIso_hom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLift.graphDiagramIso W X Y) w
lemma reducedIso_graphNormalization (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLift.liftedWeak W) (ULiftHom.objUp.{u + 1, u + 1} X) (ULiftHom.objUp.{u + 1, u +
      1} Y) w ≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLift.reducedIso W X Y).hom = (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLift.graphIso W w X Y).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization W X Y w := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso_hom_fac (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLift.liftedWeak W)]
  simp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLift.reducedIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLift.colimitIso_graphInclusion, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso_hom_fac]
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomLift
