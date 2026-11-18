module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LengthBoundary

/-!
# 元の短い語の包含の境界への持ち上げ

概要：短い語の包含は境界を経由し、元の包含と前段階の標準射を回収する。
方針：像の和の一つの項への包含と Subfunctor.lift を使う。
規約：持ち上げた同じ射の後の等式を証明する。
使われ方：境界の整合条件による余錐の構成。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory

variable (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}) (n : ℕ) {a c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (ha : a.length ≤ n)
  (f : a ⟶ c) (hf : Function.Injective f.orderHom)

def lengthBoundaryLift : F.obj a ⟶ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary F n c).toFunctor :=
  Subfunctor.lift (F.map f) (le_iSup_of_le a (le_iSup_of_le ha
    (le_iSup_of_le f (le_iSup_of_le hf le_rfl))))

lemma lengthBoundaryLift_ι : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryLift F n ha f hf ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary F n c).ι =
    F.map f := Subfunctor.lift_ι _ _

lemma lengthBoundaryLift_toStage (hF : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram F) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryLift F n ha f hf ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryToStage hF n c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n a ha := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro σ
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryStageValue_eq hF n c k _ ha f hf σ rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
