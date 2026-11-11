module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramMixedHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity

/-!
概要：strict な quasicategory 値図式の底と全変換の core を同時に評価する。
方針：元の混合評価に core 関手を適用し、各値を QCat の対象として使う。
規約：全変換空間の充填性は要求しない。
使われ方：quasicategory 値の比較の二点図式を Cat∞ 値の族へ実現する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 元の図式の値を、同じ quasicategory の QCat の対象として読む。 -/
def quasicategoryDiagramValue {C : Type u} [Category.{u} C]
    (F : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory C) (c : C) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} := F.val.obj c

/-- 底の射と元の全変換空間の core の同じ混合作用。 -/
def quasicategoryDiagramMixedHom {C : Type u} [Category.{u} C] {c d : C}
    (f : c ⟶ d) (F G : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory C) :
    SimplicialCategory.sHom F G ⟶ SimplicialCategory.sHom
      (quasicategoryDiagramValue F c) (quasicategoryDiagramValue G d) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom f
    (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget))

/-- 同じ混合作用は元の豊穣単位を保つ。 -/
lemma quasicategoryDiagramMixedHom_id {C : Type u} [Category.{u} C]
    (F : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory C) (c : C) :
    eId SSet F ≫ quasicategoryDiagramMixedHom (𝟙 c) F F =
      eId SSet (quasicategoryDiagramValue F c) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  exact congrArg (fun k ↦ k.app n s)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom_id (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget) c)

/-- 同じ混合作用は元の豊穣合成を保つ。 -/
lemma quasicategoryDiagramMixedHom_comp {C : Type u} [Category.{u} C] {c d e : C}
    (f : c ⟶ d) (g : d ⟶ e) (F G H : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory C) :
    eComp SSet F G H ≫ quasicategoryDiagramMixedHom (f ≫ g) F H =
      (quasicategoryDiagramMixedHom f F G ⊗ₘ quasicategoryDiagramMixedHom g G H) ≫
        eComp SSet (quasicategoryDiagramValue F c) (quasicategoryDiagramValue G d)
          (quasicategoryDiagramValue H e) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨h, k⟩
  apply Subtype.ext
  exact congrArg (fun m ↦ m.app n (h.val, k.val))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom_comp f g (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget)
      (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget) (H.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget))

/-- 元の全変換空間の core の豊穣構造の coherent nerve。充填性は主張しない。 -/
def QuasicategoryDiagramNerve (C : Type u) [Category.{u} C] : SSet.{u + 1} :=
  SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory C)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
