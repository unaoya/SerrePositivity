module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionHomExtraNaturality
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ExtraDegeneracyContraction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection

/-!
# 元の自由解消 Hom augmentation の収縮

概要：元の圏の Hom へ向かう自由解消 augmentation は弱ホモトピー同値。
方針：一文字の追加退化の全恒等式から実際の区間収縮を構成する。
規約：単体集合のモデル構造と標的の Kan 性は仮定しない。
使われ方：DK ホモトピー補題2.4の底の Hom の入力。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.Opposite
open scoped _root_.Simplicial

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)

def freeResolutionGeneratorHomAugmented : SimplicialObject.Augmented (Type u) :=
  { left := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorHom C X Y
    right := X ⟶ Y
    hom := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorHomAugmentation C X Y }

def freeResolutionGeneratorHomExtraDegeneracy :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorHomAugmented C X Y).ExtraDegeneracy where
  s' := ↾(_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.generatorHomSection C)
  s n := ↾(_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.generatorHomExtra C n)
  s'_comp_ε := by
    apply ConcreteCategory.hom_ext
    intro f
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.generatorHomSection_augmentation C f
  s₀_comp_δ₁ := by
    apply ConcreteCategory.hom_ext
    intro f
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.generatorHomExtra_face_one C f
  s_comp_δ₀ n := by
    apply ConcreteCategory.hom_ext
    intro f
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.generatorHomExtra_face_zero C n f
  s_comp_δ n i := by
    apply ConcreteCategory.hom_ext
    intro f
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.generatorHomExtra_face_succ C n i f
  s_comp_σ n i := by
    apply ConcreteCategory.hom_ext
    intro f
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.generatorHomExtra_degeneracy_succ C n i f

lemma freeResolutionGeneratorHomAugmentation_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorHomAugmentation C X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (SerrePositivity.SimplicialModel.ExtraDegeneracyContraction.localized_augmentation_isIso
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorHomExtraDegeneracy C X Y))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
