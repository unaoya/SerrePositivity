module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineEnrichedFoldMap

/-!
# 元の指定 hammock から全因子列への包含の合成と単位

概要：指定終端だけを持つ元の因子列への包含は指定部分圏の豊穣合成を保つ。
方針：元の同じ単位点と指定二因子の明示的な合成を回収する。
規約：指定因子の元の全語の余極限を保持する。
使われ方：豊穣関手の二つの生成部分への制限。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)

lemma marked_unitMap (X : Paths C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩ ≫ nilMap W X X =
      unitMap W X := by
  ext n p
  rfl

lemma marked_composition (X Y Z : Paths C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ≫
      nilMap W Z X = (nilMap W Y X ⊗ₘ nilMap W Z Y) ≫ composition W X Y Z := by
  ext n p
  rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
