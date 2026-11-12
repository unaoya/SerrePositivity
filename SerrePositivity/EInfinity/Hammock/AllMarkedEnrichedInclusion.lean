module

public import SerrePositivity.EInfinity.Hammock.AllMarkedUnitPoints

/-!
# 元の指定 hammock の包含の豊穣合成と単位

概要：元の包含は全 Hom の単体写像として元の合成と単位を保存する。
方針：既存の任意の点での保存を全次数で評価する。
規約：元の指定部分圏と同じ元の包含を使う。
使われ方：元の自由圏の hammock からの豊穣関手の制限。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AllMarked
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

lemma inclusion_unit (X : Paths C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩ ≫ inclusion W X X =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W.paths X := by
  ext n p
  exact inclusion_unitPoint W X n

lemma inclusion_composition (X Y Z : Paths C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ≫
      inclusion W X Z =
        (inclusion W X Y ⊗ₘ inclusion W Y Z) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W.paths X Y Z := by
  ext n p
  exact inclusion_composePoint W X Y Z p.1 p.2

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AllMarked
