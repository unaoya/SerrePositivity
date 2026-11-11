module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagRowHomotopy

/-!
# 全語の余極限上の一定行とホモトピー

概要：元の行と縦射を余極限の実際の標準射で送る。
方針：語の作用と一定行の整合を使い、元の余錐条件を適用する。
規約：単体集合のモデル構造や Kan 性を要求しない。
使われ方：指定射の往復のホモトピーを単位と比較する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {w a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

def colimitRowMap (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) : 𝟙_ SSet.{max u v} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagRowHomotopy.rowMap S ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w

lemma rowMap_wordAction (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagRowHomotopy.rowMap S ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagRowHomotopy.rowMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply CategoryTheory.Functor.ext (fun _ => rfl)

lemma colimitRowMap_wordAction (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) :
    colimitRowMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) = colimitRowMap S := by
  unfold colimitRowMap
  rw [← rowMap_wordAction, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality]

lemma colimitRowMap_empty (X : C) :
    colimitRowMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W X := rfl

def colimitRowHomotopy {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y} (f : S ⟶ T) :
    SSet.Homotopy (colimitRowMap S) (colimitRowMap T) where
  h := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagRowHomotopy.rowHomotopy f).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w
  h₀ := by rw [← Category.assoc, SSet.Homotopy.h₀]; rfl
  h₁ := by rw [← Category.assoc, SSet.Homotopy.h₁]; rfl
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
