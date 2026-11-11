module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineCompositionLaws

/-!
# 元の指定因子と非指定生成矢の像からの因子列の評価

概要：任意の圏で元の指定 hammock の合成を保つ像と非指定生成矢の像を評価する。
方針：元の因子列で再帰し、指定因子・生成矢・残りの順に合成する。
規約：入力は自由積の普遍性の像の指定であり、弱比較を仮定しない。
使われ方：元の自由積の一意な拡張の構成。
-/

@[expose] public section
universe u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C]

structure FoldData (W : MorphismProperty C) (n : SimplexCategoryᵒᵖ)
    (D : Type uD) [Category.{vD} D] where
  obj : Paths C → D
  marked : ∀ {X Y}, (AllMarked.nativeSpace W X Y).obj n → (obj X ⟶ obj Y)
  generator : ∀ g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W, obj g.val.left ⟶ obj g.val.right
  marked_unit : ∀ X, marked (AllMarked.nativeUnitPoint W X n) = 𝟙 (obj X)
  marked_comp : ∀ {X Y Z} (p : (AllMarked.nativeSpace W X Y).obj n)
    (q : (AllMarked.nativeSpace W Y Z).obj n),
    marked (AllMarked.nativeComposePoint W X Y Z p q) = marked p ≫ marked q

namespace FoldData
variable {W : MorphismProperty C} {n : SimplexCategoryᵒᵖ}
  {D : Type uD} [Category.{vD} D] (F : FoldData W n D)

def fold {X Y : Paths C} : MarkedSpine W Y n X → (F.obj X ⟶ F.obj Y)
  | .nil _ p => F.marked p
  | .cons _ g p t => F.marked p ≫ F.generator g ≫ fold t

lemma fold_nil {X Y : Paths C} (p : (AllMarked.nativeSpace W X Y).obj n) :
    F.fold (nil X p) = F.marked p := rfl

lemma fold_cons {X Y : Paths C} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W)
    (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).obj n) (t : MarkedSpine W Y n g.val.right) :
    F.fold (cons X g p t) = F.marked p ≫ F.generator g ≫ F.fold t := rfl

lemma fold_unit (X : Paths C) : F.fold (unitPoint W X n) = 𝟙 (F.obj X) := F.marked_unit X

end FoldData
end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
