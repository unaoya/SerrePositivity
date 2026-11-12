module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineExtraction
public import SerrePositivity.EInfinity.Hammock.UnmarkedFactorPaste

/-!
# 元の全因子を持つ有限切断列からの単体的貼り戻し

概要：終端は元の包含へ、cons は元の三因子の貼り戻しへ送り、単体写像にする。
方針：切断列で再帰し、元の包含・生成射・合成の自然性を使う。
規約：元の W-hammock の全点と同じ生成矢を保持する。
使われ方：反復抽出との両逆と自由積分解。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} {Y : Paths C}
  {n m : SimplexCategoryᵒᵖ}

def glue {X : Paths C} : MarkedSpine W Y n X → (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n
  | .nil X p => (AllMarked.inclusion W X Y).app n p
  | .cons X g p t => FactorTarget.pastePoint W X Y g p (glue t)

lemma glue_simplex (θ : n ⟶ m) {X : Paths C} (t : MarkedSpine W Y n X) :
    glue (map θ t) = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).map θ (glue t) := by
  induction t with
  | nil X p => exact congrArg (fun k => k p) ((AllMarked.inclusion W X Y).naturality θ)
  | cons X g p t ih =>
    change FactorTarget.pastePoint W X Y g ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).map θ p)
      (glue (map θ t)) = _
    exact (congrArg
      (FactorTarget.pastePoint W X Y g ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).map θ p)) ih).trans
      (FactorTarget.pastePoint_simplex W X Y θ g p (glue t))

variable (W Y)

def gluing (X : Paths C) : space W Y X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y where
  app _ := ↾fun t => glue t
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    exact glue_simplex θ

lemma gluing_nil (X : Paths C) (p : (AllMarked.nativeSpace W X Y).obj n) :
    (gluing W Y X).app n (nil X p) = (AllMarked.inclusion W X Y).app n p := rfl

lemma gluing_cons (X : Paths C) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).obj n)
    (t : MarkedSpine W Y n g.val.right) :
    (gluing W Y X).app n (cons X g p t) =
      FactorTarget.pastePoint W X Y g p ((gluing W Y g.val.right).app n t) := rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
