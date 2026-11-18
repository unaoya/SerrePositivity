module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AllMarkedEvaluationWeak
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedSpineProducts

/-!
# 指定因子を元の自由 groupoid の値にした因子列

概要：元の非指定生成矢と指定因子の値を同じ順序で保持する。
方針：元の有限因子列と同じ nil/cons の表示を用いる。
規約：同値類や正規形を未証明の仮定として入力しない。
使われ方：元の自由積の全 Hom と通常の局所化の比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)

abbrev valueHomType (X Y : Paths C) : Type u :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeFreeEvaluation W).obj ⟨X⟩ ⟶ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeFreeEvaluation W).obj ⟨Y⟩

def valueHom (X Y : Paths C) : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueHomType W X Y)

variable (Y : Paths C)

inductive ValueSpine : Paths C → Type u
  | nil (X : Paths C) (p : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueHomType W X Y) : ValueSpine X
  | cons (X : Paths C) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) (p : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueHomType W X g.val.left)
      (tail : ValueSpine g.val.right) : ValueSpine X

def valueSpace (Y X : Paths C) : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.ValueSpine W Y X)

variable {W Y} {n m : SimplexCategoryᵒᵖ}

def evaluatePoint {X : Paths C} : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine W Y n X → _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.ValueSpine W Y X
  | .nil X p => .nil X ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeValue W X Y).app n p)
  | .cons X g p t => .cons X g ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeValue W X g.val.left).app n p) (evaluatePoint t)

lemma evaluatePoint_simplex (θ : n ⟶ m) {X : Paths C} (t : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine W Y n X) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.evaluatePoint (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.map θ t) = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.evaluatePoint t := by
  induction t with
  | nil X p =>
    exact congrArg (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.ValueSpine.nil X)
      (congrArg (fun k => k p) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeValue W X Y).naturality θ))
  | cons X g p t ih =>
    change _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.ValueSpine.cons X g
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeValue W X g.val.left).app m ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).map θ p))
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.evaluatePoint (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.map θ t)) = _
    rw [ih]
    exact congrArg (fun q => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.ValueSpine.cons X g q (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.evaluatePoint t))
      (congrArg (fun k => k p) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeValue W X g.val.left).naturality θ))

variable (W Y)

def evaluation (X : Paths C) : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.space W Y X ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueSpace W Y X where
  app _ := ↾fun t => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.evaluatePoint t
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.evaluatePoint_simplex θ

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
