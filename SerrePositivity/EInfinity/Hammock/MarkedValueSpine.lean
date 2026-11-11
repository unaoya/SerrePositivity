module

public import SerrePositivity.EInfinity.Hammock.AllMarkedEvaluationWeak
public import SerrePositivity.EInfinity.Hammock.MarkedSpineProducts

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
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)

abbrev valueHomType (X Y : Paths C) : Type u :=
  (AllMarked.nativeFreeEvaluation W).obj ⟨X⟩ ⟶ (AllMarked.nativeFreeEvaluation W).obj ⟨Y⟩

def valueHom (X Y : Paths C) : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (valueHomType W X Y)

variable (Y : Paths C)

inductive ValueSpine : Paths C → Type u
  | nil (X : Paths C) (p : valueHomType W X Y) : ValueSpine X
  | cons (X : Paths C) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) (p : valueHomType W X g.val.left)
      (tail : ValueSpine g.val.right) : ValueSpine X

def valueSpace (Y X : Paths C) : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (ValueSpine W Y X)

variable {W Y} {n m : SimplexCategoryᵒᵖ}

def evaluatePoint {X : Paths C} : MarkedSpine W Y n X → ValueSpine W Y X
  | .nil X p => .nil X ((AllMarked.nativeValue W X Y).app n p)
  | .cons X g p t => .cons X g ((AllMarked.nativeValue W X g.val.left).app n p) (evaluatePoint t)

lemma evaluatePoint_simplex (θ : n ⟶ m) {X : Paths C} (t : MarkedSpine W Y n X) :
    evaluatePoint (map θ t) = evaluatePoint t := by
  induction t with
  | nil X p =>
    exact congrArg (ValueSpine.nil X)
      (congrArg (fun k => k p) ((AllMarked.nativeValue W X Y).naturality θ))
  | cons X g p t ih =>
    change ValueSpine.cons X g
      ((AllMarked.nativeValue W X g.val.left).app m ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).map θ p))
      (evaluatePoint (map θ t)) = _
    rw [ih]
    exact congrArg (fun q => ValueSpine.cons X g q (evaluatePoint t))
      (congrArg (fun k => k p) ((AllMarked.nativeValue W X g.val.left).naturality θ))

variable (W Y)

def evaluation (X : Paths C) : space W Y X ⟶ valueSpace W Y X where
  app _ := ↾fun t => evaluatePoint t
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    exact evaluatePoint_simplex θ

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
