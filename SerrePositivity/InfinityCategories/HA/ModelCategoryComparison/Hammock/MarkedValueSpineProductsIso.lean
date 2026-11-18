module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedValueSpine

/-!
# 指定因子の値の列と元の生成列ごとの直積の和の同型

概要：元の各指定値を同じ有限直積へ集め、全生成列で和を取る。
方針：元の nil/cons 表示で再帰し、全作用素で値が一定であることを使う。
規約：元の全指定値と全生成矢を保持する。
使われ方：全因子列の元の評価の弱比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} {Y : Paths C}
  {n m : SimplexCategoryᵒᵖ}

def packValue {X : Paths C} : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.ValueSpine W Y X →
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.sumProducts W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueHom W) Y X).obj n
  | .nil _ p => ⟨[], p⟩
  | .cons _ g p t => let s := packValue t; ⟨g :: s.1, (p, s.2)⟩

def unpackValue (X : Paths C) : ∀ gs : List (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W),
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.products W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueHom W) Y X gs).obj n → _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.ValueSpine W Y X
  | [], p => .nil X p
  | g :: gs, p => .cons X g p.1 (unpackValue g.val.right gs p.2)

lemma unpackValue_packValue {X : Paths C} (t : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.ValueSpine W Y X) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.unpackValue X (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.packValue (n := n) t).1 (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.packValue t).2 = t := by
  induction t with
  | nil => rfl
  | cons X g p t ih => exact congrArg (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.ValueSpine.cons X g p) ih

lemma packValue_unpackValue (X : Paths C) (gs : List (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W))
    (p : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.products W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueHom W) Y X gs).obj n) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.packValue (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.unpackValue X gs p) = ⟨gs, p⟩ := by
  induction gs generalizing X with
  | nil => rfl
  | cons g gs ih =>
    change (let s := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.packValue (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.unpackValue g.val.right gs p.2);
      (⟨g :: s.1, (p.1, s.2)⟩ : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.sumProducts W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueHom W) Y X).obj n)) = _
    rw [ih]
    cases p
    rfl

lemma unpackValue_simplex (θ : n ⟶ m) (X : Paths C) (gs : List (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W))
    (p : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.products W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueHom W) Y X gs).obj n) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.unpackValue X gs ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.products W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueHom W) Y X gs).map θ p) = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.unpackValue X gs p := by
  induction gs generalizing X with
  | nil => rfl
  | cons g gs ih => exact congrArg (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.ValueSpine.cons X g p.1) (ih g.val.right p.2)

variable (W Y)

def valueProductsIso (X : Paths C) : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.sumProducts W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueHom W) Y X ≅ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueSpace W Y X :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun s := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.unpackValue X s.1 s.2
      invFun := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.packValue
      left_inv s := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.packValue_unpackValue X s.1 s.2
      right_inv := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.unpackValue_packValue }) (fun θ => by
    apply ConcreteCategory.hom_ext
    intro s
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.unpackValue_simplex θ X s.1 s.2)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
