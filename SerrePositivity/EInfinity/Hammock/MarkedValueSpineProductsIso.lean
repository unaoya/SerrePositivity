module

public import SerrePositivity.EInfinity.Hammock.MarkedValueSpine

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
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} {Y : Paths C}
  {n m : SimplexCategoryᵒᵖ}

def packValue {X : Paths C} : ValueSpine W Y X →
    (sumProducts W (valueHom W) Y X).obj n
  | .nil _ p => ⟨[], p⟩
  | .cons _ g p t => let s := packValue t; ⟨g :: s.1, (p, s.2)⟩

def unpackValue (X : Paths C) : ∀ gs : List (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W),
    (products W (valueHom W) Y X gs).obj n → ValueSpine W Y X
  | [], p => .nil X p
  | g :: gs, p => .cons X g p.1 (unpackValue g.val.right gs p.2)

lemma unpackValue_packValue {X : Paths C} (t : ValueSpine W Y X) :
    unpackValue X (packValue (n := n) t).1 (packValue t).2 = t := by
  induction t with
  | nil => rfl
  | cons X g p t ih => exact congrArg (ValueSpine.cons X g p) ih

lemma packValue_unpackValue (X : Paths C) (gs : List (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W))
    (p : (products W (valueHom W) Y X gs).obj n) :
    packValue (unpackValue X gs p) = ⟨gs, p⟩ := by
  induction gs generalizing X with
  | nil => rfl
  | cons g gs ih =>
    change (let s := packValue (unpackValue g.val.right gs p.2);
      (⟨g :: s.1, (p.1, s.2)⟩ : (sumProducts W (valueHom W) Y X).obj n)) = _
    rw [ih]
    cases p
    rfl

lemma unpackValue_simplex (θ : n ⟶ m) (X : Paths C) (gs : List (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W))
    (p : (products W (valueHom W) Y X gs).obj n) :
    unpackValue X gs ((products W (valueHom W) Y X gs).map θ p) = unpackValue X gs p := by
  induction gs generalizing X with
  | nil => rfl
  | cons g gs ih => exact congrArg (ValueSpine.cons X g p.1) (ih g.val.right p.2)

variable (W Y)

def valueProductsIso (X : Paths C) : sumProducts W (valueHom W) Y X ≅ valueSpace W Y X :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun s := unpackValue X s.1 s.2
      invFun := packValue
      left_inv s := packValue_unpackValue X s.1 s.2
      right_inv := unpackValue_packValue }) (fun θ => by
    apply ConcreteCategory.hom_ext
    intro s
    exact unpackValue_simplex θ X s.1 s.2)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
