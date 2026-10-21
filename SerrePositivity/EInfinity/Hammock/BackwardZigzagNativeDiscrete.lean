module

public import SerrePositivity.EInfinity.Hammock.BackwardZigzagDiscrete
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# 元の backward 一列と指定部分圏の Hom

概要：元の一列の値を同じ端点の Hom へ回収する。
方針：全縦射と端点移送を保持する。
規約：モデル構造を要求しない。
使われ方：元の指定 Hom の弱比較への接続。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.Hammock.BackwardZigzag
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} [W.IsMultiplicative] {X Y : C}
def markedHomEquiv : {f : Y ⟶ X // W f} ≃ ((⟨Y⟩ : WideSubcategory W) ⟶ ⟨X⟩) where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f.hom, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def nativeDiscreteEquivalence : Zigzag W (Word.single .backward) X Y ≌
    Discrete ((⟨Y⟩ : WideSubcategory W) ⟶ ⟨X⟩) :=
  discreteEquivalence.trans (Discrete.equivalence markedHomEquiv)
end SerrePositivity.EInfinity.Hammock.BackwardZigzag
