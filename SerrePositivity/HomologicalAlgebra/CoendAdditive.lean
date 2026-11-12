module

public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Limits.Shapes.End

/-!
# coend 関手の加法性

## 概要
加法圏の coend 関手は、元の自然変換の和を同じ coend の射の和へ送る。

## 方針
対角の標準包含で比較し、元の自然変換の各成分の加法性を用いる。

## 規約
必要な coend の存在を型に明記する。有限性や模型構造を仮定しない。

## 使われ方
Weibel §2.2、HA 1.2.4。線形重みの鎖ホモトピーを実際の係数図式の coend へ移す。
-/

@[expose] public noncomputable section
universe w t v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
namespace SerrePositivity.HomologicalAlgebra

/-- 元の対角包含を持つ coend 関手は加法的。 -/
instance coendFunctor_additive {J : Type t} [Category.{w} J]
    {C : Type u} [Category.{v} C] [Preadditive C]
    [∀ F : Jᵒᵖ ⥤ J ⥤ C, HasCoend F] : (coendFunctor J C).Additive where
  map_add {F G} α β := by
    apply coend.hom_ext
    intro j
    change coend.ι F j ≫ coend.map (α + β) =
      coend.ι F j ≫ (coend.map α + coend.map β)
    simp only [comp_add, coend.ι_map, NatTrans.app_add, add_comp]

end SerrePositivity.HomologicalAlgebra
