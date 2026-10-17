module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorMaps
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # 右相対K-flat因子に関する導来合成関手の関手性

## 概要
右相対K-flat因子に関する導来合成関手の関手性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/KFlatBimoduleLocalization.lean、Derived/
RightKFlatComposition.lean。固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 元の全dg自然な閉零bimodule圏の右相対K-flat対象の充満部分圏。 -/
abbrev RightKFlatBimoduleCategory := ObjectProperty.FullSubcategory
  (fun Q : BimoduleCategory A C E =>
    Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))

/-- 前の変数は局所化済み、後の変数は右相対K-flatな実際のbimoduleとしての関手性。 -/
def derivedComposeWithFunctor : RightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) where
  obj Q := derivedComposeWith A B C E Q.obj Q.property
  map {Q Q'} g := derivedComposeWithMap A B C E Q.property Q'.property g.hom
  map_id Q := derivedComposeWithMap_id A B C E Q.obj Q.property
  map_comp {Q Q' Q''} g h :=
    derivedComposeWithMap_comp A B C E Q.property Q'.property Q''.property g.hom h.hom

end SerrePositivity.DifferentialGraded.BimoduleTensor
