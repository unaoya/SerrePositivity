module

public import SerrePositivity.Archive.KST.DescentConditional.FiniteFamilyCechFunctor
public import SerrePositivity.KST.Descent.FiniteZariskiCover

/-!
# 有限被覆族の実際の指定比較による Zariski 降下の法則

## 概要
有限被覆族の各引き戻しの値の積を使い、公理 (1) の実際の指定 Čech 降下の法則を型にする。

## 方針
元の有限型の圏内の有限開被覆に構成済みの全自然な増強つき図式を適用する。

## 規約
空の被覆も含む。非交和保存を別に前提とせず、被覆族そのものの積の図式で述べる。
法則の型と、その E による実現の証明を区別する。

## 使われ方
論文 公理 (1)、補題 3.2・3.3。原典の τ 位相の層論を Čech 計算で置換する入口。
-/

@[expose] public section

universe u

open CategoryTheory HomotopicalAlgebra AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]

/-- 概要：元の空間値前層の有限 Zariski 被覆族での実際の指定 Čech 降下（公理 (1)）。
方針：各添字の列の実際の引き戻しの値を積にした指定比較の弱同値を要求する。
規約：これは L に要求する法則の型。空被覆も含み、有限非交和の保存は仮定に足さない。
使われ方：有限自由 chart の局所計算と、E の Zariski 降下の実現の接続。 -/
class FiniteZariskiCechDescent (F : (FiniteTypeSchemes S)ᵒᵖ ⥤ SSet.{0}) : Prop where
  /-- 概要：有限開被覆族の指定比較は実際に弱同値（公理 (1)）。
  方針：元の被覆族の全ての引き戻しと値域の有限積を用いる。
  規約：特定の被覆に限定しない。使われ方：空被覆・非交和被覆・有限自由 chart。 -/
  descent : ∀ {Y : FiniteTypeSchemes S} (c : FiniteTypeZariskiCover Y),
    HasCechSpaceDescent SimplexCategory I J (familyCechSpace c.obj c.inclusion F)

end SerrePositivity.KST.Descent
