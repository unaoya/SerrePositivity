module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# 射の因子分解のデータ

## 概要
射の因子分解を中間対象と二つの因子および合成の等式で表す。
任意モデル源の厳密化から独立して利用できる一般道具である。

## 方針（定義・証明）
固定した射の両端を保つ構造体として定義する。
既存の構成を同じ公開名と証明のまま一般層に切り出す。

## 規約と注意
宇宙と仮定は各宣言に明示したものを用いる。
専用の比較図式・正規化充填・選択の整合性は仮定しない。

## 使われ方
一般入口GeneralToolsおよび共有Foundationsから利用する。
旧パスの互換importを通して中断中の厳密化からも利用する。
今後のS-構成・ホモトピー比較・局所化の基礎として使える。
詳細はformalization-plans/k-theory-generalization-inventory.mdの配置実施記録を参照。
-/

@[expose] public section
universe v u
open CategoryTheory
namespace SerrePositivity
/-- 固定した射の因子分解を、中間対象・左右の射・合成の等式で表す。
両端の対象と圏を固定し、facは左右の合成が元の射であることを保証する。 -/
structure ArrowFactorization {D : Type u} [Category.{v} D] {Y V : D} (g : Y ⟶ V) where
  middle : D
  left : Y ⟶ middle
  right : middle ⟶ V
  fac : left ≫ right = g


end SerrePositivity
