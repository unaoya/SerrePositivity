module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 区間と定数端点

## 概要
任意の単体的集合から標準区間の二つの端点への定数写像を作る。
任意モデル源の厳密化から独立して利用できる一般道具である。

## 方針（定義・証明）
零単体の終対象性から二つの面写像へ合成する。
既存の構成を同じ公開名と証明のまま一般層に切り出す。

## 規約と注意
宇宙と仮定は各宣言に明示したものを用いる。
専用の比較図式・正規化充填・選択の整合性は仮定しない。

## 使われ方
一般入口GeneralToolsおよび共有Foundationsから利用する。
旧パスの互換importを通して中断中の厳密化からも利用する。
今後のS-構成・ホモトピー比較・局所化の基礎として使える。
詳細はformalization-plans/archive/k-theory-generalization-inventory.mdの配置実施記録を参照。
-/

@[expose] public section
universe v
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
abbrev interval : SSet.{v} := SSet.stdSimplex.obj (SimplexCategory.mk 1)

/-- 任意の単体的集合から標準区間の零端点への定数写像を作る。
零単体の終対象性と端点の面写像を合成する。 -/
def zero (T : SSet.{v}) : T ⟶ interval :=
  SSet.stdSimplex.isTerminalObj₀.from T ≫ SSet.stdSimplex.δ (1 : Fin 2)

def one (T : SSet.{v}) : T ⟶ interval :=
  SSet.stdSimplex.isTerminalObj₀.from T ≫ SSet.stdSimplex.δ (0 : Fin 2)


end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
