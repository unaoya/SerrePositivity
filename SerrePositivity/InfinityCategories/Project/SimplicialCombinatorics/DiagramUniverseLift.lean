module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 図式の宇宙lift

## 概要
図式にULift関手を後合成して大きい宇宙の図式を作る。
任意モデル源の厳密化から独立して利用できる一般道具である。

## 方針（定義・証明）
値と射を同じULift関手で移送し、関手の合成として構成する。
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
universe w v uD vD
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveLargeParameter
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})
/-- 単体的集合の図式をULiftで大きい宇宙へ移す。
対象・射の両方を同じULift関手により移し、図式への後合成で定義する。 -/
abbrev lifted : D ⥤ SSet.{max w v} := F ⋙ SSet.uliftFunctor.{w, v}

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveLargeParameter

namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})
abbrev lifted := NerveLargeParameter.lifted.{w} F
end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter
