module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 図式とパラメータの直積

## 概要
単体的集合の図式の各値にパラメータをテンソルし両方向の自然変換を作る。
任意モデル源の厳密化から独立して利用できる一般道具である。

## 方針（定義・証明）
関手のwhiskeringで水平・垂直写像を定義し、交換則を各成分で確認する。
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
universe w uD vD
open CategoryTheory CategoryTheory.MonoidalCategory
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
variable {D : Type uD} [Category.{vD} D]
  (V K : D ⥤ SSet.{w}) (i : V ⟶ K) {A T : SSet.{w}} (j : A ⟶ T)
/-- 図式の各値に一つの単体的パラメータをテンソルする。
任意の添字圏で、右テンソル関手を図式へ後合成する。 -/
def product (K : D ⥤ SSet.{w}) (T : SSet.{w}) : D ⥤ SSet.{w} :=
  K ⋙ (tensoringRight SSet.{w}).obj T

def horizontal (T : SSet.{w}) : product V T ⟶ product K T :=
  Functor.whiskerRight i ((tensoringRight SSet.{w}).obj T)

def vertical (K : D ⥤ SSet.{w}) : product K A ⟶ product K T :=
  Functor.whiskerLeft K ((tensoringRight SSet.{w}).map j)

lemma commute : horizontal V K i A ≫ vertical j K =
    vertical j V ≫ horizontal V K i T := by
  ext d : 2
  exact whisker_exchange (i.app d) j


end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
