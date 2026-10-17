module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanActualHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyBinarySquare

/-!
# 二変数ホモトピーの固定端

## 概要
一方のホモトピーを終端で固定した二変数ホモトピーを作る。
任意モデル源の厳密化から独立して利用できる一般道具である。

## 方針（定義・証明）
反射的ホモトピーと同時評価の一般構成を組み合わせる。
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
universe v
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace SerrePositivity.SimplicialModel.BinaryIntervalTriangles
variable {T A B K : SSet.{v}} {f₀ f₁ : T ⟶ A} {g₀ g₁ : T ⟶ B}
  (F : SSet.Homotopy f₀ f₁) (G : SSet.Homotopy g₀ g₁) (k : A ⊗ B ⟶ K)
/-- 第一変数を終端で固定した二変数ホモトピーを作る。
指定した二変数写像を、反射的ホモトピーと第二変数のホモトピーで同時評価する。 -/
abbrev firstFixed := HomotopyBinarySquare.simultaneous (KanActualHomotopy.refl f₁) G k
abbrev secondFixed := HomotopyBinarySquare.simultaneous F (KanActualHomotopy.refl g₁) k


end SerrePositivity.SimplicialModel.BinaryIntervalTriangles
