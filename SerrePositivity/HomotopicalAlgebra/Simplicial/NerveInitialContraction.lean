module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# 始対象を持つ圏のnerveの収縮

## 概要
始対象を持つ圏のnerveをanodyne局所化後に零単体と同型にする。
任意モデル源の厳密化から独立して利用できる一般道具である。

## 方針（定義・証明）
始対象からの自然変換による実ホモトピーを局所化へ送る。
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
universe u v uH vH
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.NerveInitialImage
variable {C : Type u} [Category.{v} C] {a : C} (ha : IsInitial a)

def contraction : (Functor.const C).obj a ⟶ 𝟭 C where
  app c := ha.to c
  naturality {_ _} _ := ha.hom_ext _ _

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

/-- 始対象を持つ圏のnerveの局所化像は零単体の像と同型になる。
関手がanodyne射を反転することを仮定し、始対象から恒等関手への自然変換のホモトピーを使う。 -/
def terminalImageIso : L.obj (nerve C) ≅
    L.obj (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0)) where
  hom := L.map (SSet.stdSimplex.isTerminalObj₀.from (nerve C))
  inv := L.map (NerveHomotopy.point a)
  hom_inv_id := by
    rw [← L.map_comp, NerveHomotopy.constant_eq]
    have h := AnodyneHomotopy.map_homotopy_eq L hL
      (NerveHomotopy.homotopy (contraction ha))
    exact h.trans (L.map_id _)
  inv_hom_id := by
    rw [← L.map_comp]
    have h : NerveHomotopy.point a ≫ SSet.stdSimplex.isTerminalObj₀.from (nerve C) = 𝟙 _ :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h, L.map_id]

end SerrePositivity.SimplicialModel.NerveInitialImage
