module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplexCategory.Rev

/-!
# 反転した単体退化の恒等式

## 概要
標準単体の反転した退化写像と退化同士の恒等式を構成する。
任意モデル源の厳密化から独立して利用できる一般道具である。

## 方針（定義・証明）
通常の単体恒等式に反転関手と標準単体関手を適用する。
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
universe r
open CategoryTheory CategoryTheory.MonoidalCategory
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
/- 旧技術注記： Parameter degeneracy with the reversed indexing of the source resolution. -/
/-- 標準単体の退化の添字を反転したパラメータ写像を作る。
通常の退化写像に標準単体関手を適用し、モデル構造は使わない。 -/
def sigma (n : ℕ) (i : Fin (n + 1)) :
    SSet.stdSimplex.{r}.obj (SimplexCategory.mk (n + 1)) ⟶
      SSet.stdSimplex.obj (SimplexCategory.mk n) :=
  SSet.stdSimplex.map (SimplexCategory.σ i.rev)

lemma sigma_sigma (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    sigma (n + 1) i.castSucc ≫ sigma n j = sigma (n + 1) j.succ ≫ sigma n i := by
  have hs := congrArg SimplexCategory.rev.map (SimplexCategory.σ_comp_σ h)
  simp only [CategoryTheory.Functor.map_comp, SimplexCategory.rev_map_σ] at hs
  exact (SSet.stdSimplex.map_comp _ _).symm.trans
    ((congrArg SSet.stdSimplex.map hs).trans (SSet.stdSimplex.map_comp _ _))

lemma tensor_sigma_sigma (P : SSet.{r}) (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    P ◁ sigma (n + 1) i.castSucc ≫ P ◁ sigma n j =
      P ◁ sigma (n + 1) j.succ ≫ P ◁ sigma n i := by
  rw [← whiskerLeft_comp, ← whiskerLeft_comp, sigma_sigma n i j h]


end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
