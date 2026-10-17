module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# 単体圏の射列からの頂点写像

## 概要
単体圏の反対圏の射列から順序を保つ標準パラメータを作る。
任意モデル源の厳密化から独立して利用できる一般道具である。

## 方針（定義・証明）
各頂点の像を先頭への射で評価し、射列の合成則から単調性と自然性を示す。
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
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplexChainParameter
variable {n : ℕ} (c : Fin (n + 1) ⥤ SimplexCategoryᵒᵖ)

lemma prefix_comp {i j : Fin (n + 1)} (h : i ≤ j) :
    c.map (homOfLE (Fin.zero_le j)) =
      c.map (homOfLE (Fin.zero_le i)) ≫ c.map (homOfLE h) :=
  c.map_comp _ _

abbrev vertex (i : Fin (n + 1)) : Fin ((c.obj 0).unop.len + 1) :=
  (c.map (homOfLE (Fin.zero_le i))).unop.toOrderHom 0

lemma monotone : Monotone (vertex c) := by
  intro i j h
  have e := congrArg (fun f => f.unop.toOrderHom 0) (prefix_comp c h)
  change vertex c j = (c.map (homOfLE (Fin.zero_le i))).unop.toOrderHom
    ((c.map (homOfLE h)).unop.toOrderHom 0) at e
  rw [e]
  exact (c.map (homOfLE (Fin.zero_le i))).unop.toOrderHom.monotone (Fin.zero_le _)

/-- 単体圏の反対圏の射列から標準単体のパラメータ写像を作る。
先頭への射で各零頂点を評価し、その合成則から単調性を得る。 -/
def parameter : SimplexCategory.mk n ⟶ (c.obj 0).unop :=
  SimplexCategory.Hom.mk ⟨vertex c, monotone c⟩

lemma parameter_apply (i : Fin (n + 1)) :
    (parameter c).toOrderHom i = vertex c i := rfl

lemma parameter_zero : (parameter c).toOrderHom 0 = 0 := by
  change (c.map (𝟙 0)).unop.toOrderHom 0 = 0
  rw [c.map_id]
  rfl

lemma reindex {m : ℕ} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    θ ≫ parameter c =
      parameter ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
        (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))).unop := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  exact congrArg (fun f => f.unop.toOrderHom 0)
    (prefix_comp c (θ.toOrderHom.monotone (Fin.zero_le i)))

end SerrePositivity.SimplexChainParameter
