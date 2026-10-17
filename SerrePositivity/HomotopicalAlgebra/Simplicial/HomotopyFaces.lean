module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterHomotopy

/-!
# 実ホモトピーの端点と境界

## 概要
区間ホモトピーの二つの端点を標準単体の面と境界写像で表す。
任意モデル源の厳密化から独立して利用できる一般道具である。

## 方針（定義・証明）
端点の定数写像表示と境界の余極限の普遍性を使う。
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
universe r
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
namespace SerrePositivity.SimplicialModel.HomotopyEndpointComparison
/-- 実ホモトピーを標準区間の始点の面に制限すると始点の写像となる。
Kan性を要求せず、標準単体の面の定数表示とホモトピーの端点等式を使う。 -/
lemma face_zero {K Q : SSet.{r}} {e₀ e₁ : K ⟶ Q} (H : SSet.Homotopy e₀ e₁) :
    K ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ H.h = fst K _ ≫ e₀ := by
  have h : K ◁ SSet.stdSimplex.δ (1 : Fin 2) = fst K _ ≫ SSet.ι₀ := by
    rw [SSet.stdSimplex.δ_one_eq_const]
    rfl
  rw [h, Category.assoc, H.h₀]

lemma face_one {K Q : SSet.{r}} {e₀ e₁ : K ⟶ Q} (H : SSet.Homotopy e₀ e₁) :
    K ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ H.h = fst K _ ≫ e₁ := by
  have h : K ◁ SSet.stdSimplex.δ (0 : Fin 2) = fst K _ ≫ SSet.ι₁ := by
    rw [SSet.stdSimplex.δ_zero_eq_const]
    rfl
  rw [h, Category.assoc, H.h₁]

lemma boundary_eq {K Q : SSet.{r}} {e₀ e₁ : K ⟶ Q} (H : SSet.Homotopy e₀ e₁) :
    K ◁ (SSet.boundary.{r} 1).ι ≫ H.h = LargeParameterHomotopy.boundaryMap e₀ e₁ := by
  apply (LargeParameterHomotopy.boundaryColimit K).hom_ext
  rintro ⟨i⟩
  cases i with
  | left =>
    change (K ◁ SSet.boundary.ι (1 : Fin 2)) ≫ _ =
      (K ◁ SSet.boundary.ι (1 : Fin 2)) ≫ LargeParameterHomotopy.boundaryMap e₀ e₁
    rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      face_zero, LargeParameterHomotopy.boundaryMap_zero]
  | right =>
    change (K ◁ SSet.boundary.ι (0 : Fin 2)) ≫ _ =
      (K ◁ SSet.boundary.ι (0 : Fin 2)) ≫ LargeParameterHomotopy.boundaryMap e₀ e₁
    rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      face_one, LargeParameterHomotopy.boundaryMap_one]


end SerrePositivity.SimplicialModel.HomotopyEndpointComparison
