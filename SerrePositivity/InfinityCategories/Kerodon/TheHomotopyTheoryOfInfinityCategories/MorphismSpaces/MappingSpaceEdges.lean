module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# 写像空間の頂点と辺

## 概要
写像の転置とホモトピーの転置を同じ端点を持つ頂点と辺として表す。
任意モデル源の厳密化から独立して利用できる一般道具である。

## 方針（定義・証明）
テンソルと内部Homの随伴で端点を照合し、移送後も区間写像を保持する。
既存の構成を同じ公開名と証明のまま一般層に切り出す。

## 規約と注意
宇宙と仮定は各宣言に明示したものを用いる。
専用の比較図式・正規化充填・選択の整合性は仮定しない。

## 使われ方
一般入口GeneralToolsおよび共有Foundationsから利用する。
旧パスの互換importを通して中断中の厳密化からも利用する。
今後のS-構成・ホモトピー比較・局所化の基礎として使える。
詳細はformalization-plans/archive/k-theory-generalization-inventory.mdの配置実施記録を参照。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
universe r
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
/-- 単体的集合の実写像を内部Homの頂点として表す。
零単体からの定数族をテンソルと内部Homの随伴で転置する。 -/
abbrev point {K P : SSet.{r}} (e : K ⟶ P) :
    SSet.stdSimplex.{r}.obj (SimplexCategory.mk 0) ⟶ (ihom K).obj P :=
  curry (fst K _ ≫ e)

lemma edge_zero {K P : SSet.{r}} {e₀ e₁ : K ⟶ P} (H : SSet.Homotopy e₀ e₁) :
    SSet.stdSimplex.δ (1 : Fin 2) ≫ curry H.h = point e₀ := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, point, uncurry_curry]
  have h : K ◁ SSet.stdSimplex.δ (1 : Fin 2) = fst K _ ≫ SSet.ι₀ := by
    rw [SSet.stdSimplex.δ_one_eq_const]
    rfl
  rw [h, Category.assoc, H.h₀]

lemma edge_one {K P : SSet.{r}} {e₀ e₁ : K ⟶ P} (H : SSet.Homotopy e₀ e₁) :
    SSet.stdSimplex.δ (0 : Fin 2) ≫ curry H.h = point e₁ := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, point, uncurry_curry]
  have h : K ◁ SSet.stdSimplex.δ (0 : Fin 2) = fst K _ ≫ SSet.ι₁ := by
    rw [SSet.stdSimplex.δ_zero_eq_const]
    rfl
  rw [h, Category.assoc, H.h₁]

/-- Transport an existing homotopy without changing its interval map. -/
def transport {K L P Q : SSet.{r}} (u : K ⟶ L) (q : P ⟶ Q)
    {e₀ e₁ : L ⟶ P} (H : SSet.Homotopy e₀ e₁) :
    SSet.Homotopy (u ≫ e₀ ≫ q) (u ≫ e₁ ≫ q) where
  h := u ▷ SSet.stdSimplex.{r}.obj (SimplexCategory.mk 1) ≫ H.h ≫ q
  h₀ := by rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, H.h₀_assoc]; rfl
  h₁ := by rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, H.h₁_assoc]; rfl
  rel := by
    apply NatTrans.ext
    funext n
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact False.elim x.1.property

/-- Change the endpoint expressions using proved equalities, retaining the same map. -/
def changeEndpoints {K P : SSet.{r}} {e₀ e₁ f₀ f₁ : K ⟶ P}
    (H : SSet.Homotopy e₀ e₁) (h₀ : e₀ = f₀) (h₁ : e₁ = f₁) :
    SSet.Homotopy f₀ f₁ := by
  cases h₀
  cases h₁
  exact H

@[simp]
lemma changeEndpoints_h {K P : SSet.{r}} {e₀ e₁ f₀ f₁ : K ⟶ P}
    (H : SSet.Homotopy e₀ e₁) (h₀ : e₀ = f₀) (h₁ : e₁ = f₁) :
    (changeEndpoints H h₀ h₁).h = H.h := by
  cases h₀
  cases h₁
  rfl


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
