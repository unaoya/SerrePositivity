module

public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# 面と退化に関する可換性から単体的な自然変換を組み立てる

## 概要
面と退化に関する可換性から単体的な自然変換を組み立てる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
順序写像または面・退化の標準形を明示して単体作用素を計算する。
生成作用素上の一致を、単体恒等式によって全作用素上の一致へ拡張する。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0039][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0039
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Assemble a simplicial natural transformation from its face and degeneracy squares
-/

@[expose] public section
universe v u
open CategoryTheory

namespace SerrePositivity.SimplexNaturality
variable {C : Type u} [Category.{v} C] (F G : SimplicialObject C)
  (app : ∀ n : SimplexCategoryᵒᵖ, F.obj n ⟶ G.obj n)

def property : MorphismProperty SimplexCategory := fun X Y f =>
  F.map f.op ≫ app (Opposite.op X) = app (Opposite.op Y) ≫ G.map f.op

instance : (property F G app).IsMultiplicative where
  id_mem X := by simp [property]
  comp_mem f g hf hg := by
    dsimp only [property] at hf hg ⊢
    rw [op_comp, F.map_comp, G.map_comp, Category.assoc, hf, ← Category.assoc, hg,
      Category.assoc]

lemma naturality
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), F.δ i ≫ app (Opposite.op (SimplexCategory.mk n)) =
      app (Opposite.op (SimplexCategory.mk (n + 1))) ≫ G.δ i)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), F.σ i ≫
      app (Opposite.op (SimplexCategory.mk (n + 1))) =
        app (Opposite.op (SimplexCategory.mk n)) ≫ G.σ i)
    {X Y : SimplexCategoryᵒᵖ} (f : X ⟶ Y) : F.map f ≫ app Y = app X ≫ G.map f := by
  have htop : property F G app = ⊤ :=
    SimplexCategory.morphismProperty_eq_top _ hδ hσ
  have hf : property F G app f.unop := by rw [htop]; trivial
  exact hf

/-- 面と退化に関する可換性から単体的な自然変換を組み立てる。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
順序写像または面・退化の標準形を明示して単体作用素を計算する。
生成作用素上の一致を、単体恒等式によって全作用素上の一致へ拡張する。
-/
def ofFacesDegeneracies
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), F.δ i ≫ app (Opposite.op (SimplexCategory.mk n)) =
      app (Opposite.op (SimplexCategory.mk (n + 1))) ≫ G.δ i)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), F.σ i ≫
      app (Opposite.op (SimplexCategory.mk (n + 1))) =
        app (Opposite.op (SimplexCategory.mk n)) ≫ G.σ i) : F ⟶ G where
  app := app
  naturality _ _ f := naturality F G app hδ hσ f

lemma ofFacesDegeneracies_app
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), F.δ i ≫ app (Opposite.op (SimplexCategory.mk n)) =
      app (Opposite.op (SimplexCategory.mk (n + 1))) ≫ G.δ i)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), F.σ i ≫
      app (Opposite.op (SimplexCategory.mk (n + 1))) =
        app (Opposite.op (SimplexCategory.mk n)) ≫ G.σ i)
    (n : SimplexCategoryᵒᵖ) : (ofFacesDegeneracies F G app hδ hσ).app n = app n := rfl

end SerrePositivity.SimplexNaturality
