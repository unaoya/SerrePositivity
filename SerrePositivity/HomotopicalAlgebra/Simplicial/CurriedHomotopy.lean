module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceEdges

/-!
# 写像単体的集合の指定した辺から元の全区間ホモトピーを構成する

## 概要
写像単体的集合の指定した辺から元の全区間ホモトピーを構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
テンソルと内部Homの随伴で族を転置し、対応する境界の等式を比較する。
転置の単射性と自然性により、元の全パラメータ族の等式へ戻す。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0376][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0376
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A specified mapping-space edge gives the same actual interval homotopy
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.CurriedHomotopy
variable {X K : SSet.{v}} {f g : X ⟶ K}

/-- 写像単体的集合の指定した辺から元の全区間ホモトピーを構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
テンソルと内部Homの随伴で族を転置し、対応する境界の等式を比較する。
転置の単射性と自然性により、元の全パラメータ族の等式へ戻す。
-/
def ofEdge (e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ (ihom X).obj K)
    (h₀ : SSet.stdSimplex.δ (1 : Fin 2) ≫ e = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point f)
    (h₁ : SSet.stdSimplex.δ (0 : Fin 2) ≫ e = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point g) :
    SSet.Homotopy f g where
  h := uncurry e
  h₀ := by
    change SSet.ι₀ ≫ uncurry e = f
    rw [← LargeParameterHomotopy.section_zero X, Category.assoc,
      ← uncurry_natural_left, h₀, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point, uncurry_curry]
    rfl
  h₁ := by
    change SSet.ι₁ ≫ uncurry e = g
    rw [← LargeParameterHomotopy.section_one X, Category.assoc,
      ← uncurry_natural_left, h₁, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point, uncurry_curry]
    rfl
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

lemma ofEdge_h (e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ (ihom X).obj K)
    (h₀ : SSet.stdSimplex.δ (1 : Fin 2) ≫ e = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point f)
    (h₁ : SSet.stdSimplex.δ (0 : Fin 2) ≫ e = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point g) :
    (ofEdge e h₀ h₁).h = uncurry e := rfl

end SerrePositivity.SimplicialModel.CurriedHomotopy
