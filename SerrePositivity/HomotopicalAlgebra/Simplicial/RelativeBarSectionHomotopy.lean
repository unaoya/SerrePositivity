module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarSections
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-!
# 実際のcomma射からbarの全次数に整合するホモトピーを構成する

## 概要
実際のcomma射からbarの全次数に整合するホモトピーを構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0528][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0528
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A whole simplicial bar homotopy from an actual comma arrow

The same interval is natural in the label degree and the nerve degree.
Its image under every anodyne-inverting functor identifies the two sections.
-/

@[expose] public section
universe v uD vD uB vB vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v}) {b : B} {d e : D}
  (α : p.obj d ⟶ b) (β : p.obj e ⟶ b) (k : d ⟶ e) (hk : p.map k ≫ β = α)

def commaSectionHomotopyMap :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max uD vD vB} (F.obj d) ⊗
        SSet.stdSimplex.{max uD vD v vB}.obj (SimplexCategory.mk 1) ⟶
      (relative p F).obj b where
  app n := ↾fun x => (SSet.stdSimplex.objEquiv x.2).toOrderHom.monotone.functor ⋙
    sectionInterval p F α β k hk n x.1.down
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    let t := (SimplexCategory.toCat.map θ.unop).toFunctor
    let q := (SSet.stdSimplex.objEquiv x.2).toOrderHom.monotone.functor
    exact congrArg (fun J => (t ⋙ q) ⋙ J)
      (sectionInterval_operator p F α β k hk θ x.1.down).symm

lemma commaSectionHomotopyMap_zero : SSet.ι₀ ≫ commaSectionHomotopyMap p F α β k hk =
    commaSection p F α := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply CategoryTheory.Functor.hext (fun _ => rfl)
  intro i j f
  rfl

lemma commaSectionHomotopyMap_one : SSet.ι₁ ≫ commaSectionHomotopyMap p F α β k hk =
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{max uD vD vB} (F.map k) ≫ commaSection p F β := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply CategoryTheory.Functor.hext (fun _ => rfl)
  intro i j f
  rfl

/- 旧宣言の技術注記：
Both entire maps, not just their vertex values, are joined by the same actual interval.
-/
/-- 実際のcomma射からbarの全次数に整合するホモトピーを構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。
-/
def commaSectionHomotopy : SSet.Homotopy (commaSection p F α)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{max uD vD vB} (F.map k) ≫ commaSection p F β) where
  h := commaSectionHomotopyMap p F α β k hk
  h₀ := commaSectionHomotopyMap_zero p F α β k hk
  h₁ := commaSectionHomotopyMap_one p F α β k hk
  rel := by
    apply NatTrans.ext
    funext n
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact False.elim x.1.property

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max uD vD v vB} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL hk in
lemma commaSection_image_eq : L.map (commaSection p F α) =
    L.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{max uD vD vB} (F.map k) ≫ commaSection p F β) :=
  AnodyneHomotopy.map_homotopy_eq L hL (commaSectionHomotopy p F α β k hk)

end SerrePositivity.SimplicialModel.BarConstruction
