module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BarConstruction
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLift

/-!
# 図式の指定した余錐から実際のbar構成のaugmentationを構成する

## 概要
図式の指定した余錐から実際のbar構成のaugmentationを構成する。
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
[棚卸し m0346][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0346
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual augmentation of the model-free bar construction to any cocone
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] {F : D ⥤ SSet.{v}}
  {K : SSet.{v}} (a : F ⟶ (Functor.const D).obj K)

/- 旧宣言の技術注記：
Evaluate the first element of a bar chain in the actual cocone.
-/
/-- 図式の指定した余錐から実際のbar構成のaugmentationを構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。
-/
def augmentation : (functor D).obj F ⟶ SSet.uliftFunctor.{max uD vD, v}.obj K where
  app n := ↾fun c => ULift.up ((a.app (c.obj 0).obj).app n (c.obj 0).val)
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro c
    apply ULift.ext
    let i := θ.unop.toOrderHom 0
    let e := c.obj i
    let e₀ := c.obj 0
    let f := c.map (homOfLE (Fin.zero_le i))
    have ha := congrArg (fun k : F.obj e₀.obj ⟶ K => k.app n e₀.val)
      (a.naturality f.hom)
    change (a.app e.obj).app n ((F.map f.hom).app n e₀.val) =
      (a.app e₀.obj).app n e₀.val at ha
    have hf : (F.map f.hom).app n e₀.val = e.val := f.map_val
    rw [hf] at ha
    have hn := congrArg (fun k => k e.val) ((a.app e.obj).naturality θ)
    exact hn.trans (congrArg (fun z => K.map θ z) ha)

end SerrePositivity.SimplicialModel.BarConstruction
