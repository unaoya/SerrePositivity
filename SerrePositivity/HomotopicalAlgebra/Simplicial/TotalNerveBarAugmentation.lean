module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BarConstruction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexChainVertices
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ElementsChainLifting
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# 全要素の圏のnerveから対角barへの実際のaugmentationを構成する

## 概要
全要素の圏のnerveから対角barへの実際のaugmentationを構成する。
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
[棚卸し m0583][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0583
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual total-element nerve maps to the diagonal bar

Every chain uses one common parameter in its first simplex, then sends
the same restricted label along all actual prefix maps. This constructs
the bridge map without a model structure or a weak equivalence assertion.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction.TotalNerve
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})

abbrev values := Functor.uncurry.obj F
abbrev Total := (values F).Elements
abbrev degrees {n : ℕ} (c : ComposableArrows (Total F) n) :
    Fin (n + 1) ⥤ SimplexCategoryᵒᵖ :=
  c ⋙ Functor.Elements.π (values F) ⋙ CategoryTheory.Prod.snd _ _
abbrev objects {n : ℕ} (c : ComposableArrows (Total F) n) : Fin (n + 1) ⥤ D :=
  c ⋙ Functor.Elements.π (values F) ⋙ CategoryTheory.Prod.fst _ _

abbrev initialLabel {n : ℕ} (c : ComposableArrows (Total F) n) :
    (F.obj ((objects F c).obj 0)).obj (Opposite.op (SimplexCategory.mk n)) :=
  (F.obj ((objects F c).obj 0)).map (SimplexChainParameter.parameter (degrees F c)).op
    (c.obj 0).val

lemma initialLabel_reindex {n m : ℕ} (c : ComposableArrows (Total F) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (F.obj ((objects F c).obj (θ.toOrderHom 0))).map θ.op
        ((F.map ((objects F c).map (homOfLE (Fin.zero_le (θ.toOrderHom 0))))).app
          (Opposite.op (SimplexCategory.mk n)) (initialLabel F c)) =
      initialLabel F ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) := by
  let d := (SimplexCategory.toCat.map θ).toFunctor ⋙ c
  let h := c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))
  let T := F.obj ((objects F c).obj (θ.toOrderHom 0))
  let z := (F.map h.hom.1).app (c.obj 0).obj.2 (c.obj 0).val
  have hz : T.map h.hom.2 z = (c.obj (θ.toOrderHom 0)).val := h.map_val
  have hn := congrArg (fun f => f (c.obj 0).val)
    ((F.map h.hom.1).naturality (SimplexChainParameter.parameter (degrees F c)).op)
  change (F.map h.hom.1).app (Opposite.op (SimplexCategory.mk n))
    ((F.obj (c.obj 0).obj.1).map
      (SimplexChainParameter.parameter (degrees F c)).op (c.obj 0).val) =
        T.map (SimplexChainParameter.parameter (degrees F c)).op z at hn
  change T.map θ.op ((F.map h.hom.1).app (Opposite.op (SimplexCategory.mk n))
    ((F.obj (c.obj 0).obj.1).map
      (SimplexChainParameter.parameter (degrees F c)).op (c.obj 0).val)) = _
  rw [hn]
  calc
    _ = T.map (θ ≫ SimplexChainParameter.parameter (degrees F c)).op z :=
      (congrArg (fun f => f z) (T.map_comp
        (SimplexChainParameter.parameter (degrees F c)).op θ.op)).symm
    _ = T.map (SimplexChainParameter.parameter (degrees F d)).op
        (T.map h.hom.2 z) := by
      rw [SimplexChainParameter.reindex]
      exact congrArg (fun f => f z)
        (T.map_comp h.hom.2 (SimplexChainParameter.parameter (degrees F d)).op)
    _ = _ := congrArg (fun x => T.map
      (SimplexChainParameter.parameter (degrees F d)).op x) hz

abbrev simplex {n : ℕ} (c : ComposableArrows (Total F) n) :
    ComposableArrows ((F.flip.obj (Opposite.op (SimplexCategory.mk n))).Elements) n :=
  LabelledChain.lift (F.flip.obj (Opposite.op (SimplexCategory.mk n))) (objects F c)
    (initialLabel F c)

lemma first_vertex {n : ℕ} (c : ComposableArrows (Total F) n) :
    (simplex F c).obj 0 =
      (F.flip.obj (Opposite.op (SimplexCategory.mk n))).elementsMk
        ((objects F c).obj 0) (initialLabel F c) := by
  change (F.flip.obj (Opposite.op (SimplexCategory.mk n))).elementsMk _
    ((F.flip.obj (Opposite.op (SimplexCategory.mk n))).map
      ((objects F c).map (𝟙 0)) (initialLabel F c)) = _
  rw [(objects F c).map_id, CategoryTheory.Functor.map_id]
  rfl

lemma simplex_operator {n m : ℕ} (c : ComposableArrows (Total F) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (SimplexCategory.toCat.map θ).toFunctor ⋙ simplex F c ⋙ (F.flip.map θ.op).mapElements =
      simplex F ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) := by
  change ((SimplexCategory.toCat.map θ).toFunctor ⋙
    LabelledChain.lift (F.flip.obj (Opposite.op (SimplexCategory.mk n)))
      (objects F c) (initialLabel F c)) ⋙ (F.flip.map θ.op).mapElements = _
  rw [LabelledChain.reindex, LabelledChain.map]
  apply congrArg (LabelledChain.lift (F.flip.obj (Opposite.op (SimplexCategory.mk m)))
    (objects F ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)))
  exact initialLabel_reindex F c θ

/-- 全要素の圏のnerveから対角barへの実際のaugmentationを構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。
-/
def augmentation : nerve (Total F) ⟶ (BarConstruction.functor D).obj F where
  app _ := ↾fun c => simplex F c
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro c
    exact (simplex_operator F c θ.unop).symm

end SerrePositivity.SimplicialModel.BarConstruction.TotalNerve
