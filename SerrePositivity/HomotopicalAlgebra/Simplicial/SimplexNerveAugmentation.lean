module

public import SerrePositivity.CategoryTheory.SimplexChainVertices
public import Mathlib.CategoryTheory.Elements

/-!
# 単体圏のnerveから元の単体的集合への自然なaugmentationを構成する

## 概要
単体圏のnerveから元の単体的集合への自然なaugmentationを構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
圏の射列を各単体として評価し、自然変換や端点の射を明示する。
単体ごとの合成と端点の式を照合して、全体の写像を得る。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0563][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0563
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# An actual natural map from the nerve of a simplex category to its simplicial set

For a chain of face and degeneracy maps, all vertices are taken inside the
same first simplex using the actual prefix operators. No weak equivalence
of this map or model structure is assumed.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.SimplexNerveAugmentation
variable (X : SSet.{v})

abbrev parameter {n : ℕ} (c : ComposableArrows X.Elements n) :
    SimplexCategory.mk n ⟶ (c.obj 0).obj.unop :=
  SimplexChainParameter.parameter (c ⋙ Functor.Elements.π X)

abbrev simplex {n : ℕ} (c : ComposableArrows X.Elements n) :
    X.obj (Opposite.op (SimplexCategory.mk n)) :=
  X.map (parameter X c).op (c.obj 0).val

lemma simplex_operator {n m : ℕ} (c : ComposableArrows X.Elements n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    X.map θ.op (simplex X c) =
      simplex X ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) := by
  let d := (SimplexCategory.toCat.map θ).toFunctor ⋙ c
  let k := c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))
  change X.map θ.op (X.map (parameter X c).op (c.obj 0).val) =
    X.map (parameter X d).op (c.obj (θ.toOrderHom 0)).val
  calc
    _ = X.map (θ ≫ parameter X c).op (c.obj 0).val :=
      (congrArg (fun f => f (c.obj 0).val) (X.map_comp (parameter X c).op θ.op)).symm
    _ = X.map (parameter X d).op (X.map k.hom (c.obj 0).val) := by
      rw [show θ ≫ parameter X c = parameter X d ≫ k.hom.unop from
        SimplexChainParameter.reindex (c ⋙ Functor.Elements.π X) θ]
      exact congrArg (fun f => f (c.obj 0).val) (X.map_comp k.hom (parameter X d).op)
    _ = _ := congrArg (fun x => X.map (parameter X d).op x) k.map_val

/-- 単体圏のnerveから元の単体的集合への自然なaugmentationを構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
圏の射列を各単体として評価し、自然変換や端点の射を明示する。
単体ごとの合成と端点の式を照合して、全体の写像を得る。
-/
def augmentation : nerve X.Elements ⟶ X where
  app _ := ↾fun c => simplex X c
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro c
    exact (simplex_operator X c θ.unop).symm

lemma naturality {Y : SSet.{v}} (f : X ⟶ Y) :
    nerveMap f.mapElements ≫ augmentation Y = augmentation X ≫ f := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  exact (congrArg (fun k => k (c.obj 0).val)
    (f.naturality (parameter X c).op)).symm

end SerrePositivity.SimplicialModel.SimplexNerveAugmentation
