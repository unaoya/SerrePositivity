module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.PiZeroConstant
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# 離散ラベルを保つ写像から実際の単体的ファイバー間の写像を構成する

## 概要
離散ラベルを保つ写像から実際の単体的ファイバー間の写像を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0393][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0393
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual simplicial fibers over discrete labels and maps between them
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFiber
variable {I : Type v} {X Y : SSet.{v}}

lemma label_naturality (b : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete I)
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (x : X.obj n) :
    b.app m (X.map θ x) = b.app n x :=
  types_congr_hom (b.naturality θ) x

def obj (b : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete I) (i : I) : SSet.{v} where
  obj n := {x : X.obj n // b.app n x = i}
  map θ := ↾fun x => ⟨X.map θ x.1, (label_naturality b θ x.1).trans x.2⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact types_congr_hom (X.map_id n) x.1
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact types_congr_hom (X.map_comp f g) x.1

def inclusion (b : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete I) (i : I) : obj b i ⟶ X where
  app _ := ↾Subtype.val
  naturality {_ _} _ := by apply ConcreteCategory.hom_ext; intro x; rfl

/-- 離散ラベルを保つ写像から実際の単体的ファイバー間の写像を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
def map (j : X ⟶ Y) (b : Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete I) (i : I) :
    obj (j ≫ b) i ⟶ obj b i where
  app _ := ↾fun x => ⟨j.app _ x.1, x.2⟩
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact types_congr_hom (j.naturality θ) x.1

instance map_mono (j : X ⟶ Y) [Mono j] (b : Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete I) (i : I) :
    Mono (map j b i) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro n
  apply (mono_iff_injective _).mpr
  intro x y h
  apply Subtype.ext
  exact (mono_iff_injective (j.app n)).mp inferInstance (congrArg Subtype.val h)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiscreteFiber
