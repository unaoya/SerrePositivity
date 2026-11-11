module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroLocalization

/-!
# 離散値の写像をKan置換に沿って一意かつ自然に延長する

## 概要
離散値の写像をKan置換に沿って一意かつ自然に延長する。
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
[棚卸し m0394][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0394
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Unique discrete-valued extension through the actual Kan replacement

Uniqueness makes the extensions natural over arbitrary large base categories.
No model structure on simplicial sets is used.
-/

@[expose] public section
universe w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.DiscreteKanExtension

variable {A B : SSet.{w}} (i : A ⟶ B) (hi : SSet.anodyneExtensions i) {T : Type w}

include hi in
lemma pre_injective : Function.Injective (fun g : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete T => i ≫ g) := by
  intro f g h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.homEquiv.injective
  have hc : HomotopyClasses.mk f = HomotopyClasses.mk g :=
    (KanHomotopyClasses.pre_bijective i hi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete_terminal_rlp T)).injective
      (congrArg HomotopyClasses.mk h)
  exact congrArg PiZeroLocalization.classEquiv hc

def extension (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete T) : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete T :=
  (KanHomotopyExtension.exists_extension i hi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete_terminal_rlp T) f).choose

lemma extension_fac (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete T) : i ≫ extension i hi f = f :=
  (KanHomotopyExtension.exists_extension i hi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete_terminal_rlp T) f).choose_spec

lemma extension_unique (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete T) (g : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete T) (hg : i ≫ g = f) :
    g = extension i hi f := pre_injective i hi (hg.trans (extension_fac i hi f).symm)

variable {D : Type uD} [Category.{vD} D] {F : D ⥤ SSet.{w}} {T : D ⥤ Type w}
  (a : F ⟶ T ⋙ Functor.const SimplexCategoryᵒᵖ)

/-- 離散値の写像をKan置換に沿って一意かつ自然に延長する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
def naturalExtension : F ⋙ AnodyneKanReplacement.functor ⟶
    T ⋙ Functor.const SimplexCategoryᵒᵖ where
  app d := extension (AnodyneKanReplacement.unit.app (F.obj d))
    (AnodyneKanReplacement.unit_anodyne (F.obj d)) (a.app d)
  naturality {d e} f := by
    apply pre_injective (AnodyneKanReplacement.unit.app (F.obj d))
      (AnodyneKanReplacement.unit_anodyne (F.obj d))
    change AnodyneKanReplacement.unit.app (F.obj d) ≫
        (AnodyneKanReplacement.functor.map (F.map f) ≫ _) =
      AnodyneKanReplacement.unit.app (F.obj d) ≫ (_ ≫ _)
    rw [← Category.assoc, ← AnodyneKanReplacement.unit.naturality,
      Category.assoc, extension_fac, ← Category.assoc, extension_fac]
    exact a.naturality f

lemma naturalExtension_fac : Functor.whiskerLeft F AnodyneKanReplacement.unit ≫
    naturalExtension a = a := by
  apply NatTrans.ext
  funext d
  exact extension_fac _ (AnodyneKanReplacement.unit_anodyne (F.obj d)) (a.app d)

lemma naturalExtension_unique
    (b : F ⋙ AnodyneKanReplacement.functor ⟶ T ⋙ Functor.const SimplexCategoryᵒᵖ)
    (hb : Functor.whiskerLeft F AnodyneKanReplacement.unit ≫ b = a) :
    b = naturalExtension a := by
  apply NatTrans.ext
  funext d
  exact extension_unique _ (AnodyneKanReplacement.unit_anodyne (F.obj d))
    (a.app d) (b.app d) (congr_app hb d)

end SerrePositivity.SimplicialModel.DiscreteKanExtension
