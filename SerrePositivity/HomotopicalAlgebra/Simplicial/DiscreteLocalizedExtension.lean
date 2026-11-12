module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiscreteKanExtension

/-!
# 離散値の自然変換を局所化で可逆な射に沿って一意に降下させる

## 概要
離散値の自然変換を局所化で可逆な射に沿って一意に降下させる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
実写像または区間ホモトピーの関係を商へ降ろす。
代表元に依らないことを確認してから、誘導写像と比較を組み立てる。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0395][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0395
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Unique discrete-valued descent through every localized equivalence

This applies to quotient projections as well as anodyne units. No model
structure or smallness of the base category is required.
-/

@[expose] public section
universe w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.DiscreteLocalizedExtension

variable {A B : SSet.{w}} (i : A ⟶ B)
  (hi : IsIso (AnodyneHomotopy.anodyneQ.map i)) {T : Type w}

include hi in
lemma pre_bijective : Function.Bijective (fun g : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete T => i ≫ g) := by
  have ht := KanTestDetection.tests_of_anodyneQ_isIso i hi _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete_terminal_rlp T)
  constructor
  · intro f g h
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.homEquiv.injective
    have hc : HomotopyClasses.mk f = HomotopyClasses.mk g :=
      ht.injective (congrArg HomotopyClasses.mk h)
    exact congrArg PiZeroLocalization.classEquiv hc
  · intro f
    obtain ⟨c, hc⟩ := ht.surjective (HomotopyClasses.mk f)
    obtain ⟨g, rfl⟩ := Quot.exists_rep c
    refine ⟨g, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.homEquiv.injective ?_⟩
    exact congrArg PiZeroLocalization.classEquiv hc

def extension (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete T) : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete T :=
  ((pre_bijective i hi).surjective f).choose

lemma extension_fac (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete T) : i ≫ extension i hi f = f :=
  ((pre_bijective i hi).surjective f).choose_spec

lemma extension_unique (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete T) (g : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete T) (hg : i ≫ g = f) :
    g = extension i hi f := (pre_bijective i hi).injective
  (hg.trans (extension_fac i hi f).symm)

variable {D : Type uD} [Category.{vD} D] {F G : D ⥤ SSet.{w}} {T : D ⥤ Type w}
  (p : F ⟶ G) (hp : ∀ d, IsIso (AnodyneHomotopy.anodyneQ.map (p.app d)))
  (a : F ⟶ T ⋙ Functor.const SimplexCategoryᵒᵖ)

/-- 離散値の自然変換を局所化で可逆な射に沿って一意に降下させる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
実写像または区間ホモトピーの関係を商へ降ろす。
代表元に依らないことを確認してから、誘導写像と比較を組み立てる。
-/
def descend : G ⟶ T ⋙ Functor.const SimplexCategoryᵒᵖ where
  app d := extension (p.app d) (hp d) (a.app d)
  naturality {d e} f := by
    apply (pre_bijective (p.app d) (hp d)).injective
    change p.app d ≫ (G.map f ≫ _) = p.app d ≫ (_ ≫ _)
    rw [← Category.assoc, ← p.naturality, Category.assoc,
      extension_fac, ← Category.assoc, extension_fac]
    exact a.naturality f

lemma descend_fac : p ≫ descend p hp a = a := by
  apply NatTrans.ext
  funext d
  exact extension_fac _ (hp d) (a.app d)

lemma descend_unique (b : G ⟶ T ⋙ Functor.const SimplexCategoryᵒᵖ) (hb : p ≫ b = a) :
    b = descend p hp a := by
  apply NatTrans.ext
  funext d
  exact extension_unique _ (hp d) (a.app d) (b.app d) (congr_app hb d)

end SerrePositivity.SimplicialModel.DiscreteLocalizedExtension
