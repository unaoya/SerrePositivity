module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor

/-!
# 実際のファイバー図式を添字関手に沿って制限する比較を構成する

## 概要
実際のファイバー図式を添字関手に沿って制限する比較を構成する。
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
[棚卸し m0399][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0399
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Reindexing actual fiber diagrams and changing equal point families
-/

@[expose] public section
universe v uD vD uE vE
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctorReindex
variable {D : Type uD} [Category.{vD} D] {F G : D ⥤ SSet.{v}} (p : F ⟶ G)
  (b : (Functor.const D).obj (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) ⟶ G)

/- 旧宣言の技術注記：
Objectwise chosen pullbacks reindex to exactly the corresponding fiber diagram.
-/
/-- 実際のファイバー図式を添字関手に沿って制限する比較を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
def reindex {E : Type uE} [Category.{vE} E] (H : E ⥤ D) :
    H ⋙ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.functor p b ≅ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.functor (Functor.whiskerLeft H p) (Functor.whiskerLeft H b) := Iso.refl _

def congrPoint
    (b' : (Functor.const D).obj (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) ⟶ G)
    (h : b = b') : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.functor p b ≅ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.functor p b' := eqToIso (congrArg (fun c => _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.functor p c) h)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctorReindex
