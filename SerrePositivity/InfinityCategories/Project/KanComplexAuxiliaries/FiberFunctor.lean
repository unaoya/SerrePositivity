module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# 図式内の実際のpullbackファイバーへ整合する族を持ち上げる

## 概要
図式内の実際のpullbackファイバーへ整合する族を持ち上げる。
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
[棚卸し m0398][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0398
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual pullback fibers in an arbitrary simplicial diagram

Objectwise pullbacks and their actual maps form a strict functor. Natural
families over the specified point lift to that functor. No model is used.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor
variable {D : Type uD} [Category.{vD} D] {F G : D ⥤ SSet.{v}} (p : F ⟶ G)
  (b : (Functor.const D).obj (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) ⟶ G)

abbrev obj (X : D) : SSet.{v} := pullback (p.app X) (b.app X)

def map {X Y : D} (f : X ⟶ Y) : obj p b X ⟶ obj p b Y :=
  pullback.lift (pullback.fst _ _ ≫ F.map f) (pullback.snd _ _) (by
    rw [Category.assoc, p.naturality, ← Category.assoc, pullback.condition,
      Category.assoc, ← b.naturality]
    change _ ≫ 𝟙 _ ≫ _ = _
    rw [Category.id_comp])

@[reassoc (attr := simp)]
lemma map_fst {X Y : D} (f : X ⟶ Y) : map p b f ≫ pullback.fst _ _ =
    pullback.fst _ _ ≫ F.map f := pullback.lift_fst _ _ _
@[reassoc (attr := simp)]
lemma map_snd {X Y : D} (f : X ⟶ Y) : map p b f ≫ pullback.snd _ _ =
    pullback.snd _ _ := pullback.lift_snd _ _ _

def functor : D ⥤ SSet.{v} where
  obj X := obj p b X
  map f := map p b f
  map_id X := by
    apply pullback.hom_ext
    · rw [map_fst, F.map_id, Category.comp_id, Category.id_comp]
    · rw [map_snd, Category.id_comp]
  map_comp f g := by
    apply pullback.hom_ext
    · simp only [Category.assoc, map_fst, map_fst_assoc, F.map_comp]
    · simp only [Category.assoc, map_snd]

def inclusion : functor p b ⟶ F where
  app _ := pullback.fst _ _
  naturality {_ _} f := map_fst p b f

def projection : functor p b ⟶ (Functor.const D).obj
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) where
  app _ := pullback.snd _ _
  naturality {_ _} f := (map_snd p b f).trans (Category.comp_id _).symm

variable {S : SSet.{v}} (a : (Functor.const D).obj S ⟶ F)
  (ha : ∀ X, a.app X ≫ p.app X = SSet.stdSimplex.isTerminalObj₀.from S ≫ b.app X)

/-- 図式内の実際のpullbackファイバーへ整合する族を持ち上げる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
def liftFamily : (Functor.const D).obj S ⟶ functor p b where
  app X := pullback.lift (a.app X) (SSet.stdSimplex.isTerminalObj₀.from S) (ha X)
  naturality {X Y} f := by
    apply pullback.hom_ext
    · change ((𝟙 S) ≫ pullback.lift (a.app Y) _ (ha Y)) ≫ pullback.fst _ _ =
        (pullback.lift (a.app X) _ (ha X) ≫ map p b f) ≫ pullback.fst _ _
      rw [Category.id_comp, pullback.lift_fst, Category.assoc, map_fst,
        ← Category.assoc, pullback.lift_fst]
      exact (Category.id_comp _).symm.trans (a.naturality f)
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor
