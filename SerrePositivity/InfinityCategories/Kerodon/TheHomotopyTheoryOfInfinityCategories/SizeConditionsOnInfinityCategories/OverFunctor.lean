module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.OverIso

/-!
概要：底上の元の射の宇宙持ち上げを、同じ射を使う関手に束ねる。
方針：元の宇宙持ち上げ関手の恒等・合成則を両脚へ適用する。
規約：元の射と表示を保持する。
使われ方：共有境界での分類先制限の合成則。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 同じ底上の射を持ち上げる関手。 -/
def uliftOverFunctor (B : SSet.{u}) :
    Over B ⥤ Over ((SSet.uliftFunctor.{v, u}).obj B) where
  obj a := Over.mk ((SSet.uliftFunctor.{v, u}).map a.hom)
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism f
  map_id a := by
    apply Over.OverMorphism.ext
    exact (SSet.uliftFunctor.{v, u}).map_id a.left
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact (SSet.uliftFunctor.{v, u}).map_comp f.left g.left

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
