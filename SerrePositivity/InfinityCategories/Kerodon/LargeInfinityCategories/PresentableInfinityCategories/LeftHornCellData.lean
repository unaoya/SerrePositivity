module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.OverCellCopies
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
概要：固定した底へ写る全ての左ホーンを、底上で同時に付加するデータ。
方針：標準単体の底への射と左ホーンの除外頂点で添字付け、底上の全射のコピーを取る。
規約：最後の頂点を除くホーンだけを用いる。底は任意の小さい単体集合。
使われ方：left fibration を構成する一段のセル付加。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 底への標準単体と、その最後の頂点以外の左ホーンの小さい添字型。 -/
def LeftHornCellIndex (B : SSet.{u}) : Type u :=
  Σ n : ℕ, {i : Fin (n + 2) // i < Fin.last (n + 1)} × (Δ[n + 1] ⟶ B)

/-- セルの底上の標準単体。 -/
def leftHornCellTarget {B : SSet.{u}} (h : LeftHornCellIndex B) : Over B :=
  Over.mk h.2.2

/-- セルの底上のホーン。 -/
def leftHornCellSource {B : SSet.{u}} (h : LeftHornCellIndex B) : Over B :=
  Over.mk ((horn (h.1 + 1) h.2.1.val).ι ≫ h.2.2)

/-- 底を保つ元のホーン包含。 -/
def leftHornCellArrow {B : SSet.{u}} (h : LeftHornCellIndex B) :
    leftHornCellSource h ⟶ leftHornCellTarget h :=
  Over.homMk (horn (h.1 + 1) h.2.1.val).ι rfl

instance leftHornCellSource_finite {B : SSet.{u}} (h : LeftHornCellIndex B) :
    (leftHornCellSource h).left.Finite := by
  dsimp [leftHornCellSource]
  infer_instance

/-- 全左ホーンの始域の、底上の全射を添字とするコピー。 -/
def leftHornSourceCopies (B : SSet.{u}) : Over B ⥤ Over B :=
  ∐ fun h : LeftHornCellIndex B ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.overCellCopiesFunctor (leftHornCellSource h) (leftHornCellSource h)

/-- 対応する標準単体の、同じ底上の射を添字とするコピー。 -/
def leftHornTargetCopies (B : SSet.{u}) : Over B ⥤ Over B :=
  ∐ fun h : LeftHornCellIndex B ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.overCellCopiesFunctor (leftHornCellSource h) (leftHornCellTarget h)

/-- 全コピーをそれぞれの元の底上の射で評価する。 -/
def leftHornCopiesEvaluation (B : SSet.{u}) : leftHornSourceCopies B ⟶ 𝟭 (Over B) :=
  Sigma.desc fun h ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.overCellCopiesEvaluation (leftHornCellSource h)

/-- 底上の全コピーに元の左ホーン包含を適用する。 -/
def leftHornCopiesBoundary (B : SSet.{u}) : leftHornSourceCopies B ⟶ leftHornTargetCopies B :=
  Limits.Sigma.map fun h ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.overCellCopiesMap (leftHornCellSource h) (leftHornCellArrow h)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
