module
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-! # 共通の値宇宙での異なる Hom 宇宙の nerve の射
概要：対象の宇宙を共通の最大値にそろえ、Hom の宇宙を変えずに nerve の射を作る。
方針：各射列への後合成をそのまま単体的射にする。
規約：ULift による対象や射の置換をしない。使われ方：解消の因子分解圏から離散圏への比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 概要：Hom の宇宙が異なる二圏間の関手を同じ値宇宙の nerve の射にする。
方針：対象の宇宙の最大値が両方の Hom 宇宙を含む場合に、射列へ直接後合成する。
規約：元の圏と射を変更しない。使われ方：単体ごとの離散値の augmentation。 -/
def resolutionNerveMap {C D : Type (max u v w)} [Category.{v} C] [Category.{w} D]
    (F : C ⥤ D) : nerve C ⟶ nerve D where
  app _ := ↾fun c => c ⋙ F
  naturality {_ _} _ := rfl

end SerrePositivity.KST.SConstruction
