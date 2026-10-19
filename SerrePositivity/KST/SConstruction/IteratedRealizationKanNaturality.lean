module
public import SerrePositivity.KST.SConstruction.IteratedBoundaryKanComparison
public import SerrePositivity.KST.SConstruction.InnerZeroBoundaryNaturality

/-! # 元の反復実現の座標比較と Kan 比較の自然性
概要：元の最内側 S の実現から標準境界商の Kan 模型への比較は完全関手について自然。
方針：自己関手の座標同型の入力自然性と元の商射・Kan 単位の自然性を合成する。
規約：元の座標比較を変更しない。使われ方：対象の K loop 類の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 元の最内側反復実現から既存の境界商 Kan 模型への比較は厳密に自然。 -/
lemma iteratedRealizationToKan_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    iteratedSRealizationMap r f ≫ iteratedRealizationToKan r Y =
      iteratedRealizationToKan r X ≫ ((boundaryKanRealizationFunctor r).map f).right := by
  have hn : (boundaryReducedRealizationMap r f).right ≫
      (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization r Y)).right =
      (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization r X)).right ≫
        ((boundaryKanRealizationFunctor r).map f).right :=
    congrArg Under.Hom.right
      (Spectra.PointedKanReplacement.unit.naturality (boundaryReducedRealizationMap r f))
  have hq := congrArg (fun g => g ≫
    (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization r Y)).right)
    (boundaryReducedRealizationMap_quotient r f)
  simp only [Category.assoc] at hq
  rw [hn] at hq
  simp only [iteratedRealizationToKan, Category.assoc]
  rw [← Category.assoc (iteratedSRealizationMap r f),
    iteratedSRealizationCoordinateIso_naturality, Category.assoc]
  exact congrArg ((iteratedSRealizationCoordinateIso r X).hom ≫ ·) hq.symm

end SerrePositivity.KST.SConstruction
