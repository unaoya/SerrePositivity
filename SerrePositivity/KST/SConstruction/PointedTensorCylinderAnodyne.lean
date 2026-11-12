module
public import SerrePositivity.KST.SConstruction.PointedSmashAnodyne
public import SerrePositivity.KST.SConstruction.PointedTensorCylinderBoundary

/-! # 同じ自由点つき円柱の両端の anodyne 性
概要：同じ円柱の端点射は、任意の点つき入力で基礎 anodyne 射になる。
方針：既存の自由区間の面端点と一致させ、右 smash と単位同型を合成する。
規約：時刻零は面添字一。使われ方：実写像円柱射影の弱比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra

/-- 同じ時刻零の端点は、既存の自由区間の面添字一の端点。 -/
lemma pointedTensorIntervalEnd_zero_eq :
    pointedTensorIntervalEnd.{u} 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint 1 := by
  exact pointedTensorBoundaryStart_inclusion.symm.trans _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryStart_inclusion

/-- 同じ時刻一の端点は、既存の自由区間の面添字零の端点。 -/
lemma pointedTensorIntervalEnd_one_eq :
    pointedTensorIntervalEnd.{u} 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint 0 := by
  exact pointedTensorBoundaryEnd_inclusion.symm.trans _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEnd_inclusion

/-- 同じ自由点つき区間の両端点は、基礎単体集合上で anodyne。 -/
lemma pointedTensorIntervalEnd_anodyne (i : Fin 2) :
    anodyneExtensions (pointedTensorIntervalEnd.{u} i).right := by
  fin_cases i
  · erw [pointedTensorIntervalEnd_zero_eq]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint_anodyne 1
  · erw [pointedTensorIntervalEnd_one_eq]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint_anodyne 0

/-- 同じ元の円柱の両端包含は、任意の入力で基礎 anodyne 射。 -/
lemma pointedTensorCylinderEndMap_anodyne (i : Fin 2) (X : PointedSimplicialSet.{u}) :
    anodyneExtensions (pointedTensorCylinderEndMap i X).right := by
  have h := pointedWhiskerRight_anodyne _ (pointedTensorIntervalEnd_anodyne i) X
  let _ : IsIso (λ_ X).inv.right := (Under.forget (𝟙_ SSet.{u})).map_isIso (λ_ X).inv
  exact anodyneExtensions.comp_mem _ _ (anodyneExtensions.of_isIso _) h

end SerrePositivity.KST.SConstruction
