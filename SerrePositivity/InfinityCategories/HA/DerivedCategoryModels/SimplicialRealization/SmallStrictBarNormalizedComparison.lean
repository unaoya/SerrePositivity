module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalIso
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DeformationRetract

/-!
# 既存の正規化 bar の補正包含を通る同じ比較

## 概要
既存の正規化 MC bar から、同じ shifted 列の全複体への比較を作る。

## 方針
既存の補正包含と元の比較射を合成し、無条件の変形 retract と一点評価の同型を使う。

## 規約
正規化の射影・包含・ホモトピーを作り直さない。

## 使われ方
HA 1.2.4。既存の指定 native 余錐を計算した標的へ送る閉射。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- 既存の補正包含を同じ厳密な比較射の前に合成した正規化比較。 -/
def smallStrictBarNormalizedTotalHom (F : J ⥤ ModuleCategory A PUnit.{1}) :
    ForgetEnrichment.of (Complex A)
      (dgCoherentBarNormalizedModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F)) ⟶
    ForgetEnrichment.of (Complex A) (smallStrictBarTotalTarget A F) :=
  dgCoherentBarNormalizedModuleInclusionUnconditional A PUnit.{1} (smallStrictBarDiagram A F) ≫
    smallStrictBarTotalHom A F

/-- 既存の正規化補正包含の一点評価は、同じ射影を逆とする鎖ホモトピー同値。 -/
def smallStrictBarNormalizedInclusionPointHomotopyEquiv (F : J ⥤ ModuleCategory A PUnit.{1}) :
    HomotopyEquiv
      ((dgCoherentBarNormalizedModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F)).obj
        (op PUnit.unit))
      ((dgCoherentBarModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F)).obj
        (op PUnit.unit)) where
  hom := (moduleEvaluation A PUnit.{1} PUnit.unit).map
    (dgCoherentBarNormalizedModuleInclusionUnconditional A PUnit.{1} (smallStrictBarDiagram A F))
  inv := (moduleEvaluation A PUnit.{1} PUnit.unit).map
    (dgCoherentBarNormalizedModuleProjectionUnconditional A PUnit.{1} (smallStrictBarDiagram A F))
  homotopyHomInvId := Homotopy.ofEq (by
    rw [← CategoryTheory.Functor.map_comp, dgCoherentBarNormalizedModuleInclusionUnconditional_projection,
      CategoryTheory.Functor.map_id]
    rfl)
  homotopyInvHomId := by
    have h := (moduleHomotopy_evaluation A PUnit.{1}
      (dgCoherentBarNormalizedModuleRetractHomotopyUnconditional A PUnit.{1}
        (smallStrictBarDiagram A F)) PUnit.unit).some
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
    exact h

/-- 同じ正規化比較の一点評価は鎖ホモトピー同値。 -/
def smallStrictBarNormalizedTotalPointHomotopyEquiv (F : J ⥤ ModuleCategory A PUnit.{1}) :
    HomotopyEquiv
      ((dgCoherentBarNormalizedModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F)).obj
        (op PUnit.unit)) ((smallStrictBarTotalTarget A F).obj (op PUnit.unit)) :=
  (smallStrictBarNormalizedInclusionPointHomotopyEquiv A F).trans
    (HomotopyEquiv.ofIso (smallStrictBarTotalPointIso A F))

/-- 鎖ホモトピー同値の前向きの射は、同じ正規化比較の一点評価。 -/
theorem smallStrictBarNormalizedTotalPointHomotopyEquiv_hom (F : J ⥤ ModuleCategory A PUnit.{1}) :
    (smallStrictBarNormalizedTotalPointHomotopyEquiv A F).hom =
      (moduleEvaluation A PUnit.{1} PUnit.unit).map (smallStrictBarNormalizedTotalHom A F) := by
  change (moduleEvaluation A PUnit.{1} PUnit.unit).map
    (dgCoherentBarNormalizedModuleInclusionUnconditional A PUnit.{1} (smallStrictBarDiagram A F)) ≫
      (smallStrictBarTotalPointIso A F).hom =
    (moduleEvaluation A PUnit.{1} PUnit.unit).map (smallStrictBarNormalizedTotalHom A F)
  rw [smallStrictBarTotalPointIso_hom, ← CategoryTheory.Functor.map_comp]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
