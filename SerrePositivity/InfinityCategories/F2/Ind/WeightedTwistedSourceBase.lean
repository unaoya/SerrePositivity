module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTwistedComparison

/-!
概要：元の twisted-arrow 全族の始点と添字を、同じ共同分類の底へ送る。
方針：引き戻しの twisted-arrow 始点を全係数で束ね、元の相対比較で両射影を検査。
規約：底と添字を厳密に保持。使われ方：同じ左端評価の相対延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C)

/-- 元の全 twisted arrow の始点を、元の反対底へ同時に射影する。 -/
def strictRightTwistedSourceProjection : strictRightTwistedElementsDiagram F ⟶
    (CategoryTheory.Functor.const I).obj C.op where
  app i := pullback.fst (edgewiseRight C) (F.obj i).val.hom ≫ edgewiseLeft C
  naturality i j f := by
    change pullback.lift _ _ _ ≫ (pullback.fst _ _ ≫ edgewiseLeft C) = _ ≫ 𝟙 _
    rw [← Category.assoc, pullback.lift_fst, Category.comp_id]

/-- 同じ相対比較は、元の全左端評価の係数射影を厳密に保つ。 -/
lemma strictRightTwistedComparison_source :
    strictRightTwistedComparison F ≫ strictRightTwistedSourceProjection F =
      strictRightTwistedLeftEvaluation F ≫
        leftFibrationDiagramProjection (F ⋙ rightFibrationOppositeOrdinary C) := by
  apply NatTrans.ext
  funext i
  change relativeEdgewiseRightComparison (F.obj i).val.hom ≫
      (pullback.fst _ _ ≫ edgewiseLeft C) =
    edgewiseLeft (F.obj i).val.left ≫ SSet.opFunctor.map (F.obj i).val.hom
  rw [← Category.assoc, relativeEdgewiseRightComparison_fst, edgewiseLeft_naturality]

/-- 元の反対底の始点と元の添字を保つ、同じ共同底への射。 -/
def weightedTwistedSourceBase : weightedNerve (strictRightTwistedElementsDiagram F) ⟶
    C.op ⊗ nerve I := weightedNerveParameterProjection (strictRightTwistedSourceProjection F)

/-- 元の全左端評価と相対比較は、同じ共同底上で厳密に可換。 -/
lemma weightedRightTwistedEvaluation_over :
    weightedRightTwistedEvaluation F ≫
      leftFibrationWeightedProjection (F ⋙ rightFibrationOppositeOrdinary C) =
        weightedRightTwistedComparison F ≫ weightedTwistedSourceBase F := by
  rw [weightedRightTwistedEvaluation_projection,
    ← strictRightTwistedComparison_source]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, weightedNerveParameterProjection, lift_fst,
      weightedTwistedSourceBase, weightedNerveParameter, weightedRightTwistedComparison,
      weightedNerveMap_comp]
  · simp only [Category.assoc, weightedNerveParameterProjection, lift_snd,
      weightedTwistedSourceBase, weightedRightTwistedComparison, weightedNerveMap_projection]

end SerrePositivity.InfinityCategories.F2.Ind
