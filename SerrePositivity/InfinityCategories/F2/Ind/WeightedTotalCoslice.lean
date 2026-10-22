module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightFibrationTotalAssembly
public import SerrePositivity.InfinityCategories.Core.CosliceEndpointFibration
public import SerrePositivity.InfinityCategories.F1.LeftFiberKan

/-!
概要：元の全空間比較の、元の指定頂点の下の coslice 引き戻し。
方針：同じ全比較と native coslice の射影を引き戻す。
規約：filtered 性や cofinality は別工程。使われ方：Quillen A の元の試験対象。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (x : (colimit (rightFibrationTotalDiagram F)) _⦋0⦌)

/-- 元の全比較と同じ指定頂点の native coslice の引き戻し。 -/
def weightedTotalCoslice : SSet.{u} :=
  pullback (strictRightFibrationTotalAssembly F)
    (sliceUnderProjection (SSet.yonedaEquiv.symm x))

/-- 同じ全比較の coslice 引き戻しは quasicategory。 -/
instance weightedTotalCoslice_quasicategory [Quasicategory C] [IsFiltered I] :
    Quasicategory (weightedTotalCoslice F x) := by
  change Quasicategory (pullback (strictRightFibrationTotalAssembly F)
    (sliceUnderProjection (SSet.yonedaEquiv.symm x)))
  have : Quasicategory (colimit (rightFibrationTotalDiagram F)) :=
    quasicategory_of_innerFibration (strictRightFibrationColimitProjection F)
  have : LeftFibration (pullback.fst (strictRightFibrationTotalAssembly F)
      (sliceUnderProjection (SSet.yonedaEquiv.symm x))) :=
    ⟨leftFibrations.pullback_fst _ _ (LeftFibration.mem (p :=
      sliceUnderProjection (SSet.yonedaEquiv.symm x)))⟩
  have : InnerFibration (pullback.fst (strictRightFibrationTotalAssembly F)
      (sliceUnderProjection (SSet.yonedaEquiv.symm x))) := leftFibration_innerFibration _
  exact quasicategory_of_innerFibration (pullback.fst (strictRightFibrationTotalAssembly F)
    (sliceUnderProjection (SSet.yonedaEquiv.symm x)))

end SerrePositivity.InfinityCategories.F2.Ind
