module

public import SerrePositivity.EInfinity.FrameHom.FrameRoofCornerEvaluation
public import SerrePositivity.EInfinity.FrameHom.FrameRoofFiberPinchedProjection
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Stable.SpanHomotopyGluing

/-!
# 元の corner 評価の同じ qY slice 内の実ホモトピー

概要：元の全錐から評価後の pinched 族まで、同じ slice 内の実円柱を保持する。
方針：元の全体評価の円柱を制限し、元の両 fiber 同型の射影式で終端を同定する。
規約：元の全時刻・全単体を保ち、辺ごとの比較で代用しない。
使われ方：実 ProductHomMap の全三角形の slice prism 表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Limits Opposite SSet MonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)
  [LeftFibration (roofTargetProjection A Y q)]

lemma roofTargetSlicePointIso_projection : (roofTargetSlicePointIso Y q).hom ≫
    sliceOverProjection (SSet.yonedaEquiv.symm (q.app (op ⦋0⦌) (nerveVertex Y))) =
      sliceOverProjection (SSet.yonedaEquiv.symm (nerveVertex Y) ≫ q) :=
  SerrePositivity.InfinityCategories.F1B.sliceOverProjection_eqTransport (roofTargetPoint q (nerveVertex Y))

def roofCornerSourceSliceMap :
    sliceOverCorner (SSet.yonedaEquiv.symm b) (roofTargetProjection A Y q) ⟶
      sliceOver (SSet.yonedaEquiv.symm (q.app (op ⦋0⦌) (nerveVertex Y))) :=
  pullback.snd _ _ ≫ pullback.fst _ _ ≫ (roofTargetSlicePointIso Y q).hom

lemma roofCornerEvaluation_slice : roofCornerEvaluation A Y q b ≫
    pinchedFamilySlice E (q.app (op ⦋0⦌) (nerveVertex (A.obj (roofTargetDegree A Y q b))))
      (q.app (op ⦋0⦌) (nerveVertex Y)) =
    roofCornerNormalizationMap A Y q b ≫ (roofCornerTerminalEvaluation A Y q b).evaluation ≫
      vertexFiberι (roofCornerNormalizedProjection A Y q b) (roofCornerTerminal A Y q b) ≫
        pullback.fst _ _ ≫ pullback.fst _ _ ≫ (roofTargetSlicePointIso Y q).hom := by
  have h := roofCornerTerminalFiberIso_source A Y q b
  simp only [roofCornerEvaluation, Category.assoc]
  rw [roofTargetFiberPinchedIso_slice, reassoc_of% h]

def roofCornerEvaluationSliceHomotopy : SSet.Homotopy (roofCornerSourceSliceMap A Y q b)
    (roofCornerEvaluation A Y q b ≫
      pinchedFamilySlice E (q.app (op ⦋0⦌) (nerveVertex (A.obj (roofTargetDegree A Y q b))))
        (q.app (op ⦋0⦌) (nerveVertex Y))) := by
  let v := pullback.fst (roofTargetProjection A Y q)
    (nerveMap (Over.forget (roofTargetDegree A Y q b))) ≫
      pullback.fst (sliceOverProjection (SSet.yonedaEquiv.symm (nerveVertex Y) ≫ q))
        (nerveMap A ≫ q) ≫ (roofTargetSlicePointIso Y q).hom
  let H := functorHomotopyPostcomp
    (functorHomotopyPrecomp (roofCornerTerminalEvaluation A Y q b).homotopy
      (roofCornerNormalizationMap A Y q b)) v
  apply stableHomotopyRetarget H
  · dsimp only [v, roofCornerSourceSliceMap]
    simp only [Category.comp_id, ← Category.assoc]
    rw [roofCornerNormalizationMap_source]
  · dsimp only [v]
    simpa only [Category.assoc] using (roofCornerEvaluation_slice A Y q b).symm

lemma roofCornerEvaluationSliceHomotopy_h : (roofCornerEvaluationSliceHomotopy A Y q b).h =
    (roofCornerNormalizationMap A Y q b ▷ (Δ[1] : SSet.{u})) ≫
      (roofCornerTerminalEvaluation A Y q b).homotopy.h ≫
        pullback.fst _ _ ≫ pullback.fst _ _ ≫ (roofTargetSlicePointIso Y q).hom := rfl

end SerrePositivity.EInfinity.FrameHom.FrameArrows
