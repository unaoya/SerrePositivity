module
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorSuspension
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationComparisonProjection
public import SerrePositivity.InfinityCategories.Stable.SuspensionSourceHom

/-! # 完全関手の懸垂比較の始点成分

概要：完全関手の前後で選んだ suspension 図式の比較は始点を恒等に保つ。
方針：trivial Kan fibration の比較の射影の恒等式を適用する。
規約：始点と終点の表示による等号輸送を Arrow に含める。
使われ方：完全関手と懸垂の対象比較・cofiber 接続射の両立。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：懸垂図式の族の標準比較の各成分は始点で元の関手の像の恒等射になる。
方針：標準比較の底への成分を計算し、始点評価の切断の式を使う。
規約：安定な quasicategory 間の完全関手。使われ方：対象比較との一意な照合。 -/
lemma exactFunctorSuspensionFamilyIso_source_component_arrow {X Y : SSet.{u}}
    [Quasicategory X] [IsStable X] [Quasicategory Y] [IsStable Y]
    (F : X ⟶ Y) [IsExactFunctor F] (x : X _⦋0⦌) :
    Arrow.mk ((hoFunctor.map (suspensionDiagramEvaluation Y 0 0)).toFunctor.map
      ((exactFunctorSuspensionFamilyIso F).toNatIso.hom.app (SSet.HomotopyCategory.mk x))) =
    Arrow.mk (𝟙 (SSet.HomotopyCategory.mk (F.app (Opposite.op ⦋0⦌) x) : hoFunctor.obj Y)) := by
  have hsource :
      ((suspensionDiagramSourceEquivalence X).inv ≫ exactFunctorSuspensionDiagrams F) ≫
          suspensionDiagramEvaluation Y 0 0 =
        (F ≫ (suspensionDiagramSourceEquivalence Y).inv) ≫
          suspensionDiagramEvaluation Y 0 0 := by
    rw [Category.assoc, exactFunctorSuspensionDiagrams_evaluation, ← Category.assoc,
      suspensionDiagramSourceEquivalence_inv_source, Category.id_comp,
      Category.assoc, suspensionDiagramSourceEquivalence_inv_source, Category.comp_id]
  have h := functorIsoOfTrivialKanFibration_projection_component_arrow
    (suspensionDiagramEvaluation Y 0 0)
    ((suspensionDiagramSourceEquivalence X).inv ≫ exactFunctorSuspensionDiagrams F)
    (F ≫ (suspensionDiagramSourceEquivalence Y).inv) hsource x
  have hz : ((F ≫ (suspensionDiagramSourceEquivalence Y).inv) ≫
      suspensionDiagramEvaluation Y 0 0).app (Opposite.op ⦋0⦌) x =
      F.app (Opposite.op ⦋0⦌) x := by
    rw [Category.assoc, suspensionDiagramSourceEquivalence_inv_source, Category.comp_id]
  exact h.trans (congrArg (fun y : Y _⦋0⦌ =>
    Arrow.mk (𝟙 (SSet.HomotopyCategory.mk y : hoFunctor.obj Y))) hz)

end SerrePositivity.InfinityCategories
