module
public import SerrePositivity.KST.SConstruction.IteratedRealizationKanNaturality
public import SerrePositivity.KST.SConstruction.AssemblyAdjointEvaluation
public import SerrePositivity.KST.SConstruction.ZeroRowLoopComparison

/-! # 元の零行 loop 射の完全関手に関する自然性
概要：元の区間族から作った具体的 loop 射は、完全関手と既存の境界商の Kan 写像に厳密に自然。
方針：円の元の区間上で評価し、元の組み立てと Kan 比較の自然性を適用する。
規約：元の loop 射を置き換えない。使われ方：対象の K 類の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 元の零行 loop 射は正の反復だけでなく r=0 を含めて完全関手について自然。 -/
lemma zeroRowLoopComparison_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (iteratedSRealizationDiagramMap r f).app (Opposite.op ⦋1⦌) ≫ zeroRowLoopComparison r Y =
      zeroRowLoopComparison r X ≫
        ((PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map
          ((boundaryKanRealizationFunctor r).map f)).right := by
  apply loop_interval_hom_ext
  have hp := loop_interval_precomp ((boundaryKanRealizationFunctor r).obj Y)
    ((iteratedSRealizationDiagramMap r f).app (Opposite.op ⦋1⦌)) (zeroRowLoopComparison r Y)
  have hY : (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷
      (iteratedSRealizationDiagram r Y).obj (Opposite.op ⦋1⦌)) ≫
      MonoidalClosed.uncurry (zeroRowLoopComparison r Y ≫
        PointedObject.basedHomι PointedSimplicialSet.circle.{u}
          ((boundaryKanRealizationFunctor r).obj Y)) =
      diagonalAssembly 1 (iteratedSRealizationDiagram r Y) ≫ iteratedRealizationToKan r Y :=
    zeroRowLoopComparison_assembly r Y
  rw [hY] at hp
  have hq := loop_interval_postcomp (zeroRowLoopComparison r X)
    ((boundaryKanRealizationFunctor r).map f)
  rw [zeroRowLoopComparison_assembly] at hq
  refine hp.trans (Eq.trans ?_ hq.symm)
  rw [← Category.assoc, diagonalAssembly_naturality]
  simp only [Category.assoc]
  change diagonalAssembly 1 (iteratedSRealizationDiagram r X) ≫
    iteratedSRealizationMap r f ≫ iteratedRealizationToKan r Y = _
  rw [iteratedRealizationToKan_naturality]

end SerrePositivity.KST.SConstruction
