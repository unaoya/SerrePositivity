module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.KanDiagramLeftHomCutNaturality
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.KanLeftCutHead

/-!
概要：実際の左区間上の weighted head は、任意の面・退化と可換。
方針：時刻零・一の明示式を使い、元の係数と切断係数の自然性に帰着する。
規約：tail の退化拡張全体の自然性は仮定しない。
使われ方：始点固定 cone の全単体を一つの pointed prism へ貼り合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors


/-- 左区間上の実際の head は、対象の厳密な表示を移せば全ての面・退化と可換。 -/
lemma weightedKanLeftCutHead_reindex {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (σ : (nerve I) _⦋n⦌)
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (j : Fin (m + 1)) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstReindexFunctor α.toOrderHom j) ≫
      _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutHead F G x σ τ s t (α.toOrderHom j) ≫
        eqToHom (congrArg (SimplicialCategory.sHom x)
          (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramLeftHomCutSimplex_obj_reindex F G α σ s t j)) =
    _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutHead F G x ((nerve I).map α.op σ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeightRestriction α ≫
        Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor τ)
      ((SimplicialCategory.sHom F G).op.map α.op s) (Δ[1].map α.op t) j := by
  by_cases hj : (stdSimplex.objEquiv t).toOrderHom (α.toOrderHom j) = 0
  · have hjm : (stdSimplex.objEquiv (Δ[1].map α.op t)).toOrderHom j = 0 := hj
    simp only [_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutHead, dite_eq_left hj, dite_eq_left hjm,
      Category.assoc, eqToHom_trans]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient_reindex]
  · have hjm : (stdSimplex.objEquiv (Δ[1].map α.op t)).toOrderHom j ≠ 0 := hj
    simp only [_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.weightedKanLeftCutHead, dite_eq_right hj, dite_eq_right hjm,
      Category.assoc, eqToHom_trans]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.weightedConeCutCoefficient_reindex]
    rw [← Category.assoc (stdSimplex.map α), SSet.yonedaEquiv_symm_naturality_left]
    rfl

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
