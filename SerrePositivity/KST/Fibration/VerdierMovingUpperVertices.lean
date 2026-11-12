module
public import SerrePositivity.KST.Fibration.VerdierMovingUpperBoundaryEdges

/-!
概要：同じ動く上側全族の指定両端頂点を元の Verdier core Kan 対象へ厳密に戻す。
方針：元の二短辺の coherent な実辺の両端を読む。
規約：対象同型を選ばず、元の対象等号を保持する。
使われ方：K-6 c4 の全 native Hom の座標を元の指定二胞体へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (ℓ : (verdierMovingUpperLongSpace d) _⦋0⦌)
  (k : (Δ[1] : SSet.{u + 1}) _⦋0⦌)

/-- 概要：同じ上側族の全入力の始対象は元の Verdier 左端の core Kan 対象。
方針：同じ第一短辺の全一単体の始対象を評価する。
規約：対象そのものの等式。使われ方：native Hom 始域の指定座標。 -/
theorem verdierMovingUpperFamily_source :
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ) k)).obj ⟨ULift.up 0⟩ =
      stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 3)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ) k)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (show stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left) ⟶
          fullSRealizationKanObject d.left from
            _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)))).edge := by
    apply SSet.yonedaEquiv.symm.injective
    rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply]
    exact verdierMovingUpperFamily_firstEdge d ℓ k
  have ho := congrArg (fun e : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋1⦌ => e.obj ⟨ULift.up 0⟩) he
  exact ho

/-- 概要：同じ上側族の全入力の終対象は元の Verdier 右端の core Kan 対象。
方針：同じ第二短辺の標準 coherent 辺の終対象を評価する。
規約：元の動く第二短辺を保持。使われ方：native Hom 終域の指定座標。 -/
theorem verdierMovingUpperFamily_target :
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ) k)).obj ⟨ULift.up 2⟩ =
      stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (0 : Fin 3)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ) k)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((SimplicialCategory.homEquiv' (fullSRealizationKanObject d.left)
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right))).symm
          ((verdierMovingUpperLastFamily d).app (Opposite.op ⦋0⦌) k).down)).edge := by
    apply SSet.yonedaEquiv.symm.injective
    rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, verdierMovingUpperFamily_last, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coherentHomIntervalFamily_vertex]
    rfl
  have ho := congrArg (fun e : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋1⦌ => e.obj ⟨ULift.up 1⟩) he
  exact ho

end SerrePositivity.KST.Fibration
