module
public import SerrePositivity.KST.Fibration.VerdierMovingUpperShortFaces
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoherentHomFamilyVertices

/-!
概要：動く上側族の有限端点の二短辺を、元の実 Kan 射の coherent 辺へ厳密に戻す。
方針：同じ元の短辺族の標準 Hom 比較の頂点回収を消費する。
規約：辺を同型類へ弱めず、全一単体を回収する。
使われ方：K-6 c4 の指定有限二胞体の境界照合。
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

/-- 概要：全ての有限入力で第一短辺は元の実 core 包含の coherent 辺そのもの。
方針：同じ標準短辺族の回収を元の包含の豊穣頂点へ戻す。
規約：同じ全一単体。使われ方：両端に共通する指定第一短辺。 -/
theorem verdierMovingUpperFamily_firstEdge (k : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ) k =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (show stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left) ⟶
          fullSRealizationKanObject d.left from
            _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)))).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, verdierMovingUpperFamily_first,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coherentHomIntervalFamily_vertex, verdierMovingUpperFirstFamily_point]
  change SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
    ((SimplicialCategory.homEquiv' (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
      (fullSRealizationKanObject d.left)).symm
        ((SimplicialCategory.homEquiv' _ _)
          (show stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left) ⟶
            fullSRealizationKanObject d.left from
              _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)))))).edge = _
  rw [Equiv.symm_apply_apply]

/-- 概要：始端の第二短辺は元の上側実完全射の全 S• 作用の coherent 辺そのもの。
方針：元の第二短辺族の始端を同じ標準 Hom 比較の辺回収へ代入する。
規約：同じ実完全射。使われ方：指定上側始端二胞体との境界照合。 -/
theorem verdierMovingUpperFamily_first_lastEdge :
    stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (show fullSRealizationKanObject d.left ⟶
          stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right) from
            verdierOriginalFullSCompositeMap d 0)).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, verdierMovingUpperFamily_last,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coherentHomIntervalFamily_vertex, verdierMovingUpperLastFamily_first]
  change SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
    ((SimplicialCategory.homEquiv' (fullSRealizationKanObject d.left)
      (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right))).symm
        ((SimplicialCategory.homEquiv' _ _)
          (show fullSRealizationKanObject d.left ⟶
            stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right) from
              verdierOriginalFullSCompositeMap d 0)))).edge = _
  rw [Equiv.symm_apply_apply]

/-- 概要：終端の第二短辺は元の実包含・商の合成完全射の全 S• 作用の coherent 辺そのもの。
方針：元の第二短辺族の終端を同じ標準 Hom 比較の辺回収へ代入する。
規約：同じ実合成端。使われ方：指定上側終端二胞体との境界照合。 -/
theorem verdierMovingUpperFamily_last_lastEdge :
    stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (show fullSRealizationKanObject d.left ⟶
          stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right) from
            verdierOriginalFullSCompositeMap d 1)).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, verdierMovingUpperFamily_last,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coherentHomIntervalFamily_vertex, verdierMovingUpperLastFamily_last]
  change SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
    ((SimplicialCategory.homEquiv' (fullSRealizationKanObject d.left)
      (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right))).symm
        ((SimplicialCategory.homEquiv' _ _)
          (show fullSRealizationKanObject d.left ⟶
            stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right) from
              verdierOriginalFullSCompositeMap d 1)))).edge = _
  rw [Equiv.symm_apply_apply]

end SerrePositivity.KST.Fibration
