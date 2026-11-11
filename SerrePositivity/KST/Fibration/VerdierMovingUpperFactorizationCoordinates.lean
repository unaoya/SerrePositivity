module
public import SerrePositivity.KST.Fibration.ZeroMiddleNativeUpperBoundary
public import SerrePositivity.KST.Fibration.VerdierMovingUpperBoundaryEdges
public import SerrePositivity.KST.Fibration.ZeroMiddleVerdierCoordinates

/-!
概要：動く上側の始端と実 (9b) 制御上側の二短辺を、同じ Verdier 両端で厳密に照合する。
方針：同じ元の対象等号と全 S• 合成実射の HEq を coherent な辺の等号へ戻す。
規約：新しい対象同型や存在仮定を加えない。
使われ方：K-6 c4 の指定有限二胞体照合に必要な二境界条件。
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

private theorem nativeKanEdge_coordinate {A B A' B' : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).edge := by
  cases hA
  cases hB
  obtain rfl := eq_of_heq h
  rfl

private theorem nativeCoreFullInclusion_heq {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (h : A = B) :
    HEq (show stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A) ⟶ fullSRealizationKanObject A from
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A)))
      (show stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from B) ⟶ fullSRealizationKanObject B from
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from B))) := by
  cases h
  rfl

/-- 概要：制御因子分解の第一短辺は、同じ Verdier 左端の元の実 core 包含の辺。
方針：同じ元の左端等号だけで実射と coherent な辺を輸送する。
規約：新しい対象比較を選ばない。使われ方：再構成始端と制御欠面の第一境界照合。 -/
theorem verdierUpperControlled_firstEdge_coordinate (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (show stableCoreSingleKanObject ((verdierUpperTriangle d).obj ⟨ULift.up 0⟩) ⟶
        fullSRealizationKanObject ((verdierUpperTriangle d).obj ⟨ULift.up 0⟩) from
          zeroMiddleControlledFirstMap (verdierUpperTriangle d))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (show stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left) ⟶
          fullSRealizationKanObject d.left from
            _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)))).edge := by
  have hA := (verdierUpperTriangle_source d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.left_eq)
  exact nativeKanEdge_coordinate
    (congrArg (fun A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} => stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A)) hA)
    (congrArg fullSRealizationKanObject hA) _ _ (nativeCoreFullInclusion_heq hA)

/-- 概要：制御因子分解の第二短辺は元の Verdier 上側合成実射の同じ全 S• 辺。
方針：既存の元の実合成射の HEq を同じ両端の coherent 辺へ送る。
規約：元の実完全射を保持。使われ方：再構成始端と制御欠面の第二境界照合。 -/
theorem verdierUpperControlled_lastEdge_coordinate (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (zeroMiddleFullSKanComposite (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (verdierOriginalFullSCompositeMap d 0)).edge := by
  have hA := (verdierUpperTriangle_source d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.left_eq)
  have hC := (verdierUpperTriangle_target d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.right_eq)
  have h : HEq (zeroMiddleFullSKanComposite (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d)) (verdierOriginalFullSCompositeMap d 0) :=
    zeroMiddleFullSKanComposite_verdier_original_heq d
  exact nativeKanEdge_coordinate (congrArg fullSRealizationKanObject hA)
    (congrArg (fun C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} => stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C)) hC)
    _ _ h

variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (ℓ : (verdierMovingUpperLongSpace d) _⦋0⦌)

/-- 概要：動く実上側の始端と同じ実 (9b) 欠面は第一短辺を厳密に共有する。
方針：両者の元の第一短辺回収を同じ対象座標へ戻す。
規約：全一単体の一致。使われ方：有限二胞体の外延性への第一入力。 -/
theorem verdierMovingUpperFamily_first_controlled_firstFace :
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
      (zeroMiddleNativeUpperFamily (verdierUpperTriangle d)
        (verdierUpperTriangle_middle_isZero d) (Δ[1] : SSet.{u + 1}))
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  have h := congrArg (fun F => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (zeroMiddleNativeUpperFamily_first (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d) (Δ[1] : SSet.{u + 1}))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_constant] at h
  rw [verdierMovingUpperFamily_firstEdge, h]
  exact congrArg SSet.yonedaEquiv.symm (verdierUpperControlled_firstEdge_coordinate d).symm

/-- 概要：動く実上側の始端と同じ実 (9b) 欠面は第二短辺を厳密に共有する。
方針：両者の元の全 S• 合成実射回収を同じ対象座標へ戻す。
規約：全一単体の一致。使われ方：有限二胞体の外延性への第二入力。 -/
theorem verdierMovingUpperFamily_first_controlled_lastFace :
    stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
    stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
      (zeroMiddleNativeUpperFamily (verdierUpperTriangle d)
        (verdierUpperTriangle_middle_isZero d) (Δ[1] : SSet.{u + 1}))
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  have h := congrArg (fun F => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (zeroMiddleNativeUpperFamily_last (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d) (Δ[1] : SSet.{u + 1}))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_constant] at h
  rw [verdierMovingUpperFamily_first_lastEdge, h]
  exact congrArg SSet.yonedaEquiv.symm (verdierUpperControlled_lastEdge_coordinate d).symm

end SerrePositivity.KST.Fibration
