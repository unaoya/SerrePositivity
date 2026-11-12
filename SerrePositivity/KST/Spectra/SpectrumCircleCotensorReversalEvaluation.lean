module

public import SerrePositivity.KST.Spectra.SpectrumCircleCotensorReversal
public import SerrePositivity.KST.Spectra.SpectrumCircleCompanionBKPoint

/-!
概要：構成した円 cotensor の反転自己射を、元の普遍評価の loop の逆元へ照合する。
方針：元の恒等射の比較像と評価点の式を、円の単体の元の表示へ移す。
規約：元の評価の生成 loop を保持。使われ方：元の評価錐と companion 錐の符号比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 恒等射の元の成分の基本群表示は、元の普遍評価の円の単体の類そのもの。 -/
lemma circleCotensorComponentClass_identity (Y : OmegaSpectrum.{u}) :
    circleCotensorComponentClass (cotensor PointedSimplicialSet.circle Y) Y
      (SpectrumMappingAcyclic.component (𝟙 (cotensor PointedSimplicialSet.circle Y))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (SphereSimplex.equiv
      (RawSpectrumMapping.pointedSpace (cotensor PointedSimplicialSet.circle Y) Y.toKanSequence)
      1 (cotensorEvaluation PointedSimplicialSet.circle Y)) := by
  have h := congrArg (SSet.unitHomEquiv _) (circleEvaluationLoopPointMap_eq Y)
  rw [circleEvaluationLoopPointMap_vertex, PointedMapping.unitHomEquiv_post] at h
  change PointedMapping.familyVertex (cotensorEvaluation PointedSimplicialSet.circle Y) =
    (cotensorMappingEquivalence (cotensor PointedSimplicialSet.circle Y) Y
      PointedSimplicialSet.circle).hom.app _
        (vertexOfHom (𝟙 (cotensor PointedSimplicialSet.circle Y))) at h
  unfold circleCotensorComponentClass
  rw [Function.comp_apply, SpectrumMappingAcyclic.component, mapπ₀_mk, ← h,
    SphereSimplex.componentClass_familyVertex]

/-- 元の符号反転の前合成は、元の普遍評価の基本群の類をその逆元へ送る。 -/
lemma circleCotensorReversal_evaluation (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map
      (RawSpectrumMapping.pointedPre (circleCotensorReversal Y) Y.toKanSequence).right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint
        (RawSpectrumMapping.pointedPre (circleCotensorReversal Y) Y.toKanSequence))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (SphereSimplex.equiv
        (RawSpectrumMapping.pointedSpace (cotensor PointedSimplicialSet.circle Y) Y.toKanSequence)
        1 (cotensorEvaluation PointedSimplicialSet.circle Y))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (SphereSimplex.equiv
        (RawSpectrumMapping.pointedSpace (cotensor PointedSimplicialSet.circle Y) Y.toKanSequence)
        1 (cotensorEvaluation PointedSimplicialSet.circle Y)))⁻¹ := by
  have h := circleCotensorComponentClass_pre (circleCotensorReversal Y) Y
    (SpectrumMappingAcyclic.component (𝟙 (cotensor PointedSimplicialSet.circle Y)))
  rw [SpectrumMappingAcyclic.pre_component, Category.comp_id, circleCotensorReversal_class,
    circleCotensorComponentClass_identity] at h
  exact h.symm

local instance circleCotensorReversalEvaluationHomKan (z : Sp.{u} _⦋0⦌) :
    KanComplex (circleEvaluationPointedHom z).right := by
  change KanComplex (mappingSpace
    (cotensor PointedSimplicialSet.circle (nativeCotensorInput PointedSimplicialSet.circle z).val)
    (nativeCotensorInput PointedSimplicialSet.circle z).val)
  infer_instance

/-- 元の評価四角形で指定済みの loop も、同じ BF 自己射の前合成で逆元に移る。 -/
lemma circleCotensorReversal_native_loop (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map
      (RawSpectrumMapping.pointedPre
        (circleCotensorReversal (nativeCotensorInput PointedSimplicialSet.circle z).val)
        (nativeCotensorInput PointedSimplicialSet.circle z).val.toKanSequence).right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (RawSpectrumMapping.pointedPre
        (circleCotensorReversal (nativeCotensorInput PointedSimplicialSet.circle z).val)
        (nativeCotensorInput PointedSimplicialSet.circle z).val.toKanSequence))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (circleEvaluationLoopSimplex z)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (circleEvaluationLoopSimplex z))⁻¹ := by
  have h := circleCotensorReversal_evaluation
    (nativeCotensorInput PointedSimplicialSet.circle z).val
  erw [circleEvaluationLoopSimplex_evaluation] at h
  exact h

/-- 反転した companion の差の逆元は、同じ前合成で元の評価 loop の正符号の類へ戻る。 -/
lemma circleCotensorReversal_native_companion_difference (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map
      (RawSpectrumMapping.pointedPre
        (circleCotensorReversal (nativeCotensorInput PointedSimplicialSet.circle z).val)
        (nativeCotensorInput PointedSimplicialSet.circle z).val.toKanSequence).right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (RawSpectrumMapping.pointedPre
        (circleCotensorReversal (nativeCotensorInput PointedSimplicialSet.circle z).val)
        (nativeCotensorInput PointedSimplicialSet.circle z).val.toKanSequence))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (circleEvaluationCompanionSimplex z))⁻¹) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (circleEvaluationLoopSimplex z) := by
  rw [map_inv, circleEvaluationCompanion_loop_class, circleCotensorReversal_native_loop, inv_inv]

end SerrePositivity.KST.Spectra.OmegaSpectrum
