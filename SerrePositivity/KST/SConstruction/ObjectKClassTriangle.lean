module
public import SerrePositivity.KST.SConstruction.ObjectBoundaryEdgeLoop

/-! # 実際の対象 K 類の S₂ 加法関係
概要：元の S₂ の三つの S₁ 評価対象の BF K 類に加法関係を与える。
方針：元の辺と対象 loop の照合を基本群の三角形関係へ代入し、零次群へ戻す。
規約：対象類は既存の objectKClass のまま。使われ方：cofiber 列と三角圏 K₀ の関係。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open scoped Simplicial

/-- 元の object S₁ の辺は、その評価対象の基本群での K 類の逆元を表す。 -/
lemma objectBoundaryEdge_objectKClass (X : StableModel.{u})
    (e : (objectSConstruction X.carrier) _⦋1⦌) :
    kZeroFundamentalGroupEquiv X
      (Additive.toMul (objectKClass X ((sOneComparison X.carrier).app _ e))) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (objectBoundaryEdge X e))⁻¹ := by
  let d : (coreSConstruction 1 X.carrier) _⦋0⦌ :=
    ⟨e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex
      (X := sConstruction 1 X.carrier) e⟩
  let B := (boundaryKanRealizationFunctor 0).obj X
  let t := (SphereSimplex.equiv B 1).symm (objectBoundaryEdge X e)
  have hv : (zeroRowLoopComparison 0 X).app _ d = PointedMapping.familyVertex t :=
    objectBoundaryEdge_loop X e
  have hc : SphereSimplex.componentEquiv B 0
      (objectKPiZeroClass X ((sOneComparison X.carrier).app _ e)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (objectBoundaryEdge X e) := by
    have hp := (objectKPiZeroClass_sOne X d).trans (congrArg SSet.π₀.mk hv)
    have hs := SphereSimplex.componentClass_familyVertex B 0 t
    have ht := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk ((SphereSimplex.equiv B 1).apply_symm_apply
      (objectBoundaryEdge X e))
    exact (congrArg (SphereSimplex.componentEquiv B 0) hp).trans (hs.trans ht)
  exact (kZeroFundamentalGroupEquiv_objectKClass X _).trans (congrArg Inv.inv hc)

/-- 元の全 gapped S₂ の長辺の対象類は、二つの短辺の対象類の和である。 -/
lemma objectKClass_sTwo (X : StableModel.{u})
    (q : (objectSConstruction X.carrier) _⦋2⦌) :
    objectKClass X ((sOneComparison X.carrier).app _ ((objectSConstruction X.carrier).δ 1 q)) =
      objectKClass X ((sOneComparison X.carrier).app _ ((objectSConstruction X.carrier).δ 2 q)) +
        objectKClass X ((sOneComparison X.carrier).app _
          ((objectSConstruction X.carrier).δ 0 q)) := by
  apply Additive.toMul.injective
  change Additive.toMul (objectKClass X _) =
    Additive.toMul (objectKClass X _) * Additive.toMul (objectKClass X _)
  apply (kZeroFundamentalGroupEquiv X).injective
  rw [map_mul, objectBoundaryEdge_objectKClass, objectBoundaryEdge_objectKClass,
    objectBoundaryEdge_objectKClass]
  rw [← objectBoundaryTriangle_mul]
  rw [mul_inv_rev]
  exact boundaryFundamentalGroup_mul_comm X _ _

end SerrePositivity.KST.SConstruction
