module

public import SerrePositivity.KST.Spectra.FundamentalLoopNaturality
public import SerrePositivity.KST.Spectra.SpectrumCircleCompanionEdgewiseTetrahedra
public import SerrePositivity.KST.Spectra.SpectrumCircleCotensorReversalEvaluation

/-!
概要：元の解像三単体の差を基本群の逆元へ同定し、元の反転自己射で正符号の評価へ戻す。
方針：元の辺を保持する基本群–ホモトピー圏比較と、元の指定した評価 loop の式を使う。
規約：基点の移送を明示する。使われ方：元の錐全体の比較と apex 射の可逆性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleDifferenceHomKan (z : Sp.{u} _⦋0⦌) :
    KanComplex (circleEvaluationPointedHom z).right := by
  change KanComplex (mappingSpace
    (cotensor PointedSimplicialSet.circle (nativeCotensorInput PointedSimplicialSet.circle z).val)
    (nativeCotensorInput PointedSimplicialSet.circle z).val)
  infer_instance
local instance circleDifferenceHomEdgeIso (z : Sp.{u} _⦋0⦌)
    {a b : (circleEvaluationPointedHom z).right _⦋0⦌}
    (e : (circleEvaluationPointedHom z).right.Edge a b) :
    IsIso (SSet.HomotopyCategory.homMk e) :=
  IsGroupoid.all_isIso (C := hoFunctor.obj (circleEvaluationPointedHom z).right) _

/-- 元の companion の境界定数単体の辺は、元の解像三単体の同じ右辺。 -/
lemma circleCompanionSimplex_edge (z : Sp.{u} _⦋0⦌) :
    FundamentalLoop.edge (circleEvaluationCompanionSimplex z) =
      circleCompanionEdgewiseFramedEdge z .left 2 3 (by decide) := by
  apply SSet.Edge.ext
  exact (circleCompanionEdgewiseFramedEdge_companion z).symm

/-- 元の評価の境界定数単体の辺は、指定済みの普遍評価の loop の辺そのもの。 -/
lemma circleEvaluationLoopSimplex_edge (z : Sp.{u} _⦋0⦌) :
    FundamentalLoop.edge (circleEvaluationLoopSimplex z) =
      circleEvaluationHomEdge (nativeCotensorInput PointedSimplicialSet.circle z).val := by
  apply SSet.Edge.ext
  exact Equiv.apply_symm_apply _ _

/-- companion の元の基本群の類は、同じ元の解像三単体の右辺の類に移る。 -/
lemma circleCompanionClass_toHom (z : Sp.{u} _⦋0⦌) :
    FundamentalLoop.toHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (circleEvaluationCompanionSimplex z)) =
      SSet.HomotopyCategory.homMk
        (circleCompanionEdgewiseFramedEdge z .left 2 3 (by decide)) := by
  rw [FundamentalLoop.toHom_mk, circleCompanionSimplex_edge]

/-- 評価の元の基本群の類は、元の普遍評価の loop の辺の類に移る。 -/
lemma circleEvaluationClass_toHom (z : Sp.{u} _⦋0⦌) :
    FundamentalLoop.toHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (circleEvaluationLoopSimplex z)) =
      SSet.HomotopyCategory.homMk
        (circleEvaluationHomEdge (nativeCotensorInput PointedSimplicialSet.circle z).val) := by
  rw [FundamentalLoop.toHom_mk, circleEvaluationLoopSimplex_edge]

/-- 元の二つの零ホモトピーの差を、同じ基点の元のホモトピー圏の自己射として読む。 -/
def circleCompanionEdgewiseDifferenceHom (z : Sp.{u} _⦋0⦌) :
    SSet.HomotopyCategory.mk (circleEvaluationPointedHom z).basepoint ⟶
      SSet.HomotopyCategory.mk (circleEvaluationPointedHom z).basepoint :=
  inv (SSet.HomotopyCategory.homMk
      (circleCompanionEdgewiseFramedEdge z .right 0 1 (by decide))) ≫
    SSet.HomotopyCategory.homMk
      (circleCompanionEdgewiseFramedEdge z .left 0 1 (by decide))

/-- 元の二つの零ホモトピーの差は、同じ companion の基本群の逆元の像に厳密一致する。 -/
lemma circleCompanionEdgewise_difference_toHom (z : Sp.{u} _⦋0⦌) :
    circleCompanionEdgewiseDifferenceHom z =
      FundamentalLoop.toHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (circleEvaluationCompanionSimplex z))⁻¹) := by
  rw [circleCompanionEdgewiseDifferenceHom, FundamentalLoop.toHom_inv, circleCompanionClass_toHom]
  exact circleCompanionEdgewise_difference_inverse z

/-- 元の錐の差は、可逆な apex 反転の前合成で元の評価辺の正符号の類に移る。 -/
lemma circleCompanionEdgewise_difference_reversal (z : Sp.{u} _⦋0⦌) :
    FundamentalLoop.pointedHomMap (RawSpectrumMapping.pointedPre
      (circleCotensorReversal (nativeCotensorInput PointedSimplicialSet.circle z).val)
      (nativeCotensorInput PointedSimplicialSet.circle z).val.toKanSequence)
      (circleCompanionEdgewiseDifferenceHom z) =
      SSet.HomotopyCategory.homMk
        (circleEvaluationHomEdge (nativeCotensorInput PointedSimplicialSet.circle z).val) := by
  rw [circleCompanionEdgewise_difference_toHom, ← FundamentalLoop.toHom_pointed_map]
  erw [circleCotensorReversal_native_companion_difference]
  exact circleEvaluationClass_toHom z

end SerrePositivity.KST.Spectra.OmegaSpectrum
