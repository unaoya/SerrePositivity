module

public import SerrePositivity.KST.Spectra.SpectrumCircleComparisonBoundaryDifference
public import SerrePositivity.KST.Spectra.PointedHomDifferenceNaturality
public import SerrePositivity.KST.Spectra.SpectrumCircleEdgewiseDifferenceHom

/-!
概要：元の比較右辺の差は、元の apex 自己射による companion の差の前合成。
方針：右辺の一単体の式を元の edgewise 辺の像へ戻し、基点つき自然性を適用する。
規約：元の自己射と同じ Hom の基本群を保持。使われ方：反転自己同値との成分比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleComparisonActionHomKan (z : Sp.{u} _⦋0⦌) :
    KanComplex (circleEvaluationPointedHom z).right := by
  change KanComplex (mappingSpace
    (cotensor PointedSimplicialSet.circle (nativeCotensorInput PointedSimplicialSet.circle z).val)
    (nativeCotensorInput PointedSimplicialSet.circle z).val)
  infer_instance
local instance circleComparisonActionEdgeIso (z : Sp.{u} _⦋0⦌)
    {a b : (circleEvaluationPointedHom z).right _⦋0⦌}
    (e : (circleEvaluationPointedHom z).right.Edge a b) :
    IsIso (SSet.HomotopyCategory.homMk e) :=
  IsGroupoid.all_isIso (C := hoFunctor.obj (circleEvaluationPointedHom z).right) _

/-- 元の比較正方形の右辺の一単体は、元の edgewise 辺の前合成による像。 -/
lemma circleCompanionComparisonRightEdge_action (z : Sp.{u} _⦋0⦌)
    (k : Limits.WalkingPair) :
    (RawSpectrumMapping.pointedPre (circleCompanionConeComparisonHom z)
      (nativeCotensorInput PointedSimplicialSet.circle z).val.toKanSequence).right.app
        (Opposite.op ⦋1⦌) (circleCompanionEdgewiseFramedEdge z k 0 1 (of_decide_eq_true rfl)).edge =
    (circleCompanionComparisonRightEdge z k).edge := by
  have h := congrArg SSet.yonedaEquiv
    (circleCompanionComparisonRawHomSquare_includeFirst z k)
  rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.right_yoneda, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
    circleCompanionReflectedTriangle_trace, Category.assoc, SSet.yonedaEquiv_comp,
    Equiv.apply_symm_apply] at h
  simp only [NatTrans.comp_app, types_comp_apply] at h
  rw [rawPointedPre_right]
  exact h.symm

/-- 元の companion の差の前合成は、元の companion loop の正符号の類。 -/
lemma circleCompanionComparisonDifference_action (z : Sp.{u} _⦋0⦌) :
    FundamentalLoop.pointedHomMap (RawSpectrumMapping.pointedPre
      (circleCompanionConeComparisonHom z)
      (nativeCotensorInput PointedSimplicialSet.circle z).val.toKanSequence)
        (circleCompanionEdgewiseDifferenceHom z) =
    FundamentalLoop.toHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (circleEvaluationCompanionSimplex z)) := by
  let sourceReferenceIso : IsIso (SSet.HomotopyCategory.homMk
      (circleCompanionEdgewiseFramedEdge z .right 0 1 (of_decide_eq_true rfl))) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj (circleEvaluationPointedHom z).right) _
  let targetReferenceIso : IsIso (SSet.HomotopyCategory.homMk
      (circleCompanionComparisonRightEdge z .right)) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj (circleEvaluationPointedHom z).right) _
  have h := FundamentalLoop.pointedHomMap_difference
    (RawSpectrumMapping.pointedPre (circleCompanionConeComparisonHom z)
      (nativeCotensorInput PointedSimplicialSet.circle z).val.toKanSequence)
    (circleCompanionEdgewiseFramedEdge z .right 0 1 (of_decide_eq_true rfl))
    (circleCompanionEdgewiseFramedEdge z .left 0 1 (of_decide_eq_true rfl))
    (circleCompanionComparisonRightEdge z .right)
    (circleCompanionComparisonRightEdge z .left)
    (circleCompanionComparisonRightEdge_action z .right)
    (circleCompanionComparisonRightEdge_action z .left)
  exact h.trans (circleCompanionComparisonBoundary_difference z)

end SerrePositivity.KST.Spectra.OmegaSpectrum
