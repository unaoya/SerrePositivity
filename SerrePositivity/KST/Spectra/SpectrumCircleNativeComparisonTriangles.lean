module

public import SerrePositivity.KST.Spectra.SpectrumCircleComparisonCellObjects
public import SerrePositivity.KST.Spectra.SpectrumNativeZeroTriangleTrace

/-!
概要：元の比較正方形の始点の三角形を、元の評価四角形の companion と参照面へ戻す。
方針：元の cospan の形状同型の二辺と、正方形の元の二つの cone セルを計算する。
規約：元の評価四角形を保持。使われ方：比較 Hom 正方形の左辺の厳密な照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance nativeComparisonTrianglesSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の strict cospan の二辺は、形状同型で元のホーンの二辺そのものへ移る。 -/
lemma circleConeComparisonParameter_horn (k : Limits.WalkingPair) :
    circleConeComparisonParameter.{u} k ≫ CospanShape.strictCospanHornIso.hom =
      match k with
      | .left => horn₂₂.ι₀₂
      | .right => horn₂₂.ι₁₂ := by
  cases k
  all_goals
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, circleConeComparisonParameter, Equiv.apply_symm_apply]
    apply Subtype.ext
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl

/-- 元の始点の錐の三角形は、元の四角形の lower/upper の三角形そのもの。 -/
lemma circleNativeComparisonTriangle_square (z : Sp.{u} _⦋0⦌) (k : Limits.WalkingPair) :
    circleNativeComparisonTriangle z k = SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle (match k with | .left => 1 | .right => 0) ≫
        nativeCircleEvaluationSquare z) := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (circleConeComparisonParameter k) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) CospanShape.strictCospanHornIso.hom ≫
    (nativeCirclePointLoopCone z).val) = _
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _) _, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp,
    circleConeComparisonParameter_horn]
  cases k
  · change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleLeft ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫
      nativeCircleEvaluationSquare z) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_left]
  · change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleRight ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫
      nativeCircleEvaluationSquare z) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_right]

/-- 左の元の始点の三角形は、元の同じ companion 三角形の頂点評価。 -/
lemma circleNativeComparisonTriangle_left (z : Sp.{u} _⦋0⦌) :
    circleNativeComparisonTriangle z .left =
      SSet.yonedaEquiv (circleZeroCompanionTriangle ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt z) := by
  rw [circleNativeComparisonTriangle_square, nativeCircleEvaluationSquare_evaluation,
    ← Category.assoc, circleEvaluationFunctorSquare_lower]

/-- 右の元の始点の三角形は、元の同じ参照零三角形の頂点評価。 -/
lemma circleNativeComparisonTriangle_right (z : Sp.{u} _⦋0⦌) :
    circleNativeComparisonTriangle z .right =
      SSet.yonedaEquiv (circleZeroFunctorTriangle ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt z) := by
  rw [circleNativeComparisonTriangle_square, nativeCircleEvaluationSquare_evaluation,
    ← Category.assoc, circleEvaluationFunctorSquare_upper]

/-- 元の比較正方形の左側では、元の companion の Hom 経路そのものが現れる。 -/
lemma circleCompanionComparisonRawHomSquare_skipFirst_left (z : Sp.{u} _⦋0⦌) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      circleCompanionComparisonRawHomSquare z .left = circleEvaluationCompanionHomPath z := by
  unfold circleCompanionComparisonRawHomSquare
  rw [← Category.assoc, circleCompanionComparisonHomSquare_skipFirst, Category.assoc]
  have h := CoherentPathCoordinates.triangleTrace_transport
    (circleNativeComparisonTriangle_left z)
    ((circleNativeComparisonTriangle_hom z .left).trans (circleComparisonCentralHom_eq z))
    ((congrArg (fun s : Sp.{u} _⦋2⦌ ↦
      SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
      (circleEvaluationTetrahedronAt_one z)).symm.trans
        (congrArg (fun s : Sp.{u} _⦋2⦌ ↦
          SimplicialCategory.sHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
            (circleEvaluationTetrahedronAt_two z)))
  unfold circleEvaluationCompanionHomPath
  simp only [eqToHom_trans]
  exact h

end SerrePositivity.KST.Spectra.OmegaSpectrum
