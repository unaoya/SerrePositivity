module

public import SerrePositivity.KST.Spectra.PointedIhomParameterRestriction
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedUnitTriangle

/-!
概要：移した単位三角形の対角辺を、元の次段の全パラメータ評価区間の構造制限へ同定する。
方針：元のスペクトルの段条件を内部 Hom の作用の制限四角形へ渡す。
規約：端点の成分類ではなく同じ実辺を照合する。使われ方：単位側の実構造正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- BF 射影の端点表示を変えても、元の次段延長区間の同じ制限辺を保持する。 -/
lemma tracedSignedLoopUnitRestrictionInterval_path (Y : OmegaSpectrum.{u}) (n : ℕ) :
    (tracedSignedLoopUnitRestrictionInterval Y n).path =
      ((tracedSignedLoopUnitComparison Y (n + 1)).pre (Y.sigma n)).path := rfl

end OmegaSpectrum
namespace RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 元の厳密な段条件を、単位区間へ入力する二つの評価の厳密四角形として読む。 -/
lemma kanAdjointTracedUnitEvaluation_square (n : ℕ) :
    (φ ≫ pointedEvaluation X Y.toKanSequence (n + 1)) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space =
    kanAdjointStructureInput X Y φ n ≫
      PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.sigma n) := by
  rw [Category.assoc]
  erw [pointedEvaluation_condition X Y.toKanSequence n]
  simp only [kanAdjointStructureInput, pointedStep, Category.assoc]
  rfl

/-- 同じ単位二単体の対角辺は、次段評価区間の元の構造射への制限そのもの。 -/
lemma kanAdjointTracedUnitParameterTriangle_one_evaluation (n : ℕ) :
    stdSimplex.δ (1 : Fin 3) ≫ kanAdjointTracedUnitParameterTriangle X Y φ n =
      ((kanAdjointTracedUnitEvaluationInterval X Y φ (n + 1)).basedPost
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).path := by
  rw [kanAdjointTracedUnitParameterTriangle_one,
    OmegaSpectrum.tracedSignedLoopUnitRestrictionInterval_path]
  let H := OmegaSpectrum.tracedSignedLoopUnitComparison Y (n + 1)
  let e := kanAdjointStructureInput X Y φ n
  have hp := PointedMapping.VerticalPath.basedIhomMap_parameter_restrict
    (X.sigma n) (Y.sigma n) (φ ≫ pointedEvaluation X Y.toKanSequence (n + 1)) e
    (kanAdjointTracedUnitEvaluation_square X Y φ n) H
  have hr := PointedMapping.VerticalPath.basedIhomMap_pre_path
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (H.pre (Y.sigma n)) e
  change (((H.pre (Y.sigma n)).basedIhomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).pre e).path =
    (H.pre (Y.sigma n)).path ≫ (kanAdjointTracedUnitStructureAction X Y φ n).right at hr
  have hh :
      ((kanAdjointTracedUnitEvaluationInterval X Y φ (n + 1)).basedPost
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).path =
      (((H.basedIhomMap (X.level (n + 1)).space).pre
        (φ ≫ pointedEvaluation X Y.toKanSequence (n + 1))).basedPost
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).path := by
    change (kanAdjointTracedUnitEvaluationInterval X Y φ (n + 1)).path ≫ _ = _
    rw [kanAdjointTracedUnitEvaluationInterval_path]
    rfl
  exact hr.symm.trans (hp.symm.trans hh.symm)

end RawSpectrumMapping
end SerrePositivity.KST.Spectra
