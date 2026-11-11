module

public import SerrePositivity.KST.Spectra.PointedEvaluationAction
public import SerrePositivity.KST.Spectra.PointedIhomParameterRestriction
public import SerrePositivity.KST.Spectra.SpectrumSignedEvaluationSourceCoordinates

/-!
概要：元の評価由来の段射を、次段の全 Hom の作用と同じ raw 源比較へ同定する。
方針：普遍評価の交換恒等式に、反転反復の自然性と前合成の合成則を適用する。
規約：同じ元の全 Hom の射の等式。使われ方：トレース付き源の実区間の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
open RawSpectrumMapping

/-- 元の普遍評価の交換座標は、内部 Hom の作用に同じ BF 射影を入力したもの。 -/
lemma evaluationPostAt_exchange_action (K : PointedSimplicialSet.{u})
    (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    evaluationPostAt K X Y n ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso ((cotensor K X).level n).space K (Y.level n).space).inv =
    PointedMapping.ihomAction K (X.level n).space (Y.level n).space ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((cotensorProjection K X).app n)
        (PointedObject.basedHom K (Y.level n).space) :=
  PointedMapping.evaluationPost_exchange ((cotensorProjection K X).app n)

/-- 反転補正と源比較を一つの実際の raw 源射へまとめた、元の実評価の段座標。 -/
lemma signedEvaluationAt_action (X Y : OmegaSpectrum.{u})
    (e : X ⟶ tail (cotensor CirclePower.space.{u} X)) (n : ℕ) :
    signedEvaluationAt X Y e ≫
      pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) n =
    pointedEvaluation X Y.toKanSequence (n + 1) ≫
      PointedMapping.ihomAction CirclePower.space.{u}
        (X.level (n + 1)).space (Y.level (n + 1)).space ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (e.app n ≫ (signedLoopRawComparison X).app n)
        (PointedObject.basedHom CirclePower.space.{u} (Y.level (n + 1)).space) := by
  rw [signedEvaluationAt_evaluation]
  rw [← Category.assoc (evaluationPostAt CirclePower.space.{u} X Y (n + 1)),
    evaluationPostAt_exchange_action]
  simp only [Category.assoc]
  erw [PointedMapping.ihomParameterAction_restrict_input_assoc
    (V := (Y.level (n + 1)).space) (CirclePower.reversalIterate n)
    ((cotensorProjection CirclePower.space.{u} X).app (n + 1))]
  rw [signedLoopRawComparison_app]
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp, Category.assoc]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
