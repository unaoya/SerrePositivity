module

public import SerrePositivity.KST.Spectra.SpectrumTracedSourceUnitEvaluationSquare

/-!
概要：源単位の同じ実正方形を、段射の源制限と構造像の比較へ戻す。
方針：評価区間の転置の厳密交換と、交換同型の逆向きを使う。
規約：源の非定数構造辺を明示して保持。使われ方：元の自然性正方形との境界比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
open OmegaSpectrum.CotensorCompatible
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 元の源構造入力区間を、同じ符号付き loop パラメータ列射へ後合成した実区間。 -/
def tracedSourceUnitStructureInterval (n : ℕ) :=
  (OmegaSpectrum.signedLoopUnitStructurePath X n).basedPost
    ((KanSequence.signedLoopParameterHom
      (homOfParameterFamily X Y.toKanSequence A φ)).app (n + 1))

/-- 元の源単位評価区間の転置が持つ、同じ源制限・構造像の実正方形。 -/
def tracedSourceUnitStageSquare (n : ℕ) :
    SSet.Homotopy
      ((((kanAdjointTracedSourceEvaluationInterval X Y (n + 1)).pre φ).basedTranspose.pre
        (X.sigma n)).path)
      ((PointedMapping.VerticalPath.basedPost
        (PointedMapping.VerticalPath.forgetProjection
          ((kanAdjointTracedSourceEvaluationInterval X Y n).pre φ).basedTranspose.suspension)
        ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path)
    where
  h := (tracedSourceUnitEvaluationSquare X Y φ n).h ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right
  h₀ := by
    rw [← Category.assoc, (tracedSourceUnitEvaluationSquare X Y φ n).h₀]
    exact basedTranspose_restriction_path (X.sigma n)
      ((kanAdjointTracedSourceEvaluationInterval X Y (n + 1)).pre φ)
  h₁ := by
    rw [← Category.assoc, (tracedSourceUnitEvaluationSquare X Y φ n).h₁]
    exact basedTranspose_step_path X (KanSequence.signedLoopTail Y.toKanSequence) n
      ((kanAdjointTracedSourceEvaluationInterval X Y n).pre φ)
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 源構造作用を段射座標へ戻すと、元の同じ列射への後合成に厳密一致する。 -/
lemma tracedSourceUnitStructureAction_transpose (n : ℕ) :
    tracedSourceUnitStructureAction X Y φ n ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom =
    PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      ((KanSequence.signedLoopParameterHom
        (homOfParameterFamily X Y.toKanSequence A φ)).app (n + 1)) := by
  rw [tracedSourceUnitStructureAction_post, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.hom_eq_inv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) A,
    Iso.inv_hom_id, Category.comp_id]

/-- 段射表示の左辺全体は、同じ源構造入力区間への実際の後合成。 -/
lemma tracedSourceUnitStageSquare_start (n : ℕ) :
    SquareAdjustment.leftSide ≫ (tracedSourceUnitStageSquare X Y φ n).h =
      (tracedSourceUnitStructureInterval X Y φ n).path := by
  change SquareAdjustment.leftSide ≫ ((tracedSourceUnitEvaluationSquare X Y φ n).h ≫ _) = _
  rw [← Category.assoc, tracedSourceUnitEvaluationSquare_start,
    PointedMapping.VerticalPath.basedPreAction_action_path]
  change ((OmegaSpectrum.signedLoopUnitStructurePath X n).path ≫
    (tracedSourceUnitStructureAction X Y φ n).right) ≫ _ = _
  have h := congrArg Under.Hom.right (tracedSourceUnitStructureAction_transpose X Y φ n)
  change (tracedSourceUnitStructureAction X Y φ n).right ≫ _ = _ at h
  rw [Category.assoc, h]
  rfl

/-- 段射表示でも、右辺全体は同じ厳密な終点の構造頂点で一定。 -/
lemma tracedSourceUnitStageSquare_finish (n : ℕ) :
    SquareAdjustment.rightSide ≫ (tracedSourceUnitStageSquare X Y φ n).h =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right.app _
          (PointedMapping.familyVertex ((φ ≫ tracedSourceUnitAction X Y n) ≫
            pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n))) := by
  change SquareAdjustment.rightSide ≫ ((tracedSourceUnitEvaluationSquare X Y φ n).h ≫ _) = _
  rw [← Category.assoc, tracedSourceUnitEvaluationSquare_finish, SSet.const_comp]
  rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
