module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedUnitSquare
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointPastedBoundary

/-!
概要：単位の実構造正方形を段射座標へ転置し、既存の貼り合わせ正方形と同じ境界へ照合する。
方針：同じ正方形全体に内部 Hom の交換同型を後合成する。
規約：共有辺の収縮は仮定しない。使われ方：二つの厳密化の共通構造境界での貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 同じ単位正方形全体を、既存の段射正方形と同じ内部 Hom の座標へ移す。 -/
def kanAdjointTracedUnitStructureSquare (n : ℕ) :
    SSet.Homotopy
      ((((kanAdjointTracedUnitEvaluationInterval X Y φ (n + 1)).basedPost
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).path) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right)
      (((OmegaSpectrum.tracedSignedLoopUnitStepInterval Y n).path ≫
        (kanAdjointTracedUnitStructureAction X Y φ n).right) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right) where
  h := (kanAdjointTracedUnitParameterSquare X Y φ n).h ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right
  h₀ := by rw [← Category.assoc, (kanAdjointTracedUnitParameterSquare X Y φ n).h₀]; rfl
  h₁ := by rw [← Category.assoc, (kanAdjointTracedUnitParameterSquare X Y φ n).h₁]; rfl
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 転置した同じ始点境界は、既存の正方形に残っていた元の実構造区間そのもの。 -/
lemma kanAdjointTracedUnitStructureSquare_start (n : ℕ) :
    SquareAdjustment.leftSide ≫ (kanAdjointTracedUnitStructureSquare X Y φ n).h =
      (kanAdjointTracedStructureInterval X Y φ n).path := by
  change SquareAdjustment.leftSide ≫ ((kanAdjointTracedUnitParameterSquare X Y φ n).h ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right) = _
  rw [← Category.assoc, kanAdjointTracedUnitParameterSquare_start]
  have he := kanAdjointTracedStructureInterval_path X Y φ n
  change (kanAdjointTracedStructureInterval X Y φ n).path =
    (kanAdjointParameterStructureInterval X Y φ n).path ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right at he
  exact he.symm

/-- 転置後も、単位の同じ厳密構造頂点の像で終点境界全体が一定。 -/
lemma kanAdjointTracedUnitStructureSquare_finish (n : ℕ) :
    SquareAdjustment.rightSide ≫ (kanAdjointTracedUnitStructureSquare X Y φ n).h =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right.app _
        (PointedMapping.familyVertex
          ((φ ≫ pointedPost X
              (OmegaSpectrum.sequenceHom (OmegaSpectrum.tracedSignedLoopUnit Y)) ≫
            pointedPost X (OmegaSpectrum.signedLoopProjection Y) ≫
            pointedEvaluation X (KanSequence.signedLoopTail Y.toKanSequence) (n + 1)) ≫
            _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
              ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space))) := by
  change SquareAdjustment.rightSide ≫ ((kanAdjointTracedUnitParameterSquare X Y φ n).h ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right) = _
  rw [← Category.assoc, kanAdjointTracedUnitParameterSquare_finish, SSet.const_comp]
  rfl

/-- 二つの正方形は、同じ非定数の元の構造区間を辺全体として厳密に共有する。 -/
lemma kanAdjointTracedUnitStructureSquare_shared_start
    {B : PointedSimplicialSet.{u}} (j : B ⟶ A) [Mono j.right] (n : ℕ) :
    SquareAdjustment.leftSide ≫ (kanAdjointTracedUnitStructureSquare X Y φ n).h =
    SquareAdjustment.leftSide ≫ (kanAdjointRelativeTracedPastedSquare X Y φ j n).h := by
  rw [kanAdjointTracedUnitStructureSquare_start, kanAdjointRelativeTracedPastedSquare_start]

end SerrePositivity.KST.Spectra.RawSpectrumMapping
