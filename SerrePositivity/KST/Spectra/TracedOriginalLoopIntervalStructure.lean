module

public import SerrePositivity.KST.Spectra.RawSpectrumIntervalStructureMap
public import SerrePositivity.KST.Spectra.TracedOriginalLoopSourceInterval

/-!
概要：源比較自身の段区間は、元の全 Hom 区間から来るため構造条件を区間全体で満たす。
方針：同じ全 Hom 区間を恒等射で評価し、転置・単位評価する一般構造定理を適用する。
規約：新たな区間を選ばない。使われ方：実評価側の最初の比較辺の構造正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
open RawSpectrumMapping

/-- 元の全 Hom の同じ区間を、元の恒等射の単位族へ制限する。 -/
def tracedOriginalLoopWholeUnitInterval (X : OmegaSpectrum.{u}) :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (pointedSpace X (KanSequence.signedLoopTail X.toKanSequence)))
      (pointedIdentity X ≫ pointedPost X (tracedOriginalLoopRawComparison X))
      (pointedIdentity X ≫ (pointedPost X (sequenceHom (tracedSignedLoopUnit X)) ≫
        pointedPost X (signedLoopProjection X))) :=
  (tracedOriginalLoopRawComparison_post_interval X X).pre (pointedIdentity X)

/-- 段の単位区間は、同じ全 Hom の単位区間の同じ段評価の辺そのもの。 -/
lemma tracedOriginalLoop_unit_interval_whole_path (X : OmegaSpectrum.{u}) (n : ℕ) :
    (tracedOriginalLoopRawComparison_unit_interval X n).path =
      ((tracedOriginalLoopWholeUnitInterval X).basedPost
        (pointedEvaluation X (KanSequence.signedLoopTail X.toKanSequence) n)).path := by
  change (((tracedOriginalLoopRawComparison_post_interval X X).basedPost
    (pointedEvaluation X (KanSequence.signedLoopTail X.toKanSequence) n)).pre
      (pointedIdentity X)).path = _
  exact PointedMapping.VerticalPath.pre_basedPost_path _ _ _

/-- 源自身の段区間は、同じ全 Hom の転置段区間を同じ列の単位で評価したもの。 -/
lemma tracedOriginalLoop_level_interval_whole_path (X : OmegaSpectrum.{u}) (n : ℕ) :
    (tracedOriginalLoopRawComparison_level_interval X n).path =
      (pointedInterval_mappedStage X (KanSequence.signedLoopTail X.toKanSequence)
        (KanSequence.signedLoopTail X.toKanSequence) (tracedOriginalLoopWholeUnitInterval X)
        (KanSequence.mappingUnitEvaluation (KanSequence.signedLoopTail X.toKanSequence))
        n).path := by
  have h := tracedOriginalLoop_unit_interval_whole_path X n
  have ht := congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso
    (𝟙_ PointedSimplicialSet.{u}) (X.level n).space
    ((KanSequence.signedLoopTail X.toKanSequence).level n).space).hom.right) h
  exact congrArg (· ≫ ((ihom (X.level n).space).map
    ((KanSequence.mappingUnitEvaluation (KanSequence.signedLoopTail X.toKanSequence)).app n)).right)
      ht

/-- 同じ元の源区間の二つの構造経路は、端点だけでなく辺全体で厳密に一致する。 -/
lemma tracedOriginalLoop_level_interval_structure_path (X : OmegaSpectrum.{u}) (n : ℕ) :
    ((tracedOriginalLoopRawComparison_level_interval X (n + 1)).pre (X.sigma n)).path =
      ((tracedOriginalLoopRawComparison_level_interval X n).suspension.forgetProjection.basedPost
        ((KanSequence.signedLoopTail X.toKanSequence).sigma n)).path := by
  have h := pointedInterval_mappedStage_condition X (KanSequence.signedLoopTail X.toKanSequence)
    (KanSequence.signedLoopTail X.toKanSequence) (tracedOriginalLoopWholeUnitInterval X)
    (KanSequence.mappingUnitEvaluation (KanSequence.signedLoopTail X.toKanSequence)) n
  rw [PointedMapping.VerticalPath.suspension_basedPost_path] at h ⊢
  change (tracedOriginalLoopRawComparison_level_interval X (n + 1)).path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
        ((KanSequence.signedLoopTail X.toKanSequence).level (n + 1)).space).right = _
  rw [tracedOriginalLoop_level_interval_whole_path,
    tracedOriginalLoop_level_interval_whole_path]
  exact h

/-- 源区間の最初の構造正方形は、同じ構造辺を保つ定数な正方形でよい。 -/
def tracedOriginalLoop_level_interval_structure_square (X : OmegaSpectrum.{u}) (n : ℕ) :
    SSet.Homotopy
      (((tracedOriginalLoopRawComparison_level_interval X (n + 1)).pre (X.sigma n)).path)
      (((tracedOriginalLoopRawComparison_level_interval X n).suspension.forgetProjection.basedPost
        ((KanSequence.signedLoopTail X.toKanSequence).sigma n)).path) := by
  rw [tracedOriginalLoop_level_interval_structure_path]
  exact SSet.RelativeMorphism.Homotopy.refl _

end SerrePositivity.KST.Spectra.OmegaSpectrum
