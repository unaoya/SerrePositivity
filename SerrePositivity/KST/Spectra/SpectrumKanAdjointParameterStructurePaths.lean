module

public import SerrePositivity.KST.Spectra.SignedLoopStructurePaths
public import SerrePositivity.KST.Spectra.PointedBasedPathClosed
public import SerrePositivity.KST.Spectra.SequenceParameterTranspose
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointParameterStructure

/-!
概要：元の全 Hom 上の Kan 随伴の構造比較を、交換符号の普遍区間から移した有限鎖で実現する。
方針：内部 Hom の作用・元の普遍評価・転置を、区間を選び直さずに適用する。
規約：一般の指定部分への垂直性は別工程。使われ方：相対厳密化の元の構造区間の追跡。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 全 Hom 上の元の構造比較を、普遍的な交換符号区間から作った基点固定有限鎖で実現する。 -/
lemma kanAdjointParameterLeft_basedChain (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.VerticalChain (PointedObject.toPoint
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space))
      (kanAdjointParameterLeft X Y n ≫
        pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)
      (kanAdjointParameterLeft X Y (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space) := by
  have hs := PointedMapping.VerticalChain.basedIhomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
    (KanSequence.kanAdjoint_signedLoopTail_basedChain Y.toKanSequence_omega n)
  have h := hs.pre (pointedEvaluation X Y.toKanSequence n ≫
    suspensionHom (X.level n).space (Y.level n).space)
  rw [kanAdjointParameterLeft_step, kanAdjointParameterLeft_source_restriction]
  exact h

/-- 元の全 Hom の構造比較の有限鎖を、cotensor 値の列の実際の構造比較へ転置する。 -/
lemma kanAdjointParameter_transpose_basedChain (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.VerticalChain (PointedObject.toPoint
      ((KanSequence.mapping (pointedSpace X Y.toKanSequence)
        (KanSequence.signedLoopTail Y.toKanSequence)).level (n + 1)).space)
      (PointedSimplicialSet.circle.{u} ◁
        PointedMapping.transpose (kanAdjointParameterLeft X Y n) ≫
          (KanSequence.mapping (pointedSpace X Y.toKanSequence)
            (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)
      (X.sigma n ≫ PointedMapping.transpose (kanAdjointParameterLeft X Y (n + 1))) := by
  have h := (kanAdjointParameterLeft_basedChain X Y n).basedTranspose
  have hl := transpose_step X (KanSequence.signedLoopTail Y.toKanSequence)
    (pointedSpace X Y.toKanSequence) n (kanAdjointParameterLeft X Y n)
  have hr := transpose_restriction X (KanSequence.signedLoopTail Y.toKanSequence)
    (pointedSpace X Y.toKanSequence) n (kanAdjointParameterLeft X Y (n + 1))
  rw [hl, hr] at h
  exact h

end SerrePositivity.KST.Spectra.RawSpectrumMapping
