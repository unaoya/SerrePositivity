module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointParametricCoordinates
public import SerrePositivity.KST.Spectra.PointedParametricPost

/-!
概要：元の全 Hom 段評価と通常円の Ω 随伴の厳密全族可換式を構成する。
方針：保存済みの通常円制限の厳密可換式を転置し、標準全族作用の源制限へ戻す。
規約：enriched 自然性を仮定しない。使われ方：元の交換区間の全族移送への実入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 元の段評価全体は、通常円の元の Ω 随伴に対して厳密な全族可換式を持つ。 -/
lemma pointedEvaluation_parametric_adjoint (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (X.level n).space (X.level (n + 1)).space (X.sigma n) ≫
      PointedMapping.parametricPost PointedSimplicialSet.circle.{u}
        (pointedEvaluation X Y.toKanSequence (n + 1)) =
    PointedMapping.transpose (pointedEvaluation X Y.toKanSequence n) ≫
      PointedObject.basedHomMap (pointedSpace X Y.toKanSequence)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (Y.level n).space (Y.level (n + 1)).space (Y.sigma n)) := by
  let M := pointedSpace X Y.toKanSequence
  let qX := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (X.level (n + 1)).space
  let qY := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit.{u} (Y.level (n + 1)).space
  let aY := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (Y.level n).space (Y.level (n + 1)).space (Y.sigma n)
  have h : kanAdjointParameterRight X Y n ≫
      PointedObject.basedHomMap (X.level n).space qY =
    pointedEvaluation X Y.toKanSequence n ≫ PointedObject.basedHomMap (X.level n).space aY :=
    kanAdjointParameterRight_restriction X Y n
  have ht := congrArg PointedMapping.transpose h
  have hr := PointedMapping.transpose_post (kanAdjointParameterRight X Y n) qY
  have hl := PointedMapping.transpose_post (pointedEvaluation X Y.toKanSequence n) aY
  have hb := hr.symm.trans (ht.trans hl)
  rw [kanAdjointParameterRight_transpose] at hb
  have hc := PointedMapping.parametricPost_restrict CirclePower.unit.{u}
    (pointedEvaluation X Y.toKanSequence (n + 1))
  change PointedMapping.parametricPost CirclePower.space.{u}
      (pointedEvaluation X Y.toKanSequence (n + 1)) ≫ PointedObject.basedHomMap M qY =
    qX ≫ PointedMapping.parametricPost PointedSimplicialSet.circle.{u}
      (pointedEvaluation X Y.toKanSequence (n + 1)) at hc
  have hk := KanSequence.kanAdjoint_comparison X.toKanSequence n
  change KanSequence.kanAdjoint X.toKanSequence n ≫ qX =
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (X.level n).space (X.level (n + 1)).space (X.sigma n) at hk
  calc
    _ = (KanSequence.kanAdjoint X.toKanSequence n ≫ qX) ≫
        PointedMapping.parametricPost PointedSimplicialSet.circle.{u}
          (pointedEvaluation X Y.toKanSequence (n + 1)) :=
      congrArg (· ≫ PointedMapping.parametricPost PointedSimplicialSet.circle.{u}
        (pointedEvaluation X Y.toKanSequence (n + 1))) hk.symm
    _ = KanSequence.kanAdjoint X.toKanSequence n ≫
        (qX ≫ PointedMapping.parametricPost PointedSimplicialSet.circle.{u}
          (pointedEvaluation X Y.toKanSequence (n + 1))) := Category.assoc _ _ _
    _ = KanSequence.kanAdjoint X.toKanSequence n ≫
        (PointedMapping.parametricPost CirclePower.space.{u}
          (pointedEvaluation X Y.toKanSequence (n + 1)) ≫
            PointedObject.basedHomMap M qY) := congrArg (_ ≫ ·) hc.symm
    _ = (KanSequence.kanAdjoint X.toKanSequence n ≫
        PointedMapping.parametricPost CirclePower.space.{u}
          (pointedEvaluation X Y.toKanSequence (n + 1))) ≫
            PointedObject.basedHomMap M qY := (Category.assoc _ _ _).symm
    _ = _ := hb

end SerrePositivity.KST.Spectra.RawSpectrumMapping
