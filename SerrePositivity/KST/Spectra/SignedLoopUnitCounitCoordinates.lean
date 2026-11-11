module

public import SerrePositivity.KST.Spectra.SignedLoopUnitPostTrace
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointCounitCoordinates

/-!
概要：元の BF 単位の射影を厳密化した列射へ照合し、零段の counit を元の評価へ厳密に戻す。
方針：rectifyInto の持ち上げ式と、厳密化が零段を変更しないことを使う。
規約：高い段でも元の Kan 随伴に厳密一致するとは仮定しない。
使われ方：元の単位トレースと Kan 随伴比較の最初の境界の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
open RawSpectrumMapping

/-- 元の BF 単位の raw 射影は、同じ逐次厳密化から得た列射そのもの。 -/
lemma signedLoopUnit_projection_rectify (X : OmegaSpectrum.{u}) (n : ℕ) :
    (signedLoopUnit X).app n ≫ (signedLoopProjection X).app n =
    (KanSequence.rectify (X := X.toKanSequence)
      (Y := KanSequence.signedLoopTail X.toKanSequence) X.sigma_mono
      (KanSequence.kanAdjoint X.toKanSequence)
      (KanSequence.kanAdjoint_signedLoopTail_comm X.toKanSequence_omega)).app n :=
  rectifyInto_projection X (KanSequence.signedLoopTail X.toKanSequence)
    (KanSequence.signedLoopTail_omegaCondition X.toKanSequence_omega)
    (KanSequence.kanAdjoint X.toKanSequence)
    (KanSequence.kanAdjoint_signedLoopTail_comm X.toKanSequence_omega) n

/-- 零段の raw 射影は、元の選択済み Kan 随伴に厳密一致する。 -/
lemma signedLoopUnit_projection_zero (X : OmegaSpectrum.{u}) :
    (signedLoopUnit X).app 0 ≫ (signedLoopProjection X).app 0 =
      KanSequence.kanAdjoint X.toKanSequence 0 := by
  rw [signedLoopUnit_projection_rectify]
  rfl

/-- 元の全 Hom の単位後合成の零段は、同じ Kan 随伴座標そのもの。 -/
lemma signedLoopUnit_post_zero (A X : OmegaSpectrum.{u}) :
    pointedPost A (sequenceHom (signedLoopUnit X)) ≫
      pointedPost A (signedLoopProjection X) ≫
      pointedEvaluation A (KanSequence.signedLoopTail X.toKanSequence) 0 =
    kanAdjointParameterLeft A X 0 := by
  simp only [pointedPost_evaluation, pointedPost_evaluation_assoc]
  change pointedEvaluation A X.toKanSequence 0 ≫
      (ihom (A.level 0).space).map ((signedLoopUnit X).app 0) ≫
      (ihom (A.level 0).space).map ((signedLoopProjection X).app 0) =
    pointedEvaluation A X.toKanSequence 0 ≫
      (ihom (A.level 0).space).map (KanSequence.kanAdjoint X.toKanSequence 0)
  rw [← Functor.map_comp, signedLoopUnit_projection_zero]

/-- 単位後合成の零段 counit は、元の次段評価の元の構造射への制限そのもの。 -/
lemma signedLoopUnit_post_zero_counit (A X : OmegaSpectrum.{u}) :
    (pointedPost A (sequenceHom (signedLoopUnit X)) ≫
      pointedPost A (signedLoopProjection X) ≫
      pointedEvaluation A (KanSequence.signedLoopTail X.toKanSequence) 0) ≫
      kanLoopCounit (A.level 0).space (X.level 1).space =
    pointedEvaluation A X.toKanSequence 1 ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (A.sigma 0) (X.level 1).space := by
  rw [signedLoopUnit_post_zero, kanAdjointParameterLeft_counit]

end SerrePositivity.KST.Spectra.OmegaSpectrum
