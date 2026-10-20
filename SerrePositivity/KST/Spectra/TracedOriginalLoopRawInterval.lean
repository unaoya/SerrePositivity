module

public import SerrePositivity.KST.Spectra.TracedOriginalLoopModelMap

/-!
概要：トレース付き源比較を raw な符号付き loop 列へ戻し、同じ全 Hom 区間を保持する。
方針：選択済み逆射の同じ全 Hom 区間に、BF 射影の後合成を適用する。
規約：段ごとに区間を選び直さない。使われ方：実評価側の構造区間の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
open RawSpectrumMapping

/-- 元の BF 源から、置換前の同じ符号付き loop 列への実際の列射。 -/
def tracedOriginalLoopRawComparison (X : OmegaSpectrum.{u}) :
    KanSequence.Hom X.toKanSequence (KanSequence.signedLoopTail X.toKanSequence) :=
  (sequenceHom (tracedOriginalLoopModelMap X)).comp (signedLoopRawComparison X)

/-- 同じ BF 比較と射影を合成すると、同じ置換前の列射へ厳密に戻る。 -/
lemma tracedOriginalLoopRawComparison_post_factor (A X : OmegaSpectrum.{u}) :
    (pointedPost A (sequenceHom (tracedOriginalLoopModelMap X)) ≫
      pointedPost A (sequenceHom (signedLoopComparison X))) ≫
      pointedPost A (signedLoopProjection X) =
    pointedPost A (tracedOriginalLoopRawComparison X) := by
  rw [Category.assoc, pointedPost_comp_eq A (sequenceHom (signedLoopComparison X))
    (signedLoopProjection X) (signedLoopRawComparison X) (signedLoopComparison_projection X)]
  exact pointedPost_comp_eq A (sequenceHom (tracedOriginalLoopModelMap X))
    (signedLoopRawComparison X) (tracedOriginalLoopRawComparison X) (fun _ => rfl)

/-- 置換前でも、元の同じ全 Hom 区間でトレース付き単位の射影へ変形する。 -/
def tracedOriginalLoopRawComparison_post_interval (A X : OmegaSpectrum.{u}) :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (pointedSpace A (KanSequence.signedLoopTail X.toKanSequence)))
      (pointedPost A (tracedOriginalLoopRawComparison X))
      (pointedPost A (sequenceHom (tracedSignedLoopUnit X)) ≫
        pointedPost A (signedLoopProjection X)) :=
  ((tracedOriginalLoopModelMap_unit_post_interval A X).basedPost
    (pointedPost A (signedLoopProjection X))).changeEndpoints
      (tracedOriginalLoopRawComparison_post_factor A X).symm rfl

/-- raw 区間全体は元の BF 区間への同じ射影の後合成であり、別の選択はしない。 -/
lemma tracedOriginalLoopRawComparison_post_interval_h (A X : OmegaSpectrum.{u}) :
    (tracedOriginalLoopRawComparison_post_interval A X).homotopy.h =
      (tracedOriginalLoopModelMap_unit_post_interval A X).homotopy.h ≫
        (pointedPost A (signedLoopProjection X)).right := by
  rw [tracedOriginalLoopRawComparison_post_interval,
    PointedMapping.VerticalPath.changeEndpoints_homotopy_h,
    PointedMapping.VerticalPath.basedPost_homotopy_h]

/-- 同じ区間を各段へ評価したもの。両端だけの成分比較への置き換えはしない。 -/
def tracedOriginalLoopRawComparison_stage_interval (A X : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (kanAdjointParameterTarget A X n))
      (pointedEvaluation A X.toKanSequence n ≫
        (ihom (A.level n).space).map ((tracedOriginalLoopRawComparison X).app n))
      (pointedEvaluation A X.toKanSequence n ≫
        (ihom (A.level n).space).map
          ((tracedSignedLoopUnit X).app n ≫ (signedLoopProjection X).app n)) := by
  let P := (tracedOriginalLoopRawComparison_post_interval A X).basedPost
    (pointedEvaluation A (KanSequence.signedLoopTail X.toKanSequence) n)
  have hs : pointedEvaluation A X.toKanSequence n ≫
      (ihom (A.level n).space).map ((tracedOriginalLoopRawComparison X).app n) =
      pointedPost A (tracedOriginalLoopRawComparison X) ≫
        pointedEvaluation A (KanSequence.signedLoopTail X.toKanSequence) n :=
    (pointedPost_evaluation A (tracedOriginalLoopRawComparison X) n).symm
  have ht : pointedEvaluation A X.toKanSequence n ≫
      (ihom (A.level n).space).map
        ((tracedSignedLoopUnit X).app n ≫ (signedLoopProjection X).app n) =
      (pointedPost A (sequenceHom (tracedSignedLoopUnit X)) ≫
        pointedPost A (signedLoopProjection X)) ≫
          pointedEvaluation A (KanSequence.signedLoopTail X.toKanSequence) n := by
    rw [Category.assoc, pointedPost_evaluation, ← Category.assoc, pointedPost_evaluation]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  exact P.changeEndpoints hs ht

end SerrePositivity.KST.Spectra.OmegaSpectrum
