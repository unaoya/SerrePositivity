module
public import SerrePositivity.KST.SConstruction.OuterStagePasting
public import SerrePositivity.KST.SConstruction.SpecifiedTriangleAttachmentFaces

/-! # 元の両外側面の全接続辺を同じ実複体内で回収する
概要：外側二部分面の全ホーン辺と両段面の全対角辺を、元の接続先へ厳密に照合する。
方針：指定三角形の全ホーン式と対角辺の pushout の共有式を使う。
規約：実複体内の全区間の等号を保持し、面を選び直さない。
使われ方：元の raw BF 比較三角形を貼るための頂点・対角面の厳密な同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial

/-- 左外側二部分面の全下面は、元の同じ左正規化出口。 -/
lemma outerBinaryPasting_left_first :
    stdSimplex.δ 2 ≫ outerBinaryPastingLeftCell.{u} =
      correctionNormalizationPastingLeftTarget ≫ outerBinaryPastingOriginal := by
  unfold outerBinaryPastingLeftCell outerBinaryPastingOriginal
  rw [← Category.assoc, specifiedTriangleAttachment_face _ 2 (by decide)]
  simp only [Category.assoc]
  rw [← Category.assoc (horn₂₁.ι₀₁) correctionOuterLeftHorn,
    correctionOuterLeftHorn_first]

/-- 左外側二部分面の全上面は、元の同じ交換下面。 -/
lemma outerBinaryPasting_left_second :
    stdSimplex.δ 0 ≫ outerBinaryPastingLeftCell.{u} =
      correctionOuterLeftSecond ≫ outerBinaryPastingOriginal := by
  unfold outerBinaryPastingLeftCell outerBinaryPastingOriginal
  rw [← Category.assoc, specifiedTriangleAttachment_face _ 0 (by decide)]
  simp only [Category.assoc]
  rw [← Category.assoc (horn₂₁.ι₁₂) correctionOuterLeftHorn,
    correctionOuterLeftHorn_second]

/-- 右外側二部分面の全下面は、元の同じ最初の補正辺。 -/
lemma outerBinaryPasting_right_first :
    stdSimplex.δ 2 ≫ outerBinaryPastingRightCell.{u} =
      correctionOuterRightFirst ≫ outerBinaryPastingOriginal := by
  rw [outerBinaryPastingRightCell, specifiedTriangleAttachment_face _ 2 (by decide)]
  simp only [outerBinaryRightAttachingHorn, outerBinaryPastingOriginal, ← Category.assoc]
  rw [correctionOuterRightHorn_first]

/-- 右外側二部分面の全上面は、元の同じ右正規化出口。 -/
lemma outerBinaryPasting_right_second :
    stdSimplex.δ 0 ≫ outerBinaryPastingRightCell.{u} =
      correctionNormalizationPastingRightTarget ≫ outerBinaryPastingOriginal := by
  rw [outerBinaryPastingRightCell, specifiedTriangleAttachment_face _ 0 (by decide)]
  simp only [outerBinaryRightAttachingHorn, outerBinaryPastingOriginal, ← Category.assoc]
  rw [correctionOuterRightHorn_second]

/-- 左外側段面の全対角は、元の左二部分面の同じ全対角辺。 -/
lemma outerStagePasting_left_diagonal :
    stdSimplex.δ 1 ≫ outerStagePastingLeftCell.{u} =
      stdSimplex.δ 1 ≫ outerBinaryPastingLeftCell ≫ outerStagePastingOriginal := by
  unfold outerStagePastingLeftCell outerStagePastingOriginal
    outerStageLeftCell outerStageLeftOriginal
  simpa only [Category.assoc] using
    congrArg (· ≫ pushout.inl outerStageRightAttachingEdge.{u} (stdSimplex.δ.{u} (1 : Fin 3)))
      (pushout.condition
        (f := stdSimplex.δ.{u} (1 : Fin 3) ≫ outerBinaryPastingLeftCell.{u})
        (g := stdSimplex.δ.{u} (1 : Fin 3))).symm

/-- 右外側段面の全対角も、元の右二部分面の同じ全対角辺。 -/
lemma outerStagePasting_right_diagonal :
    stdSimplex.δ 1 ≫ outerStagePastingRightCell.{u} =
      stdSimplex.δ 1 ≫ outerBinaryPastingRightCell ≫ outerStagePastingOriginal := by
  unfold outerStagePastingRightCell outerStagePastingOriginal outerStageRightAttachingEdge
  exact (pushout.condition).symm.trans (Category.assoc _ _ _)

end SerrePositivity.KST.SConstruction
