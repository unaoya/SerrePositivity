module
public import SerrePositivity.KST.SConstruction.CorrectionInterchangePasting
public import SerrePositivity.KST.SConstruction.FixedCylinderAttachment

/-! # 六面比較複体へ両全正規化円柱を共有境界ごと貼る
概要：六面比較の左右の指定辺へ、全入力境界を固定する二つの全円柱を順に接続する。
方針：入口と全側面を同じ辺へ折り畳む相対円柱の pushout を二度使う。
規約：元の全六面・両全円柱・出口の共有全境界を実複体内で保持する。
使われ方：外側二入力の両全二部分面を、同じ新しい補正辺と同じ端点に貼る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 元の前二射段面の下面全体。 -/
def correctionNormalizationLeftEdge : (Δ[1] : SSet.{u}) ⟶ correctionInterchangePasting :=
  stdSimplex.δ 2 ≫ triangleDiagonalPastingFirst ≫ doubleDiagonalTrianglePastingFirst 0 2 ≫
    correctionInterchangePastingOriginal

/-- 元の後二射段面の下面全体。 -/
def correctionNormalizationRightEdge : (Δ[1] : SSet.{u}) ⟶ correctionInterchangePasting :=
  stdSimplex.δ 2 ≫ triangleDiagonalPastingFirst ≫ doubleDiagonalTrianglePastingSecond 0 2 ≫
    correctionInterchangePastingOriginal

/-- 左の全境界固定円柱を貼った中間実複体。 -/
def correctionNormalizationLeftDomain : SSet.{u} :=
  fixedCylinderAttachment (SSet.boundary.{u} 1).ι correctionNormalizationLeftEdge

/-- 左円柱接続後も同じ既存右補正辺全体を使う。 -/
def correctionNormalizationRightAttachingEdge :
    (Δ[1] : SSet.{u}) ⟶ correctionNormalizationLeftDomain :=
  correctionNormalizationRightEdge ≫
    fixedCylinderAttachmentOriginal (SSet.boundary.{u} 1).ι correctionNormalizationLeftEdge

/-- 元の六面と両全境界固定円柱を保持する最終実複体。 -/
def correctionNormalizationPasting : SSet.{u} :=
  fixedCylinderAttachment (SSet.boundary.{u} 1).ι correctionNormalizationRightAttachingEdge

/-- 元の六面実複体全体の包含。 -/
def correctionNormalizationPastingOriginal :
    correctionInterchangePasting.{u} ⟶ correctionNormalizationPasting :=
  fixedCylinderAttachmentOriginal (SSet.boundary.{u} 1).ι correctionNormalizationLeftEdge ≫
    fixedCylinderAttachmentOriginal (SSet.boundary.{u} 1).ι
      correctionNormalizationRightAttachingEdge

/-- 元の左全正規化円柱の包含。 -/
def correctionNormalizationPastingLeftCell :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ correctionNormalizationPasting :=
  fixedCylinderAttachmentCell (SSet.boundary.{u} 1).ι correctionNormalizationLeftEdge ≫
    fixedCylinderAttachmentOriginal (SSet.boundary.{u} 1).ι
      correctionNormalizationRightAttachingEdge

/-- 元の右全正規化円柱の包含。 -/
def correctionNormalizationPastingRightCell :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ correctionNormalizationPasting :=
  fixedCylinderAttachmentCell (SSet.boundary.{u} 1).ι correctionNormalizationRightAttachingEdge

/-- 左の同じ全正規化円柱の出口。 -/
def correctionNormalizationPastingLeftTarget : (Δ[1] : SSet.{u}) ⟶ correctionNormalizationPasting :=
  fixedCylinderAttachmentTarget (SSet.boundary.{u} 1).ι correctionNormalizationLeftEdge ≫
    fixedCylinderAttachmentOriginal (SSet.boundary.{u} 1).ι
      correctionNormalizationRightAttachingEdge

/-- 右の同じ全正規化円柱の出口。 -/
def correctionNormalizationPastingRightTarget :
    (Δ[1] : SSet.{u}) ⟶ correctionNormalizationPasting :=
  fixedCylinderAttachmentTarget (SSet.boundary.{u} 1).ι correctionNormalizationRightAttachingEdge

/-- 左出口の全区間境界は、実複体内で元の同じ境界を厳密に保持する。 -/
lemma correctionNormalizationPastingLeftTarget_boundary :
    (SSet.boundary 1).ι ≫ correctionNormalizationPastingLeftTarget.{u} =
      (SSet.boundary 1).ι ≫ correctionNormalizationLeftEdge ≫
        correctionNormalizationPastingOriginal := by
  rw [correctionNormalizationPastingLeftTarget, ← Category.assoc,
    fixedCylinderAttachmentTarget_boundary]
  simp only [correctionNormalizationPastingOriginal, Category.assoc]

/-- 右出口の全区間境界も、実複体内で元の同じ境界を厳密に保持する。 -/
lemma correctionNormalizationPastingRightTarget_boundary :
    (SSet.boundary 1).ι ≫ correctionNormalizationPastingRightTarget.{u} =
      (SSet.boundary 1).ι ≫ correctionNormalizationRightEdge ≫
        correctionNormalizationPastingOriginal := by
  rw [correctionNormalizationPastingRightTarget, fixedCylinderAttachmentTarget_boundary]
  simp only [correctionNormalizationRightAttachingEdge, correctionNormalizationPastingOriginal,
    Category.assoc]

end SerrePositivity.KST.SConstruction
