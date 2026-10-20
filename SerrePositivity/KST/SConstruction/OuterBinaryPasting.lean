module
public import SerrePositivity.KST.SConstruction.OuterCorrectionHorns
public import SerrePositivity.KST.SConstruction.SpecifiedTriangleAttachment

/-! # 元の両外側二部分三角形の全体を同じ補正複体へ貼る
概要：正規化出口を含む元の両内ホーンへ、元の左右二部分三角形を全体として接続する。
方針：指定全ホーンへの三角形接続を順に二回行い、両全像を回収する。
規約：元の六面・両全円柱・両外側二部分面を保持し、三角形を充填し直さない。
使われ方：外側の元の両段三角形を同じ全対角補正辺で接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 左外側の元の全二部分面を貼った中間複体。 -/
def outerBinaryLeftDomain : SSet.{u} := specifiedTriangleAttachment correctionOuterLeftHorn.{u}

/-- 左外側面接続後の、元の同じ全右内ホーン。 -/
def outerBinaryRightAttachingHorn : (Λ[2, 1] : SSet.{u}) ⟶ outerBinaryLeftDomain :=
  correctionOuterRightHorn ≫ specifiedTriangleAttachmentOriginal correctionOuterLeftHorn

/-- 元の左右外側二部分面を全体として保持する実比較複体。 -/
def outerBinaryPasting : SSet.{u} := specifiedTriangleAttachment outerBinaryRightAttachingHorn.{u}

/-- 元の六面・両正規化円柱の実複体全体の包含。 -/
def outerBinaryPastingOriginal : correctionNormalizationPasting.{u} ⟶ outerBinaryPasting :=
  specifiedTriangleAttachmentOriginal correctionOuterLeftHorn ≫
    specifiedTriangleAttachmentOriginal outerBinaryRightAttachingHorn

/-- 元の左外側二部分三角形全体の包含。 -/
def outerBinaryPastingLeftCell : (Δ[2] : SSet.{u}) ⟶ outerBinaryPasting :=
  specifiedTriangleAttachmentCell correctionOuterLeftHorn ≫
    specifiedTriangleAttachmentOriginal outerBinaryRightAttachingHorn

/-- 元の右外側二部分三角形全体の包含。 -/
def outerBinaryPastingRightCell : (Δ[2] : SSet.{u}) ⟶ outerBinaryPasting :=
  specifiedTriangleAttachmentCell outerBinaryRightAttachingHorn

variable {E : SSet.{u}} (P : correctionNormalizationPasting.{u} ⟶ E)
  (L R : (Δ[2] : SSet.{u}) ⟶ E)
  (hl₀ : correctionNormalizationPastingLeftTarget ≫ P = stdSimplex.δ 2 ≫ L)
  (hl₁ : correctionOuterLeftSecond ≫ P = stdSimplex.δ 0 ≫ L)
  (hr₀ : correctionOuterRightFirst ≫ P = stdSimplex.δ 2 ≫ R)
  (hr₁ : correctionNormalizationPastingRightTarget ≫ P = stdSimplex.δ 0 ≫ R)

/-- 元の左全二部分面と元の全比較複体を同時に保持する中間写像。 -/
def outerBinaryLeftMap : outerBinaryLeftDomain ⟶ E :=
  specifiedTriangleAttachmentMap correctionOuterLeftHorn P L
    (specifiedInnerHorn_map _ _ _
      (by rw [correctionOuterLeftHorn_first]; exact hl₀)
      (by rw [correctionOuterLeftHorn_second]; exact hl₁))

/-- 左接続後も元の全比較複体を厳密に回収する。 -/
lemma outerBinaryLeftMap_original :
    specifiedTriangleAttachmentOriginal correctionOuterLeftHorn ≫
        outerBinaryLeftMap P L hl₀ hl₁ = P :=
  specifiedTriangleAttachmentMap_original _ _ _ _

/-- 元の左全二部分面そのものを厳密に回収する。 -/
lemma outerBinaryLeftMap_cell :
    specifiedTriangleAttachmentCell correctionOuterLeftHorn ≫
        outerBinaryLeftMap P L hl₀ hl₁ = L :=
  specifiedTriangleAttachmentMap_cell _ _ _ _

/-- 元の両外側全二部分面と元の比較複体全体を同時に保持する実写像。 -/
def outerBinaryPastingMap : outerBinaryPasting ⟶ E :=
  specifiedTriangleAttachmentMap outerBinaryRightAttachingHorn (outerBinaryLeftMap P L hl₀ hl₁) R
    (by
      rw [outerBinaryRightAttachingHorn, Category.assoc, outerBinaryLeftMap_original]
      exact specifiedInnerHorn_map _ _ _
        (by rw [correctionOuterRightHorn_first]; exact hr₀)
        (by rw [correctionOuterRightHorn_second]; exact hr₁))

/-- 元の六面・両全正規化円柱を持つ比較複体全体を厳密に回収する。 -/
lemma outerBinaryPastingMap_original :
    outerBinaryPastingOriginal ≫ outerBinaryPastingMap P L R hl₀ hl₁ hr₀ hr₁ = P := by
  rw [outerBinaryPastingOriginal, outerBinaryPastingMap, Category.assoc,
    specifiedTriangleAttachmentMap_original, outerBinaryLeftMap_original]

/-- 元の左外側全二部分面を厳密に回収する。 -/
lemma outerBinaryPastingMap_left :
    outerBinaryPastingLeftCell ≫ outerBinaryPastingMap P L R hl₀ hl₁ hr₀ hr₁ = L := by
  rw [outerBinaryPastingLeftCell, outerBinaryPastingMap, Category.assoc,
    specifiedTriangleAttachmentMap_original, outerBinaryLeftMap_cell]

/-- 元の右外側全二部分面も厳密に回収する。 -/
lemma outerBinaryPastingMap_right :
    outerBinaryPastingRightCell ≫ outerBinaryPastingMap P L R hl₀ hl₁ hr₀ hr₁ = R :=
  specifiedTriangleAttachmentMap_cell _ _ _ _

end SerrePositivity.KST.SConstruction
