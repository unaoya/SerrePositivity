module
public import SerrePositivity.KST.SConstruction.TripleRawAttachmentCorners

/-! # 元の raw BF 二三角形を同じ全比較複体へ接続する
概要：既存の二辺へ第一面を、共有対角と第二 whisker へ第二面を貼る実複体。
方針：内ホーン、外ホーンの順に指定三角形の接続を使う。
規約：元の全十二面と全比較円柱を保持し、三角形を選び直さない。
使われ方：生成第四辺と指定左辺の端点固定比較を同じ実複体から回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 元の第一 BF 面の二辺を同じ接合点で貼った全内ホーン。 -/
def tripleRawFirstHorn : (Λ[2, 1] : SSet.{u}) ⟶ tripleSharedDirectRealizationPasting :=
  horn₂₁.isPushout.desc tripleRawFirstLower tripleRawFirstUpper tripleRawFirst_corner

/-- 内ホーンの全下面を厳密に回収する。 -/
lemma tripleRawFirstHorn_lower :
    horn₂₁.ι₀₁ ≫ tripleRawFirstHorn.{u} = tripleRawFirstLower :=
  horn₂₁.isPushout.inl_desc _ _ _

/-- 内ホーンの全上面を厳密に回収する。 -/
lemma tripleRawFirstHorn_upper :
    horn₂₁.ι₁₂ ≫ tripleRawFirstHorn.{u} = tripleRawFirstUpper :=
  horn₂₁.isPushout.inr_desc _ _ _

/-- 元の第一全 BF 面を貼った中間実複体。 -/
def tripleRawFirstDomain : SSet.{u} := specifiedTriangleAttachment tripleRawFirstHorn

/-- 元の全十面・全比較族を持つ複体の包含。 -/
def tripleRawFirstOriginal : tripleSharedDirectRealizationPasting.{u} ⟶ tripleRawFirstDomain :=
  specifiedTriangleAttachmentOriginal tripleRawFirstHorn

/-- 元の第一全 BF 面の包含。 -/
def tripleRawFirstCell : (Δ[2] : SSet.{u}) ⟶ tripleRawFirstDomain :=
  specifiedTriangleAttachmentCell tripleRawFirstHorn

/-- 元の第二 whisker は第一面接続後も同じ全辺。 -/
def tripleRawSecondAttachingUpper : (Δ[1] : SSet.{u}) ⟶ tripleRawFirstDomain :=
  tripleRawSecondUpper ≫ tripleRawFirstOriginal

/-- 第一 BF 面の全上辺は元の同じ第一 whisker。 -/
lemma tripleRawFirstCell_upper :
    stdSimplex.δ 0 ≫ tripleRawFirstCell.{u} = tripleRawFirstUpper ≫ tripleRawFirstOriginal := by
  rw [tripleRawFirstCell, specifiedTriangleAttachment_face _ 0 (by decide)]
  rw [← Category.assoc, tripleRawFirstHorn_upper]
  rfl

/-- 第一対角と第二 whisker は実複体内で同じ終点を共有する。 -/
lemma tripleRawSecond_corner :
    stdSimplex.δ 0 ≫ stdSimplex.δ 1 ≫ tripleRawFirstCell.{u} =
      stdSimplex.δ 0 ≫ tripleRawSecondAttachingUpper := by
  have he : stdSimplex.δ.{u} (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) =
      stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) :=
    stdSimplex.δ_comp_δ_self (i := (0 : Fin 2))
  calc
    _ = stdSimplex.δ 0 ≫ stdSimplex.δ 0 ≫ tripleRawFirstCell := by
      simp only [← Category.assoc]
      rw [he]
    _ = stdSimplex.δ 0 ≫ tripleRawFirstUpper ≫ tripleRawFirstOriginal := by
      rw [tripleRawFirstCell_upper]
    _ = _ := by
      simpa only [tripleRawSecondAttachingUpper, Category.assoc] using
        congrArg (· ≫ tripleRawFirstOriginal) tripleRawWhiskers_target.{u}

/-- 元の共通対角と第二 whisker を貼る全外ホーン。 -/
def tripleRawSecondHorn : (Λ[2, 2] : SSet.{u}) ⟶ tripleRawFirstDomain :=
  horn₂₂.isPushout.desc (stdSimplex.δ 1 ≫ tripleRawFirstCell)
    tripleRawSecondAttachingUpper tripleRawSecond_corner

/-- 外ホーンは第一面の同じ全対角を回収する。 -/
lemma tripleRawSecondHorn_diagonal :
    horn₂₂.ι₀₂ ≫ tripleRawSecondHorn.{u} = stdSimplex.δ 1 ≫ tripleRawFirstCell :=
  horn₂₂.isPushout.inl_desc _ _ _

/-- 外ホーンは第二 whisker の同じ全辺を回収する。 -/
lemma tripleRawSecondHorn_upper :
    horn₂₂.ι₁₂ ≫ tripleRawSecondHorn.{u} = tripleRawSecondAttachingUpper :=
  horn₂₂.isPushout.inr_desc _ _ _

/-- 元の両 BF 全面・全十面・全比較族を接続した実複体。 -/
def tripleRawDiagramPasting : SSet.{u} := specifiedTriangleAttachment tripleRawSecondHorn

/-- 元の第一 BF 面までの全複体の包含。 -/
def tripleRawDiagramPastingFirstOriginal : tripleRawFirstDomain.{u} ⟶ tripleRawDiagramPasting :=
  specifiedTriangleAttachmentOriginal tripleRawSecondHorn

/-- 元の全十面・全円柱・全高次比較の複体全体の包含。 -/
def tripleRawDiagramPastingOriginal :
    tripleSharedDirectRealizationPasting.{u} ⟶ tripleRawDiagramPasting :=
  tripleRawFirstOriginal ≫ tripleRawDiagramPastingFirstOriginal

/-- 元の第一全 BF 面は同じ全二単体の像。 -/
def tripleRawDiagramPastingFirst : (Δ[2] : SSet.{u}) ⟶ tripleRawDiagramPasting :=
  tripleRawFirstCell ≫ tripleRawDiagramPastingFirstOriginal

/-- 元の第二全 BF 面も同じ全二単体の像。 -/
def tripleRawDiagramPastingSecond : (Δ[2] : SSet.{u}) ⟶ tripleRawDiagramPasting :=
  specifiedTriangleAttachmentCell tripleRawSecondHorn

/-- 元の両 BF 面は同じ全対角辺を実複体内で厳密に共有する。 -/
lemma tripleRawDiagramPasting_diagonal :
    stdSimplex.δ 1 ≫ tripleRawDiagramPastingFirst.{u} =
      stdSimplex.δ 1 ≫ tripleRawDiagramPastingSecond := by
  rw [tripleRawDiagramPastingSecond, specifiedTriangleAttachment_face _ 1 (by decide)]
  simpa only [tripleRawDiagramPastingFirst, tripleRawDiagramPastingFirstOriginal,
    Category.assoc] using
    congrArg (· ≫ specifiedTriangleAttachmentOriginal tripleRawSecondHorn)
      tripleRawSecondHorn_diagonal.{u}.symm

/-- 元の外ホーン全辺の像の一致は全外ホーンの一致を与える。 -/
lemma specifiedOuterHorn_map {B E : SSet.{u}} (q : (Λ[2, 2] : SSet.{u}) ⟶ B)
    (P : B ⟶ E) (T : (Δ[2] : SSet.{u}) ⟶ E)
    (h₀ : (horn₂₂.ι₀₂ ≫ q) ≫ P = stdSimplex.δ 1 ≫ T)
    (h₁ : (horn₂₂.ι₁₂ ≫ q) ≫ P = stdSimplex.δ 0 ≫ T) :
    q ≫ P = (SSet.horn 2 (2 : Fin 3)).ι ≫ T := by
  apply horn₂₂.isPushout.hom_ext
  · rw [← Category.assoc, ← Category.assoc, SSet.horn.ι_ι]
    exact h₀
  · rw [← Category.assoc, ← Category.assoc, SSet.horn.ι_ι]
    exact h₁

end SerrePositivity.KST.SConstruction
