module
public import SerrePositivity.KST.SConstruction.TripleRawDiagramPasting

/-! # raw BF 二面の全接続辺を同じ実複体内で回収する
概要：第一面の両辺と第二面の上辺を、元の同じ既存辺へ厳密に照合する。
方針：指定三角形接続の全ホーン面の式を使う。
規約：全区間写像の等号を保持し、頂点だけの等号に弱めない。
使われ方：十二面の合成式を同じ辺路として消去する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 第一 BF 面の下面は既存の同じ右比較辺全体。 -/
lemma tripleRawDiagramPasting_first_lower :
    stdSimplex.δ 2 ≫ tripleRawDiagramPastingFirst.{u} =
      tripleRawFirstLower ≫ tripleRawDiagramPastingOriginal := by
  rw [tripleRawDiagramPastingFirst, ← Category.assoc, tripleRawFirstCell,
    specifiedTriangleAttachment_face _ 2 (by decide)]
  simp only [Category.assoc, tripleRawDiagramPastingOriginal, tripleRawFirstOriginal]
  rw [← Category.assoc horn₂₁.ι₀₁ tripleRawFirstHorn, tripleRawFirstHorn_lower]

/-- 第一 BF 面の上辺は元の同じ第一 whisker 全体。 -/
lemma tripleRawDiagramPasting_first_upper :
    stdSimplex.δ 0 ≫ tripleRawDiagramPastingFirst.{u} =
      tripleRawFirstUpper ≫ tripleRawDiagramPastingOriginal := by
  rw [tripleRawDiagramPastingFirst, ← Category.assoc, tripleRawFirstCell_upper]
  rfl

/-- 第二 BF 面の上辺も元の同じ第二 whisker 全体。 -/
lemma tripleRawDiagramPasting_second_upper :
    stdSimplex.δ 0 ≫ tripleRawDiagramPastingSecond.{u} =
      tripleRawSecondUpper ≫ tripleRawDiagramPastingOriginal := by
  rw [tripleRawDiagramPastingSecond, specifiedTriangleAttachment_face _ 0 (by decide)]
  rw [← Category.assoc, tripleRawSecondHorn_upper]
  rfl

end SerrePositivity.KST.SConstruction
