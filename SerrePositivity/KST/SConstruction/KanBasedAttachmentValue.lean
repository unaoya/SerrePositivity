module
public import SerrePositivity.KST.SConstruction.KanBasedCylinderValue
public import SerrePositivity.KST.SConstruction.FixedCylinderComparisonAttachment

/-! # 境界固定円柱の接続を通した元の辺の群値
概要：全境界を固定して貼った円柱の入口と出口は、どの Kan 値写像の下でも同じ値を持つ。
方針：元の接続複体内の全境界固定式と、全円柱の入口・出口の厳密な回収を使う。
規約：接続後の実写像を入力に使い、二辺の類の一致を仮定しない。
使われ方：十二面複体の両正規化円柱と共有直接比較の値の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {B E : SSet.{u}} [KanComplex E] (c : hoFunctor.obj E)

/-- 元の全境界固定接続の出口の値は入口の同じ全辺の値。 -/
lemma kanBasedEdgeValue_attachment (e : (Δ[1] : SSet.{u}) ⟶ B)
    (P : fixedCylinderAttachment (SSet.boundary 1).ι e ⟶ E) :
    kanBasedEdgeValue c (fixedCylinderAttachmentTarget (SSet.boundary 1).ι e ≫ P) =
      kanBasedEdgeValue c (e ≫ fixedCylinderAttachmentOriginal (SSet.boundary 1).ι e ≫ P) := by
  have h := kanBasedEdgeValue_relative c
    (fixedCylinderAttachmentCell (SSet.boundary 1).ι e ≫ P)
    (e ≫ fixedCylinderAttachmentOriginal (SSet.boundary 1).ι e ≫ P)
    (by
      rw [← Category.assoc, fixedCylinderAttachment_vertical]
      simp only [Category.assoc])
  simp only [← Category.assoc, fixedCylinderAttachment_source] at h
  exact h.symm

/-- 元の全境界固定比較接続は、既存の両全辺の同じ値を与える。 -/
lemma kanBasedEdgeValue_comparisonAttachment (e d : (Δ[1] : SSet.{u}) ⟶ B)
    (P : fixedCylinderComparisonAttachment (SSet.boundary 1).ι e d ⟶ E) :
    kanBasedEdgeValue c (e ≫ fixedCylinderComparisonOriginal (SSet.boundary 1).ι e d ≫ P) =
      kanBasedEdgeValue c (d ≫ fixedCylinderComparisonOriginal (SSet.boundary 1).ι e d ≫ P) := by
  have h := kanBasedEdgeValue_relative c
    (fixedCylinderComparisonCell (SSet.boundary 1).ι e d ≫ P)
    (e ≫ fixedCylinderComparisonOriginal (SSet.boundary 1).ι e d ≫ P)
    (by
      rw [← Category.assoc, fixedCylinderComparison_vertical]
      simp only [Category.assoc])
  simpa only [← Category.assoc, fixedCylinderComparison_source,
    fixedCylinderComparison_target] using h

end SerrePositivity.KST.SConstruction
