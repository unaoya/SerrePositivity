module
public import SerrePositivity.KST.SConstruction.FixedCylinderAttachment
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # 既存の二辺の間へ元の全境界固定比較円柱を貼る
概要：元の全境界固定円柱を既存の第一辺へ接続し、出口を既存の第二辺全体へ貼る。
方針：全境界固定円柱接続の後、同じ全出口と既存辺を coequalizer で厳密に同定する。
規約：元の全円柱と全既存複体を保持し、比較円柱を選び直さない。
使われ方：左右の元の直接補正辺の全比較を、同じ全段面複体へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 共通固定境界の表示は、元の始点辺の同じ全境界固定式へ移せる。 -/
lemma fixedBoundaryHomotopy_source {A U E : SSet.{u}} (j : A ⟶ U)
    {f g : U ⟶ E} (H : SSet.Homotopy f g) (b : A ⟶ E)
    (hr : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ b) :
    (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ j ≫ f := by
  have hb : j ≫ f = b := by
    calc
      _ = SSet.ι₀ ≫ (j ▷ (Δ[1] : SSet.{u})) ≫ H.h := by
        rw [SSet.ι₀_comp_assoc, H.h₀]
      _ = SSet.ι₀ ≫ fst A Δ[1] ≫ b := congrArg (SSet.ι₀ ≫ ·) hr
      _ = _ := by rw [SSet.ι₀_fst_assoc]
  exact hr.trans (congrArg (fst A Δ[1] ≫ ·) hb.symm)

variable {A U B : SSet.{u}} (j : A ⟶ U) (e d : U ⟶ B)

/-- 元の全境界固定円柱の出口を、既存の第二辺全体へ貼った実複体。 -/
def fixedCylinderComparisonAttachment : SSet.{u} :=
  coequalizer (fixedCylinderAttachmentTarget j e) (d ≫ fixedCylinderAttachmentOriginal j e)

/-- 元の既存複体全体の同じ像。 -/
def fixedCylinderComparisonOriginal : B ⟶ fixedCylinderComparisonAttachment j e d :=
  fixedCylinderAttachmentOriginal j e ≫
    coequalizer.π (fixedCylinderAttachmentTarget j e) (d ≫ fixedCylinderAttachmentOriginal j e)

/-- 元の全比較円柱の同じ像。 -/
def fixedCylinderComparisonCell : U ⊗ (Δ[1] : SSet.{u}) ⟶
    fixedCylinderComparisonAttachment j e d :=
  fixedCylinderAttachmentCell j e ≫
    coequalizer.π (fixedCylinderAttachmentTarget j e) (d ≫ fixedCylinderAttachmentOriginal j e)

/-- 元の第一辺は、実複体内で比較円柱の同じ全入口。 -/
lemma fixedCylinderComparison_source :
    SSet.ι₀ ≫ fixedCylinderComparisonCell j e d = e ≫ fixedCylinderComparisonOriginal j e d := by
  rw [fixedCylinderComparisonCell, ← Category.assoc, fixedCylinderAttachment_source]
  simp only [fixedCylinderComparisonOriginal, Category.assoc]

/-- 元の第二辺も、実複体内で比較円柱の同じ全出口。 -/
lemma fixedCylinderComparison_target :
    SSet.ι₁ ≫ fixedCylinderComparisonCell j e d = d ≫ fixedCylinderComparisonOriginal j e d := by
  rw [fixedCylinderComparisonCell, ← Category.assoc]
  change fixedCylinderAttachmentTarget j e ≫
    coequalizer.π (fixedCylinderAttachmentTarget j e) (d ≫ fixedCylinderAttachmentOriginal j e) = _
  exact (coequalizer.condition _ _).trans (Category.assoc _ _ _)

/-- 元の全入力境界の比較は、実複体内で全時刻を通して同じ既存境界へ折り畳まれる。 -/
lemma fixedCylinderComparison_vertical :
    (j ▷ (Δ[1] : SSet.{u})) ≫ fixedCylinderComparisonCell j e d =
      fst A Δ[1] ≫ j ≫ e ≫ fixedCylinderComparisonOriginal j e d := by
  rw [fixedCylinderComparisonCell, ← Category.assoc, fixedCylinderAttachment_vertical]
  simp only [fixedCylinderComparisonOriginal, Category.assoc]

variable {E : SSet.{u}} (P : B ⟶ E) {f g : U ⟶ E} (H : SSet.Homotopy f g)
  (he : e ≫ P = f) (hd : d ≫ P = g)
  (hr : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ j ≫ f)

/-- 元の全比較円柱と既存の両辺・全複体を同時に保持する実写像。 -/
def fixedCylinderComparisonMap : fixedCylinderComparisonAttachment j e d ⟶ E :=
  coequalizer.desc (fixedCylinderAttachmentMap j e P H he hr)
    ((fixedCylinderAttachmentMap_target j e P H he hr).trans
      (((Category.assoc _ _ _).trans
        ((congrArg (d ≫ ·) (fixedCylinderAttachmentMap_original j e P H he hr)).trans hd)).symm))

/-- 元の既存複体全体を厳密に回収する。 -/
lemma fixedCylinderComparisonMap_original :
    fixedCylinderComparisonOriginal j e d ≫ fixedCylinderComparisonMap j e d P H he hd hr = P := by
  rw [fixedCylinderComparisonOriginal, fixedCylinderComparisonMap, Category.assoc,
    coequalizer.π_desc, fixedCylinderAttachmentMap_original]

/-- 元の全比較円柱そのものも厳密に回収する。 -/
lemma fixedCylinderComparisonMap_cell :
    fixedCylinderComparisonCell j e d ≫ fixedCylinderComparisonMap j e d P H he hd hr = H.h := by
  rw [fixedCylinderComparisonCell, fixedCylinderComparisonMap, Category.assoc,
    coequalizer.π_desc, fixedCylinderAttachmentMap_cell]

end SerrePositivity.KST.SConstruction
