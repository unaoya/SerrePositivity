module
public import SerrePositivity.KST.SConstruction.FixedCylinderBoundary

/-! # 元の全境界固定円柱を共有境界ごと実複体へ貼る
概要：元の円柱の入口と全入力境界を既存複体へ同時に貼り、出口の境界も同じ頂点に保つ。
方針：入口・全側面の境界複体を元の辺へ折り畳み、同じ全円柱との pushout を取る。
規約：元の全円柱と全既存複体を保持し、全入力境界を全時刻で厳密に固定する。
使われ方：共有端点を変更せずに元の正規化円柱を六面比較複体へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {A U B : SSet.{u}} (j : A ⟶ U) (e : U ⟶ B)

/-- 元の入口と全入力境界を既存の同じ辺へ貼った円柱接続複体。 -/
def fixedCylinderAttachment : SSet.{u} :=
  pushout (fixedCylinderBoundaryFold j ≫ e) (fixedCylinderBoundaryInclusion j)

/-- 元の既存複体全体の同じ包含。 -/
def fixedCylinderAttachmentOriginal : B ⟶ fixedCylinderAttachment j e :=
  pushout.inl (fixedCylinderBoundaryFold j ≫ e) (fixedCylinderBoundaryInclusion j)

/-- 元の全円柱の同じ包含。 -/
def fixedCylinderAttachmentCell : U ⊗ (Δ[1] : SSet.{u}) ⟶ fixedCylinderAttachment j e :=
  pushout.inr (fixedCylinderBoundaryFold j ≫ e) (fixedCylinderBoundaryInclusion j)

/-- 同じ全円柱の出口。 -/
def fixedCylinderAttachmentTarget : U ⟶ fixedCylinderAttachment j e :=
  SSet.ι₁ ≫ fixedCylinderAttachmentCell j e

/-- 元の全入口は、実複体内で既存の同じ全辺。 -/
lemma fixedCylinderAttachment_source :
    SSet.ι₀ ≫ fixedCylinderAttachmentCell j e = e ≫ fixedCylinderAttachmentOriginal j e := by
  have hs := congrArg (fixedCylinderBoundarySource j ≫ ·)
    (pushout.condition (f := fixedCylinderBoundaryFold j ≫ e)
      (g := fixedCylinderBoundaryInclusion j))
  simp only [← Category.assoc, fixedCylinderBoundaryFold_source,
    fixedCylinderBoundaryInclusion_source, Category.id_comp] at hs
  exact hs.symm

/-- 全入力境界上の円柱は、実複体内でも全時刻で既存の同じ境界へ折り畳まれる。 -/
lemma fixedCylinderAttachment_vertical :
    (j ▷ (Δ[1] : SSet.{u})) ≫ fixedCylinderAttachmentCell j e =
      fst A Δ[1] ≫ j ≫ e ≫ fixedCylinderAttachmentOriginal j e := by
  have hv := congrArg (fixedCylinderBoundaryVertical j ≫ ·)
    (pushout.condition (f := fixedCylinderBoundaryFold j ≫ e)
      (g := fixedCylinderBoundaryInclusion j))
  simp only [← Category.assoc, fixedCylinderBoundaryFold_vertical,
    fixedCylinderBoundaryInclusion_vertical] at hv
  exact hv.symm

/-- 出口の全入力境界は、実複体内で既存の同じ境界を厳密に保つ。 -/
lemma fixedCylinderAttachmentTarget_boundary :
    j ≫ fixedCylinderAttachmentTarget j e = j ≫ e ≫ fixedCylinderAttachmentOriginal j e := by
  rw [fixedCylinderAttachmentTarget, ← SSet.ι₁_comp_assoc, fixedCylinderAttachment_vertical,
    SSet.ι₁_fst_assoc]

variable {E : SSet.{u}} (P : B ⟶ E) {f g : U ⟶ E} (H : SSet.Homotopy f g)
  (he : e ≫ P = f)
  (hr : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ j ≫ f)

/-- 元の全境界固定円柱と既存複体を同時に保持する、接続全体の実写像。 -/
def fixedCylinderAttachmentMap : fixedCylinderAttachment j e ⟶ E :=
  pushout.desc (f := fixedCylinderBoundaryFold j ≫ e) (g := fixedCylinderBoundaryInclusion j)
    P H.h (((Category.assoc _ _ _).trans
      (congrArg (fixedCylinderBoundaryFold j ≫ ·) he)).trans
        (fixedCylinderBoundary_map j H hr).symm)

/-- 元の既存複体全体を厳密に回収する。 -/
lemma fixedCylinderAttachmentMap_original :
    fixedCylinderAttachmentOriginal j e ≫ fixedCylinderAttachmentMap j e P H he hr = P :=
  pushout.inl_desc _ _ _

/-- 元の同じ全円柱を厳密に回収する。 -/
lemma fixedCylinderAttachmentMap_cell :
    fixedCylinderAttachmentCell j e ≫ fixedCylinderAttachmentMap j e P H he hr = H.h :=
  pushout.inr_desc _ _ _

/-- 元の円柱の出口も、同じ元の全終点族を厳密に回収する。 -/
lemma fixedCylinderAttachmentMap_target :
    fixedCylinderAttachmentTarget j e ≫ fixedCylinderAttachmentMap j e P H he hr = g := by
  rw [fixedCylinderAttachmentTarget, Category.assoc, fixedCylinderAttachmentMap_cell, H.h₁]

end SerrePositivity.KST.SConstruction
