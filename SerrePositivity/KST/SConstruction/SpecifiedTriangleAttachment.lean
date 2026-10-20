module
public import SerrePositivity.KST.SConstruction.CorrectionPastingTriangleAttachment

/-! # 指定した全ホーンへ元の同じ全三角形を貼る
概要：既存複体の指定全ホーンへ、対応する元の三角形全体を貼る。
方針：ホーン包含の pushout と、元の全ホーンの厳密な像の一致を使う。
規約：元の全三角形を保持し、Kan 充填で新しい面を選ばない。
使われ方：外側二部分面と元の BF 比較二三角形の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
variable {B : SSet.{u}} {k : Fin 3} (a : (Λ[2, k] : SSet.{u}) ⟶ B)

/-- 指定全ホーンへ元の全三角形を貼った実複体。 -/
def specifiedTriangleAttachment : SSet.{u} := pushout a (SSet.horn 2 k).ι

/-- 元の既存複体全体の包含。 -/
def specifiedTriangleAttachmentOriginal : B ⟶ specifiedTriangleAttachment a :=
  pushout.inl a (SSet.horn 2 k).ι

/-- 元の指定全三角形の包含。 -/
def specifiedTriangleAttachmentCell : (Δ[2] : SSet.{u}) ⟶ specifiedTriangleAttachment a :=
  pushout.inr a (SSet.horn 2 k).ι

/-- 元の全ホーンは実複体内で同じ三角形の全ホーン。 -/
lemma specifiedTriangleAttachment_shared :
    a ≫ specifiedTriangleAttachmentOriginal a =
      (SSet.horn 2 k).ι ≫ specifiedTriangleAttachmentCell a := pushout.condition

variable {E : SSet.{u}} (P : B ⟶ E) (T : (Δ[2] : SSet.{u}) ⟶ E)
  (ha : a ≫ P = (SSet.horn 2 k).ι ≫ T)

/-- 元の既存複体と全指定三角形を同時に保持する全写像。 -/
def specifiedTriangleAttachmentMap : specifiedTriangleAttachment a ⟶ E :=
  pushout.desc (f := a) (g := (SSet.horn 2 k).ι) P T ha

/-- 元の全既存複体を厳密に回収する。 -/
lemma specifiedTriangleAttachmentMap_original :
    specifiedTriangleAttachmentOriginal a ≫ specifiedTriangleAttachmentMap a P T ha = P :=
  pushout.inl_desc _ _ _

/-- 元の全指定三角形も厳密に回収する。 -/
lemma specifiedTriangleAttachmentMap_cell :
    specifiedTriangleAttachmentCell a ≫ specifiedTriangleAttachmentMap a P T ha = T :=
  pushout.inr_desc _ _ _

/-- 元の内ホーンの全両辺の一致は、全ホーンの実写像の一致を与える。 -/
lemma specifiedInnerHorn_map {B E : SSet.{u}} (q : (Λ[2, 1] : SSet.{u}) ⟶ B)
    (P : B ⟶ E) (T : (Δ[2] : SSet.{u}) ⟶ E)
    (h₀ : (horn₂₁.ι₀₁ ≫ q) ≫ P = stdSimplex.δ 2 ≫ T)
    (h₁ : (horn₂₁.ι₁₂ ≫ q) ≫ P = stdSimplex.δ 0 ≫ T) :
    q ≫ P = (SSet.horn 2 (1 : Fin 3)).ι ≫ T := by
  apply horn₂₁.isPushout.hom_ext
  · rw [← Category.assoc, ← Category.assoc, SSet.horn.ι_ι]
    exact h₀
  · rw [← Category.assoc, ← Category.assoc, SSet.horn.ι_ι]
    exact h₁

end SerrePositivity.KST.SConstruction
