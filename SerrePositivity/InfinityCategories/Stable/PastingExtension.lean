module
public import SerrePositivity.InfinityCategories.Stable.ColimitExistenceTransfer
public import SerrePositivity.InfinityCategories.Stable.PastingLeftAttachment
public import SerrePositivity.InfinityCategories.Stable.PastingCornerJoinIso

/-! # 指定した五頂点図式から押し出し長方形への延長

概要：左が押し出しである五頂点図式は、外側基底の余極限から右も押し出しとなる長方形へ延長できる。
方針：左の普遍余錐を付加する制限射で余極限を持ち上げ、join と長方形の同型を使う。
規約：五頂点上の図式と外側基底上の余極限余錐を厳密に保持する。
使われ方：懸垂と cofiber から有限余極限を構成するための貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：五頂点図式の左四角形を取り出す。
方針：左四角形の標準形と部分複体包含で制限する。
規約：まだ長方形全体の図式は与えない。使われ方：左押し出しの仮定。 -/
def pastingCornerLeftDiagram {X : SSet.{u}} (G : (pastingCorner : SSet.{u}) ⟶ X) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X :=
  pastingLeftSquareIso.hom ≫ Subcomplex.homOfLE pastingLeftSquare_le_corner ≫ G

/-- 概要：左が押し出しである五頂点図式は外側基底で選んだ余極限を保って長方形へ延長できる。
方針：余極限付加の厳密な延長を使い、得られた余錐を長方形表示に直す。
規約：右四角形も押し出しとなる。使われ方：有限余極限の存在を組み立てる工程。 -/
lemma exists_pastingExtension_of_outerColimit {X : SSet.{u}} [Quasicategory X]
    (G : (pastingCorner : SSet.{u}) ⟶ X) (hleft : IsPushoutSquare (pastingCornerLeftDiagram G))
    (d : JoinCocone (pastingOuterBaseToCorner ≫ G)) (hd : IsColimitCone d) :
    ∃ F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X,
      pastingCorner.ι ≫ F = G ∧ IsPushoutSquare (pastingSquare F 0) ∧
        (pastingOuterCocone F).val = d.val := by
  let c := pushoutCocone (pastingCornerLeftDiagram G)
  have hj : pastingLeftAttachmentCone ≫ G = c.val := rfl
  obtain ⟨e, he, hek, _⟩ := exists_colimitCocone_extension_of_colimit_attachment c hleft
    (pastingLeftSpanIso.hom ≫ pastingLeftSpan.ι) pastingLeftAttachmentCone
    pastingOuterBaseToCorner pastingLeftAttachment_isPushout G hj d hd
  let F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X := pastingCornerJoinIso.inv ≫ e.val
  have hcorner : pastingCorner.ι ≫ F = G := by
    have hi : pastingCorner.ι ≫ pastingCornerJoinIso.inv =
        joinInl (pastingCorner : SSet.{u}) Δ[0] := by
      rw [← pastingCornerCocone_inl, Category.assoc]
      change joinInl _ _ ≫ (pastingCornerJoinIso.hom ≫ pastingCornerJoinIso.inv) = _
      rw [Iso.hom_inv_id, Category.comp_id]
    change pastingCorner.ι ≫ (pastingCornerJoinIso.inv ≫ e.val) = _
    rw [← Category.assoc, hi]
    exact e.property
  have hval : (pastingCocone F).val = e.val := by
    change pastingCornerJoinIso.hom ≫ (pastingCornerJoinIso.inv ≫ e.val) = _
    rw [Iso.hom_inv_id_assoc]
  refine ⟨F, hcorner, ?_, ?_⟩
  · apply (pastingCocone_isColimitCone_iff_right F).1
    exact (isColimitCone_iff_of_val_eq (pastingCocone F) e hval).2 he
  · have h := congrArg Subtype.val hek
    change joinMap pastingOuterBaseToCorner (𝟙 Δ[0]) ≫ e.val = d.val at h
    change joinMap pastingOuterBaseToCorner (𝟙 Δ[0]) ≫ (pastingCocone F).val = _
    rw [hval]
    exact h

end SerrePositivity.InfinityCategories
