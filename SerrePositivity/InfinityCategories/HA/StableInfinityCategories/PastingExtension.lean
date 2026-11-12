module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ColimitExistenceTransfer
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingLeftAttachment
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingCornerJoinIso

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：五頂点図式の左四角形を取り出す。
方針：左四角形の標準形と部分複体包含で制限する。
規約：まだ長方形全体の図式は与えない。使われ方：左押し出しの仮定。 -/
def pastingCornerLeftDiagram {X : SSet.{u}} (G : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) ⟶ X) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquareIso.hom ≫ Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare_le_corner ≫ G

/-- 概要：左が押し出しである五頂点図式は外側基底で選んだ余極限を保って長方形へ延長できる。
方針：余極限付加の厳密な延長を使い、得られた余錐を長方形表示に直す。
規約：右四角形も押し出しとなる。使われ方：有限余極限の存在を組み立てる工程。 -/
lemma exists_pastingExtension_of_outerColimit {X : SSet.{u}} [Quasicategory X]
    (G : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) ⟶ X) (hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (pastingCornerLeftDiagram G))
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner ≫ G)) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d) :
    ∃ F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ F = G ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0) ∧
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterCocone F).val = d.val := by
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (pastingCornerLeftDiagram G)
  have hj : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftAttachmentCone ≫ G = c.val := rfl
  obtain ⟨e, he, hek, _⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_colimitCocone_extension_of_colimit_attachment c hleft
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSpan.ι) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftAttachmentCone
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftAttachment_isPushout G hj d hd
  let F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerJoinIso.inv ≫ e.val
  have hcorner : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ F = G := by
    have hi : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerJoinIso.inv =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) Δ[0] := by
      rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCornerCocone_inl, Category.assoc]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerJoinIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerJoinIso.inv) = _
      rw [Iso.hom_inv_id, Category.comp_id]
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerJoinIso.inv ≫ e.val) = _
    rw [← Category.assoc, hi]
    exact e.property
  have hval : (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.pastingCocone F).val = e.val := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerJoinIso.hom ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerJoinIso.inv ≫ e.val) = _
    rw [Iso.hom_inv_id_assoc]
  refine ⟨F, hcorner, ?_, ?_⟩
  · apply (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.pastingCocone_isColimitCone_iff_right F).1
    exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.pastingCocone F) e hval).2 he
  · have h := congrArg Subtype.val hek
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner (𝟙 Δ[0]) ≫ e.val = d.val at h
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner (𝟙 Δ[0]) ≫ (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.pastingCocone F).val = _
    rw [hval]
    exact h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
