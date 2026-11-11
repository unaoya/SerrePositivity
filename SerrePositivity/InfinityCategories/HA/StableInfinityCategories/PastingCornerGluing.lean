module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingBottomTriangle
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingExtension

/-! # 左四角形と底辺二単体の貼り合わせ

概要：下辺の一致する四角形と二単体は五頂点図式へ一意に貼り合わせられる。
方針：部分複体の和と交わりの pushout を標準の正方形・区間・二単体へ移す。
規約：両方の入力図式を厳密に保持する。使われ方：懸垂と零射からの直和の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：左四角形を五頂点図式へ含める。
方針：左四角形の標準同型を部分複体包含と合成する。
規約：標準四角形からの射。使われ方：図式の貼り合わせの第一包含。 -/
def pastingCornerLeftInclusion : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquareIso.hom ≫ Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare_le_corner

/-- 概要：底辺二単体を五頂点図式へ含める。
方針：底辺三角形の標準同型を部分複体包含と合成する。
規約：標準二単体からの射。使われ方：図式の貼り合わせの第二包含。 -/
def pastingCornerBottomInclusion : (Δ[2] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingBottomFaceIso.hom ≫ Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingBottomFace_le_corner

/-- 概要：五頂点図式は左四角形と底辺二単体の下辺に沿う pushout である。
方針：部分複体の双カルテジアン四角形を三つの標準同型で移す。
規約：共通辺は二単体の面 δ₂。使われ方：四角形と合成二単体を同時に指定する。 -/
lemma pastingCornerBottom_isPushout :
    IsPushout _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge.{u} (stdSimplex.δ (2 : Fin 3))
      pastingCornerLeftInclusion pastingCornerBottomInclusion := by
  let sq : Subcomplex.BicartSq (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare ⊓ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingBottomFace)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingBottomFace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner := {
    sup_eq := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare_sup_bottomFace
    inf_eq := rfl }
  apply sq.isPushout.of_iso' _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingBottomIntersectionIso _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquareIso
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingBottomFaceIso (Iso.refl _)
  · apply (cancel_mono _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare.ι).1
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Prod.ext
    · rfl
    · apply stdSimplex.ext
      intro j
      rfl
  · apply (cancel_mono _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingBottomFace.ι).1
    rfl
  · rfl
  · rfl

/-- 概要：下辺の一致する四角形と二単体を五頂点図式へ貼る。
方針：形状の pushout の降下射を使う。
規約：値域に仮定を課さない。使われ方：懸垂と合成二単体の入力図式。 -/
def pastingCornerGlue {X : SSet.{u}} (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (τ : (Δ[2] : SSet.{u}) ⟶ X) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ L = stdSimplex.δ (2 : Fin 3) ≫ τ) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) ⟶ X := pastingCornerBottom_isPushout.desc L τ h

/-- 概要：貼り合わせは左四角形を厳密に保持する。
方針：pushout の第一包含の式。規約：射の等号。
使われ方：左四角形の普遍性の移送。 -/
lemma pastingCornerGlue_left {X : SSet.{u}} (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (τ : (Δ[2] : SSet.{u}) ⟶ X) (h) :
    pastingCornerLeftInclusion ≫ pastingCornerGlue L τ h = L :=
  pastingCornerBottom_isPushout.inl_desc _ _ _

/-- 概要：貼り合わせは底辺の二単体を厳密に保持する。
方針：pushout の第二包含の式。規約：射の等号。
使われ方：零射の合成の指定。 -/
lemma pastingCornerGlue_bottom {X : SSet.{u}} (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (τ : (Δ[2] : SSet.{u}) ⟶ X) (h) :
    pastingCornerBottomInclusion ≫ pastingCornerGlue L τ h = τ :=
  pastingCornerBottom_isPushout.inr_desc _ _ _

/-- 概要：貼り合わせた五頂点図式の左四角形は入力と厳密に一致する。
方針：第一包含の式を左図式の定義で読む。
規約：余極限の仮定は不要。使われ方：長方形の延長定理への適用。 -/
lemma pastingCornerLeftDiagram_glue {X : SSet.{u}} (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (τ : (Δ[2] : SSet.{u}) ⟶ X) (h) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerLeftDiagram (pastingCornerGlue L τ h) = L := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquareIso.hom ≫
    (Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare_le_corner ≫ pastingCornerGlue L τ h) = L
  rw [← Category.assoc]
  exact pastingCornerGlue_left L τ h

/-- 概要：押し出し四角形と合成二単体から、右も押し出しとなる長方形を構成する。
方針：五頂点図式へ貼り、外側基底の指定余極限を持ち上げる。
規約：左四角形・下側二単体・外側余錐を厳密に保持する。
使われ方：懸垂と cofiber を組み合わせる有限余極限の構成。 -/
lemma exists_pushoutRectangle_of_left_and_bottom {X : SSet.{u}} [Quasicategory X]
    (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (τ : (Δ[2] : SSet.{u}) ⟶ X)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ L = stdSimplex.δ (2 : Fin 3) ≫ τ) (hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare L)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner ≫ pastingCornerGlue L τ h))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d) :
    ∃ F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2 = L ∧ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingBottomTriangle F = τ ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0) ∧ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterCocone F).val = d.val := by
  have hgl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerLeftDiagram (pastingCornerGlue L τ h)) := by
    rw [pastingCornerLeftDiagram_glue]
    exact hleft
  obtain ⟨F, hF, hp, hdF⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_pastingExtension_of_outerColimit
    (pastingCornerGlue L τ h) hgl d hd
  have hi : pastingCornerLeftInclusion.{u} ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι =
      stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u}) := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquareIso.hom ≫
      (Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquare_le_corner ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι) = _
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftSquareIso_hom_ι
  have hb : pastingCornerBottomInclusion.{u} ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι =
      CartesianMonoidalCategory.lift (𝟙 (Δ[2] : SSet.{u}))
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  refine ⟨F, ?_, ?_, hp, hdF⟩
  · change (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ F = L
    rw [← hi, Category.assoc, hF]
    exact pastingCornerGlue_left L τ h
  · change CartesianMonoidalCategory.lift (𝟙 (Δ[2] : SSet.{u}))
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ F = τ
    rw [← hb, Category.assoc, hF]
    exact pastingCornerGlue_bottom L τ h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
