module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroSourceProjection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SplitCofiberConnecting

/-! # 二項余積の包含と標準射影を持つ cofiber 列

概要：零始点の押し出しの第一包含の cofiber 列の第二射は、二項余積の標準第二射影となる。
方針：列四角形への延長で得た射影を二項余積の普遍性で同定する。
規約：端点の等号は Arrow の等号に含める。使われ方：標準余積三角形と双積の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：二項余積の第一包含と標準第二射影は、接続射が零の cofiber/fiber 列で表せる。
方針：零始点の押し出しを列四角形へ延長し、元の二本の包含との合成で射影を同定する。
規約：三対象を元の指定頂点に一致させる。使われ方：標準余積との三角形の比較。 -/
lemma exists_coproductCofiberSequence {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R)
    (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 0)) :
    ∃ (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t),
      Arrow.mk t.hoShortComplex.f = Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight R) ∧
      Arrow.mk t.hoShortComplex.g = Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproductSnd R hR hz.1) ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 1 0 ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 1 1 ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 1 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 1 ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t ∧ IsSplitEpi t.hoShortComplex.g ∧ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht = 0 := by
  obtain ⟨F, hleft, houter, hzero, hpush, hpull, _⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_splitCofiberRectangle R hR hz
  obtain ⟨b, hb, hclass⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_pastingProjection_eq_coproductSnd R hR hz F hleft houter
  let t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X :=
    { square := (β_ Δ[1] Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0
      zero_corner := by
        change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0) 1 0)
        rw [hzero]
        exact hz }
  have hinc : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow t.square).edge = (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow R).edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge]
    apply congrArg SSet.yonedaEquiv
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2 = _
    rw [hleft]
  have hproj : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow t.square).edge = b.edge := by
    rw [hb, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge]
    apply congrArg SSet.yonedaEquiv
    rfl
  have hfa : Arrow.mk t.hoShortComplex.f = Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight R) :=
    SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hinc
  have hga : Arrow.mk t.hoShortComplex.g =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproductSnd R hR hz.1) := by
    exact (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hproj).trans
      (congrArg Arrow.mk hclass)
  have hsnd : IsSplitEpi (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproductSnd R hR hz.1) :=
    IsSplitEpi.mk' {
      section_ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoTop R
      id := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproduct_top_snd R hR hz.1 }
  have hs : IsSplitEpi t.hoShortComplex.g := by
    change IsSplitEpi (Arrow.mk t.hoShortComplex.g).hom
    rw [hga]
    exact hsnd
  let : IsSplitEpi t.hoShortComplex.g := hs
  have ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t :=
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0)).1 hpush
  refine ⟨t, ht, hfa, hga, ?_, ?_, ?_,
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_transpose (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0)).1 hpull,
    hs, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting_eq_zero_of_epi t ht⟩
  · have he : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) 1 0 := rfl
    rw [he, hleft]
  · have he : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) 1 1 := rfl
    rw [he, hleft]
  · have he : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 1 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) 1 1 := rfl
    rw [he, houter]
    rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
