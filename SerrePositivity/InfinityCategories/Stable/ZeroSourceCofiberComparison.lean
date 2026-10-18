module
public import SerrePositivity.InfinityCategories.Stable.ZeroSourceProjection
public import SerrePositivity.InfinityCategories.Stable.SplitCofiberConnecting

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
namespace SerrePositivity.InfinityCategories

/-- 概要：二項余積の第一包含と標準第二射影は、接続射が零の cofiber/fiber 列で表せる。
方針：零始点の押し出しを列四角形へ延長し、元の二本の包含との合成で射影を同定する。
規約：三対象を元の指定頂点に一致させる。使われ方：標準余積との三角形の比較。 -/
lemma exists_coproductCofiberSequence {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : IsPushoutSquare R)
    (hz : IsZeroVertex (squareVertex R 0 0)) :
    ∃ (t : ZeroTriangle X) (ht : IsCofiberSequence t),
      Arrow.mk t.hoShortComplex.f = Arrow.mk (squareHoRight R) ∧
      Arrow.mk t.hoShortComplex.g = Arrow.mk (zeroSourceCoproductSnd R hR hz.1) ∧
      squareVertex t.square 0 0 = squareVertex R 1 0 ∧
      squareVertex t.square 1 0 = squareVertex R 1 1 ∧
      squareVertex t.square 1 1 = squareVertex R 0 1 ∧
      IsFiberSequence t ∧ IsSplitEpi t.hoShortComplex.g ∧ cofiberConnecting t ht = 0 := by
  obtain ⟨F, hleft, houter, hzero, hpush, hpull, _⟩ := exists_splitCofiberRectangle R hR hz
  obtain ⟨b, hb, hclass⟩ := exists_pastingProjection_eq_coproductSnd R hR hz F hleft houter
  let t : ZeroTriangle X :=
    { square := (β_ Δ[1] Δ[1]).hom ≫ pastingSquare F 0
      zero_corner := by
        change IsZeroVertex (squareVertex (pastingSquare F 0) 1 0)
        rw [hzero]
        exact hz }
  have hinc : (squareBottomArrow t.square).edge = (squareRightArrow R).edge := by
    rw [squareBottomArrow_edge, squareRightArrow_edge]
    apply congrArg SSet.yonedaEquiv
    change squareRightEdge ≫ pastingSquare F 2 = _
    rw [hleft]
  have hproj : (squareRightArrow t.square).edge = b.edge := by
    rw [hb, squareRightArrow_edge, squareTopArrow_edge]
    apply congrArg SSet.yonedaEquiv
    rfl
  have hfa : Arrow.mk t.hoShortComplex.f = Arrow.mk (squareHoRight R) :=
    SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hinc
  have hga : Arrow.mk t.hoShortComplex.g =
      Arrow.mk (zeroSourceCoproductSnd R hR hz.1) := by
    exact (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hproj).trans
      (congrArg Arrow.mk hclass)
  have hsnd : IsSplitEpi (zeroSourceCoproductSnd R hR hz.1) :=
    IsSplitEpi.mk' {
      section_ := squareHoTop R
      id := zeroSourceCoproduct_top_snd R hR hz.1 }
  have hs : IsSplitEpi t.hoShortComplex.g := by
    change IsSplitEpi (Arrow.mk t.hoShortComplex.g).hom
    rw [hga]
    exact hsnd
  let : IsSplitEpi t.hoShortComplex.g := hs
  have ht : IsCofiberSequence t :=
    (isPushoutSquare_iff_transpose (pastingSquare F 0)).1 hpush
  refine ⟨t, ht, hfa, hga, ?_, ?_, ?_,
    (isPullbackSquare_iff_transpose (pastingSquare F 0)).1 hpull,
    hs, cofiberConnecting_eq_zero_of_epi t ht⟩
  · have he : squareVertex t.square 0 0 = squareVertex (pastingSquare F 2) 1 0 := rfl
    rw [he, hleft]
  · have he : squareVertex t.square 1 0 = squareVertex (pastingSquare F 2) 1 1 := rfl
    rw [he, hleft]
  · have he : squareVertex t.square 1 1 = squareVertex (pastingSquare F 1) 1 1 := rfl
    rw [he, houter]
    rfl

end SerrePositivity.InfinityCategories
