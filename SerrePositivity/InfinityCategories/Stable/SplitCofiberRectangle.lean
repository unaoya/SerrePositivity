module
public import SerrePositivity.InfinityCategories.Stable.PastingSplitProjection
public import SerrePositivity.InfinityCategories.Stable.SquareDuality

/-! # 零始点の押し出しの包含の cofiber

概要：零始点の押し出しの一方の包含を、他方を cofiber とする列へ延長する。
方針：戻り二単体と列四角形を保持した長方形を作り、右側を転置して安定性を使う。
規約：元の押し出しを厳密に保持する。使われ方：和の包含と射影の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：零始点の押し出しは外側が列四角形で右側が双カルテジアンの長方形へ延長できる。
方針：底辺の戻り二単体を選び、右四角形の零角を転置して安定性を適用する。
規約：左四角形と外側四角形を厳密に保持する。使われ方：和の包含の fiber/cofiber。 -/
lemma exists_splitCofiberRectangle {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hL : IsPushoutSquare L)
    (hz : IsZeroVertex (squareVertex L 0 0)) :
    ∃ F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X,
      pastingSquare F 2 = L ∧
      pastingSquare F 1 = squareColumnDiagram (squareLeftEdge ≫ L) ∧
      squareVertex (pastingSquare F 0) 1 0 = squareVertex L 0 0 ∧
      IsPushoutSquare (pastingSquare F 0) ∧ IsPullbackSquare (pastingSquare F 0) ∧
        IsSplitEpi (squareHoTop (pastingSquare F 0)) := by
  obtain ⟨τ, hτ₂, hτ₁⟩ := exists_zeroReturnTriangle hz (squareBottomArrow L)
  have h : squareBottomEdge ≫ L = stdSimplex.δ (2 : Fin 3) ≫ τ := by
    rw [hτ₂, squareBottomArrow_edge]
    exact ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).symm_apply_apply
      (squareBottomEdge ≫ L)).symm
  obtain ⟨F, hleft, _, hright, houter⟩ :=
    exists_pushoutRectangle_of_returnTriangle L hL τ h hτ₁
  have hzero : squareVertex (pastingSquare F 0) 1 0 = squareVertex L 0 0 := by
    have hv : squareVertex (pastingSquare F 0) 1 0 =
        squareVertex (pastingSquare F 1) 1 0 := rfl
    rw [houter] at hv
    exact hv
  let t : ZeroTriangle X :=
    { square := (β_ Δ[1] Δ[1]).hom ≫ pastingSquare F 0
      zero_corner := by
        change IsZeroVertex (squareVertex (pastingSquare F 0) 1 0)
        rw [hzero]
        exact hz }
  have ht : IsPullbackSquare t.square := IsStable.pullback_of_pushout t
    ((isPushoutSquare_iff_transpose (pastingSquare F 0)).1 hright)
  exact ⟨F, hleft, houter, hzero, hright,
    (isPullbackSquare_iff_transpose (pastingSquare F 0)).2 ht,
    pastingTop_isSplitEpi_of_outer_column F (squareLeftEdge ≫ L) houter⟩

/-- 概要：零始点の押し出しの第一包含の cofiber は他方の入力頂点であり、fiber 列でもある。
方針：前補題の右四角形を転置し、共有辺と列四角形の終点を計算する。
規約：第一包含の実際の射と三つの対象を保持し、第二射の切断も示す。使われ方：積と余積の比較。 -/
lemma exists_cofiberSequence_of_zeroSourcePushout {X : SSet.{u}}
    [Quasicategory X] [IsStable X]
    (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hL : IsPushoutSquare L)
    (hz : IsZeroVertex (squareVertex L 0 0)) :
    ∃ t : ZeroTriangle X,
      squareBottomEdge ≫ t.square = squareRightEdge ≫ L ∧
      squareVertex t.square 0 0 = squareVertex L 1 0 ∧
      squareVertex t.square 1 0 = squareVertex L 1 1 ∧
      squareVertex t.square 1 1 = squareVertex L 0 1 ∧
      IsCofiberSequence t ∧ IsFiberSequence t ∧ IsSplitEpi (squareHoRight t.square) := by
  obtain ⟨F, hleft, houter, hzero, hpush, hpull, hsplit⟩ := exists_splitCofiberRectangle L hL hz
  let t : ZeroTriangle X :=
    { square := (β_ Δ[1] Δ[1]).hom ≫ pastingSquare F 0
      zero_corner := by
        change IsZeroVertex (squareVertex (pastingSquare F 0) 1 0)
        rw [hzero]
        exact hz }
  refine ⟨t, ?_, ?_, ?_, ?_,
    (isPushoutSquare_iff_transpose (pastingSquare F 0)).1 hpush,
    (isPullbackSquare_iff_transpose (pastingSquare F 0)).1 hpull, ?_⟩
  · have he : squareBottomEdge ≫ t.square = squareRightEdge ≫ pastingSquare F 2 := rfl
    rw [he, hleft]
  · have he : squareVertex t.square 0 0 = squareVertex (pastingSquare F 2) 1 0 := rfl
    rw [he, hleft]
  · have he : squareVertex t.square 1 0 = squareVertex (pastingSquare F 2) 1 1 := rfl
    rw [he, hleft]
  · have he : squareVertex t.square 1 1 = squareVertex (pastingSquare F 1) 1 1 := rfl
    rw [he, houter]
    rfl
  · have he : (squareRightArrow t.square).edge =
        (squareTopArrow (pastingSquare F 0)).edge := by
      rw [squareRightArrow_edge, squareTopArrow_edge]
      apply congrArg SSet.yonedaEquiv
      rfl
    have ha := SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ he
    change IsSplitEpi (Arrow.mk (squareHoRight t.square)).hom
    change Arrow.mk (squareHoRight t.square) = Arrow.mk (squareHoTop (pastingSquare F 0)) at ha
    rw [ha]
    exact hsplit

end SerrePositivity.InfinityCategories
