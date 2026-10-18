module
public import SerrePositivity.InfinityCategories.Stable.CofiberRotationRectangle
public import SerrePositivity.InfinityCategories.Stable.CofiberConnectingIndependence
public import SerrePositivity.InfinityCategories.Stable.PastingSplitProjection
public import SerrePositivity.InfinityCategories.Stable.ArrowSquareHomotopy

/-! # 回転列の第二射と接続射

概要：回転長方形から得た列の第一射は元の第二射、第二射は指定 suspension への接続射である。
方針：左から外側への始点固定の比較の第三成分を右面の上辺と照合する。
規約：三角形の回転の第三射の符号は別途証明する。使われ方：TR2 の最初の二射の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：回転後の始点は元の中間対象。
方針：共有辺の始点と左面の一致を使う。
規約：頂点の厳密な等号。使われ方：回転後の三対象の照合。 -/
lemma CofiberRotationRectangle.rotated_source {X : SSet.{u}} {t : ZeroTriangle X}
    (r : CofiberRotationRectangle t) :
    squareVertex r.rotatedZeroTriangle.square 0 0 = squareVertex t.square 1 0 := by
  have hv : squareVertex r.rotatedZeroTriangle.square 0 0 =
      squareVertex (pastingSquare r.diagram 2) 1 0 := rfl
  rw [hv, r.left_eq]

/-- 概要：回転後の中間対象は元の cofiber。
方針：共有辺の終点と左面の一致を使う。
規約：頂点の厳密な等号。使われ方：回転後の三対象の照合。 -/
lemma CofiberRotationRectangle.rotated_middle {X : SSet.{u}} {t : ZeroTriangle X}
    (r : CofiberRotationRectangle t) :
    squareVertex r.rotatedZeroTriangle.square 1 0 = squareVertex t.square 1 1 := by
  have hv : squareVertex r.rotatedZeroTriangle.square 1 0 =
      squareVertex (pastingSquare r.diagram 2) 1 1 := rfl
  rw [hv, r.left_eq]

/-- 概要：回転後の終点は外側 suspension の頂点。
方針：右面と外側の右上は同じ頂点。
規約：定義からの等号。使われ方：回転後の suspension 対象の照合。 -/
lemma CofiberRotationRectangle.rotated_target {X : SSet.{u}} {t : ZeroTriangle X}
    (r : CofiberRotationRectangle t) :
    squareVertex r.rotatedZeroTriangle.square 1 1 = r.suspensionSquare.vertex := rfl

/-- 概要：回転後の第一射は元の第二射である。
方針：転置した右面の下辺と元の右辺の一次単体を比較する。
規約：端点の表示は Arrow の等号に含める。使われ方：回転三角形の第一射。 -/
lemma CofiberRotationRectangle.rotated_f_arrow {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] {t : ZeroTriangle X} (r : CofiberRotationRectangle t) :
    Arrow.mk r.rotatedZeroTriangle.hoShortComplex.f = Arrow.mk t.hoShortComplex.g := by
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  rw [squareBottomArrow_edge, squareRightArrow_edge]
  apply congrArg SSet.yonedaEquiv
  change squareLeftEdge ≫ pastingSquare r.diagram 0 = squareRightEdge ≫ t.square
  rw [← pastingSquare_sharedEdge, r.left_eq]

/-- 概要：回転後の第二射は長方形の右面の上辺である。
方針：転置した右面の右辺と上辺の一次単体を比較する。
規約：端点の表示は Arrow の等号に含める。使われ方：接続射との比較の中間式。 -/
lemma CofiberRotationRectangle.rotated_g_arrow_top {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] {t : ZeroTriangle X} (r : CofiberRotationRectangle t) :
    Arrow.mk r.rotatedZeroTriangle.hoShortComplex.g =
      Arrow.mk (squareHoTop (pastingSquare r.diagram 0)) := by
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  rw [squareRightArrow_edge, squareTopArrow_edge]
  rfl

/-- 概要：回転後の第二射は外側 suspension への接続射である。
方針：比較の第三成分を上辺と同定し、始点固定の比較の選択独立性を使う。
規約：追加の安定性は不要、入力は cofiber 列と回転長方形。使われ方：TR2 の第二射の同定。 -/
lemma CofiberRotationRectangle.rotated_g_arrow_connecting {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] {t : ZeroTriangle X} (ht : IsCofiberSequence t)
    (r : CofiberRotationRectangle t) :
    Arrow.mk r.rotatedZeroTriangle.hoShortComplex.g =
      Arrow.mk (cofiberConnectingToSuspension t ht r.suspensionSquare) := by
  let Q := r.comparisonHomotopy
  have hpath : ((stdSimplex.δ (0 : Fin 2) ≫ squareRightEdge) ▷ (Δ[1] : SSet.{u})) ≫ Q.h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (squareTopArrow (pastingSquare r.diagram 0)).edge := by
    calc
      _ = snd Δ[0] Δ[1] ≫ (squareTopEdge ≫ pastingSquare r.diagram 0) :=
        pastingLeftToOuterHomotopy_target r.diagram
      _ = _ := by
        rw [squareTopArrow_edge]
        exact congrArg (fun q => snd (Δ[0] : SSet.{u}) Δ[1] ≫ q)
          (SSet.yonedaEquiv.symm_apply_apply (squareTopEdge ≫ pastingSquare r.diagram 0)).symm
  have he := homotopyNatTransOfEndpoints_vertexPath_arrow Q
    (stdSimplex.δ (0 : Fin 2) ≫ squareRightEdge)
    (squareTopArrow (pastingSquare r.diagram 0)) hpath
  have hi : SSet.yonedaEquiv
      (stdSimplex.δ (0 : Fin 2) ≫ squareRightEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1 := by
    apply Prod.ext <;> decide
  rw [hi] at he
  have hc := cofiberComparison_τ₃_eq_connectingToSuspension t ht r.suspensionSquare Q
    r.comparisonHomotopy_source
  exact r.rotated_g_arrow_top.trans (he.symm.trans (congrArg Arrow.mk hc))

end SerrePositivity.InfinityCategories
