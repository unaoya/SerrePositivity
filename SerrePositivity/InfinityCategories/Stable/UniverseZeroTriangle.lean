module
public import SerrePositivity.InfinityCategories.Stable.UniverseStabilityDescent

/-! # 実零角付き三角形の宇宙降下

概要：持ち上げた任意の実零角付き四角形を、その全頂点と普遍性を保持して降ろす。
方針：実四角形の写像の全単射と零性・普遍性の宇宙比較を使う。
規約：指定辺や cofiber の選択は要求しない。使われ方：実安定閉包の帰納的降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial
variable {X : SSet.{u}}

/-- 任意の実零角付き四角形を元の宇宙へ降ろす。 -/
def ZeroTriangle.down (t : ZeroTriangle ((SSet.uliftFunctor.{v, u}).obj X)) :
    ZeroTriangle X where
  square := (uliftSquareHomEquiv.{u, v} X).symm t.square
  zero_corner := by
    have hF : uliftSquare ((uliftSquareHomEquiv.{u, v} X).symm t.square) = t.square :=
      (uliftSquareHomEquiv.{u, v} X).apply_symm_apply t.square
    apply (isZeroVertex_iff_ulift.{u, v} _).mpr
    rw [← uliftSquare_vertex, hF]
    exact t.zero_corner

/-- 降ろした実四角形を持ち上げると、元の四角形と厳密に一致。 -/
lemma ZeroTriangle.ulift_down_square (t : ZeroTriangle ((SSet.uliftFunctor.{v, u}).obj X)) :
    uliftSquare.{u, v} t.down.square = t.square :=
  (uliftSquareHomEquiv.{u, v} X).apply_symm_apply t.square

/-- 降ろした四角形の各頂点は、元の頂点から ULift を外したもの。 -/
lemma ZeroTriangle.down_vertex (t : ZeroTriangle ((SSet.uliftFunctor.{v, u}).obj X))
    (i j : Fin 2) : squareVertex t.down.square i j = (squareVertex t.square i j).down := by
  have h := congrArg (fun F => squareVertex F i j) t.ulift_down_square
  rw [uliftSquare_vertex] at h
  exact congrArg ULift.down h

/-- 実 cofiber 性は任意の零角付き四角形の宇宙降下で保たれる。 -/
lemma ZeroTriangle.isCofiber_down (t : ZeroTriangle ((SSet.uliftFunctor.{v, u}).obj X))
    (ht : IsCofiberSequence t) : IsCofiberSequence t.down := by
  apply (isPushoutSquare_iff_ulift.{u, v} t.down.square).mpr
  rw [t.ulift_down_square]
  exact ht

/-- 実 fiber 性も任意の零角付き四角形の宇宙降下で保たれる。 -/
lemma ZeroTriangle.isFiber_down (t : ZeroTriangle ((SSet.uliftFunctor.{v, u}).obj X))
    (ht : IsFiberSequence t) : IsFiberSequence t.down := by
  apply (isPullbackSquare_iff_ulift.{u, v} t.down.square).mpr
  rw [t.ulift_down_square]
  exact ht

end SerrePositivity.InfinityCategories
