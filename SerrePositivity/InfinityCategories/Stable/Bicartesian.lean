module
public import SerrePositivity.InfinityCategories.Stable.ZeroEndPasting
public import SerrePositivity.InfinityCategories.Stable.PullbackPasting
public import SerrePositivity.InfinityCategories.Stable.StableOpposite

/-! # 安定な ∞ 圏の双カルテジアン四角形

概要：安定な quasicategory では任意の四角形の押し出し性と引き戻し性が同値である。
方針：押し出しの右に零対象を付加し、零角を持つ右側と外側に安定性を使って打ち消す。
規約：全有限極限・余極限の存在は追加仮定しない。使われ方：双積・回転・八面体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右下の零角を持つ押し出しは引き戻しでもある。
方針：転置して安定性の零角の位置に合わせる。
規約：零角以外の頂点は任意。使われ方：零終点を付加した長方形。 -/
lemma IsStable.pullback_of_pushout_zero_bottomRight {X : SSet.{u}} [Quasicategory X]
    [IsStable X] (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : IsPushoutSquare R)
    (hz : IsZeroVertex (squareVertex R 1 0)) : IsPullbackSquare R := by
  let t : ZeroTriangle X :=
    { square := (β_ Δ[1] Δ[1]).hom ≫ R
      zero_corner := hz }
  exact (isPullbackSquare_iff_transpose R).2
    (IsStable.pullback_of_pushout t ((isPushoutSquare_iff_transpose R).1 hR))

/-- 概要：安定な quasicategory の任意の押し出しは引き戻しである。
方針：零対象への合成二単体を付加し、右と外側の零角で引き戻し性を得て打ち消す。
規約：元の四角形に零角は不要。使われ方：HA Proposition 1.1.3.4 の四角形の条件。 -/
lemma IsStable.pullback_of_pushout_square {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : IsPushoutSquare R) :
    IsPullbackSquare R := by
  let z := chosenZeroVertex X
  obtain ⟨τ, hτ, hlast⟩ := exists_terminalCompositeTriangle z.isTerminal (squareBottomArrow R)
  have h : squareBottomEdge ≫ R = stdSimplex.δ (2 : Fin 3) ≫ τ := by
    rw [hτ, squareBottomArrow_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply (squareBottomEdge ≫ R)).symm
  have hz : IsZeroVertex (τ.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (2 : Fin 3))) := by
    rw [hlast]
    exact z.isZero
  obtain ⟨F, hleft, hbottom, hright, houter⟩ :=
    exists_pushoutRectangle_of_zeroEnd R hR τ h hz
  have hzright : IsZeroVertex (squareVertex (pastingSquare F 0) 1 0) := by
    change IsZeroVertex ((pastingBottomTriangle F).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (2 : Fin 3)))
    rw [hbottom]
    exact hz
  have hzouter : IsZeroVertex (squareVertex (pastingSquare F 1) 1 0) := hzright
  have hp := isPullbackSquare_pasting_cancel_right F
    (IsStable.pullback_of_pushout_zero_bottomRight _ hright hzright)
    (IsStable.pullback_of_pushout_zero_bottomRight _ houter hzouter)
  rw [hleft] at hp
  exact hp

/-- 概要：安定な quasicategory の任意の引き戻しは押し出しである。
方針：反対の安定な単体集合で押し出しからの判定を使う。
規約：元の四角形に零角は不要。使われ方：双カルテジアン性の逆方向。 -/
lemma IsStable.pushout_of_pullback_square {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : IsPullbackSquare R) :
    IsPushoutSquare R :=
  (isPushoutSquare_iff_dualSquare R).2
    (IsStable.pullback_of_pushout_square (dualSquare R)
      ((isPullbackSquare_iff_dualSquare R).1 hR))

/-- 概要：安定な quasicategory の任意の四角形は引き戻しであることと押し出しであることが同値。
方針：零対象の付加と双対化で得た二方向を組み合わせる。
規約：有限極限・余極限の存在を前提に加えない。使われ方：安定性の四角形による判定。 -/
lemma IsStable.pullback_iff_pushout_square {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) : IsPullbackSquare R ↔ IsPushoutSquare R :=
  ⟨IsStable.pushout_of_pullback_square R, IsStable.pullback_of_pushout_square R⟩

end SerrePositivity.InfinityCategories
