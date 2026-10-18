module
public import SerrePositivity.InfinityCategories.Stable.SquareBinaryCocone

/-! # 零始点の押し出しの二項余積性

概要：零始点の押し出しの右辺・上辺は h C の二項余積の包含となる。
方針：始対象を忘れた二点図式の余極限を、一次単体の一致で指定した二本の辺へ移す。
規約：安定性は不要。使われ方：幾何学的 cofiber 列と Mathlib の余積の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：一次単体が一致する二組の辺は、二項余錐の余極限性も一致する。
方針：辺の両端を同定してから辺自体の等号へ帰着する。
規約：quasicategory 性は不要。使われ方：端点の表示を含む二項余積の輸送。 -/
def binaryCofan_isColimit_of_edge_eq {X : SSet.{u}}
    {x y z x' y' z' : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj X) y z)
    (f' : SSet.Truncated.Edge (X := (truncation 2).obj X) x' z')
    (g' : SSet.Truncated.Edge (X := (truncation 2).obj X) y' z')
    (hf : f.edge = f'.edge) (hg : g.edge = g'.edge)
    (hc : IsColimit (BinaryCofan.mk
      (SSet.Truncated.HomotopyCategory.homMk f) (SSet.Truncated.HomotopyCategory.homMk g))) :
    IsColimit (BinaryCofan.mk
      (SSet.Truncated.HomotopyCategory.homMk f') (SSet.Truncated.HomotopyCategory.homMk g')) := by
  have hx : x = x' := f.src_eq.symm.trans ((congrArg (X.δ 1) hf).trans f'.src_eq)
  have hy : y = y' := g.src_eq.symm.trans ((congrArg (X.δ 1) hg).trans g'.src_eq)
  have hz : z = z' := f.tgt_eq.symm.trans ((congrArg (X.δ 0) hf).trans f'.tgt_eq)
  subst x'
  subst y'
  subst z'
  have hff : f = f' := SSet.Truncated.Edge.ext hf
  have hgg : g = g' := SSet.Truncated.Edge.ext hg
  rwa [← hff, ← hgg]

/-- 概要：始点が始対象の押し出しを二点図式に制限すると余極限余錐になる。
方針：span の join 表示で始対象を忘れる余極限判定を使う。
規約：値域は quasicategory、始点は零対象でなくてもよい。
使われ方：零始点の押し出しの二項余積性。 -/
lemma squareBinaryCocone_isColimit {X : SSet.{u}} [Quasicategory X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : IsPushoutSquare R)
    (hz : IsInitialVertex (squareVertex R 0 0)) : IsColimitCone (squareBinaryCocone R) := by
  let J := spanPointJoinIso.hom ≫ pushoutSpan R
  let d : JoinCocone J := (pushoutCocone R).restrict spanPointJoinIso.hom
  have hd : IsColimitCone d :=
    (isColimitCone_iff_restrict_of_isIso (pushoutCocone R) spanPointJoinIso.hom).1 hR
  have hsource : joinInl (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]) ≫ J =
      stdSimplex.δ (1 : Fin 2) ≫ squareBottomEdge ≫ R := by
    change _ ≫ (spanPointJoinIso.hom ≫ pushoutSpan R) = _
    rw [← Category.assoc, spanPointJoinIso_source, Category.assoc]
    rw [pushoutSpan, ← Category.assoc horn₂₀.ι₀₁, spanSquareBoundary_bottomEdge]
  have hj : IsInitialVertex (SSet.yonedaEquiv
      (joinInl (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]) ≫ J)) := by
    rw [hsource, stdSimplex.yonedaEquiv_δ_comp, squareBottomEdge_source]
    exact hz
  exact (isColimitCone_iff_restrict_joinInr_of_initial J hj d).1 hd

/-- 概要：始点が始対象の押し出しの右辺・上辺は h C の普遍二項余錐となる。
方針：二点図式の余極限を作り、二つの脚の一次単体の一致で指定した辺へ移す。
規約：値域は quasicategory、安定性は不要。使われ方：余積の標準包含との照合。 -/
def zeroSourcePushout_isBinaryCoproduct {X : SSet.{u}} [Quasicategory X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : IsPushoutSquare R)
    (hz : IsInitialVertex (squareVertex R 0 0)) :
    IsColimit (BinaryCofan.mk (squareHoRight R) (squareHoTop R)) :=
  binaryCofan_isColimit_of_edge_eq _ _ _ _
    (squareBinaryCocone_leg_left R) (squareBinaryCocone_leg_right R)
    (binaryColimit_isColimit (squareBinaryCocone R) (squareBinaryCocone_isColimit R hR hz))

end SerrePositivity.InfinityCategories
