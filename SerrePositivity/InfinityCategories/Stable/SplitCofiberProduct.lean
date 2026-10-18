module
public import SerrePositivity.InfinityCategories.Stable.Bicartesian
public import SerrePositivity.InfinityCategories.Stable.ZeroTargetProduct

/-! # 分裂 cofiber 列からの二項積

概要：cofiber 列の第一射に左逆があれば、中間対象は始対象と cofiber の二項積である。
方針：左逆への合成二単体を付加し、終点が零の右押し出しを二項積として読む。
規約：加法構造は使わない。使われ方：二項余積の標準射影の積性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：一次単体が一致する二組の辺は二項錐の極限性も一致する。
方針：辺の両端を同定してから辺自体の等号へ帰着する。
規約：値域の quasicategory 性は不要。使われ方：貼り合わせから得た射影の照合。 -/
def binaryFan_isLimit_of_edge_eq {X : SSet.{u}}
    {x y z x' y' z' : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) z x)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj X) z y)
    (f' : SSet.Truncated.Edge (X := (truncation 2).obj X) z' x')
    (g' : SSet.Truncated.Edge (X := (truncation 2).obj X) z' y')
    (hf : f.edge = f'.edge) (hg : g.edge = g'.edge)
    (hc : IsLimit (BinaryFan.mk
      (SSet.Truncated.HomotopyCategory.homMk f) (SSet.Truncated.HomotopyCategory.homMk g))) :
    IsLimit (BinaryFan.mk
      (SSet.Truncated.HomotopyCategory.homMk f') (SSet.Truncated.HomotopyCategory.homMk g')) := by
  have hx : x = x' := f.tgt_eq.symm.trans ((congrArg (X.δ 0) hf).trans f'.tgt_eq)
  have hy : y = y' := g.tgt_eq.symm.trans ((congrArg (X.δ 0) hg).trans g'.tgt_eq)
  have hz : z = z' := f.src_eq.symm.trans ((congrArg (X.δ 1) hf).trans f'.src_eq)
  subst x'
  subst y'
  subst z'
  have hff : f = f' := SSet.Truncated.Edge.ext hf
  have hgg : g = g' := SSet.Truncated.Edge.ext hg
  rwa [← hff, ← hgg]

/-- 概要：cofiber 列の第一射と指定した左逆から、左逆と第二射の二項積性が得られる。
方針：指定した分裂を合成二単体に直し、列四角形の右に付加して積四角形を得る。
規約：安定性だけを仮定し加法は使わない。使われ方：h C の双積性。 -/
def ZeroTriangle.binaryProductOfRetraction {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (t : ZeroTriangle X) (ht : IsCofiberSequence t)
    (r : squareHoVertex t.square 1 0 ⟶ squareHoVertex t.square 0 0)
    (hr : squareHoBottom t.square ≫ r = 𝟙 _) :
    IsLimit (BinaryFan.mk r (squareHoRight t.square)) := by
  apply Classical.choice
  obtain ⟨g, hg⟩ := homotopyCategory_homMk_surjective
    (squareVertex t.square 1 0) (squareVertex t.square 0 0) r
  let e := SSet.Truncated.Edge.id (X := (truncation 2).obj X) (squareVertex t.square 0 0)
  have hc : SSet.Truncated.HomotopyCategory.homMk (squareBottomArrow t.square) ≫
      SSet.Truncated.HomotopyCategory.homMk g = SSet.Truncated.HomotopyCategory.homMk e := by
    rw [hg, SSet.Truncated.HomotopyCategory.homMk_id]
    exact hr
  obtain ⟨c⟩ := compStruct_nonempty_of_homMk_fac hc
  let τ : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm c.simplex
  have hface (i : Fin 3) : SSet.yonedaEquiv (stdSimplex.δ i ≫ τ) = X.δ i c.simplex := by
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact congrArg (X.δ i) (SSet.yonedaEquiv.apply_symm_apply c.simplex)
  have hfirst : squareBottomEdge ≫ t.square = stdSimplex.δ (2 : Fin 3) ≫ τ := by
    apply SSet.yonedaEquiv.injective
    exact ((squareBottomArrow_edge t.square).symm.trans c.d₂.symm).trans (hface 2).symm
  have hreturn : stdSimplex.δ (1 : Fin 3) ≫ τ = SSet.const (squareVertex t.square 0 0) := by
    apply SSet.yonedaEquiv.injective
    exact (hface 1).trans (c.d₁.trans (pinchedConstant_one _).symm)
  obtain ⟨F, hleft, hbottom, hright, houter⟩ :=
    exists_pushoutRectangle_of_returnTriangle t.square ht τ hfirst hreturn
  have hterminal : IsTerminalVertex (squareVertex (pastingSquare F 0) 1 1) := by
    have hv : squareVertex (pastingSquare F 0) 1 1 =
        squareVertex (pastingSquare F 1) 1 1 := rfl
    rw [hv, houter]
    exact t.zero_corner.2
  have hp := terminalTargetPullback_isBinaryProduct (pastingSquare F 0)
    (IsStable.pullback_of_pushout_square _ hright) hterminal
  have hf : (squareBottomArrow (pastingSquare F 0)).edge = g.edge := by
    rw [squareBottomArrow_edge, pastingSquare_bottomEdge, hbottom]
    exact (hface 0).trans c.d₀
  have hs : (squareLeftArrow (pastingSquare F 0)).edge =
      (squareRightArrow t.square).edge := by
    rw [squareLeftArrow_edge, squareRightArrow_edge]
    apply congrArg SSet.yonedaEquiv
    rw [← pastingSquare_sharedEdge, hleft]
  have hp' := binaryFan_isLimit_of_edge_eq _ _ g (squareRightArrow t.square) hf hs hp
  rw [hg] at hp'
  exact ⟨hp'⟩

end SerrePositivity.InfinityCategories
