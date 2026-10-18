module
public import SerrePositivity.InfinityCategories.Stable.ZeroSourceCoproductComparison
public import SerrePositivity.InfinityCategories.Stable.PastingHomotopyComposition

/-! # 貼り合わせの射影と二項余積射影の一致

概要：零始点の押し出しを列四角形へ延長して得る射影は、二項余積の第二射影である。
方針：包含との合成零と、元の第二包含との合成恒等から普遍性で比較する。
規約：実際の射影の一次単体を保持する。使われ方：標準余積の cofiber 列。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：一次単体が一致する二組の辺は合成零も同時に満たす。
方針：三頂点を同定してから辺の等号へ帰着する。
規約：零射のみを仮定。使われ方：指定した包含と射影への合成零の輸送。 -/
private lemma homMk_comp_zero_of_edge_eq {X : SSet.{u}}
    [HasZeroMorphisms (hoFunctor.obj X)] {x y z x' y' z' : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj X) y z)
    (f' : SSet.Truncated.Edge (X := (truncation 2).obj X) x' y')
    (g' : SSet.Truncated.Edge (X := (truncation 2).obj X) y' z')
    (hf : f.edge = f'.edge) (hg : g.edge = g'.edge)
    (h : SSet.Truncated.HomotopyCategory.homMk f ≫
      SSet.Truncated.HomotopyCategory.homMk g =
        (0 : @Quiver.Hom (hoFunctor.obj X) _
          (SSet.HomotopyCategory.mk x) (SSet.HomotopyCategory.mk z))) :
    SSet.Truncated.HomotopyCategory.homMk f' ≫ SSet.Truncated.HomotopyCategory.homMk g' =
      (0 : @Quiver.Hom (hoFunctor.obj X) _
        (SSet.HomotopyCategory.mk x') (SSet.HomotopyCategory.mk z')) := by
  have hx : x = x' := f.src_eq.symm.trans ((congrArg (X.δ 1) hf).trans f'.src_eq)
  have hy : y = y' := f.tgt_eq.symm.trans ((congrArg (X.δ 0) hf).trans f'.tgt_eq)
  have hz : z = z' := g.tgt_eq.symm.trans ((congrArg (X.δ 0) hg).trans g'.tgt_eq)
  subst x'
  subst y'
  subst z'
  have hff : f = f' := SSet.Truncated.Edge.ext hf
  have hgg : g = g' := SSet.Truncated.Edge.ext hg
  rwa [← hff, ← hgg]

/-- 概要：外側が列四角形である延長長方形の右上辺は、元の二項余積の第二射影を表す。
方針：上側の合成二単体で第二包含との合成恒等を、右零角で第一包含との合成零を示す。
規約：元の頂点間の辺として射影を取り出す。使われ方：標準 cofiber 列との照合。 -/
lemma exists_pastingProjection_eq_coproductSnd {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : IsPushoutSquare R)
    (hz : IsZeroVertex (squareVertex R 0 0))
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hleft : pastingSquare F 2 = R)
    (houter : pastingSquare F 1 = squareColumnDiagram (squareLeftEdge ≫ R)) :
    ∃ b : SSet.Truncated.Edge (X := (truncation 2).obj X)
        (squareVertex R 1 1) (squareVertex R 0 1),
      b.edge = (squareTopArrow (pastingSquare F 0)).edge ∧
      SSet.Truncated.HomotopyCategory.homMk b = zeroSourceCoproductSnd R hR hz.1 := by
  have hs : squareVertex (pastingSquare F 0) 0 1 = squareVertex R 1 1 := by
    change squareVertex (pastingSquare F 2) 1 1 = _
    rw [hleft]
  have ht : squareVertex (pastingSquare F 0) 1 1 = squareVertex R 0 1 := by
    change squareVertex (pastingSquare F 1) 1 1 = _
    rw [houter]
    rfl
  let b : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (squareVertex R 1 1) (squareVertex R 0 1) :=
    { edge := (squareTopArrow (pastingSquare F 0)).edge
      src_eq := (squareTopArrow (pastingSquare F 0)).src_eq.trans hs
      tgt_eq := (squareTopArrow (pastingSquare F 0)).tgt_eq.trans ht }
  have he : (squareTopArrow (pastingSquare F 1)).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X) (squareVertex R 0 1)).edge := by
    rw [squareTopArrow_edge, houter]
    have hi : squareTopEdge ≫ squareColumnDiagram (squareLeftEdge ≫ R) =
        SSet.const (squareVertex R 0 1) := by
      simp only [squareTopEdge, squareColumnDiagram, ← Category.assoc, lift_snd, SSet.const_comp]
      rfl
    rw [hi]
    exact pinchedConstant_one _
  have hcomp : (squareTopArrow R).CompStruct b
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X) (squareVertex R 0 1)) :=
    { simplex := (pastingTopCompStruct F).simplex
      d₂ := (pastingTopCompStruct F).d₂.trans (by rw [hleft])
      d₀ := (pastingTopCompStruct F).d₀
      d₁ := (pastingTopCompStruct F).d₁.trans he }
  have htop : squareHoTop R ≫ SSet.Truncated.HomotopyCategory.homMk b = 𝟙 _ :=
    (SSet.Truncated.HomotopyCategory.homMk_comp_homMk hcomp).trans
      (SSet.Truncated.HomotopyCategory.homMk_id (V := (truncation 2).obj X)
        (squareVertex R 0 1))
  let t : ZeroTriangle X :=
    { square := (β_ Δ[1] Δ[1]).hom ≫ pastingSquare F 0
      zero_corner := by
        change IsZeroVertex (squareVertex (pastingSquare F 1) 1 0)
        rw [houter]
        exact hz }
  have hf : (squareBottomArrow t.square).edge = (squareRightArrow R).edge := by
    rw [squareBottomArrow_edge, squareRightArrow_edge]
    apply congrArg SSet.yonedaEquiv
    change squareRightEdge ≫ pastingSquare F 2 = _
    rw [hleft]
  have hg : (squareRightArrow t.square).edge = b.edge := by
    change (squareRightArrow t.square).edge = (squareTopArrow (pastingSquare F 0)).edge
    rw [squareRightArrow_edge, squareTopArrow_edge]
    apply congrArg SSet.yonedaEquiv
    rfl
  have hright : squareHoRight R ≫ SSet.Truncated.HomotopyCategory.homMk b = 0 :=
    homMk_comp_zero_of_edge_eq _ _ _ _ hf hg t.homMk_comp_eq_zero
  refine ⟨b, rfl, ?_⟩
  apply BinaryCofan.IsColimit.hom_ext (zeroSourcePushout_isBinaryCoproduct R hR hz.1)
  · exact hright.trans (zeroSourceCoproduct_right_snd R hR hz.1).symm
  · exact htop.trans (zeroSourceCoproduct_top_snd R hR hz.1).symm

end SerrePositivity.InfinityCategories
