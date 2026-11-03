module

public import SerrePositivity.KST.LocalizingInvariants.ZeroCospanHomotopyUniqueness
public import SerrePositivity.KST.LocalizingInvariants.FiberSquareHomotopyUniqueness
public import SerrePositivity.InfinityCategories.Core.Pointed

/-!
概要：零角を持つ pullback 四角形の比較は、右辺への全関手としての制限で決まる。
方針：零第二枝の cospan 制限の忠実性と、普遍錐の制限の忠実性を順に使う。
規約：右辺の頂点成分や h の可換式では足りない。使われ方：模型比較と元の prism の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.FiberSquareHomotopy

lemma cospan_zeroSecond {X : SSet.{u}} (F : ZeroTriangle X) :
    ZeroCospan.zeroSecond X (functorVertex (pullbackCospan F.square)) := by
  change IsZeroSourceArrow (functorVertex (horn₂₂.ι₁₂ ≫ pullbackCospan F.square))
  unfold IsZeroSourceArrow
  rw [evaluateFunctorAt_functorVertex]
  change IsZeroVertex ((horn₂₂.ι₁₂ ≫ cospanSquareBoundary ≫ F.square).app _ _)
  rw [← Category.assoc, cospanSquareBoundary_topEdge]
  exact F.zero_corner

lemma homMk_eq_of_right {X : SSet.{u}} [Quasicategory X] [HasZeroVertex X]
    (F G : ZeroTriangle X) (hF : IsFiberSequence F) (hG : IsFiberSequence G)
    (H J : SSet.Homotopy F.square G.square)
    (h : (hoFunctor.map ((pre squareRightEdge).app X)).toFunctor.map
        (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) =
      (hoFunctor.map ((pre squareRightEdge).app X)).toFunctor.map
        (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J))) :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J) := by
  apply homMk_eq_of_cospan F.square G.square hF hG H J
  apply ZeroCospan.homotopy_homMk_eq (pullbackCospan F.square) (pullbackCospan G.square)
    (cospan_zeroSecond F) (cospan_zeroSecond G)
  rw [← homMk_functorEdge_precomp, ← homMk_functorEdge_precomp,
    ← homMk_functorEdge_precomp, ← homMk_functorEdge_precomp]
  have hp : (pre cospanSquareBoundary).app X ≫ (pre horn₂₂.ι₀₂).app X =
      (pre squareRightEdge).app X := by
    rw [← NatTrans.comp_app, ← pre_map, cospanSquareBoundary_rightEdge]
  change (hoFunctor.map ((pre cospanSquareBoundary).app X ≫
      (pre horn₂₂.ι₀₂).app X)).toFunctor.map
        (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) =
    (hoFunctor.map ((pre cospanSquareBoundary).app X ≫
      (pre horn₂₂.ι₀₂).app X)).toFunctor.map
        (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J))
  rw [hp]
  exact h

end SerrePositivity.KST.LocalizingInvariants.FiberSquareHomotopy
