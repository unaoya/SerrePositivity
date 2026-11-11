module

public import SerrePositivity.KST.LocalizingInvariants.ZeroCospanHomotopyUniqueness
public import SerrePositivity.KST.LocalizingInvariants.FiberSquareHomotopyUniqueness
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed

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

lemma cospan_zeroSecond {X : SSet.{u}} (F : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) :
    ZeroCospan.zeroSecond X (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan F.square)) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₂.ι₁₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan F.square))
  unfold _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((horn₂₂.ι₁₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ F.square).app _ _)
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge]
  exact F.zero_corner

lemma homMk_eq_of_right {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X]
    (F G : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence F) (hG : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence G)
    (H J : SSet.Homotopy F.square G.square)
    (h : (hoFunctor.map ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).app X)).toFunctor.map
        (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) =
      (hoFunctor.map ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).app X)).toFunctor.map
        (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J))) :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J) := by
  apply homMk_eq_of_cospan F.square G.square hF hG H J
  apply ZeroCospan.homotopy_homMk_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan F.square) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan G.square)
    (cospan_zeroSecond F) (cospan_zeroSecond G)
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homMk_functorEdge_precomp, ← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homMk_functorEdge_precomp,
    ← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homMk_functorEdge_precomp, ← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homMk_functorEdge_precomp]
  have hp : (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary).app X ≫ (pre horn₂₂.ι₀₂).app X =
      (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).app X := by
    rw [← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge]
  change (hoFunctor.map ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary).app X ≫
      (pre horn₂₂.ι₀₂).app X)).toFunctor.map
        (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) =
    (hoFunctor.map ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary).app X ≫
      (pre horn₂₂.ι₀₂).app X)).toFunctor.map
        (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J))
  rw [hp]
  exact h

end SerrePositivity.KST.LocalizingInvariants.FiberSquareHomotopy
