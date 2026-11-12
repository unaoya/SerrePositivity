module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CospanSingleFibrationComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomotopyCospanEndComparison

/-!
概要：一脚が Kan fibration の厳密な引き戻しを、同じ cospan の Bousfield–Kan end へ比較する。
方針：元の引き戻しの通常の極限錐を形状同値で移し、既存の標準比較を適用する。
規約：元の頂点と両射影を保持。使われ方：native 切断の引き戻しの普遍性の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {L M R : SSet.{u}} (f : L ⟶ M) (g : R ⟶ M)

/-- 元の引き戻し頂点と両射影を持つ、小さい cospan 上の通常の極限錐。 -/
def strictKanPullbackEndCone :
    Cone ((AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan) ⋙ cospan f g) :=
  (PullbackCone.mk (pullback.fst f g) (pullback.snd f g) pullback.condition).whisker AsSmall.down

/-- 同じ元の引き戻し頂点を持つ錐は、形状の宇宙移送後も通常の極限。 -/
def strictKanPullbackEndCone_isLimit : IsLimit (strictKanPullbackEndCone f g) :=
  (pullbackIsPullback f g).whiskerEquivalence
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).symm

/-- 元の左射影を保持する。 -/
lemma strictKanPullbackEndCone_left :
    (strictKanPullbackEndCone f g).π.app (AsSmall.up.obj WalkingCospan.left) =
      pullback.fst f g := rfl

/-- 元の右射影も保持する。 -/
lemma strictKanPullbackEndCone_right :
    (strictKanPullbackEndCone f g).π.app (AsSmall.up.obj WalkingCospan.right) =
      pullback.snd f g := rfl

/-- 元の厳密な引き戻しから同じ cospan の end への標準比較。 -/
def strictKanPullbackEndComparison : pullback f g ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
      ((AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan) ⋙ cospan f g) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (strictKanPullbackEndCone f g)

/-- 一脚が fibration の Kan cospan では、この実際の標準比較が単体的ホモトピー同値。 -/
lemma strictKanPullbackEndComparison_homotopyEquivalence
    [KanComplex L] [KanComplex M] [KanComplex R] [Fibration f] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (strictKanPullbackEndComparison f g) := by
  have : Fibration
      (((AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan) ⋙ cospan f g).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := inferInstanceAs (Fibration f)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence
    _ _ (strictKanPullbackEndCone_isLimit f g)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
