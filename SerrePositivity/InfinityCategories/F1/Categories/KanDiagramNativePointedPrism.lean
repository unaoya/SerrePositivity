module

public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramNativeLeftIntervalEvaluation
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedKanParameterizedPrism

/-!
概要：native な左区間の対象評価に沿う、両端を指定した実際の pointed prism を構成する。
方針：元の strict 変換の評価の prism を共通 Hom の右端で制限し、底の厳密な式を使う。
規約：これは各対象の全パラメーターでの構成であり、weighted 始域上への貼り合わせは別課題。
使われ方：分類写像の実際の全 Hom 作用と weighted 比較の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 各対象で、同じ native 区間上に元の変換の評価を終点とする pointed prism を作る。 -/
def kanDiagramNativePointedTransportFamily
    {I : Type u} [SmallCategory I] (F G : KanDiagramObject I) (i : I) :
    FiberTransportFamily
      (b := spaceInfinityVertex (kanObjectOpFunctor.obj (G.val.obj i)))
      pointedSpaceProjection (pointedSpaceLeftResolutionComparison (F.val.obj i))
      (intervalMappingUncurry (kanDiagramOppositeLeftHomInterval F G) ≫
        evaluateFunctorAt (ULift.up (nerveVertex i))) := by
  let f := uncurry (strictDiagramMappingComponent
    (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) i)
  let T := (pointedKanParameterizedTransportFamily
    (X := F.val.obj i) (Y := G.val.obj i) f).precomp
      ((SSet.uliftFunctor.{u + 1, u}).map (edgewiseRight (SimplicialCategory.sHom F G)))
  have hBase : intervalMappingUncurry (kanDiagramOppositeLeftHomInterval F G) ≫
      evaluateFunctorAt (ULift.up (nerveVertex i)) =
      (Δ[1] ◁ (SSet.uliftFunctor.{u + 1, u}).map
        (edgewiseRight (SimplicialCategory.sHom F G))) ≫
      intervalMappingUncurry (kanParameterizedLeftHomInterval
        (X := F.val.obj i) (Y := G.val.obj i) f) := by
    rw [kanDiagramOppositeLeftHomInterval_evaluate_action,
      kanParameterizedLeftHomInterval, intervalMappingUncurry_precomp,
      intervalMappingUncurry_curryOfEndpoints, pointedReverseKanHomInterval_eq_left]
    simp only [whiskerLeft_comp, Category.assoc]
    rfl
  refine
    { endpoint := T.endpoint
      prism := T.prism
      start := T.start
      finish := T.finish
      over_base := ?_ }
  rw [hBase]
  exact T.over_base

/-- 同じ共通 Hom の右端を使った元の strict 変換の評価が prism の実際の終点。 -/
lemma kanDiagramNativePointedTransportFamily_endpoint
    {I : Type u} [SmallCategory I] (F G : KanDiagramObject I) (i : I) :
    (kanDiagramNativePointedTransportFamily F G i).endpoint =
      ((SSet.uliftFunctor.{u + 1, u}).obj (F.val.obj i).obj ◁
        (SSet.uliftFunctor.{u + 1, u}).map (edgewiseRight (SimplicialCategory.sHom F G))) ≫
      (uliftTensorIso (F.val.obj i).obj (SimplicialCategory.sHom F G)).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (uncurry (strictDiagramMappingComponent
        (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) i)) ≫
      pointedSpaceLeftResolutionComparison (G.val.obj i) := rfl

end SerrePositivity.InfinityCategories
