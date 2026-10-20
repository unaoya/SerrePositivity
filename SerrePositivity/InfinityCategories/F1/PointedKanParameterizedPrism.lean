module

public import SerrePositivity.InfinityCategories.F1.PointedKanParameterizedAction
public import SerrePositivity.InfinityCategories.F1.FiberTransportFamilyNaturality

/-!
概要：任意の Kan 作用に対し、両端が元の作用に厳密に一致する pointed prism を作る。
方針：豊穣合成の反転 prism を同じ係数とパラメーターで制限し、標準係数で正規化する。
規約：各頂点で輸送を選び直さず、全パラメーターで一つの実際の prism を保持する。
使われ方：native な区間に沿う weighted prism の対象ごとの構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 元の Kan 作用の始点と底を保つ、明示的な pointed 輸送族。 -/
def pointedKanParameterizedTransportFamily {X Y : KanObject.{u}} {H : SSet.{u}}
    (f : X.obj ⊗ H ⟶ Y.obj) :
    FiberTransportFamily (b := spaceInfinityVertex (kanObjectOpFunctor.obj Y))
      pointedSpaceProjection (pointedSpaceLeftResolutionComparison X)
      (intervalMappingUncurry (kanParameterizedLeftHomInterval f)) := by
  let cX := (SSet.uliftFunctor.{u + 1, u}).map (pointedSpaceLeftCoefficientIso X).hom ≫
    (uliftOppositeIso
      (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj X))).hom
  let cY := (SSet.uliftFunctor.{u + 1, u}).map (pointedSpaceLeftCoefficientIso Y).hom ≫
    (uliftOppositeIso
      (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj Y))).hom
  let T := ((pointedReverseKanCompositionTransportFamily
    (kanObjectOpFunctor.obj X) (kanObjectOpFunctor.obj Y)).precomposeSource cX).precomp
      (leftPointHomReverseParameter f)
  have hX : cX ≫ pointedReverseKanFiberComparison (kanObjectOpFunctor.obj X) =
      pointedSpaceLeftResolutionComparison X := pointedReverseKanFiberComparison_resolution X
  have hY : cY ≫ pointedReverseKanFiberComparison (kanObjectOpFunctor.obj Y) =
      pointedSpaceLeftResolutionComparison Y := pointedReverseKanFiberComparison_resolution Y
  have hEnd : T.endpoint = (uliftTensorIso X.obj H).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map f ≫ pointedSpaceLeftResolutionComparison Y := by
    have h := congrArg (fun k => k ≫
      pointedReverseKanFiberComparison (kanObjectOpFunctor.obj Y))
        (leftPointHomReverseComposition_coefficient f)
    change ((cX ⊗ₘ leftPointHomReverseParameter f) ≫
      coherentReverseHomComposition (Opposite.op (kanObjectOpFunctor.obj Y))
        (Opposite.op (kanObjectOpFunctor.obj X)) (Opposite.op pointKanObject)) ≫
      pointedReverseKanFiberComparison (kanObjectOpFunctor.obj Y) = _
    calc
      _ = (uliftTensorIso X.obj H).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map f ≫
          cY ≫ pointedReverseKanFiberComparison (kanObjectOpFunctor.obj Y) := by
        simpa only [cX, cY, Category.assoc] using h
      _ = _ := by rw [hY]
  have hBase : intervalMappingUncurry (kanParameterizedLeftHomInterval f) =
      (Δ[1] ◁ leftPointHomReverseParameter f) ≫
        pointedReverseKanHomInterval (kanObjectOpFunctor.obj X) (kanObjectOpFunctor.obj Y) := by
    rw [kanParameterizedLeftHomInterval, intervalMappingUncurry_precomp,
      intervalMappingUncurry_curryOfEndpoints]
  refine
    { endpoint := (uliftTensorIso X.obj H).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map f ≫ pointedSpaceLeftResolutionComparison Y
      prism := T.prism
      start := ?_
      finish := ?_
      over_base := ?_ }
  · simpa only [← hX, Category.assoc] using T.start
  · rw [← hEnd]
    exact T.finish
  · rw [hBase]
    exact T.over_base

/-- 構成した prism の終点は、同じパラメーターでの元の Kan 作用そのもの。 -/
lemma pointedKanParameterizedTransportFamily_endpoint {X Y : KanObject.{u}} {H : SSet.{u}}
    (f : X.obj ⊗ H ⟶ Y.obj) :
    (pointedKanParameterizedTransportFamily f).endpoint =
      (uliftTensorIso X.obj H).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map f ≫
        pointedSpaceLeftResolutionComparison Y := rfl

end SerrePositivity.InfinityCategories
