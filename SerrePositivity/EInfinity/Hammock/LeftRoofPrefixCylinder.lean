module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.NerveNatTransCylinder
public import SerrePositivity.EInfinity.Hammock.LeftRoofPrefixEndpoints

/-!
# 各始点の元の roof 円柱の全単体での計算

概要：Under 全円柱とその余極限像を同じ自然変換から計算する。
方針：四列比較の成分を公開し、元の円柱の全次数評価公式を適用する。
規約：元の graph 円柱と恒等列の正規化をそのまま保持する。
使われ方：始点変更への円柱全体の厳密な自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.LeftRoof.Prefix
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
variable {C I : Type u} [Category.{u} C] [Category.{u} I]
  (W : MorphismProperty C) [W.IsMultiplicative]
  (U : I ⥤ C) {X Y : C} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, W (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), W (U.map a)) (i : I)

def component : upperDiagram W U σ hU i ⟶ lowerDiagram W U p hp σ hU i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramComponent W (restrictedFrame U i) (restrictedAugmentation U p i)
    (restrictedAugmentation_weak W U p hp i) (p.app i) (restrictedRightLeg U σ i)
    (fun f => restrictedFrame_map_weak W U hU i f) (fixedSource U i) (𝟙 _)
    (fun _ => W.id_mem (U.obj i)) (inclusion U i)
    (by rw [Category.id_comp]; exact augmentation_triangle U p i)
    (fun f => fixedSource_map_weak W U i f)

lemma graphHomotopy_h_app (n : SimplexCategoryᵒᵖ)
    (a : (nerve (Under i)).obj n) (t : (Δ[1] : SSet.{u}).obj n) :
    (graphHomotopy W U p hp σ hU i).h.app n (a, t) =
      ((stdSimplex.objEquiv t).toOrderHom.monotone.functor.prod' a) ⋙
        Functor.uncurry.obj (ComposableArrows.mk₁ (component W U p hp σ hU i)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nerveNatTransHomotopy_app (component W U p hp σ hU i) n a t

lemma arrowHomotopy_h_app (n : SimplexCategoryᵒᵖ)
    (a : (nerve (Under i)).obj n) (t : (Δ[1] : SSet.{u}).obj n) :
    (arrowHomotopy W U p hp σ hU i).h.app n (a, t) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W (U.obj i) Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.word).app n
        (((stdSimplex.objEquiv t).toOrderHom.monotone.functor.prod' a) ⋙
          Functor.uncurry.obj (ComposableArrows.mk₁ (component W U p hp σ hU i))) := by
  rw [arrowHomotopy_h]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W (U.obj i) Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.word).app n
    ((graphHomotopy W U p hp σ hU i).h.app n (a, t)) = _
  rw [graphHomotopy_h_app]

end SerrePositivity.EInfinity.Hammock.LeftRoof.Prefix
