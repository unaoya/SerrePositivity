module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.RightIntervalCutHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PrismCutCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutRightEndpoint

/-!
概要：標準 coherent 区間族の全 Hom を、元の最後の零座標で評価する。
方針：切断後の最大座標を、元の path の切断座標へ戻す既存の式を使う。
規約：標準比較そのものの全高次 Hom の等式。
使われ方：正規化した全対角の厳密照合。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

lemma controlledTriangleRightIntervalHom
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Z : C} {n : ℕ}
    (s : (SimplicialCategory.sHom X Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 1) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex s t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_zero s t i hi)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_one s t j hj)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap t hi j ≫ SSet.yonedaEquiv.symm s := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_mixedHom s t i j hi hj]
  simp only [← Category.assoc]
  apply congrArg (fun f => f ≫ SSet.yonedaEquiv.symm s)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut_maximumMap t i j hi (by rw [hj]; decide)).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap_front t hi j).symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
