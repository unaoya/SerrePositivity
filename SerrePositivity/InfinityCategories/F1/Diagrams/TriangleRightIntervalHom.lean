module

public import SerrePositivity.InfinityCategories.F1.Coherent.RightIntervalCutHom
public import SerrePositivity.InfinityCategories.F1.Coherent.PrismCutCoordinates
public import SerrePositivity.InfinityCategories.F1.Coherent.PathCutRightEndpoint

/-!
概要：標準 coherent 区間族の全 Hom を、元の最後の零座標で評価する。
方針：切断後の最大座標を、元の path の切断座標へ戻す既存の式を使う。
規約：標準比較そのものの全高次 Hom の等式。
使われ方：正規化した全対角の厳密照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma controlledTriangleRightIntervalHom
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Z : C} {n : ℕ}
    (s : (SimplicialCategory.sHom X Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 1) :
    (coherentRightIntervalCutSimplex s t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentRightIntervalCutSimplex_obj_zero s t i hi)
        (coherentRightIntervalCutSimplex_obj_one s t j hj)) =
      pathCutLastZeroMap t hi j ≫ SSet.yonedaEquiv.symm s := by
  rw [coherentRightIntervalCutSimplex_mixedHom s t i j hi hj]
  simp only [← Category.assoc]
  apply congrArg (fun f => f ≫ SSet.yonedaEquiv.symm s)
  exact (coherentPrismCut_maximumMap t i j hi (by rw [hj]; decide)).symm.trans
    (pathCutLastZeroMap_front t hi j).symm

end SerrePositivity.InfinityCategories
