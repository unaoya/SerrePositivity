module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionReverse
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointSliceReverseCoordinates

/-!
概要：元の反転合成 prism の錐の射を、元の反転した合成単体で全次数に計算する。
方針：slice の反転の実座標と同じ標準 join の反転同型を合成する。
規約：元の二区間係数を保持。使われ方：元の fixed 射の実 pointed prism の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z : C)

/-- 同じ元の反転合成 prism の実錐の射は、同じ元の合成単体の反転である。 -/
lemma coherentCompositionReversePrism_app_val {n : ℕ}
    (t : (Δ[1] : SSet.{max u v}) _⦋n⦌)
    (a : ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z)).op _⦋n⦌)
    (b : ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y)).op _⦋n⦌) :
    ((coherentCompositionReversePrism X Y Z).app (Opposite.op ⦋n⦌) (t, a, b)).val =
    (leftPointStdSimplexIso n).hom ≫ (stdSimplex.opIso ⦋n + 1⦌).inv ≫
      SSet.opFunctor.map (SSet.yonedaEquiv.symm
        (coherentCompositionSimplex (SSet.opObjEquiv b).down (SSet.opObjEquiv a).down
          (stableReverseOrderHom (stdSimplex.objEquiv t).toOrderHom))) := by
  change (((cofinalPointSliceOverOpIso (coherentNerveVertex Z)).hom.left).app
    (Opposite.op ⦋n⦌) (SSet.opObjEquiv.symm
      (coherentCompositionSliceSimplex (SSet.opObjEquiv b).down (SSet.opObjEquiv a).down
        (stableReverseOrderHom (stdSimplex.objEquiv t).toOrderHom)))).val = _
  rw [cofinalPointSliceOverOpIso_app_val]
  change _ ≫ _ ≫ SSet.opFunctor.map ((joinStdSimplexIso n 0).hom ≫
    SSet.yonedaEquiv.symm
      (coherentCompositionSimplex (SSet.opObjEquiv b).down (SSet.opObjEquiv a).down
        (stableReverseOrderHom (stdSimplex.objEquiv t).toOrderHom))) = _
  rw [Functor.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ SSet.opFunctor.map (SSet.yonedaEquiv.symm
      (coherentCompositionSimplex (SSet.opObjEquiv b).down (SSet.opObjEquiv a).down
        (stableReverseOrderHom (stdSimplex.objEquiv t).toOrderHom))))
    (pointJoinReverseIso_inv_coordinates.{max u v} n)

end SerrePositivity.InfinityCategories.F2
