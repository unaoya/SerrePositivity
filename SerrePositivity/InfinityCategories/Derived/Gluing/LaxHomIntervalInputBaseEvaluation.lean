module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomIntervalCoordinatesIso
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedPullbackInputEvaluation
/-!
概要：正本標的の入力側の底作用を元の導来二脚の全 join 族として評価する。
方針：引き戻しの元の第二脚の評価へ同じ入力座標同型の逆を適用する。
規約：元二入力・全パラメーター・固定終点を保持する。
使われ方：底の区間座標を既存の導来二作用へ厳密に照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
lemma dgGluingLaxHomIntervalInputBase_raw_evaluation :
    intervalMappingUncurry ((dgGluingLaxHomRawInputIso R C D M X Y).inv ≫
      dgGluingLaxHomIntervalInputBase R C D M X Y) =
    rightMappingSpacePrism _ ≫
      pinchedHomUncurry (dgGluingLaxHomRawInputIso R C D M X Y).inv ≫
      ((dgGluingUniverseDerivedYoneda.{u,v,w} R C) ⊗ₘ
        (dgGluingUniverseDerivedCoefficient R C D M)) := by
  exact dgGluingPinchedHomPullbackBaseMap_evaluation
    (F2.arrowEndpointPair ((SSet.uliftFunctor.{max (u + 1) v w,max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)))
    ((dgGluingUniverseDerivedYoneda.{u,v,w} R C) ⊗ₘ
      (dgGluingUniverseDerivedCoefficient R C D M))
    ((dgGluingUniverseDerivedNerveLaxComparison R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex (A := R) X)))
    ((dgGluingUniverseDerivedNerveLaxComparison R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex (A := R) Y)))
    (dgGluingLaxHomRawInputIso R C D M X Y).inv
end SerrePositivity.InfinityCategories
