module

public import SerrePositivity.InfinityCategories.F2.Ind.YonedaSlice
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFiberIso
public import SerrePositivity.InfinityCategories.F1.YonedaPresheafEvaluation

/-!
概要：元の Yoneda slice の指定 fiber を、元の前層 F の指定値と比較する。
方針：引き戻しの fiber 同型と元の右写像空間の同型を、同じ Yoneda 評価へ続ける。
規約：各点の同値性を全空間の比較射の存在と混同しない。
使われ方：小さい元の圏から標準密度余錐への比較を作るための fiber 側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
attribute [local instance] vertexFiber_kanComplex
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 同じ Yoneda slice の fiber は、元の表現可能前層から F への右写像空間と厳密に同型。 -/
def presheafYonedaSliceFiberMappingIso (x : C _⦋0⦌) :
    vertexFiber (presheafYonedaSliceProjection F) (ULift.up x) ≅
      pinchedHom (functorVertex (representablePresheafInfinity x)) (functorVertex F) :=
  vertexFiberPullbackIso
      (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex F))) (yonedaInfinityMap C)
      (ULift.up x) ≪≫
    eqToIso (congrArg (vertexFiber
      (sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex F))))
      (yonedaInfinityMap_vertex x)) ≪≫
    (pinchedHomSliceFiberIso
      (functorVertex (representablePresheafInfinity x)) (functorVertex F)).symm

/-- 元の同じ fiber は、元の前層 F の指定対象での値の宇宙持ち上げと同値。 -/
def presheafYonedaSliceFiberValueEquivalence (x : C _⦋0⦌) :
    QCatEquivalence (vertexFiber (presheafYonedaSliceProjection F) (ULift.up x))
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up (SSet.opObjEquiv.symm x)))).obj) :=
  (qCatEquivalenceOfIso (presheafYonedaSliceFiberMappingIso F x)).trans
    (yonedaPresheafEvaluationEquivalence x F)

end SerrePositivity.InfinityCategories.F2.Ind
