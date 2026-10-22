module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeEvaluation
public import SerrePositivity.InfinityCategories.F1.SmallLeftUnstraighteningOverMap
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFiberTransport
public import SerrePositivity.InfinityCategories.F1B.KanVertexFiberSquareIso

/-!
概要：同じ共同係数分類の小さい値 fiber を、元の native 評価頂点の pointed fiber へ移す。
方針：元の縮小 fiber 同型・元の引き戻し fiber 同型・厳密な評価頂点の式を合成する。
規約：元の値 fiber と指定頂点を保持。使われ方：元の係数評価の値比較の因子分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I) (x : C _⦋0⦌)
local notation "Q" => weightedLeftCoefficientDiagram (F ⋙ rightFibrationOppositeOrdinary C) i
local notation "z" => weightedCoefficientNativeEvaluationVertex κ F hF i x

/-- 同じ係数分類の元の小さい値 fiber は、元の native 評価頂点の pointed fiber と同型。 -/
def weightedCoefficientNativeFiberPointedIso :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (vertexFiber (smallLeftUnstraighteningProjection Q) (SSet.opObjEquiv.symm x)) ≅
        vertexFiber pointedSpaceProjection z :=
  smallLeftUnstraighteningFiberIso Q (SSet.opObjEquiv.symm x) ≪≫
    leftUnstraighteningFiberIso Q (ULift.up (SSet.opObjEquiv.symm x)) ≪≫
      eqToIso (congrArg (vertexFiber pointedSpaceProjection)
        (weightedCoefficientNativeEvaluationVertex_eq κ F hF i x).symm)

/-- 同じ pointed fiber 比較を全体へ含めると、元の係数全空間の比較を回収する。 -/
lemma weightedCoefficientNativeFiberPointedIso_ι :
    (weightedCoefficientNativeFiberPointedIso κ F hF i x).hom ≫
      vertexFiberι pointedSpaceProjection z =
      (SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberι (smallLeftUnstraighteningProjection Q) (SSet.opObjEquiv.symm x)) ≫
          (smallLeftUnstraighteningIso Q).hom ≫ pullback.fst pointedSpaceProjection Q := by
  simp only [weightedCoefficientNativeFiberPointedIso, Iso.trans_hom, Category.assoc]
  rw [F1B.kanVertexFiberι_eqTransport pointedSpaceProjection
    (weightedCoefficientNativeEvaluationVertex_eq κ F hF i x).symm]
  have hl := congrArg (fun f ↦
    (smallLeftUnstraighteningFiberIso Q (SSet.opObjEquiv.symm x)).hom ≫ f)
    (leftUnstraighteningFiberIso_hom_ι Q (ULift.up (SSet.opObjEquiv.symm x)))
  have hs := congrArg (fun f ↦ f ≫ pullback.fst pointedSpaceProjection Q)
    (smallLeftUnstraighteningFiberIso_hom_ι Q (SSet.opObjEquiv.symm x))
  exact hl.trans (by simpa only [Category.assoc] using hs)

end SerrePositivity.InfinityCategories.F2.Ind
