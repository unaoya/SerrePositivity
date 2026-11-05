module

public import SerrePositivity.InfinityCategories.F2.Tensor.SetSectionsSieveNaturality
public import SerrePositivity.InfinityCategories.F2.Tensor.SetSectionsLimitNaturality

/-!
概要：評価錐の三角形を、全写像空間のホモトピー圏の等式として取り出す。
規約：G8 の切断比較との照合は別の課題であり、この等式だけでは②を主張しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.SetWeight
open HomotopyLimits

/-- 評価から指定極限への二経路は、全写像空間を対象とするホモトピー圏で等しい。 -/
lemma sieveEvaluation_postcompose_homMk_eq
    {C : Type u} [SmallCategory C] {U : C} {E : SSet.{u + 1}} [Quasicategory E]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve Cᵒᵖ) ⟶ E)
    (S : Sieve U) (M : E _⦋0⦌)
    (cS : JoinCone (diagram S.functor F)) (hcS : IsLimitCone cS)
    (cU : JoinCone (diagram (yoneda.obj U) F)) (hcU : IsLimitCone cU) :
    Truncated.HomotopyCategory.homMk
      (coherentNerveEdge (C := KanObject.{u + 1})
        (X := ⟨pinchedHom M
          (F.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Opposite.op U)))), inferInstance⟩)
        (Y := ⟨pinchedHom M cS.vertex, inferInstance⟩)
        (PinchedInterval.postcompose M (Truncated.HomotopyCategory.homMk
            (representableEvaluationMap F cU hcU).toTruncated) ≫
          PinchedInterval.postcompose M (Truncated.HomotopyCategory.homMk
            (sieveSectionsMap S F cS hcS cU hcU).toTruncated) :
          pinchedHom M (F.app (Opposite.op ⦋0⦌)
            (ULift.up (nerveVertex (Opposite.op U)))) ⟶ pinchedHom M cS.vertex)).toTruncated =
    Truncated.HomotopyCategory.homMk
      (coherentNerveEdge (C := KanObject.{u + 1})
        (X := ⟨pinchedHom M
          (F.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Opposite.op U)))), inferInstance⟩)
        (Y := ⟨pinchedHom M cS.vertex, inferInstance⟩)
        (PinchedInterval.postcompose M (Truncated.HomotopyCategory.homMk
          (sieveEvaluationMap F S cS hcS).toTruncated))).toTruncated :=
  coherentKanEdge_homMk_eq_of_functorIso
    (sieveEvaluation_postcomposeIso F S M cS hcS cU hcU)

end SerrePositivity.InfinityCategories.SetWeight
