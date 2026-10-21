module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSecondHomSpan
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSecondTriangleHomLong
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSecondTriangleHomMiddle

/-!
概要：元の第二面の Hom への射影は、分解三角形の同じ両端の分類 Hom を回収する。
方針：同じ三角形の共有頂点を、元の三つの比較 path で評価する。
規約：元の第二面と既存の比較 span の両評価を保持する。
使われ方：二段の元の Hom 輸送を第二面の元の Hom へ降ろす。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ第二面の一評価は、元の結合比較 Hom の一評価を回収する。 -/
lemma cocartesianBaseChangeSecondHomDecomposition_one :
    cocartesianBaseChangeSecondTriangleHomLong l k p q ≫
        cocartesianBaseChangeSecondHomSpanOne l k p q =
      cocartesianBaseChangeSecondTriangleHomSecond l k p q ≫
        cocartesianBaseChangeAssociativityHomSpanOne l k p q := by
  have h : equivalenceTriangleFace
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) 1 ≫
        equivalencePathEndpoint _ 1 = equivalenceTriangleFace
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) 0 ≫
        equivalencePathEndpoint _ 1 := by
    rw [equivalenceTriangleFace_endpoint, equivalenceTriangleFace_endpoint]
    exact congrArg (equivalenceTriangleEvaluation _) (show
      (1 : Fin 3).succAbove (1 : Fin 2) = (0 : Fin 3).succAbove (1 : Fin 2) by decide)
  have hL : intervalMappingUncurry (cocartesianBaseChangeSecondTriangleHomLong l k p q ≫
      cocartesianBaseChangeSecondHomSpanOne l k p q) =
      intervalMappingUncurry (cocartesianBaseChangeSecondTriangleHomLong l k p q) ≫
        equivalencePathEndpoint
          (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) 1 := by
    exact intervalHomPathEndpoint_uncurry (cocartesianBaseChangeSecondHomPath l k) 1
      (coherentNerveVertex p) (coherentNerveVertex q)
      (cocartesianBaseChangeSecondHomPath_one_vertex l k p)
      (cocartesianBaseChangeSecondHomPath_one_vertex l k q) _
  have hR : intervalMappingUncurry (cocartesianBaseChangeSecondTriangleHomSecond l k p q ≫
      cocartesianBaseChangeAssociativityHomSpanOne l k p q) =
      intervalMappingUncurry (cocartesianBaseChangeSecondTriangleHomSecond l k p q) ≫
        equivalencePathEndpoint
          (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) 1 := by
    exact intervalHomPathEndpoint_uncurry (cocartesianBaseChangeAssociativityHomPath l k) 1
      (coherentNerveVertex p) (coherentNerveVertex q)
      (cocartesianBaseChangeAssociativityHomPath_one_vertex l k p)
      (cocartesianBaseChangeAssociativityHomPath_one_vertex l k q) _
  have hF : intervalMappingUncurry (cocartesianBaseChangeSecondTriangleHomLong l k p q) =
      intervalMappingUncurry (𝟙 (cocartesianBaseChangeSecondTriangleHomSpace l k p q)) ≫
        equivalenceTriangleFace _ 1 := by
    unfold cocartesianBaseChangeSecondTriangleHomLong intervalHomFamilyProjection
    exact intervalMappingPostOfEq_universal_uncurry _ _ _ _ _
  have hG : intervalMappingUncurry (cocartesianBaseChangeSecondTriangleHomSecond l k p q) =
      intervalMappingUncurry (𝟙 (cocartesianBaseChangeSecondTriangleHomSpace l k p q)) ≫
        equivalenceTriangleFace _ 0 := by
    unfold cocartesianBaseChangeSecondTriangleHomSecond intervalHomFamilyProjection
    exact intervalMappingPostOfEq_universal_uncurry _ _ _ _ _
  apply intervalMappingUncurry_injective
  rw [hL, hR, hF, hG]
  simpa only [Category.assoc] using congrArg (fun f ↦ intervalMappingUncurry
    (𝟙 (cocartesianBaseChangeSecondTriangleHomSpace l k p q)) ≫ f) h

end SerrePositivity.InfinityCategories
